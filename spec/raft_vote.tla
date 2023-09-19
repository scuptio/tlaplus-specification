--------------------------------- MODULE raft_vote ---------------------------------

EXTENDS channel, history, raft_common, Naturals, FiniteSets, Sequences, TLC

CONSTANT ENABLE_ACTION
CONSTANT MAX_TERM
CONSTANT VALUE
CONSTANT ENABLE_HISTORY
CONSTANT NODE_ID

VARIABLE v_voted_for
VARIABLE v_vote_granted
VARIABLE v_state


VARIABLE v_log
VARIABLE v_snapshot
VARIABLE v_current_term

VARIABLE __action__
VARIABLE v_history

v_vars == <<
    v_voted_for,
    v_vote_granted,
    v_state,
    v_log,
    v_current_term,
    v_history
>>

VarsVote == <<
    v_vars,
    __action__,
    VarsChannel
>>

InitVote ==
    /\ InitSaftyStateDefault(
        v_state,
        v_current_term,
        v_log,
        v_snapshot,
        v_voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM
        )
    /\ v_vote_granted = InitVoteGranted(NODE_ID)
    /\ v_history = InitHistory
    /\ InitChannel
    /\ __action__ = InitActionEmpty


__PreCandidate ==
    PreCandidate


----


\* NODE_ID i times out and starts a new election.
VoteRequestVote(i, max_term) == 
    /\ TermLE(i, v_current_term, max_term)
    /\ v_state[i] \in {Candidate}
    /\ v_voted_for[i] = {}
    /\ v_current_term' = [v_current_term EXCEPT ![i] = v_current_term[i] + 1]
    /\ v_voted_for' = [v_voted_for EXCEPT ![i] = {i}]
    /\ v_vote_granted'   = [v_vote_granted EXCEPT ![i] = {i}]
    /\  LET msgs ==   
            [
                msg_type        : {VoteRequest},
                term            : {v_current_term[i] + 1},
                last_log_term   : {LastLogTerm(v_log[i])},
                last_log_index  : {Len(v_log[i])},
                source          : {i},
                dest            : NODE_ID \ {i}
            ]
        IN ChannelSend' = WithMessageSet(msgs, ChannelSend)
    /\ NewAction(__action__, i, i, "RequestVote", "Internal", {}, ENABLE_ACTION)
    /\ UNCHANGED <<ChannelRecv, 
            v_log, 
            v_state,
            v_history
            >>

----

__HandleNope ==
    /\ UNCHANGED <<v_vars, ChannelSend>>

\* Network v_state transitions
VoteUpdateTerm(msg) ==
    /\ msg.msg_type = VoteRequest
    /\ "term" \in DOMAIN msg
    /\  LET  term == msg.term
            i == msg.dest
        IN
        /\ term > v_current_term[i]
        /\ v_current_term' = [v_current_term EXCEPT ![i] = term]
        /\ v_state' = [v_state EXCEPT ![i] = Follower]
        /\ v_voted_for' = [v_voted_for EXCEPT ![i] = {}]
        /\ NewAction(__action__, i, i, "VoteUpdateTerm", "Internal", [term |-> term], ENABLE_ACTION)
        /\ UNCHANGED <<ChannelSend, ChannelRecv, v_log, v_history>>

__HandleVoteRequest(i, j, m) ==
    LET term == m.term
        last_log_term == m.last_log_term
        last_log_index == m.last_log_index
        grant == VoteCanGrant(
                    v_current_term,
                    v_log,
                    v_voted_for,
                    j,
                    i,
                    m.term, 
                    m.last_log_term, 
                    m.last_log_index)
        reply ==  [
                msg_type        |-> VoteResponse,
                term            |-> v_current_term[i],
                v_granted    |-> grant,
                source          |-> i,
                dest            |-> j
            ]
    IN 
    /\ m.term <= v_current_term[i]
    /\ (\/ (/\ grant
            /\ v_voted_for' = [v_voted_for EXCEPT ![i] = {j}] 
           )
        \/ (/\ ~grant
            /\ UNCHANGED v_voted_for 
           )
        )
    /\ ChannelSend' = WithMessage(reply, ChannelSend)               
    /\ UNCHANGED << 
            v_current_term,
            v_vote_granted,
            v_log, 
            v_state,
            v_history
        >>

BecomeLeader(i) ==
    /\ v_vote_granted[i] \in QuorumOf(NODE_ID)
    /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] = {}]
    /\ v_state' = [v_state EXCEPT ![i] = Leader]
    
    /\ LET o == 
        [
            election |-> 
            [
               leader |-> i,
               term |-> v_current_term[i],
               log |-> v_log[i],
               snapshot |-> [term |-> 0, index |-> 0]
            ]
        ] 
        IN v_history' = AppendHistory(v_history, o, ENABLE_HISTORY)
    /\ NewAction(__action__, i, i, "BecomeLeader", "Internal", {}, ENABLE_ACTION)
    /\ UNCHANGED <<ChannelSend, ChannelRecv, v_current_term, v_voted_for, v_log>>

\* NODE_ID i receives a RequestVote response from server j with
\* m.term = v_current_term[i].
__HandleVoteResponse(i, j, m) ==
    \* This tallies votes even when the current v_state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.term = v_current_term[i]
    /\ v_state[i] = Candidate 
    /\ (\/( /\ m.v_granted
            /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] =
                                    v_vote_granted[i] \cup {j}]                
            )
        \/ ( /\ ~m.v_granted
                /\ UNCHANGED <<v_vote_granted, v_state>>
            )
        )   
     /\ UNCHANGED <<v_current_term, v_voted_for, v_log, v_state>>

HandleVoteRequest(msg) ==
    /\ msg.msg_type = VoteRequest
    /\ ClearRecvMessage(msg)
    /\ (\/ __HandleVoteRequest(msg.dest, msg.source, msg)
        \/ __HandleNope)
    /\ NewAction(__action__, msg.dest, msg.dest, "HandleVoteRequest", "Internal", msg, ENABLE_ACTION)
    /\ UNCHANGED <<v_history>>
             
HandleVoteResponse(msg) ==
    /\ msg.msg_type = VoteResponse
    /\ ClearRecvMessage(msg)
    /\ (\/ __HandleVoteResponse(msg.dest, msg.source, msg)
        \/ __HandleNope)
    /\ NewAction(__action__, msg.dest, msg.dest, "HandleVoteResponse", "Internal", msg, ENABLE_ACTION)
    /\ UNCHANGED <<ChannelSend, v_history>>

\* End of message handlers.
----

VoteRestartNode(i) ==
    /\ RestartNode(i)
    /\ NewAction(__action__, i, i, "VoteRestartNode", "Internal", {}, ENABLE_ACTION)
    /\ v_state' = [v_state EXCEPT ![i] = Follower]
    /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] = {}]
    /\ UNCHANGED <<
        v_current_term, 
        v_log,
        v_voted_for,
        v_history
      >>

VoteRecvMessage(m) ==
    /\ m.msg_type \in {VoteRequest, VoteResponse}
    /\ RecvMessage(m) 
    /\ NewAction(__action__, m.source, m.dest, "VoteReceiveMessage", "Input", m, ENABLE_ACTION)
    /\ UNCHANGED <<v_vars, ChannelSend, v_history>>

NextVote ==
    \/ \E m \in ChannelSend : VoteRecvMessage(m)
    \/ \E i \in NODE_ID : VoteRestartNode(i)
    \/ \E i \in NODE_ID : BecomeLeader(i)
    \/ (\/ \E i \in NODE_ID : VoteRequestVote(i, MAX_TERM)
        \/ \E m \in ChannelRecv : HandleVoteRequest(m)
        \/ \E m \in ChannelRecv : HandleVoteResponse(m)
       )
    
SpecVote == 
    /\ InitVote 
    /\ [][NextVote]_VarsVote

MappingVote == 
  INSTANCE abstract_vote WITH
    ENABLE_ACTION <- FALSE,
    MAX_TERM <- MAX_TERM,
    VALUE <- VALUE,
    __action__ <- {},
    av_current_term <- v_current_term,
    av_log <- v_log,
    av_state <- v_state,
    av_voted_for <- v_voted_for,
    av_snapshot <- v_snapshot
\* There is at most one leader per term:
AtMostOneLeaderPerTerm ==
    InvariantAtMostOneLeaderPerTerm(v_history, ENABLE_HISTORY)

             
RefinementVote == MappingVote!SpecAV
===============================================================================


