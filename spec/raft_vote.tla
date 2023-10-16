--------------------------------- MODULE raft_vote ---------------------------------

EXTENDS 
    action, 
    raft_common, 
    history, 
    Naturals, 
    FiniteSets, 
    Sequences, 
    TLC
    
CONSTANT MAX_TERM
CONSTANT VALUE
CONSTANT RECONFIG_VALUE
CONSTANT NODE_ID
CONSTANT CHECK_SAFETY
CONSTANT ENABLE_ACTION
CONSTANT STATE_DB_PATH
----


VARIABLE v_state
VARIABLE v_current_term
VARIABLE v_log
VARIABLE v_snapshot
VARIABLE v_voted_for
VARIABLE v_vote_granted
VARIABLE v_history
VARIABLE v_channel
VARIABLE __action__



vars == <<
    v_state,
    v_current_term,
    v_log, 
    v_snapshot,
    v_voted_for,
    v_vote_granted,
    v_channel,
    v_history,
    __action__
>>

vars_view == <<
    v_state,
    v_current_term,
    v_log, 
    v_snapshot,
    v_voted_for,
    v_vote_granted,
    v_channel
>>

__ActionInit == "DTMTesting::Setup"
__ActionBecomeLeader == "DTMTesting::BecomeLeader"
__ActionTimeoutRequestVote == "DTMTesting::TimeoutRequestVote"
__ActionRestartNode == "DTMTesting::Restart"

_RaftVariables(_nid) ==
    [
        state |-> v_state[_nid],
        current_term |-> v_current_term[_nid],
        log |-> v_log[_nid],
        snapshot |-> v_snapshot[_nid],
        voted_for |-> v_voted_for[_nid]
    ]


InitVote ==
    /\ ( IF STATE_DB_PATH = "" THEN
        InitSaftyStateTrival(
                v_state,
                v_current_term,
                v_log,
                v_snapshot,
                v_voted_for,
                NODE_ID,
                VALUE,
                MAX_TERM,
                1, 
                1
            )
      ELSE
        /\ DBOpen(STATE_DB_PATH)
        /\ LET s == QueryAllStates
           IN /\ \E e \in s:
                /\ v_state = e.state
                /\ v_current_term = e.current_term
                /\ v_log = e.log
                /\ v_snapshot = e.snapshot
                /\ v_voted_for = e.voted_for
       )
    /\ v_vote_granted = InitVoteGranted(NODE_ID)
    /\ v_history = InitHistory
    /\ v_channel = {}
    /\ LET actions == ActionsFromHandle(
            _RaftVariables,
            NODE_ID, 
            ActionInput, 
            __ActionInit 
            ) 
        IN InitAction(
            __action__,
            actions
        )



----


\* NODE_ID _node_id times out and starts a new election.
VoteTimeoutRequestVote(_node_id, _max_term) == 
    /\ TermLE(_node_id, v_current_term, _max_term)
    /\ v_state[_node_id] = Follower
    /\ v_state' = [v_state EXCEPT ![_node_id] = Candidate]
    /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = v_current_term[_node_id] + 1]
    /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _node_id]
    /\ v_vote_granted'   = [v_vote_granted EXCEPT ![_node_id] = {_node_id}]
    /\  LET 
    
            payload == [
                term            |-> v_current_term[_node_id] + 1,
                last_log_term   |-> LastLogTerm(v_log[_node_id]),
                last_log_index  |-> Len(v_log[_node_id])
            ]  
            messages == MessageSet({_node_id}, NODE_ID \ {_node_id}, VoteRequest,  payload)
            actions_input == Action(ActionInput, Message(_node_id, _node_id, __ActionTimeoutRequestVote, {}))
            actions_output == Actions(ActionOutput, messages)
        IN /\ v_channel' = WithMessageSet(messages, v_channel)
           /\ SetAction(__action__, actions_input \o actions_output)
    /\ UNCHANGED <<
            v_log, 
            v_snapshot,
            v_history
            >>

__HandleVoteRequest(_node_id, _from_node_id, _msg_payload, _action_seq) ==
    LET term == _msg_payload.term
        last_log_term == _msg_payload.last_log_term
        last_log_index == _msg_payload.last_log_index
        grant == VoteCanGrant(
                    v_current_term,
                    v_log,
                    v_voted_for,
                    _from_node_id,
                    _node_id,
                    _msg_payload.term, 
                    _msg_payload.last_log_term, 
                    _msg_payload.last_log_index)
        payload == [
                term |-> v_current_term[_node_id],
                vote_granted |-> grant
            ]
        reply ==  Message(_node_id, _from_node_id, VoteResponse, payload)
    IN /\  (IF _msg_payload.term <= v_current_term[_node_id] THEN

                    /\ (\/ (/\ grant
                            /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _from_node_id] 
                           )
                        \/ (/\ ~grant
                            /\ UNCHANGED v_voted_for 
                           )
                       )
                    /\ SetAction(__action__, AppendActionSeq(_action_seq, Action(ActionOutput, reply)))
                    /\ UNCHANGED <<v_current_term>>        
             ELSE /\ (\/ ( /\ grant 
                           \* update voted for and current_term
                           /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _from_node_id] 
                           /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term]
                          )
                      \/ ( /\ ~grant
                           /\ UNCHANGED <<v_voted_for, v_current_term>>
                         )     
                     )
                  /\ SetAction(__action__, _action_seq)
             ) 
        /\ v_channel' = WithMessage(reply, v_channel)   
        /\ UNCHANGED << 
                v_vote_granted,
                v_log, 
                v_snapshot,
                v_state,
                v_history
            >>

HandleVoteRequest(msg) ==
    /\ msg.name = VoteRequest
    /\ LET _action_seq == Action(ActionInput, msg)
       IN  __HandleVoteRequest(msg.dest, msg.source, msg.payload, _action_seq)
    /\ UNCHANGED <<v_history>>
    
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
        IN v_history' = AppendHistory(v_history, o, CHECK_SAFETY)
    /\ LET action == Action(ActionInternal, Message(i, i, __ActionBecomeLeader, {}))
       IN SetAction(__action__, action)
    /\ UNCHANGED <<v_channel, v_current_term, v_voted_for, v_log, v_snapshot>>

\* NODE_ID i receives a RequestVote response from server j with
\* m.term = v_current_term[i].
__HandleVoteResponse(i, _from_node, _m) ==
    \* This tallies votes even when the current v_state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ IF _m.term = v_current_term[i] THEN
            /\ v_state[i] = Candidate 
            /\ (\/( /\ _m.vote_granted
                    /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] =
                                            v_vote_granted[i] \cup {_from_node}]                
                    )
                \/ ( /\ ~_m.vote_granted
                     /\ UNCHANGED <<v_vote_granted, v_state>>
                    )
                )   
             
        ELSE
            /\ UNCHANGED <<v_vote_granted, v_state>>
    /\ UNCHANGED <<v_current_term, v_voted_for, v_log, v_snapshot, v_state>>
             
HandleVoteResponse(msg) ==
    /\ msg.name = VoteResponse
    /\ __HandleVoteResponse(msg.dest, msg.source, msg.payload)
    /\ LET action_seq == Action(ActionInternal, msg)
       IN SetAction(__action__, action_seq)
    /\ UNCHANGED <<v_channel, v_history>>

\* End of message handlers.
----

VoteRestartNode(i) ==
    /\ LET action == Action(ActionInternal, MessageLocal(i, __ActionRestartNode,  {}))
       IN SetAction(__action__,  action)
    /\ v_state' = [v_state EXCEPT ![i] = Follower]
    /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] = {}]
    /\ UNCHANGED <<
        v_channel,
        v_current_term, 
        v_snapshot,
        v_log,
        v_voted_for,
        v_history
      >>


NextVote ==
    \/ \E m \in v_channel : HandleVoteRequest(m)
    \/ \E m \in v_channel : HandleVoteResponse(m)
    \/ \E i \in NODE_ID : VoteRestartNode(i)
    \/ \E i \in NODE_ID : BecomeLeader(i)
    \/ \E i \in NODE_ID : VoteTimeoutRequestVote(i, MAX_TERM)

    
Spec == 
    /\ InitVote 
    /\ [][NextVote]_vars


===============================================================================


