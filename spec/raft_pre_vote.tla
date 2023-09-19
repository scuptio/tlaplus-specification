--------------------------------- MODULE raft_pre_vote ---------------------------------


EXTENDS channel, raft_common, Naturals, FiniteSets, Sequences, TLC, StateStore

CONSTANT ENABLE_ACTION
CONSTANT ENABLE_RESTART
CONSTANT MAX_TERM
CONSTANT VALUE
CONSTANT NODE_ID
CONSTANT INIT_JSON_PATH

VARIABLE pv_message

\* read only variable
VARIABLE pv_current_term
VARIABLE pv_log
VARIABLE pv_snapshot
VARIABLE pv_voted_for

\* write variable
VARIABLE pv_granted
VARIABLE pv_state

VARIABLE __action__


VarsPV == <<
    pv_current_term,
    pv_state,
    pv_log,
    pv_granted,
    pv_voted_for,
    pv_snapshot,
    pv_message
>>

VarsAllPV == <<
    VarsPV,
    __action__
    >>

_HandleInitNodePayload(_nid) ==
    [
        state |-> pv_state[_nid],
        current_term |-> pv_current_term[_nid],
        log |-> pv_log[_nid],
        snapshot |-> pv_snapshot[_nid],
        voted_for |-> pv_voted_for[_nid]
    ]
    
InitPV ==
    /\ LET value == DeserializeValue(INIT_JSON_PATH)
       IN (
        /\ pv_state = value.state
        /\ pv_current_term = value.current_term
        /\ pv_log = value.log
        /\ pv_snapshot = value.snapshot
        /\ pv_voted_for = value.voted_for
       )
    /\ InitSaftyStateDefault(
        pv_state,
        pv_current_term,
        pv_log,
        pv_snapshot,
        pv_voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM
        )
    /\ pv_granted = InitVoteGranted(NODE_ID)
    /\ pv_message = {}
    /\ __action__ = ActionSeqOfEachNodeHandle(
                NODE_ID, 
                ActionInput, 
                __MsgInitRaft, 
                _HandleInitNodePayload, 
                ENABLE_ACTION) 

    
PVRequestVote(i, _max_term) == 
   /\ TermLE(i, pv_current_term, _max_term)
   /\ pv_state[i] \in {Follower}
   /\ pv_state' = [pv_state EXCEPT ![i] = PreCandidate]
   /\ pv_granted' = [pv_granted EXCEPT ![i] = {i}]
   /\ LET m_set == [
                source : {i},
                dest : NODE_ID \ {i},
                name : {PreVoteRequest},
                payload : {[                
                    next_term       |-> pv_current_term[i] + 1,
                    last_log_term   |-> LastLogTerm(pv_log[i]),
                    last_log_index  |-> Len(pv_log[i])
                ]}
            ]
            request_vote == Message(i, i, __MsgRequestPreVote, {})
            request_vote_action == Action(ActionInput, request_vote, ENABLE_ACTION) 
      IN /\ pv_message' = WithMessageSet(m_set, pv_message)
         /\ __action__' = SendMessageAction(request_vote_action, m_set, ENABLE_ACTION)
   /\ UNCHANGED <<
        pv_snapshot,
        pv_log, 
        pv_current_term,
        pv_voted_for
      >>

PVCanGrant(src, dst, term, last_log_term, last_log_index) ==
    /\ IsLastLogTermIndexOK(pv_log, dst, last_log_term, last_log_index)
    /\ (\/ term > pv_current_term[dst]
        \/  (/\ term = pv_current_term[dst]
            /\ (\/ pv_voted_for[dst] = {}
                \/ pv_voted_for[dst] = {src}
                )
            )
        )
        
HandlePVRequest(msg) ==
    /\ msg.name = PreVoteRequest
    /\ (LET grant == VoteCanGrant(
                    pv_current_term,
                    pv_log,
                    pv_voted_for,
                    msg.source, 
                    msg.dest, 
                    msg.payload.next_term, 
                    msg.payload.last_log_term, 
                    msg.payload.last_log_index)
               actions == ReceiveMessageAction(<<>>, msg, ENABLE_ACTION)
               reply ==  
                    Message(msg.dest, msg.source, PreVoteResponse,
                        [
                             next_term |-> msg.payload.next_term,
                             pv_granted |-> grant
                        ]
                    )
        IN /\ pv_message' = WithMessage(reply, pv_message)
           /\ __action__' = SendMessageAction(actions, {reply}, ENABLE_ACTION)
      )  
   /\ UNCHANGED <<
        pv_snapshot,
        pv_granted,
        pv_state,
        pv_current_term,
        pv_log, 
        pv_voted_for    
     >>
        
BecomeCandidate(i) ==
    /\ pv_state[i] = PreCandidate 
    /\ pv_granted[i] \in QuorumOf(NODE_ID)
    /\ pv_state' = [pv_state EXCEPT ![i] = Candidate]
    /\ pv_granted' = [pv_granted EXCEPT ![i] = {}]
    /\ LET message == Message(i, i , __MsgBecomeCandidate, {})
       IN __action__' = Action(ActionInternal, message, ENABLE_ACTION)        
    /\ UNCHANGED <<
            pv_snapshot,
            pv_message,
            pv_current_term,
            pv_log,         
            pv_voted_for
        >>

               
HandlePreVoteResponse(msg) ==
    /\ msg.name = PreVoteResponse
    /\ msg.payload.next_term = pv_current_term[msg.dest] + 1
    /\ pv_state[msg.dest] = PreCandidate 
    /\ (\/ (/\ msg.payload.pv_granted
            /\ pv_granted' = [
                pv_granted EXCEPT ![msg.dest] =
                pv_granted[msg.dest] \cup {msg.source}
              ]
           )
        \/ UNCHANGED <<pv_granted>>
       )
   /\ __action__' = ReceiveMessageAction(<<>>, msg, ENABLE_ACTION)
   /\ UNCHANGED <<
        pv_snapshot,
        pv_message,
        pv_state,
        pv_current_term,
        pv_log,         
        pv_voted_for>>

PVRestartNode(i) ==
    /\ LET message == Message(i, i , __MsgRestartNode, {})
       IN __action__' = Action(ActionInput, message, ENABLE_ACTION) 
    /\ pv_state' = [pv_state EXCEPT ![i] = Follower]
    /\ pv_granted' = [pv_granted EXCEPT ![i] = {}]
    /\ UNCHANGED <<
        pv_message,
        pv_snapshot,
        pv_current_term, 
        pv_log,
        pv_voted_for
      >>

NextPV ==
    \/ ENABLE_RESTART /\ \E i \in NODE_ID : PVRestartNode(i)
    \/ \E i \in NODE_ID : BecomeCandidate(i)
    \/ (\/ \E i \in NODE_ID : PVRequestVote(i, MAX_TERM)
        \/ \E m \in pv_message : HandlePVRequest(m)
        \/ \E m \in pv_message : HandlePreVoteResponse(m)
       )

SpecPV == 
    /\ InitPV 
    /\ [][NextPV]_VarsAllPV

Spec == SpecPV


===============================================================================
