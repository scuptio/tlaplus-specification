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
CONSTANT DB_ACTION_PATH
----


VARIABLE v_state
VARIABLE v_current_term
VARIABLE v_log
VARIABLE v_snapshot
VARIABLE v_voted_for
VARIABLE v_vote_granted
VARIABLE v_history
VARIABLE v_channel
VARIABLE v_pc
VARIABLE v_pc_context
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
    v_pc,
    v_pc_context,
    __action__
>>

vars_view == <<
    v_state,
    v_current_term,
    v_log, 
    v_snapshot,
    v_voted_for,
    v_vote_granted,
    v_pc,
    v_channel
>>



vars_except_action_and_pc == <<
    v_state,
    v_current_term,
    v_log, 
    v_snapshot,
    v_voted_for,
    v_vote_granted,
    v_channel,
    v_history
>>


ContextNull == [null |-> "null"]
ContextHasMessage(_context) == "message" \in DOMAIN _context

_RaftVariables(_nid) ==
    [
        state |-> v_state[_nid],
        current_term |-> v_current_term[_nid],
        log |-> v_log[_nid],
        snapshot |-> v_snapshot[_nid],
        voted_for |-> v_voted_for[_nid],
        vote_granted |-> v_vote_granted[_nid],
        commit_index |-> 0,
        match_index |-> {},
        next_index |-> [n \in NODE_ID |-> 1]
    ]


_RaftVariablesNew(_nid, _context) ==
    [
        state |-> IF "state" \in DOMAIN _context THEN _context.state[_nid] ELSE v_state[_nid],
        current_term |-> IF "current_term" \in DOMAIN _context THEN _context.current_term[_nid] ELSE v_current_term[_nid],
        log |-> IF "log" \in DOMAIN _context THEN _context.log[_nid] ELSE v_log[_nid],
        snapshot |-> IF "snapshot" \in DOMAIN _context THEN _context.snapshot[_nid] ELSE v_snapshot[_nid],
        voted_for |-> IF "voted_for" \in DOMAIN _context THEN _context.voted_for[_nid] ELSE v_voted_for[_nid],
        vote_granted |-> IF "vote_granted" \in DOMAIN _context THEN _context.vote_granted[_nid] ELSE v_vote_granted[_nid],
        commit_index |-> 0,
        match_index |-> {},
        next_index |-> [n \in NODE_ID |-> 1]
    ]

ActionSeqCheckNew(_node_id, _context) ==
    ActionsFromHandleContext(
            _RaftVariablesNew,
            {_node_id}, 
            ActionCheck, 
            __ActionCheck,
            _context
       )

ActionSeqCheck(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            {_node_id}, 
            ActionCheck, 
            __ActionCheck
       )


       
ActionSeqSetup ==
    ActionsFromHandle(
            _RaftVariables,
            NODE_ID, 
            ActionSetup, 
            __ActionInit
       )

SaveActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__', DB_ACTION_PATH)

InitSaveActions == 
    /\ DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)
        
Init ==
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
        /\ LET s == QueryAllValues(STATE_DB_PATH)
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
    /\ v_pc = [i \in NODE_ID |-> [state |-> "next"]]
    /\ v_pc_context = [i \in NODE_ID |-> ContextNull]
    /\ LET actions == ActionSeqSetup
        IN InitAction(
            __action__,
            actions,
            actions
        )
    /\ InitSaveActions


----


\* NODE_ID _node_id times out and starts a new election.
VoteTimeoutRequestVote(_node_id, _max_term) == 
    /\ v_pc[_node_id].state = "next"
    /\ TermLE(_node_id, v_current_term, _max_term)
    /\ v_state[_node_id] = Follower
    /\ v_state' = [v_state EXCEPT ![_node_id] = Candidate]
    /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = v_current_term[_node_id] + 1]
    /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _node_id]
    /\ v_vote_granted'   = [v_vote_granted EXCEPT ![_node_id] = {_node_id}]
    /\  LET 
    
            payload == [
                term            |-> v_current_term[_node_id] + 1,
                last_log_term   |-> LastLogTerm(v_log[_node_id], v_snapshot[_node_id]),
                last_log_index  |-> Len(v_log[_node_id]),
                source_nid |-> _node_id
            ]  
            messages == MessageSet({_node_id}, NODE_ID \ {_node_id}, VoteRequest,  payload)
            actions_input == Action(ActionInput, MessageNP(_node_id, _node_id, __ActionRequestVote))
            actions_output == Actions(ActionOutput, messages)
            actions0 == ActionSeqCheck(_node_id)
            actions == ActionSeqSetup
        IN /\ v_channel' = WithMessageSet(messages, v_channel)
           /\ SetAction(__action__, actions, actions0 \o actions_input \o actions_output)
    /\ UNCHANGED <<
            v_log, 
            v_snapshot,
            v_history,
            v_pc,
            v_pc_context
            >>

__HandleVoteRequest(_node_id, _from_node_id, _msg_payload) ==
    LET term == _msg_payload.term
        last_log_term == _msg_payload.last_log_term
        last_log_index == _msg_payload.last_log_index
        grant == VoteCanGrant(
                    v_current_term,
                    v_log,
                    v_snapshot,
                    v_voted_for,
                    _from_node_id,
                    _node_id,
                    _msg_payload.term, 
                    _msg_payload.last_log_term, 
                    _msg_payload.last_log_index)
        payload == [
                term |-> term,
                vote_granted |-> grant,
                source_nid |-> _node_id
            ]
        a1 == Action(ActionInternal, MessageLocal(_node_id, __ActionHandleVoteRequest, _msg_payload))   
        reply ==  Message(_node_id, _from_node_id, VoteResponse, payload)
        a2 == Action(ActionOutput, reply)
        actions == ActionSeqSetup
    IN /\  (IF _msg_payload.term <= v_current_term[_node_id] THEN

                    /\ (\/ (/\ grant
                            /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _from_node_id] 
                           )
                        \/ (/\ ~grant
                            /\ UNCHANGED v_voted_for 
                           )
                       )
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
             ) 
        /\ SetAction(__action__, actions, a1 \o a2)
        /\ v_channel' = WithMessage(reply, v_channel)   
        /\ UNCHANGED << 
                v_vote_granted,
                v_log, 
                v_snapshot,
                v_state,
                v_history
            >>


\* NODE_ID i receives a RequestVote response from server j with
\* m.term = v_current_term[i].
__HandleVoteResponse(i, _from_node, _m) ==
    \* This tallies votes even when the current v_state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.

    /\  LET _actions == Action(ActionInternal, MessageLocal(i, __ActionHandleVoteResponse, _m))  
           actions == ActionSeqSetup
        IN 
        IF _m.term = v_current_term[i] THEN
            /\ v_state[i] \in {Candidate, Leader} 
            /\ (\/( /\ _m.vote_granted
                    /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] =
                                            v_vote_granted[i] \cup {_from_node}]    
                    /\ IF  /\ v_state[i] = Candidate
                           /\ v_vote_granted[i] \cup {_from_node} \in  QuorumOf(NODE_ID)
                       THEN
                        (     /\ LET o == 
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
                              /\ v_state' = [v_state EXCEPT ![i] = Leader]
                              /\ LET check_new == ActionSeqCheckNew(i, [vote_granted |-> v_vote_granted, state |-> v_state]) 
                                 IN SetAction(__action__, actions,  _actions \o check_new)
                          )
                       ELSE
                            
                            /\ LET check_new == ActionSeqCheckNew(i, [vote_granted |-> v_vote_granted])  
                               IN SetAction(__action__, actions, _actions \o check_new)
                            /\ UNCHANGED <<v_history, v_state>>                   
                    )
                \/ ( /\ ~_m.vote_granted
                     /\ UNCHANGED <<v_vote_granted, v_state, v_history>>
                     /\ LET check ==  ActionSeqCheck(i)
                        IN SetAction(__action__, actions,  _actions \o check)
                    )
                )   
        ELSE
            /\ UNCHANGED <<v_vote_granted, v_state, v_history>>
            /\ SetAction(__action__, actions,  _actions)
    /\ UNCHANGED <<v_current_term, v_voted_for, v_log, v_snapshot>>


_UpdateTerm(_node_id, _term) ==
    /\ IF _term > v_current_term[_node_id] THEN
           (/\ v_current_term'    = [v_current_term EXCEPT ![_node_id] = _term]
            /\ v_state'          = [v_state       EXCEPT ![_node_id] = Follower]
            /\ v_voted_for'       = [v_voted_for    EXCEPT ![_node_id] = INVALID_NODE_ID]
           )
       ELSE
            UNCHANGED <<v_current_term, v_state, v_voted_for>>
    /\ LET _a == Action(ActionInternal, MessageLocal(_node_id, __ActionHandleUpdateTerm, _term))
            actions == ActionSeqSetup
       IN SetAction(__action__, actions, _a)    
    /\ UNCHANGED<<
            v_log, 
            v_snapshot,
            v_channel,
            v_history,
            v_vote_granted
        >>

\* End of message handlers.
----

RecvMessage(m) ==
    LET m_type == m.name
        source == m.source
        dest == m.dest
        node_id == dest
        payload == m.payload
        actions1 == ActionSeqCheck(node_id)
        actions2 == Action(ActionInput, m)
        actions == actions1 \o actions2
        actions0 == ActionSeqSetup
        action_id == IdOfAction(__action__)
    IN
    CASE m_type = VoteRequest -> (
        CASE v_pc[node_id].state = "next" -> (
             /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "vote_request_step1"]]
             /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = [message |-> m, id |-> action_id]]
             /\ SetAction(__action__, actions0, actions)
             /\ UNCHANGED <<vars_except_action_and_pc>>
        )
        [] /\ v_pc[node_id].state = "vote_request_step1"
           /\ ContextHasMessage(v_pc_context[node_id])
           /\ ContinuousAction(__action__, v_pc_context[node_id])
           /\ v_pc_context[node_id].message = m
             -> (
             /\ v_pc ' = [v_pc EXCEPT ![node_id] = [ v_pc[node_id] EXCEPT !.state = "vote_request_step2"]]
             /\ v_pc_context' = [v_pc_context EXCEPT ![node_id].id =  action_id]
             /\ _UpdateTerm(node_id, payload.term)
        )
        [] /\ v_pc[node_id].state = "vote_request_step2" 
           /\ ContextHasMessage(v_pc_context[node_id])
           /\ ContinuousAction(__action__, v_pc_context[node_id])
           /\ v_pc_context[node_id].message = m 
            -> (
             /\ __HandleVoteRequest(dest, source, payload)
             /\ UNCHANGED <<v_history>>
             /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "next"]]
             /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = ContextNull]
        )
        [] OTHER -> FALSE
    )
    [] m_type = VoteResponse -> (
        CASE v_pc[node_id].state = "next" -> (
             /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "vote_response_step1"]]
             /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = [message |-> m, id |-> action_id]]
             /\ SetAction(__action__, actions0, actions)
             /\ UNCHANGED <<vars_except_action_and_pc>>
        )
        [] /\ v_pc[node_id].state = "vote_response_step1" 
           /\ ContextHasMessage(v_pc_context[node_id])
           /\ ContinuousAction(__action__, v_pc_context[node_id])
           /\ v_pc_context[node_id].message = m
            -> (
             /\ v_pc_context' = [v_pc_context EXCEPT ![node_id].id =  action_id]
             /\ v_pc ' = [v_pc EXCEPT ![node_id] = [ v_pc[node_id] EXCEPT !.state = "vote_response_step2"]]
             /\ _UpdateTerm(node_id, payload.term)
        )
        [] /\ v_pc[node_id].state = "vote_response_step2" 
           /\ ContextHasMessage(v_pc_context[node_id])
           /\ ContinuousAction(__action__, v_pc_context[node_id])
           /\ v_pc_context[node_id].message = m
            -> (
            /\ __HandleVoteResponse(m.dest, m.source, m.payload)
            /\ UNCHANGED <<v_channel>>
            /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "next"]]
            /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = ContextNull]
        )
        [] OTHER -> FALSE
    )
    [] OTHER -> (
        FALSE
    )


RestartNode(i) ==
    /\ v_pc' = [v_pc EXCEPT ![i] = [state |-> "next"]]
    /\ v_state' = [v_state EXCEPT ![i] = Follower]
    /\ v_vote_granted'   = [v_vote_granted EXCEPT ![i] = {}]
    /\ LET _a == Action(ActionInput, MessageLocalNP(i, __ActionRestartNode))
            actions0 == ActionSeqSetup
       IN SetAction(__action__, actions0, _a)    
    /\ UNCHANGED <<
            v_current_term,
            v_log, 
            v_snapshot,
            v_voted_for,
            v_channel,
            v_history,
            v_pc_context
         >>
         
Next ==
    \/ \E m \in v_channel : 
        /\ RecvMessage(m)
        /\ SaveActions
    \/ \E i \in NODE_ID : 
        /\ VoteTimeoutRequestVote(i, MAX_TERM)
        /\ SaveActions

        
Spec == 
    /\ Init 
    /\ [][Next]_vars


===============================================================================


