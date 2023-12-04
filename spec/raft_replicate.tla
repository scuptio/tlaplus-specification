--------------------------------- MODULE raft_replicate ---------------------------------



EXTENDS 
    action, 
    raft_common, 
    raft_replicate_common,  
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
CONSTANT DB_STATE_PATH
CONSTANT DB_ACTION_PATH
CONSTANT APPEND_ENTRIES_MAX
----



VARIABLE v_state
VARIABLE v_log
VARIABLE v_voted_for
VARIABLE v_snapshot
VARIABLE v_commit_index
VARIABLE v_next_index
VARIABLE v_match_index
VARIABLE v_acked_value
VARIABLE v_messages

\* readonly
VARIABLE v_current_term

VARIABLE v_history


VARIABLE v_pc
VARIABLE v_pc_context
VARIABLE __action__


vars == <<
    v_state,
    v_current_term,
    v_log, 
    v_voted_for,
    v_snapshot,
    v_commit_index,
    v_next_index,
    v_match_index,
    v_messages,
    v_pc,
    v_pc_context,
    v_history,
    v_acked_value,    
    __action__
>>

vars_view == <<
    v_state,
    v_current_term,
    v_log, 
    v_voted_for,
    v_snapshot,
    v_commit_index,
    v_next_index,
    v_match_index,
    v_messages,
    v_pc
>>

vars_except_action_and_pc == <<
    v_state,
    v_current_term,
    v_log, 
    v_voted_for,
    v_snapshot,
    v_commit_index,
    v_next_index,
    v_match_index,
    v_messages,
    v_history,
    v_acked_value
>>

vars_pc == <<v_pc, v_pc_context>>

_RaftVariables(_nid) ==
    [
        state |-> v_state[_nid],
        current_term |-> v_current_term[_nid],
        log |-> v_log[_nid],
        snapshot |-> v_snapshot[_nid],
        voted_for |-> v_voted_for[_nid],
        vote_granted |-> {},
        commit_index |-> v_commit_index[_nid],
        match_index |-> v_match_index[_nid],
        next_index |-> v_next_index[_nid]
    ]




ActionCheckState(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            {_node_id}, 
            ActionCheck, 
            __ActionCheck
       )

InitActionSeqSetup ==
    ActionsFromHandle(
            _RaftVariables,
            NODE_ID, 
            ActionSetup, 
            __ActionInit
       )
       
ActionSeqSetupAll ==
    ActionsFromHandle(
            _RaftVariables,
            NODE_ID, 
            ActionSetup, 
            __ActionInit
       )

    
SaveActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__', DB_ACTION_PATH)

SaveInitActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)

ContextNull == [null |-> "null"]
ContextHasMessage(_context) == "message" \in DOMAIN _context
                
Init ==
    /\ IF  DB_STATE_PATH = "" THEN (
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
         )
         ELSE (LET s == QueryAllValues(DB_STATE_PATH)
                IN /\ \E e \in s:
                    /\ v_state = e.state
                    /\ v_current_term = e.current_term
                    /\ v_log = e.log
                    /\ v_snapshot = e.snapshot
                    /\ v_voted_for = e.voted_for
               )   
    /\ v_messages = {}
    /\ v_commit_index = [i \in NODE_ID |-> v_snapshot[i].index]
    /\ v_next_index = [i \in NODE_ID |-> 
            IF v_state[i] = Leader THEN
                [j \in NODE_ID |-> LastLogIndex(v_log[i], v_snapshot[i])]
            ELSE 
                [j \in NODE_ID |-> 1]
            ]
    /\ v_match_index = [i \in NODE_ID |-> [j \in NODE_ID |-> 0]]

    /\ v_history = <<>>
    /\ v_acked_value = {}
    /\ v_pc = [i \in NODE_ID |-> [state |-> "next"]]
    /\ v_pc_context = [i \in NODE_ID |-> ContextNull]
    /\ LET actions == InitActionSeqSetup
        IN InitAction(
            __action__,
            actions,
            actions
        )
    /\ SaveInitActions

                                               
RECURSIVE AppendRequestMessages(_, _, _, _, _, _, _, _, _)

LastEntryIndex(_log, _next_index, i, j) ==
    Min({
        IF Len(_log[i]) > 0 THEN
            _log[i][Len(_log[i])].index 
        ELSE
            0,
        _next_index[i][j]
    })

PrevLogIndex(_next_index, i, j) ==
    IF _next_index[i][j] > 0 THEN
        _next_index[i][j] - 1
    ELSE
        0



MessageApplySnapshot(
    _source,
    _dest,
    _term,
    _snapshot
) == 
     Message(_source, _dest, ApplyReq,
         [
            source_nid      |-> _source,
            term     |-> _term,
            id       |-> "",
            snapshot |-> _snapshot,
            iter      |-> <<>>
         ]
     )

MessageAppendRequest(
    _source,
    _dest,
    _term,
    _prev_log_index,
    _prev_log_term,
    _log_entries,
    _commit_index,
    _leader_log,
    _leader_snapshot,
    _aux_payload
) ==
    LET  payload == 
                IF _aux_payload THEN
            
                        [
                            source_nid      |-> _source,
                            term            |-> _term,
                            prev_log_index  |-> _prev_log_index,
                            prev_log_term   |-> _prev_log_term,
                            log_entries     |-> _log_entries,
                            commit_index    |-> _commit_index,
                            
                            \* only valid for checking safty invariant
                            leader_log    |-> _leader_log,
                            leader_snapshot |-> _leader_snapshot
                        ]
                    
                ELSE
                        [
                            source_nid      |-> _source,
                            term            |-> _term,
                            prev_log_index  |-> _prev_log_index,
                            prev_log_term   |-> _prev_log_term,
                            log_entries     |-> _log_entries,
                            commit_index    |-> _commit_index
                        ]          
    IN Message(_source, _dest, AppendRequest, payload)
    
                    
AppendRequestMessages(
    _log, 
    _next_index, 
    _commit_index, 
    _current_term,
    _snapshot,
    _append_max,
    i, 
    servers, msgs
) ==
    IF servers = {} \/ servers = {i} THEN 
        msgs
    ELSE LET 
            j == CHOOSE j \in servers : i /= j
            prev_log_index == PrevLogIndex(_next_index, i, j)
            message == IF prev_log_index < _snapshot[i].index THEN (
                    LET apply_snapshot_message == MessageApplySnapshot(
                        i, 
                        j,
                        _current_term[i],
                        _snapshot[i])
                    IN apply_snapshot_message
                )
                ELSE (
                    LET prev_log_term == LogTerm(
                                _log,
                                _snapshot,
                                i, 
                                prev_log_index)
                       \* Send up to APPEND_ENTRIES_MAX entries, constrained by the end of the r_log[i].
                        entries == LogEntries(
                                _log,
                                _snapshot,
                                i, 
                                prev_log_index + 1, 
                                _append_max)
                        commit_index == _commit_index[i]
                        append_message == MessageAppendRequest(
                                i,                          \*_source,
                                j,                          \*_dest,
                                _current_term[i],           \* _term,
                                prev_log_index,             \* _prev_log_index,
                                prev_log_term,              \* _prev_log_term,
                                entries,                    \* _log_entries,
                                commit_index,                      \* _commit_index,
                                _log[i],                    \* _leader_log,
                                _snapshot[i],               \* _leader_snapshot,
                                CHECK_SAFETY     \* _aux_payload
                            )
                     IN append_message
                  ) \* end else
          IN AppendRequestMessages(
                _log, _next_index, 
                _commit_index,
                _current_term,
                _snapshot,
                 _append_max,
                i, 
                servers \ {j}, 
                msgs \cup {message}
            )

                 
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendLogEntries(i) ==
    /\ v_pc[i].state = "next"
    /\ v_state[i] = Leader
    /\ LET node_ids == NODE_ID
           n == APPEND_ENTRIES_MAX 
           msgs == AppendRequestMessages(
                v_log, v_next_index, 
                v_commit_index, 
                v_current_term,
                v_snapshot,
                n,
                i, node_ids \ {i}, {})
             actions0 == ActionSeqSetupAll
             actions1 == ActionCheckState(i)
             actions2 == Action(ActionInput, MessageLocalNP(i, __ActionAppendLog))
             actions3 == Actions(ActionOutput, msgs)
       IN /\ v_messages' = WithMessageSet(msgs, v_messages)
          /\ SetAction(__action__, actions0, actions1 \o actions2 \o actions3)    
    /\ UNCHANGED <<
            v_commit_index, 
            v_current_term, v_state, 
            v_voted_for, v_snapshot, v_log, 
            v_history,
            v_match_index,
            v_next_index,
            v_acked_value,
            vars_pc
            >>
        
_HandleAppendLog(_node_id, _from_node_id, _payload, _setup_action) ==
    LET prev_log_index == _payload.prev_log_index
        prev_log_term ==_payload.prev_log_term
        log_ok == LogPrevEntryOK(
            v_log, 
            v_snapshot,
            _node_id, 
            prev_log_index, 
            prev_log_term)
        term == _payload.term
        log_entries == _payload.log_entries
        leader_commit_index == _payload.commit_index
        result == HandleAppendLogInner(
                v_log,
                v_snapshot,
                v_current_term,
                v_state,
                v_history,
                RECONFIG_VALUE,
                _node_id,
                _from_node_id,
                prev_log_index,
                prev_log_term,
                term,
                log_entries
                )
         action_handle_append == Action(ActionInternal, Message(_node_id, _node_id, __ActionHandleAppendLogRequest, _payload))
    IN /\  (CASE  result.append_result = APPEND_RESULT_REJECT -> (
                /\ LET reply_payload == [
                            source_nid |-> _node_id,
                            term |-> v_current_term[_node_id],
                            append_success |-> FALSE,
                            match_index |-> v_snapshot[_node_id].index
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  /\ v_messages' = WithMessage(reply_message, v_messages)
                        /\ SetAction(__action__, _setup_action,   action_handle_append \o output_action)    
                /\ UNCHANGED <<v_current_term, v_state, v_voted_for, v_log, v_snapshot,  v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_TO_FOLLOWER -> (
                /\ v_state' = [v_state EXCEPT ![_node_id] = Follower]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
                /\ UNCHANGED <<v_current_term, v_log, v_snapshot, v_messages, v_history, v_commit_index>>
                /\ SetAction(__action__, _setup_action,   action_handle_append)    
            )
            [] result.append_result = APPEND_RESULT_STALE_INDEX -> (
                /\ LET reply_payload == [
                            source_nid |-> _node_id,
                            term |-> term,
                            append_success |-> TRUE,
                            match_index |-> v_snapshot[_node_id].index
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  /\ v_messages' = WithMessage(reply_message, v_messages)
                        /\ SetAction(__action__, _setup_action, action_handle_append \o output_action)    
                /\ UNCHANGED <<v_current_term, v_state, v_voted_for, v_log, v_snapshot, v_history, v_commit_index>>                         
            )
            [] result.append_result = APPEND_RESULT_ACCEPT -> (
                /\ LET reply_payload == [
                            source_nid |-> _node_id,
                            term |-> term,
                            append_success |-> TRUE, 
                            match_index |-> result.match_index
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  (/\ v_messages' = WithMessage(reply_message, v_messages)
                         /\ SetAction(__action__, _setup_action,    action_handle_append \o output_action)) 
                /\ v_log' = [v_log EXCEPT ![_node_id] = result.log]
                /\ LET last_log_index == LastLogIndex(v_log'[_node_id], v_snapshot[_node_id])
                       commit_index == Min({last_log_index, leader_commit_index})
                   IN 
                        v_commit_index' = [v_commit_index EXCEPT ![_node_id] = commit_index]
                /\ (IF CHECK_SAFETY 
                    THEN (
                        LET leader_log == _payload.leader_log
                            leader_snapshot == _payload.leader_snapshot
                            op == [
                                follower_append |-> [
                                    node_id |-> _node_id,
                                    leader_log |-> leader_log,
                                    leader_snapshot |-> leader_snapshot,
                                    follower_log |-> result.log,
                                    follower_snapshot |-> v_snapshot[_node_id]
                                ]
                            ]
                            IN v_history' = AppendHistory(v_history, op, CHECK_SAFETY)
                    )
                    ELSE 
                        UNCHANGED <<v_history>>
                    )
                /\ UNCHANGED <<v_current_term, v_state, v_voted_for, v_snapshot>>
            )
            [] OTHER  -> (
                FALSE
            )
        )
        /\ UNCHANGED <<v_acked_value, v_next_index, v_match_index>>

Agree(_match_index, _index, _node_id, _ids) ==
    {_node_id} \cup {j \in _ids :  
        /\ j /= _node_id
        /\ _match_index[_node_id][j] >= _index
        } \in QuorumOf(_ids)


AgreeIndex(_match_index, _node_id, _ids) ==
    IF Len(v_log[_node_id]) = 0 THEN 
        {}
    ELSE
        LET index_set == {v_log[_node_id][j].index: j \in DOMAIN  v_log[_node_id]}
        IN {i \in index_set : Agree(_match_index, i, _node_id, _ids) }
    
    
_HandleAdvanceCommitIndex(_match_index, _node_id) ==
    LET agree_indexes == AgreeIndex(_match_index, _node_id, NODE_ID)
    IN IF agree_indexes /= {} THEN
        LET max_index == Max(agree_indexes)
        IN (IF max_index > v_commit_index[_node_id] THEN 
                v_commit_index' = [v_commit_index EXCEPT ![_node_id] = max_index]
            ELSE 
                UNCHANGED <<v_commit_index>>
           )
       ELSE
           UNCHANGED <<v_commit_index>> 
        
_HandleAppendLogResponse(_node_id, _source, _payload) ==
    IF /\ v_state[_node_id] = Leader
       /\ _payload.term = v_current_term[_node_id]
    THEN (
        /\ (\/ (/\ _payload.append_success
                /\ v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = _payload.match_index + 1]
                /\ v_match_index' = [v_match_index EXCEPT ![_node_id][_source] = _payload.match_index]
                /\ _HandleAdvanceCommitIndex(v_match_index', _node_id)
               )
            \/ (/\ \lnot _payload.append_success
                /\ v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = Max({v_next_index[_node_id][_source] - 1, 1})]
                /\ UNCHANGED <<v_commit_index, v_match_index>>
               )
            )
        /\ UNCHANGED <<v_log, v_voted_for, v_current_term, v_acked_value,
                        v_messages, v_snapshot, v_state, v_history>>
         )
     ELSE UNCHANGED <<vars_except_action_and_pc>>


    

_UpdateTerm(_node_id, _term) ==
    /\ IF _term > v_current_term[_node_id] THEN
           (/\ v_current_term'    = [v_current_term EXCEPT ![_node_id] = _term]
            /\ v_state'          = [v_state       EXCEPT ![_node_id] = Follower]
            /\ v_voted_for'       = [v_voted_for    EXCEPT ![_node_id] = INVALID_NODE_ID]
           )
       ELSE
            UNCHANGED <<v_current_term, v_state, v_voted_for>>
    /\ UNCHANGED<<v_match_index, v_next_index, v_commit_index, 
            v_acked_value,
            v_log, 
            v_snapshot,
            v_messages,
            v_history
        >>
       
RecvMessage(node_id) ==
    /\ v_pc[node_id].state = "next" 
    /\ \E m \in v_messages:
        /\ m.dest = node_id
        /\  LET action_id == IdOfAction(__action__)
                source == m.source
                dest == m.dest
                payload == m.payload
                name == m.name
                actions0 == ActionSeqSetupAll
                actions1 == ActionCheckState(dest)
                actions2 == Action(ActionInput, m)
            IN \/ (/\ name \in  {AppendRequest, ApplyReq}
                   /\ IF name = AppendRequest THEN
                        v_pc' = [v_pc EXCEPT ![dest] = [ state |-> "app_req1"]]
                      ELSE
                        v_pc' = [v_pc EXCEPT ![dest] = [ state |-> "apl_req1"]]
                   /\ v_pc_context' = [v_pc_context EXCEPT ![dest] = [message |-> m, id |-> action_id]]
                   /\ SetAction(__action__,actions0, actions1 \o actions2)
                   /\  UNCHANGED <<v_state,
                                v_current_term,
                                v_log, 
                                v_voted_for,
                                v_snapshot,
                                v_commit_index,
                                v_next_index,
                                v_match_index,
                                v_messages,
                                v_history,
                                v_acked_value
                                >>
                   )
               \/ (/\ name =  AppendResponse
                   /\ v_pc' = [v_pc EXCEPT ![dest] = [ state |-> "app_resp1"]]
                   /\ v_pc_context' = [v_pc_context EXCEPT ![dest] = [message |-> m, id |-> action_id]]
                   /\ SetAction(__action__, actions0, actions1 \o actions2)
                   /\  UNCHANGED <<v_state,
                                v_current_term,
                                v_log, 
                                v_voted_for,
                                v_snapshot,
                                v_commit_index,
                                v_next_index,
                                v_match_index,
                                v_messages,
                                v_history,
                                v_acked_value
                                >>
                  )
               \/ (/\ name =  ApplyResp
                   /\ SetAction(__action__, actions0, actions1 \o actions2)
                   /\  UNCHANGED <<
                                v_pc,
                                v_pc_context,
                                v_state,
                                v_current_term,
                                v_log, 
                                v_voted_for,
                                v_snapshot,
                                v_commit_index,
                                v_next_index,
                                v_match_index,
                                v_messages,
                                v_history,
                                v_acked_value
                                >>
                  )
                  

UpdateTerm(node_id) ==
    /\ v_pc[node_id].state \in {"app_req1",  "app_resp1", "apl_req1"}
    /\ ContextHasMessage(v_pc_context[node_id])
    /\ PrevIdOfAction(__action__) = v_pc_context[node_id].id
    /\ LET message ==  v_pc_context[node_id].message
            payload == message.payload
            actions0 == ActionSeqSetupAll
            action_id == IdOfAction(__action__)
        IN
         /\ _UpdateTerm(node_id, payload.term)
         /\ (\/ (/\ v_pc[node_id].state = "app_req1"
                /\ v_pc' = [v_pc EXCEPT ![node_id] = [v_pc[node_id] EXCEPT !.state = "app_req2"]]
                )
             \/ (/\ v_pc[node_id].state = "app_resp1"
                /\ v_pc' = [v_pc EXCEPT ![node_id] = [v_pc[node_id] EXCEPT !.state = "app_resp2"]]
                )
             \/ (/\ v_pc[node_id].state = "apl_req1"
                /\ v_pc' = [v_pc EXCEPT ![node_id] = [v_pc[node_id] EXCEPT !.state = "apl_req2"]]
                )
             )
         /\ v_pc_context' = [v_pc_context EXCEPT ![node_id].id =  action_id]
         /\ SetAction(__action__, actions0, Action(ActionInternal, Message(node_id, node_id, __ActionHandleUpdateTerm, payload.term)))
    

HandleAppendLogReq(_node_id) ==
    /\ v_pc[_node_id].state = "app_req2" 
    /\ ContextHasMessage(v_pc_context[_node_id])
    /\ PrevIdOfAction(__action__) = v_pc_context[_node_id].id
    /\ LET message == v_pc_context[_node_id].message 
           from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
       IN /\ message.name = AppendRequest
          /\ _HandleAppendLog(_node_id, from_node_id, payload, actions0) 
          /\ v_pc' = [v_pc EXCEPT ![_node_id] = [ state |-> "next"]]
          /\ v_pc_context' = [v_pc_context EXCEPT ![_node_id] = ContextNull]


HandleApplySnapshotReq(_node_id) ==
    /\ v_pc[_node_id].state = "apl_req2" 
    /\ ContextHasMessage(v_pc_context[_node_id])
    /\ PrevIdOfAction(__action__) = v_pc_context[_node_id].id
    /\ LET message == v_pc_context[_node_id].message 
           from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
       IN (/\ message.name = ApplyReq
           /\ v_pc' = [v_pc EXCEPT ![_node_id] = [ state |-> "next"]]
           /\ v_pc_context' = [v_pc_context EXCEPT ![_node_id] = ContextNull]
           /\ v_snapshot' = [v_snapshot EXCEPT ![_node_id] = payload.snapshot]
           /\ LET resp_payload ==  [source_nid |-> _node_id, term |-> v_current_term[_node_id], id |-> payload.id, iter |-> <<>>]
                  resp == Message(_node_id, from_node_id, ApplyResp, resp_payload)  
                  action2 == Action(ActionOutput, resp)
                  action1 == Action(ActionInternal, Message(_node_id, _node_id, __ActionHandleApplySnapshotRequest, payload))
              IN SetAction(__action__, actions0, action1 \o action2)
           /\ UNCHANGED <<
                        v_state,
                        v_current_term,
                        v_log, 
                        v_voted_for,
                        v_commit_index,
                        v_next_index,
                        v_match_index,
                        v_messages,
                        v_history,
                        v_acked_value
                        >>
           )
          
HandleAppendLogResp(_node_id) ==
    /\ v_pc[_node_id].state = "app_resp2" 
    /\ ContextHasMessage(v_pc_context[_node_id])
    /\ LET message == v_pc_context[_node_id].message 
           from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
           action1 == Action(ActionInternal, Message(_node_id, _node_id, __ActionHandleAppendLogResponse, payload))       
       IN /\ _HandleAppendLogResponse(_node_id, from_node_id, payload) 
          /\ SetAction(__action__, actions0, action1)
          /\ v_pc' = [v_pc EXCEPT ![_node_id] = [ state |-> "next"]]
          /\ v_pc_context' = [v_pc_context EXCEPT ![_node_id] = ContextNull]
            
Next == 
    \/ \E i \in NODE_ID : 
        /\ RecvMessage(i)
        /\ SaveActions
    \/ \E i \in NODE_ID : 
        /\ AppendLogEntries(i)
        /\ SaveActions
    \/ \E i \in NODE_ID : 
        /\ HandleAppendLogReq(i)
        /\ SaveActions
    \/ \E i \in NODE_ID : 
        /\ HandleAppendLogResp(i)
        /\ SaveActions
    \/ \E i \in NODE_ID : 
        /\ HandleApplySnapshotReq(i)
        /\ SaveActions
    \/ \E i \in NODE_ID : 
        /\ UpdateTerm(i)
        /\ SaveActions
\* to Next.
Spec == 
    /\ Init 
    /\ [][Next]_vars
----

StateOK ==
    BaseStateOK(
        v_state,
        v_current_term,
        v_log,
        v_snapshot,
        v_voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM)
   

LogTermGrowOK ==
    LogTermGrow(v_log, v_snapshot, NODE_ID)
            
        
PrefixCommitted ==
    InvariantPrefixCommitted(
        v_log,
        MAX_TERM,
        NODE_ID,
        v_history)
        
AtMostOneLeaderPerTerm ==  
    InvariantAtMostOneLeaderPerTerm(
          v_history)
    
SnapshotCommit ==    
    InvariantSnapshotCommit(
        v_log,
        v_snapshot,
        NODE_ID)
    
LogPrefixOK ==    
    InvariantLogPrefix(
        v_log,
        v_snapshot,
        NODE_ID)
    
FollowerAppend ==    
    InvariantFollowerAppend(
        v_history)
        
LogStateOK == 
    LogOK( 
        v_current_term,
        v_log,
        v_snapshot,
        NODE_ID,
        VALUE,
        MAX_TERM)

Invariant ==
    /\ StateOK
    /\ LogTermGrowOK
    /\ LogStateOK
    /\ PrefixCommitted
    /\ AtMostOneLeaderPerTerm
    /\ SnapshotCommit
    /\ LogPrefixOK
    /\ FollowerAppend


===============================================================================


