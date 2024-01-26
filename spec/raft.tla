--------------------------------- MODULE raft ---------------------------------



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
CONSTANT VOTE
CONSTANT REPLICATE
CONSTANT REASTART
CONSTANT CLIENT_REQUEST
\*CONSTANT DISABLE_VOTE_NODE_NUM
\*CONSTANT DISABLE_REPLICATE_NODE_NUM
----



VARIABLE v_state
VARIABLE v_log
VARIABLE v_voted_for
VARIABLE v_snapshot
VARIABLE v_vote_granted
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

VARIABLE v_restart_cnt
VARIABLE v_replicate_cnt
VARIABLE v_vote_cnt
VARIABLE v_request_cnt

vars_control == <<v_restart_cnt, v_replicate_cnt, v_vote_cnt, v_request_cnt>>

vars == <<
    v_state,
    v_current_term,
    v_log, 
    v_voted_for,
    v_snapshot,
    v_commit_index,
    v_next_index,
    v_match_index,
    v_vote_granted,
    v_messages,
    v_pc,
    v_pc_context,
    v_history,
    v_acked_value,    
    __action__,
    vars_control
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
    v_vote_granted,
    v_pc,
    v_pc_context,
    v_messages
>>

vars_hard_state == <<
    v_current_term,
    v_log, 
    v_voted_for,
    v_snapshot
>>

vars_except_action_and_pc == <<
    vars_hard_state,
    v_state,
    v_commit_index,
    v_next_index,
    v_match_index,
    v_vote_granted,
    v_messages,
    v_history,
    v_acked_value
>>

vars_except_action == <<
    vars_hard_state,
    v_state,
    v_commit_index,
    v_next_index,
    v_match_index,
    v_acked_value,
    v_vote_granted,
    v_messages,
    v_history,
    v_pc,
    v_pc_context
>>

vars_vote == <<v_vote_granted>>
vars_replicate == <<v_commit_index, v_next_index, v_match_index, v_acked_value>>

vars_pc == <<v_pc, v_pc_context>>

enable_action == ENABLE_ACTION


SetActionE(    
    _action_variable,
    _action_sequence1,
    _action_sequence2)==
    SetAction(
        _action_variable,
        _action_sequence1,
        _action_sequence2,
        enable_action)

InitActionE(    
    _action_variable,
    _action_sequence1,
    _action_sequence2)==
    InitAction(
        _action_variable,
        _action_sequence1,
        _action_sequence2,
        enable_action)
        
_RaftVariables(_nid) ==
    [
        state |-> v_state[_nid],
        current_term |-> v_current_term[_nid],
        log |-> v_log[_nid],
        snapshot |-> v_snapshot[_nid],
        voted_for |-> v_voted_for[_nid],
        vote_granted |-> v_vote_granted[_nid],
        commit_index |-> v_commit_index[_nid],
        match_index |-> v_match_index[_nid],
        next_index |-> v_next_index[_nid]
    ]

(*
DisableVoteNode ==
    IF DISABLE_VOTE_NODE_NUM = 0 THEN
        {}
    ELSE
        ChooseFromSet(NODE_ID, DISABLE_VOTE_NODE_NUM)


DisableReplicateNode ==
    IF DISABLE_REPLICATE_NODE_NUM = 0 THEN
        {}
    ELSE
        ChooseFromSet(NODE_ID, DISABLE_REPLICATE_NODE_NUM)
*)
               
ActionCheckState(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            {_node_id}, 
            ActionCheck, 
            __ActionCheck
       )


_RaftVariablesNew(_nid, _context) ==
    [
        state |-> IF "state" \in DOMAIN _context THEN _context.state[_nid] ELSE v_state[_nid],
        current_term |-> IF "current_term" \in DOMAIN _context THEN _context.current_term[_nid] ELSE v_current_term[_nid],
        log |-> IF "log" \in DOMAIN _context THEN _context.log[_nid] ELSE v_log[_nid],
        snapshot |-> IF "snapshot" \in DOMAIN _context THEN _context.snapshot[_nid] ELSE v_snapshot[_nid],
        voted_for |-> IF "voted_for" \in DOMAIN _context THEN _context.voted_for[_nid] ELSE v_voted_for[_nid],
        vote_granted |-> IF "vote_granted" \in DOMAIN _context THEN _context.vote_granted[_nid] ELSE v_vote_granted[_nid],
        commit_index |-> v_commit_index[_nid],
        match_index |-> v_match_index[_nid],
        next_index |-> v_next_index[_nid]
    ]

ActionSeqCheckNew(_node_id, _context) ==
    ActionsFromHandleContext(
            _RaftVariablesNew,
            {_node_id}, 
            ActionCheck, 
            __ActionCheck,
            _context
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
        SaveValue(__action__, DB_ACTION_PATH)

SaveInitActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)

ContextNull == [null |-> "null"]
ContextHasMessage(_context) == "message" \in DOMAIN _context

CntAppendLog == "App"
CntHandleAppendReq == "HAppReq"
CntHandleAppendResp == "HAppReq"
CntLogCompaction == "LogComp"
CntHandleApplyReq == "HAplReq"
ReplicateCntDomain == {CntAppendLog, CntHandleAppendReq, CntHandleAppendResp,  CntLogCompaction, CntHandleApplyReq}

CntVoteReq == "Vote"
CntHandleVoteReq == "HVoteReq"
CntHandleVoteResp == "HVoteResp"
VoteCntDomain == {CntVoteReq, CntHandleVoteReq, CntHandleVoteResp}

         
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
    /\ v_next_index = [i \in NODE_ID |-> [j \in NODE_ID |-> 1]]
    /\ v_match_index = [i \in NODE_ID |-> [j \in NODE_ID |-> 0]]
    /\ v_vote_granted = [i \in NODE_ID |-> {}]
    /\ v_history = <<>>
    /\ v_acked_value = {}
    /\ v_pc = [i \in NODE_ID |-> [state |-> "next"]]
    /\ v_pc_context = [i \in NODE_ID |-> ContextNull]
    /\ v_restart_cnt = 0
    /\ v_replicate_cnt = [i \in ReplicateCntDomain |-> 0] 
    /\ v_vote_cnt = [i \in VoteCntDomain |-> 0]
    /\ v_request_cnt = 0
    /\ LET actions == InitActionSeqSetup
       IN InitActionT(
            __action__,
            actions,
            actions
        )


                                               
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


_UpdateTerm(_node_id, _term) ==
    IF _term > v_current_term[_node_id] THEN
            [state |-> Follower, current_term |-> _term, voted_for |-> INVALID_NODE_ID]
    ELSE
            [state |-> v_state[_node_id], current_term |-> v_current_term[_node_id], voted_for |-> v_voted_for[_node_id]]


    
    
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


UpdateAckedValues(
    _log, _snapshot, index
) ==
    IF CHECK_SAFETY THEN 
        v_acked_value' = v_acked_value \cup AllValuesLEIndex(_log, _snapshot, index, VALUE)
    ELSE 
        UNCHANGED <<v_acked_value>>             
                              

_BecomeLeader(
    _node_id,
    _v_current_term,
    _v_state,
    _v_next_index,
    _v_match_index,
    _v_commit_index,
    _v_log,
    _v_snapshot,
    _v_history
)==
    /\ LET o == 
        [
            election |-> 
            [
               leader |-> _node_id,
               term |-> _v_current_term[_node_id],
               log |-> _v_log[_node_id],
               snapshot |-> _v_snapshot[_node_id]
            ]
        ] 
        IN _v_history' = AppendHistory(_v_history, o, CHECK_SAFETY)
    /\ v_state' = [v_state EXCEPT ![_node_id] = Leader]
    /\ LET last_log_index == LastLogIndex(_v_log[_node_id], _v_snapshot[_node_id])
        IN  _v_next_index' = [_v_next_index EXCEPT ![_node_id] = [j \in NODE_ID |-> last_log_index + 1]]
    /\ _v_match_index' = [_v_match_index EXCEPT ![_node_id] = [j \in NODE_ID |-> _v_snapshot[_node_id].index]]
    /\ _v_commit_index' = [_v_commit_index EXCEPT ![_node_id] = _v_snapshot[_node_id].index]



\* NODE_ID _node_id times out and starts a new election.
VoteRequestVote(_node_id, _max_term) == 
    /\ v_pc[_node_id].state = "next"
    /\ TermLE(_node_id, v_current_term, _max_term)
    /\ v_state[_node_id] = Follower
    /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = v_current_term[_node_id] + 1]
    /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _node_id]
    /\ IF {_node_id} = NODE_ID THEN
                _BecomeLeader(
                    _node_id,
                    v_current_term',
                    v_state,
                    v_next_index,
                    v_match_index,
                    v_commit_index,
                    v_log,
                    v_snapshot,v_history)
           ELSE /\ v_state' = [v_state EXCEPT ![_node_id] = Candidate]
                /\ UNCHANGED <<v_history, v_match_index, v_next_index, v_commit_index>>
    /\ v_vote_granted'   = [v_vote_granted EXCEPT ![_node_id] = {_node_id}]
    /\  LET  payload == [
                term            |-> v_current_term[_node_id] + 1,
                last_log_term   |-> LastLogTerm(v_log[_node_id], v_snapshot[_node_id]),
                last_log_index  |-> LastLogIndex(v_log[_node_id], v_snapshot[_node_id]),
                source_nid |-> _node_id
            ]  
            messages == MessageSet({_node_id}, NODE_ID \ {_node_id}, VoteRequest,  payload)
            actions_input == Action(ActionInput, MessageNP(_node_id, _node_id, __ActionRequestVote))
            actions_output == Actions(ActionOutput, messages)
            actions0 == ActionCheckState(_node_id)
            actions == ActionSeqSetupAll
        IN /\ v_messages' = WithMessageSet(messages, v_messages)
           /\ SetActionE(__action__, actions, actions0 \o actions_input \o actions_output)
    /\ UNCHANGED <<
            v_log, 
            v_snapshot,
            v_history,
            v_pc,
            v_pc_context,
            v_acked_value
            >>
            
__HandleVoteRequest(_node_id, _from_node_id, _msg_payload, action) ==
    LET term_context == _UpdateTerm(_node_id, _msg_payload.term)
        last_log_term == _msg_payload.last_log_term
        last_log_index == _msg_payload.last_log_index
        grant == VoteCanGrant(
                    term_context.current_term,
                    v_log[_node_id],
                    v_snapshot[_node_id],
                    term_context.voted_for,
                    _from_node_id,
                    _msg_payload.term, 
                    _msg_payload.last_log_term, 
                    _msg_payload.last_log_index)
        payload == [
                term |-> term_context.current_term,
                vote_granted |-> grant,
                source_nid |-> _node_id
            ]
        a1 == action  
        reply ==  Message(_node_id, _from_node_id, VoteResponse, payload)
        a2 == Action(ActionOutput, reply)
        actions == ActionSeqSetupAll
    IN /\  (\/ (/\ grant
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _from_node_id] 
                /\ v_state' = [v_state EXCEPT ![_node_id] = term_context.state]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]
               )
            \/ (/\ ~grant
                /\ v_state' = [v_state EXCEPT ![_node_id] = term_context.state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]
               )
           )
        /\ SetActionE(__action__, actions, a1 \o a2)
        /\ v_messages' = WithMessage(reply, v_messages)   
        /\ UNCHANGED << 
                v_vote_granted,
                v_log, 
                v_snapshot,
                v_history
            >>


\* NODE_ID i receives a RequestVote response from server j with
\* m.term = v_current_term[i].
__HandleVoteResponse(i, _from_node, _m, _actions) ==
     /\ LET actions == ActionSeqSetupAll
        IN 
        IF _m.term = v_current_term[i] THEN
            /\ v_state[i] \in {Candidate, Leader} 
            /\ (\/( /\ _m.vote_granted
                    /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] =
                                            v_vote_granted[i] \cup {_from_node}]    
                    /\ IF  /\ v_state[i] = Candidate
                           /\ v_vote_granted[i] \cup {_from_node} \in  QuorumOf(NODE_ID)
                       THEN
                        (     _BecomeLeader(
                                    i,
                                    v_current_term,
                                    v_state,
                                    v_next_index,
                                    v_match_index,
                                    v_commit_index,
                                    v_log,
                                    v_snapshot,v_history)
                              /\ SetActionE(__action__, actions,  _actions)
                              /\ UNCHANGED <<v_voted_for, v_current_term>>
                          )
                       ELSE   
                            /\ SetActionE(__action__, actions, _actions)
                            /\ UNCHANGED <<
                                v_state, v_voted_for, v_current_term,
                                v_next_index, v_match_index, v_commit_index, v_history>>                   
                    )
                \/ ( /\ ~_m.vote_granted
                     /\ SetActionE(__action__, actions,  _actions)
                     /\ UNCHANGED <<
                                v_state, v_voted_for, v_current_term, v_vote_granted,  
                                v_next_index, v_match_index, v_commit_index, v_history>>
                    )
                )
             
        ELSE 
             /\ LET term_context == _UpdateTerm(i, _m.term)
                IN (/\ v_state' = [v_state EXCEPT ![i] = term_context.state]
                    /\ v_voted_for' = [v_voted_for EXCEPT ![i] = term_context.voted_for]
                    /\ v_current_term' = [v_current_term EXCEPT ![i] = term_context.current_term]   
                )
             /\ UNCHANGED <<v_vote_granted,  v_next_index, v_commit_index, v_match_index, v_history>>
             /\ SetActionE(__action__, actions,  _actions)
    /\ UNCHANGED <<v_log, v_snapshot>>

                 
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
          /\ SetActionE(__action__, actions0, actions1 \o actions2 \o actions3)    
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
    /\ UNCHANGED <<vars_vote>>
    


_HandleAppendLog(_node_id, _from_node_id, _payload, _setup_action, _input_action) ==
    LET term_context == _UpdateTerm(_node_id, _payload.term)
        current_term == term_context.current_term
        current_state == term_context.state
        current_voted_for == term_context.voted_for
        prev_log_index == _payload.prev_log_index
        prev_log_term ==_payload.prev_log_term
        log_ok == LogPrevEntryOK(
            v_log[_node_id], 
            v_snapshot[_node_id],
            prev_log_index, 
            prev_log_term)
        term == _payload.term
        log_entries == _payload.log_entries
        commit_index == _payload.commit_index
        result == HandleAppendLogInner(
                _node_id,        
                v_log[_node_id],
                v_snapshot[_node_id],
                current_term,
                current_state,
                v_history,
                RECONFIG_VALUE,
                _from_node_id,
                prev_log_index,
                prev_log_term,
                term,
                log_entries
                )
         action_handle_append == _input_action
    IN /\  (CASE  result.append_result = APPEND_RESULT_REJECT -> (
                /\ LET next_index == 
                        (IF v_snapshot[_node_id].index > prev_log_index THEN
                            v_snapshot[_node_id].index
                         ELSE
                            0
                         )
                        reply_payload == [
                            source_nid |-> _node_id,
                            term |-> current_term,
                            append_success |-> FALSE,
                            match_index |-> 0,
                            next_index |-> next_index
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  /\ v_messages' = WithMessage(reply_message, v_messages)
                        /\ SetActionE(__action__, _setup_action,   action_handle_append \o output_action)    
                /\ v_state' = [v_state EXCEPT ![_node_id] = current_state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = current_voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ UNCHANGED <<v_acked_value, v_log, v_snapshot,  v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_TO_FOLLOWER -> (
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ v_state' = [v_state EXCEPT ![_node_id] = Follower]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
                /\ SetActionE(__action__, _setup_action,   action_handle_append)    
                /\ UNCHANGED <<v_acked_value, v_log, v_snapshot, v_messages, v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_ACCEPT -> (
                /\ LET reply_payload == [
                            source_nid |-> _node_id,
                            term |-> current_term,
                            append_success |-> TRUE, 
                            match_index |-> result.match_index,
                            next_index |-> 0
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  (/\ v_messages' = WithMessage(reply_message, v_messages)
                         /\ SetActionE(__action__, _setup_action,    action_handle_append \o output_action)) 
                /\ v_log' = [v_log EXCEPT ![_node_id] = result.log]
                /\ IF commit_index > v_commit_index[_node_id] /\ commit_index <= result.match_index THEN
                      \* update the commit index and acked values
                      /\ v_commit_index' = [v_commit_index EXCEPT ![_node_id] = commit_index]
                      /\ UpdateAckedValues(v_log'[_node_id], v_snapshot[_node_id], commit_index)
                   ELSE 
                        UNCHANGED <<v_acked_value, v_commit_index>>
                /\ (IF CHECK_SAFETY
                    THEN (
                        LET leader_log == _payload.leader_log
                            leader_snapshot == _payload.leader_snapshot
                            op == [
                                follower_append |-> [
                                    \*leader |-> _from_node_id,
                                    \*message |-> _payload,
                                    \*node_id |-> _node_id,
                                    leader_log |-> leader_log,
                                    leader_snapshot |-> leader_snapshot,
                                    follower_log |->  
                                            IF Len(result.log) = 0 THEN
                                                <<>>
                                            ELSE
                                                SubSeq(result.log, 1, result.match_index - v_snapshot[_node_id].index),
                                    follower_snapshot |-> v_snapshot[_node_id]
                                ]
                            ]
                            IN v_history' = AppendHistory(v_history, op, CHECK_SAFETY)
                    )
                    ELSE 
                        UNCHANGED <<v_history>>
                    )
                /\ v_state' = [v_state EXCEPT ![_node_id] = current_state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = current_voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ UNCHANGED <<v_snapshot>>
            )
            [] OTHER  -> (
                FALSE
            )
        )
        /\ UNCHANGED << v_next_index, v_match_index>>

Agree(_match_index, _index, _node_id, _ids) ==
    {_node_id} \cup {j \in _ids :  
        /\ j /= _node_id
        /\ _match_index[_node_id][j] >= _index
        } \in QuorumOf(_ids)


AgreeIndex(_match_index, _v_log, _v_snapshot, _node_id, _ids) ==
    LET index_set == {_v_log[_node_id][j].index: j \in DOMAIN  _v_log[_node_id]} \cup 1.._v_snapshot[_node_id].index
    IN {i \in index_set : Agree(_match_index, i, _node_id, _ids) }
    
    
_HandleAdvanceCommitIndex(_match_index, _v_log, _v_snapshot, _node_id) ==
    LET agree_indexes == AgreeIndex(_match_index, _v_log, _v_snapshot, _node_id, NODE_ID)
    IN IF agree_indexes /= {} THEN
        LET max_index == Max(agree_indexes)
        IN (IF max_index > v_commit_index[_node_id] THEN 
                /\ v_commit_index' = [v_commit_index EXCEPT ![_node_id] = max_index]
                /\ UpdateAckedValues(v_log[_node_id], v_snapshot[_node_id], max_index)
            ELSE 
                UNCHANGED <<v_acked_value, v_commit_index>>
           )
       ELSE
           UNCHANGED <<v_acked_value, v_commit_index>> 
        
_HandleAppendLogResponse(_node_id, _source, _payload) ==
    LET term_context == _UpdateTerm(_node_id, _payload.term)
    IN  /\ ( IF term_context.state = Leader 
              /\ _payload.term = v_current_term[_node_id]
              THEN (
                    /\ (\/ (/\ _payload.append_success
                            /\ v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = _payload.match_index + 1]
                            /\ v_match_index' = [v_match_index EXCEPT ![_node_id][_source] = _payload.match_index]
                            /\ _HandleAdvanceCommitIndex(v_match_index', v_log, v_snapshot, _node_id)
                           )
                        \/ (/\ \lnot _payload.append_success
                            /\ IF _payload.next_index > 0 THEN
                                    LET last_log_index == LastLogIndex(v_log[_node_id], v_snapshot[_node_id])
                                        new_next_index == Min({last_log_index + 1, _payload.next_index})
                                    IN v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                               ELSE 
                                    LET new_next_index == Max({v_next_index[_node_id][_source] - 1, 1})
                                    IN v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                            /\ UNCHANGED <<v_acked_value, v_commit_index, v_match_index>>
                           )
                        )
                    /\ UNCHANGED <<v_log,v_messages, v_snapshot,  v_history>>
                     )
             ELSE 
                UNCHANGED <<
                    v_acked_value,
                    v_log, 
                    v_snapshot,
                    v_commit_index,
                    v_next_index,
                    v_match_index,
                    v_vote_granted,
                    v_messages,
                    v_history
                    >>
            )
     /\ v_state' = [v_state EXCEPT ![_node_id] = term_context.state]
     /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
     /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]

    



HandleVoteReq(node_id, message) ==
    /\ message.dest = node_id
    /\ message.name = VoteRequest
    /\ LET actions1 == ActionCheckState(node_id)
           actions2 == Action(ActionInput, message)
       IN __HandleVoteRequest(message.dest, message.source, message.payload, actions1 \o actions2)
    /\ UNCHANGED <<v_history, vars_replicate>>
    /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "next"]]
    /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = ContextNull]
    
HandleVoteResp(node_id, message) ==
    /\ message.dest = node_id
    /\ message.name = VoteResponse
    /\ LET
          actions1 == ActionCheckState(node_id) 
          actions2 == Action(ActionInput, message)
       IN __HandleVoteResponse(message.dest, message.source, message.payload, actions1 \o actions2)
    /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "next"]]
    /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = ContextNull]
    /\ UNCHANGED <<v_messages, v_acked_value>>
        

HandleAppendLogReq(_node_id, message) ==
    /\ message.dest = _node_id
    /\ message.name = AppendRequest
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
           actions1 == ActionCheckState(_node_id)
           actions2 == Action(ActionInput, message)
       IN /\ _HandleAppendLog(_node_id, from_node_id, payload, actions0, actions1 \o actions2) 
          /\ v_pc' = [v_pc EXCEPT ![_node_id] = [ state |-> "next"]]
          /\ v_pc_context' = [v_pc_context EXCEPT ![_node_id] = ContextNull]
    /\ UNCHANGED <<vars_vote>>
    

HandleApplySnapshotReq(_node_id, message) ==
    /\ message.dest = _node_id
    /\ message.name = ApplyReq
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
           actions1 == ActionCheckState(_node_id)
           term_context == _UpdateTerm(_node_id, payload.term)
       IN  /\ (IF payload.term = term_context.current_term THEN
                 ( /\ IF /\ payload.snapshot.index >= LastLogIndex(v_log[_node_id], v_snapshot[_node_id])
                         /\ payload.snapshot.index > v_commit_index[_node_id]
                      THEN
                        /\ v_snapshot' = [v_snapshot EXCEPT ![_node_id] = payload.snapshot]
                        /\ v_log' = [v_log EXCEPT ![_node_id] = <<>> ]
                      ELSE
                        UNCHANGED <<v_snapshot, v_log>>
                   /\ LET resp_payload ==  [source_nid |-> _node_id, term |-> term_context.current_term, id |-> payload.id, iter |-> <<>>]
                          resp == Message(_node_id, from_node_id, ApplyResp, resp_payload)  
                          actions3 == Action(ActionOutput, resp)
                          actions2 == Action(ActionInput, message)
                      IN SetActionE(__action__, actions0, actions1 \o actions2 \o actions3)
                 )
             ELSE
                   /\ LET actions2 == Action(ActionInput, message)
                      IN SetActionE(__action__, actions0, actions1 \o actions2)
                   /\ UNCHANGED <<v_snapshot, v_log>>
              )
           /\ v_state' = [v_state EXCEPT ![_node_id] = term_context.state]
           /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
           /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]
           /\ UNCHANGED <<
                        v_pc,
                        v_pc_context,
                        v_commit_index,
                        v_next_index,
                        v_match_index,
                        v_messages,
                        v_history,
                        v_acked_value
                        >>
     /\ UNCHANGED <<vars_vote>>
         
HandleAppendLogResp(_node_id, message) ==
    /\ message.dest = _node_id
    /\ message.name = AppendResponse
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
           actions1 == ActionCheckState(_node_id)
           actions2 == Action(ActionInput, message)
       IN /\ _HandleAppendLogResponse(_node_id, from_node_id, payload) 
          /\ SetActionE(__action__, actions0, actions1 \o actions2)
          /\ v_pc' = [v_pc EXCEPT ![_node_id] = [ state |-> "next"]]
          /\ v_pc_context' = [v_pc_context EXCEPT ![_node_id] = ContextNull]
    /\ UNCHANGED <<vars_vote>>


RestartNode(i) ==
    /\ v_pc[i].state = "next"
    /\ v_pc' = [v_pc EXCEPT ![i] = [state |-> "next"]]
    /\ v_state' = [v_state EXCEPT ![i] = Follower]
    /\ v_vote_granted'   = [v_vote_granted EXCEPT ![i] = {}]
    /\ v_next_index' = [v_next_index EXCEPT ![i] = [j \in NODE_ID |-> 1]]
    /\ v_match_index' = [v_match_index EXCEPT ![i] = [j \in NODE_ID |-> 0]]
    /\ v_commit_index' = [v_commit_index EXCEPT ![i] = v_snapshot[i].index]
    /\ LET _a == Action(ActionInput, MessageLocalNP(i, __ActionRestartNode))
            actions0 == ActionSeqSetupAll
       IN SetActionE(__action__, actions0, _a)    
    /\ UNCHANGED <<
            v_current_term,
            v_log, 
            v_snapshot,
            v_voted_for,
            v_messages,
            v_history,
            v_pc_context,
            v_acked_value
         >>


LogCompaction(nid) ==
    /\ v_pc[nid].state = "next"
    /\ v_snapshot[nid].index < v_commit_index[nid]
    /\ LET  last_log_index == LastLogIndex(v_log[nid], v_snapshot[nid])
            compact_log_index == Min({last_log_index, v_commit_index[nid]})
            offset == LogIndexToOffset(v_log[nid], v_snapshot[nid], compact_log_index)
            term == LogTermOfIndex(v_log[nid], v_snapshot[nid], compact_log_index)
            compact_log == SubSeq(v_log[nid], 1, offset)
            
       IN ( /\ offset > 0
            /\ LET snapshot_values == { 
                v \in [
                    value:VALUE,
                    index:1..last_log_index
                ]  : 
                    \E i \in 1..Len(compact_log): 
                        /\ compact_log[i].value = v.value
                        /\ compact_log[i].index = v.index
                        }
               IN v_snapshot' = [v_snapshot EXCEPT  ![nid] = [index |-> compact_log_index, term |-> term, value |-> v_snapshot[nid].value \cup snapshot_values] ]
            /\ v_log' = [v_log EXCEPT  ![nid] = SubSeq(v_log[nid], offset + 1, Len(v_log[nid]))]
            /\ LET  actions0 == ActionSeqSetupAll
                    actions1 == ActionCheckState(nid)
                    actions2 == Action(ActionInput, Message(nid, nid, __ActionLogCompaction, compact_log_index))
                IN SetActionE(__action__, actions0, actions1 \o actions2)
           )
    /\ UNCHANGED <<
            v_state,
            v_current_term,
            v_voted_for,
            v_messages,
            v_history,
            v_pc,
            v_pc_context,
            vars_vote,
            vars_replicate
            >>


ClientRequest(nid, v) ==
    /\ v_state[nid] = Leader
    /\ ~LogHasValue(v_log[nid], v_snapshot[nid], v)
    /\  LET entry == [
                index |-> LastLogIndex(v_log[nid], v_snapshot[nid]) + 1,
                term  |-> v_current_term[nid],
                value |-> v]
        IN /\ v_log' = [v_log EXCEPT ![nid] = Append(v_log[nid], entry)]
    /\ LET  actions0 == ActionSeqSetupAll
            actions1 == ActionCheckState(nid)
            actions2 == Action(ActionInput, Message(nid, nid, __ActionClientRequest, v))
        IN SetActionE(__action__, actions0, actions1 \o actions2)
    /\ IF NODE_ID = {nid} THEN
          _HandleAdvanceCommitIndex(v_match_index, v_log', v_snapshot, nid)
       ELSE
           UNCHANGED <<v_commit_index,v_acked_value>>
    /\ UNCHANGED <<
            v_history, v_current_term, v_state, 
            v_voted_for, v_snapshot, v_messages, 
            vars_vote,
            v_next_index, v_match_index, 
            v_pc, v_pc_context
            >> 

                          
Next == 
    \/ \E i \in NODE_ID : 
        \/ (/\ (\/ (/\ v_replicate_cnt[CntAppendLog] <= REPLICATE
                    /\ AppendLogEntries(i) 
                    /\ v_replicate_cnt' = [v_replicate_cnt EXCEPT ![CntAppendLog] = v_replicate_cnt[CntAppendLog] + 1 ]
                   )
                \/ (/\ v_replicate_cnt[CntLogCompaction] <= REPLICATE
                    /\ LogCompaction(i)
                    /\ v_replicate_cnt' = [v_replicate_cnt EXCEPT ![CntLogCompaction] = v_replicate_cnt[CntLogCompaction] + 1 ]
                   )
                \/ (\E m \in v_messages :
                    \/ ( /\ v_replicate_cnt[CntHandleAppendReq] <= REPLICATE
                         /\ HandleAppendLogReq(i, m) 
                         /\ v_replicate_cnt' = [v_replicate_cnt EXCEPT ![CntHandleAppendReq] = v_replicate_cnt[CntHandleAppendReq] + 1 ]
                       )
                    \/ ( /\ v_replicate_cnt[CntHandleAppendResp] <= REPLICATE
                         /\ HandleAppendLogResp(i, m)
                         /\ v_replicate_cnt' = [v_replicate_cnt EXCEPT ![CntHandleAppendResp] = v_replicate_cnt[CntHandleAppendResp] + 1 ]
                       )
                    \/ ( /\ v_replicate_cnt[CntHandleApplyReq] <= REPLICATE
                         /\ HandleApplySnapshotReq(i, m)
                         /\ v_replicate_cnt' = [v_replicate_cnt EXCEPT ![CntHandleApplyReq] = v_replicate_cnt[CntHandleApplyReq] + 1 ]
                        )
                    )
               )
            /\ UNCHANGED <<v_vote_cnt, v_restart_cnt, v_request_cnt>>
           )
        \/ (/\ (\/ (/\ v_vote_cnt[CntVoteReq] <= VOTE
                    /\ VoteRequestVote(i, MAX_TERM)
                    /\ v_vote_cnt' = [v_vote_cnt EXCEPT ![CntVoteReq] = v_vote_cnt[CntVoteReq] + 1 ]
                   )
                \/ (\E m \in v_messages :
                   \/ (/\ v_vote_cnt[CntHandleVoteReq] <= VOTE
                       /\ HandleVoteReq(i, m) 
                       /\ v_vote_cnt' = [v_vote_cnt EXCEPT ![CntHandleVoteReq] = v_vote_cnt[CntHandleVoteReq] + 1 ]
                       )
                   \/ ( /\ v_vote_cnt[CntHandleVoteResp] <= VOTE
                        /\ HandleVoteResp(i, m))
                        /\ v_vote_cnt' = [v_vote_cnt EXCEPT ![CntHandleVoteResp] = v_vote_cnt[CntHandleVoteResp] + 1 ]
                      )
               )
            /\ UNCHANGED <<v_replicate_cnt, v_restart_cnt, v_request_cnt>>  
           )
        \/ (/\ v_restart_cnt < REASTART 
            /\ RestartNode(i)
            /\ v_restart_cnt' = v_restart_cnt + 1
            /\ UNCHANGED <<v_replicate_cnt, v_vote_cnt, v_request_cnt>> 
            )
        \/ (/\ v_request_cnt < CLIENT_REQUEST
            /\ \E v \in VALUE:
                ClientRequest(i, v)
            /\ v_request_cnt' = v_request_cnt + 1
            /\ UNCHANGED <<v_replicate_cnt, v_vote_cnt, v_restart_cnt>> 
            )

  

\* to Next.
Spec == 
    /\ Init 
    /\ [][Next]_vars
----

     

AssertStateOK ==
    /\ BaseStateOK(
        v_state,
        v_current_term,
        v_log,
        v_snapshot,
        v_voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM)
    /\ LogOK( 
        v_current_term,
        v_log,
        v_snapshot,
        NODE_ID,
        VALUE,
        MAX_TERM)

AssertLogIndexTermGrow ==
    InvLogIndexTermGrow(v_log, v_snapshot, NODE_ID)
            
        
AssertPrefixCommitted ==
    InvPrefixCommitted(
        NODE_ID,
        v_commit_index,
        v_log,
        v_snapshot)
        
AssertAtMostOneLeaderPerTerm ==  
    InvAtMostOneLeaderPerTerm(
          v_history)
    
    
AssertFollowerAppend ==    
    InvFollowerAppend(
        v_history)



AssertLeaderHasAllAckedValues ==
    InvLeaderHasAllAckedValues (
        NODE_ID,
        VALUE,
        v_acked_value,
        v_state,
        v_current_term,
        v_log,
        v_snapshot
        )


===============================================================================


