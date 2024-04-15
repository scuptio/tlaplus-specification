--------------------------------- MODULE raft ---------------------------------



EXTENDS 
    action, 
    raft_common,
    raft_replicate_common,
    history, 
    Naturals, 
    FiniteSets, 
    Sequences, 
    Integers,
    TLC

CONSTANT VALUE

CONSTANT NODE_ID
CONSTANT MAX_TERM
CONSTANT CHECK_SAFETY
CONSTANT ENABLE_ACTION
CONSTANT DB_STATE_PATH
CONSTANT DB_ACTION_PATH
CONSTANT APPEND_ENTRIES_MAX


CONSTANT VOTE
CONSTANT REPLICATE
CONSTANT RESTART
CONSTANT RECONFIG
CONSTANT CLIENT_REQUEST

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
VARIABLE v_current_term
VARIABLE v_config_committed
VARIABLE v_config_new
VARIABLE v_follower_config
VARIABLE v_follower_term_cindex

VARIABLE v_history



VARIABLE __action__

VARIABLE v_cnt_limit




TERM_VALUE == Nat

vars_config == <<
    v_config_committed,
    v_config_new,
    v_follower_config,
    v_follower_term_cindex
>>

vars_leader == <<
    v_vote_granted,
    v_next_index,
    v_match_index,
    v_follower_config,
    v_follower_term_cindex
>>

vars_control == <<v_cnt_limit>>

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
    v_history,
    v_acked_value,  
    v_config_committed,
    v_config_new,
    v_follower_config,
    v_follower_term_cindex,  
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
    v_config_committed,
    v_config_new,
    v_follower_config,
    v_follower_term_cindex, 
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
    v_history
>>

vars_vote == <<v_vote_granted>>
vars_replicate == <<v_commit_index, v_next_index, v_match_index, v_acked_value>>



        
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
       
InitActionSeqSetup(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            _node_id, 
            ActionSetup, 
            __ActionInit
       )
       
ActionSeqSetupAll(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            _node_id, 
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

CntVoteReq == "Vote"
CntHandleVoteReq == "HVoteReq"
CntHandleVoteResp == "HVoteResp"



CntRestart == "Restart"


CntClientReq == "ClientReq"
CntTickUpConf == "TickUpConfReq"
CntHandleUpConfReq == "HUpConfReq"
CntHandleUpConfResp == "HUpConfResp"
CntReConfBegin == "ReConfBegin"
CntReConfCommit == "ReConfCommit"

CntLimitDomain == {

CntAppendLog, CntHandleAppendReq, CntHandleAppendResp,  
CntLogCompaction, CntHandleApplyReq,
CntClientReq,
CntRestart,
CntVoteReq, CntHandleVoteReq, CntHandleVoteResp,
CntTickUpConf,
CntHandleUpConfReq,
CntHandleUpConfResp,
CntReConfBegin,
CntReConfCommit
}


\* TODO, initialized state     
_Init(
    _node_id,
    _value,
    _enable_state_db,
    _enable_action,
    _state_db_path
)
 ==
    /\ IF  _enable_state_db THEN (
            InitSaftyStateTrival(
                v_state,
                v_current_term,
                v_log,
                v_snapshot,
                v_voted_for,
                _node_id,
                _value,
                1,
                1, 
                1
                )
         )
         ELSE (LET s == QueryAllValues(_state_db_path)
                IN /\ \E e \in s:
                    /\ v_state = e.state
                    /\ v_current_term = e.current_term
                    /\ v_log = e.log
                    /\ v_snapshot = e.snapshot
                    /\ v_voted_for = e.voted_for
               )   
    /\ v_messages = {}
    /\ v_commit_index = [i \in _node_id |-> v_snapshot[i].index]
    /\ v_next_index = [i \in _node_id |-> [j \in NODE_ID |-> 1]]
    /\ v_match_index = [i \in _node_id |-> [j \in NODE_ID |-> 0]]
    /\ v_vote_granted = [i \in _node_id |-> {}]
    /\ v_history = <<>>
    /\ v_acked_value = {}
    /\ v_config_committed = [i \in _node_id |-> 
                [version |-> 1, term |-> v_current_term[i], node |-> _node_id]
            ]
    /\ v_config_new = [i \in _node_id |-> 
                [version |-> 1, term |-> v_current_term[i], node |-> _node_id, commit_index |-> v_commit_index[i]]
            ]
    /\ v_follower_config = [i \in _node_id |-> [j \in _node_id |-> NULL]]
    /\ v_follower_term_cindex = [i \in _node_id |-> [j \in _node_id |-> [term |-> 0, commit_index |-> 0]]]
    /\ v_cnt_limit = [i \in CntLimitDomain |-> 0]
    /\ LET actions == InitActionSeqSetup(_node_id)
       IN __action__ = InitAction(
            actions,
            actions,
            _enable_action
        )


_ConfigQuorumCheck(
    _leader,
    _config,
    _follower_config,
    _check_config_new
) ==
    /\ _config /= NULL
    /\ _leader \in _config.node
    /\ \E Q \in QuorumOf(_config.node):
            /\ _leader \in Q
            /\ \A j \in Q \ {_leader}:
                /\ _follower_config[j] /= NULL
                /\ IF _check_config_new THEN
                        /\ _follower_config[j].config_new.version = _config.version
                        /\ _follower_config[j].config_new.term = _config.term
                   ELSE
                        /\ _follower_config[j].config_committed.version = _config.version
                        /\ _follower_config[j].config_committed.term = _config.term
                        
_TermCommitIndexQuorumCheck(
    _leader,
    _leader_term,
    _config_new,
    _follower_term_cindex
) ==
    /\ _config_new /= NULL
    /\ _leader \in _config_new.node
    /\ \E Q \in QuorumOf(_config_new.node):
           /\ _leader \in Q
           /\ \A j \in Q \ {_leader}:
                /\ _follower_term_cindex[j].term = _leader_term
                /\ _follower_term_cindex[j].commit_index >= _config_new.commit_index

           

_QuorumOverlapped(_node_set1, _node_set2) ==
    \A q1 \in QuorumOf(_node_set1), q2 \in QuorumOf(_node_set2):
        q1 \cap q2 /= {}


    
_ConfigNew(_config_committed, _config_new, _i) ==
     IF _config_new[_i] /= NULL THEN
        _config_committed[_i]
     ELSE
        _config_new[_i]
        
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


MessageUpdateConfigReq(
    _source,
    _dest,
    _term,
    _config_committed,
    _config_new
) ==
     Message(_source, _dest, UpdateConfigReq,
         [
            source_nid      |-> _source,
            term     |-> _term,
            config_committed |-> 
                [
                    term |-> _config_committed.term,
                    version |-> _config_committed.version,
                    node |-> _config_committed.node
                ],
            config_new |-> 
                [
                    term |-> _config_new.term,
                    version |-> _config_new.version,
                    node |-> _config_new.node
                ]
         ]
     )

MessageUpdateConfigResp(
    _source,
    _dest,
    _term,
    _config_committed,
    _config_new
) ==
     Message(_source, _dest, UpdateConfigResp,
         [
            source_nid |-> _source,
            term     |-> _term,
            config_committed |-> _config_committed,
            config_new |-> _config_new
         ]
     )
          
_UpdateTerm(_node_id, _term) ==
    IF _term > v_current_term[_node_id] THEN
            [state |-> Follower, current_term |-> _term, voted_for |-> INVALID_NODE_ID]
    ELSE
            [state |-> v_state[_node_id], current_term |-> v_current_term[_node_id], voted_for |-> v_voted_for[_node_id]]


_ConfigVersionLess(_c1, _c2) ==
    \/ _c1.term < _c2.term
    \/ (/\ _c1.term = _c2.term 
        /\ _c1.version < _c2.version
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


_AppendRequestMessages(
    _log, 
    _next_index, 
    _commit_index, 
    _current_term,
    _snapshot,
    _append_max,
    _source, 
    _dest,
    _check_safety
) ==
    LET prev_log_index == PrevLogIndex(_next_index, _source, _dest)
    IN IF prev_log_index < _snapshot[_source].index THEN (
            LET apply_message == MessageApplySnapshot(
                _source, 
                _dest,
                _current_term[_source],
                _snapshot[_source])
            IN apply_message
        )
        ELSE (
            LET prev_log_term == LogTerm(
                        _log,
                        _snapshot,
                        _source, 
                        prev_log_index)
               \* Send up to APPEND_ENTRIES_MAX entries, constrained by the end of the r_log[i].
                entries == LogEntries(
                        _log,
                        _snapshot,
                        _source, 
                        prev_log_index + 1, 
                        _append_max)
                commit_index == _commit_index[_source]
                append_message == MessageAppendRequest(
                        _source,                          \*_source,
                        _dest,                          \*_dest,
                        _current_term[_source],           \* _term,
                        prev_log_index,             \* _prev_log_index,
                        prev_log_term,              \* _prev_log_term,
                        entries,                    \* _log_entries,
                        commit_index,                      \* _commit_index,
                        _log[_source],                    \* _leader_log,
                        _snapshot[_source],               \* _leader_snapshot,
                        _check_safety     \* _aux_payload
                    )
             IN append_message
          ) \* end else
         
                                   
AppendRequestMessages(
    _log, 
    _next_index, 
    _commit_index, 
    _current_term,
    _snapshot,
    _append_max,
    _source, 
    servers, msgs,
    _check_safety
) ==
    LET f == [dest \in servers \ {_source} |-> 
                _AppendRequestMessages(
                    _log, 
                    _next_index, 
                    _commit_index, 
                    _current_term,
                    _snapshot,
                    _append_max,
                    _source, 
                    dest,
                    _check_safety
                    )
             ]
    IN {f[id] : id \in DOMAIN f}
    

UpdateAckedValues(
    _log, 
    _snapshot, 
    index, 
    _check_safety
) ==
    IF _check_safety THEN 
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
    _v_history,
    _check_safety
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
        IN _v_history' = AppendHistory(_v_history, o, _check_safety)
    /\ v_state' = [v_state EXCEPT ![_node_id] = Leader]
    /\ LET last_log_index == LastLogIndex(_v_log[_node_id], _v_snapshot[_node_id])
        IN  _v_next_index' = [_v_next_index EXCEPT ![_node_id] = [j \in NODE_ID |-> last_log_index + 1]]
    /\ _v_match_index' = [_v_match_index EXCEPT ![_node_id] = [j \in NODE_ID |-> _v_snapshot[_node_id].index]]
    /\ _v_commit_index' = [_v_commit_index EXCEPT ![_node_id] = _v_snapshot[_node_id].index]


_ClearLeaderVar(_nid, _nid_set) ==
    /\ v_vote_granted'   = [v_vote_granted EXCEPT ![_nid] = {}]
    /\ v_next_index' = [v_next_index EXCEPT ![_nid] = [j \in NODE_ID |-> 1]]
    /\ v_match_index' = [v_match_index EXCEPT ![_nid] = [j \in NODE_ID |-> 0]]
    /\ v_commit_index' = [v_commit_index EXCEPT ![_nid] = v_snapshot[_nid].index]
    /\ v_follower_term_cindex' = [v_follower_term_cindex EXCEPT ![_nid] = [j \in _nid_set |-> [term |-> 0, commit_index |-> 0]]]
    /\ v_follower_config' = [v_follower_config EXCEPT ![_nid] = [j \in _nid_set |-> NULL]]

_UnchangedLeaderVar(_nid) ==
    /\ UNCHANGED <<v_vote_granted, v_match_index, v_commit_index, v_follower_term_cindex, v_follower_config>>
    

\* NODE_ID _node_id times out and starts a new election.
VoteRequestVote(_node_id, _max_term, _check_safety, _node_id_set, _enable_action) == 
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
                    v_snapshot,v_history, _check_safety)
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
            actions == ActionSeqSetupAll(_node_id_set)
        IN /\ v_messages' = WithMessageSet(messages, v_messages)
           /\ SetAction(__action__, actions, actions0 \o actions_input \o actions_output, _enable_action)
    /\ UNCHANGED <<
            v_log, 
            v_snapshot,
            v_history,
            v_acked_value,
            vars_config
            >>
            
__HandleVoteRequest(_node_id, _from_node_id, _msg_payload, action, _node_id_set, _enable_action) ==
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
        actions == ActionSeqSetupAll(_node_id_set)
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
        /\ SetAction(__action__, actions, a1 \o a2, _enable_action)
        /\ v_messages' = WithMessage(reply, v_messages)   
        /\ UNCHANGED << 
                v_vote_granted,
                v_log, 
                v_snapshot,
                v_history,
                vars_config
            >>


\* NODE_ID i receives a RequestVote response from server j with
\* m.term = v_current_term[i].
__HandleVoteResponse(i, _from_node, _m, _actions, _check_safety, _node_id, _enable_action) ==
     /\ LET actions == ActionSeqSetupAll(_node_id)
        IN 
        IF _m.term = v_current_term[i] THEN
            /\ v_state[i] \in {Candidate, Leader} 
            /\ (\/( /\ _m.vote_granted
                    /\ v_vote_granted' = [v_vote_granted EXCEPT ![i] =
                                            v_vote_granted[i] \cup {_from_node}]    
                    /\ IF  /\ v_state[i] = Candidate
                           /\ LET granted_set == v_vote_granted[i] \cup {_from_node} 
                              IN /\ granted_set \in  QuorumOf(v_config_committed[i].node)
                                 /\ (\/ v_config_new[i] = v_config_committed[i]
                                     \/ granted_set \in QuorumOf(v_config_new[i].node)
                                    )
                       THEN
                        (     _BecomeLeader(
                                    i,
                                    v_current_term,
                                    v_state,
                                    v_next_index,
                                    v_match_index,
                                    v_commit_index,
                                    v_log,
                                    v_snapshot,v_history, _check_safety)
                              /\ SetAction(__action__, actions,  _actions, _enable_action)
                              /\ UNCHANGED <<v_voted_for, v_current_term>>
                          )
                       ELSE   
                            /\ SetAction(__action__, actions, _actions, _enable_action)
                            /\ UNCHANGED <<
                                v_state, v_voted_for, v_current_term,
                                v_next_index, v_match_index, v_commit_index, v_history>>                   
                    )
                \/ ( /\ ~_m.vote_granted
                     /\ SetAction(__action__, actions,  _actions, _enable_action)
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
             /\ SetAction(__action__, actions,  _actions, _enable_action)
    /\ UNCHANGED <<v_log, v_snapshot, vars_config>>

                 
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendLogEntries(i, _append_entries_max, _check_safety, _node_id, _enalbe_action) ==
    /\ v_state[i] = Leader
    /\ LET node_ids == v_config_committed[i].node \cup v_config_new[i].node
           n == _append_entries_max 
           msgs == AppendRequestMessages(
                v_log, v_next_index, 
                v_commit_index, 
                v_current_term,
                v_snapshot,
                n,
                i, node_ids \ {i}, {}, _check_safety)
             actions0 == ActionSeqSetupAll(_node_id)
             actions1 == ActionCheckState(i)
             actions2 == Action(ActionInput, MessageLocalNP(i, __ActionAppendLog))
             actions3 == Actions(ActionOutput, msgs)
       IN /\ v_messages' = WithMessageSet(msgs, v_messages)
          /\ SetAction(__action__, actions0, actions1 \o actions2 \o actions3, _enalbe_action)    
    /\ UNCHANGED <<
            v_commit_index, 
            v_current_term, v_state, 
            v_voted_for, v_snapshot, v_log, 
            v_history,
            v_match_index,
            v_next_index,
            v_acked_value
            >>
    /\ UNCHANGED <<vars_vote, vars_config>>
    


_HandleAppendLog(
    _node_id, 
    _from_node_id, 
    _payload, 
    _setup_action, 
    _input_action,
    _check_safety,
    _enable_action
) ==
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
                            commit_index |-> 0,
                            match_index |-> 0,
                            next_index |-> next_index
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  /\ v_messages' = WithMessage(reply_message, v_messages)
                        /\ SetAction(__action__, _setup_action,   action_handle_append \o output_action, _enable_action)    
                /\ v_state' = [v_state EXCEPT ![_node_id] = current_state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = current_voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ UNCHANGED <<v_acked_value, v_log, v_snapshot,  v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_TO_FOLLOWER -> (
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ v_state' = [v_state EXCEPT ![_node_id] = Follower]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
                /\ SetAction(__action__, _setup_action,   action_handle_append, _enable_action)    
                /\ UNCHANGED <<v_acked_value, v_log, v_snapshot, v_messages, v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_ACCEPT -> (
                /\ LET c_index == 
                        IF commit_index > v_commit_index[_node_id] THEN
                            IF commit_index <= result.match_index THEN
                                commit_index
                            ELSE
                                result.match_index
                        ELSE
                            v_commit_index[_node_id]
                        
                        reply_payload == [
                            source_nid |-> _node_id,
                            term |-> current_term,
                            append_success |-> TRUE, 
                            match_index |-> result.match_index,
                            commit_index |-> c_index,
                            next_index |-> 0
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  (/\ v_commit_index' = [v_commit_index EXCEPT ![_node_id] = c_index]
                         /\ v_messages' = WithMessage(reply_message, v_messages)
                         /\ v_log' = [v_log EXCEPT ![_node_id] = result.log]
                         /\ IF c_index > v_commit_index[_node_id] THEN
                              \* update the commit index and acked values
                              /\ UpdateAckedValues(v_log'[_node_id], v_snapshot[_node_id], commit_index, _check_safety)
                            ELSE 
                                UNCHANGED <<v_acked_value>>
                         /\ SetAction(__action__, _setup_action,    action_handle_append \o output_action, _enable_action)
                         ) 
                /\ (IF _check_safety
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
                            IN v_history' = AppendHistory(v_history, op, _check_safety)
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

Agree(_match_index, _index, _node_id, _v_config_committed, _v_config_new) ==
    /\ LET _node_old == _v_config_committed[_node_id].node
          IN {_node_id} \cup 
            {
                j \in _node_old :  
                    /\ j /= _node_id
                    /\ _match_index[_node_id][j] >= _index
            } \in QuorumOf(_node_old)
    /\ (\/ _v_config_new[_node_id] = _v_config_committed[_node_id]
        \/ LET _node_new == _v_config_new[_node_id].node
           IN {_node_id} \cup 
                {
                    j \in _node_new :  
                        /\ j /= _node_id
                        /\ _match_index[_node_id][j] >= _index
                } \in QuorumOf(_node_new)
          )

AgreeIndex(_match_index, _v_log, _v_snapshot, _node_id, _v_config_committed, _v_config_new) ==
    LET index_set == {_v_log[_node_id][j].index: j \in DOMAIN  _v_log[_node_id]} \cup 1.._v_snapshot[_node_id].index
    IN {i \in index_set : Agree(_match_index, i, _node_id, _v_config_committed, _v_config_new) }
    
    
_HandleAdvanceCommitIndex(_match_index, _v_log, _v_snapshot, 
     _v_config_committed, _v_config_new,
    _node_id, _node_id_set, _check_safety
) ==
    LET agree_indexes == AgreeIndex(_match_index, _v_log, _v_snapshot, _node_id,  _v_config_committed, _v_config_new)
    IN IF agree_indexes /= {} THEN
        LET max_index == Max(agree_indexes)
        IN (IF max_index > v_commit_index[_node_id] THEN 
                /\ v_commit_index' = [v_commit_index EXCEPT ![_node_id] = max_index]
                /\ UpdateAckedValues(v_log[_node_id], v_snapshot[_node_id], max_index, _check_safety)
            ELSE 
                UNCHANGED <<v_acked_value, v_commit_index>>
           )
       ELSE
           UNCHANGED <<v_acked_value, v_commit_index>> 
        
_HandleAppendLogResponse(_node_id, _source, _payload, _node_id_set, _check_safety) ==
    LET term_context == _UpdateTerm(_node_id, _payload.term)
    IN  /\ ( IF term_context.state = Leader 
              /\ _payload.term = v_current_term[_node_id]
              THEN (
                    /\ (\/ (/\ _payload.append_success
                            /\ v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = _payload.match_index + 1]
                            /\ v_match_index' = [v_match_index EXCEPT ![_node_id][_source] = _payload.match_index]
                            /\ _HandleAdvanceCommitIndex(v_match_index', v_log, v_snapshot,
                                    v_config_committed, v_config_new,
                                 _node_id, _node_id_set, _check_safety)
                            /\ v_follower_term_cindex' = [v_follower_term_cindex EXCEPT ![_node_id][_source] = [term |-> _payload.term, commit_index |-> _payload.commit_index] ]
                           )
                        \/ (/\ \lnot _payload.append_success
                            /\ IF _payload.next_index > 0 THEN
                                    LET last_log_index == LastLogIndex(v_log[_node_id], v_snapshot[_node_id])
                                        new_next_index == Min({last_log_index + 1, _payload.next_index})
                                    IN v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                               ELSE 
                                    LET new_next_index == Max({v_next_index[_node_id][_source] - 1, 1})
                                    IN v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                            /\ UNCHANGED <<v_acked_value, v_commit_index, v_match_index, v_follower_term_cindex>>
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
                    v_follower_term_cindex,
                    v_history
                    >>
            )
     /\ v_state' = [v_state EXCEPT ![_node_id] = term_context.state]
     /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
     /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]


HandleVoteReq(node_id, message, _node_id_set, _enable_action) ==
    /\ message.dest = node_id
    /\ message.name = VoteRequest
    /\ LET actions1 == ActionCheckState(node_id)
           actions2 == Action(ActionInput, message)
       IN __HandleVoteRequest(message.dest, message.source, message.payload, actions1 \o actions2, _node_id_set, _enable_action)
    /\ UNCHANGED <<v_history, vars_replicate>>


    
HandleVoteResp(node_id, message, _check_safety, _node_id_set, _enable_action) ==
    /\ message.dest = node_id
    /\ message.name = VoteResponse
    /\ LET
          actions1 == ActionCheckState(node_id) 
          actions2 == Action(ActionInput, message)
       IN __HandleVoteResponse(message.dest, message.source, message.payload, actions1 \o actions2, _check_safety, _node_id_set, _enable_action)
    /\ UNCHANGED <<v_messages, v_acked_value>>
        

HandleAppendLogReq(_node_id, message, _check_safety, _node_id_set, _enable_action) ==
    /\ message.dest = _node_id
    /\ message.name = AppendRequest
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll(_node_id_set)
           actions1 == ActionCheckState(_node_id)
           actions2 == Action(ActionInput, message)
       IN /\ _HandleAppendLog(_node_id, from_node_id, payload, actions0, actions1 \o actions2, _check_safety, _enable_action) 
    /\ UNCHANGED <<vars_vote, vars_config>>
    

HandleApplySnapshotReq(_node_id, message, _node_id_set, _enable_action) ==
    /\ message.dest = _node_id
    /\ message.name = ApplyReq
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll(_node_id_set)
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
                      IN SetAction(__action__, actions0, actions1 \o actions2 \o actions3, _enable_action)
                 )
             ELSE
                   /\ LET actions2 == Action(ActionInput, message)
                      IN SetAction(__action__, actions0, actions1 \o actions2, _enable_action)
                   /\ UNCHANGED <<v_snapshot, v_log>>
              )
           /\ v_state' = [v_state EXCEPT ![_node_id] = term_context.state]
           /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
           /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]
           /\ UNCHANGED <<
                        v_commit_index,
                        v_next_index,
                        v_match_index,
                        v_messages,
                        v_history,
                        v_acked_value
                        >>
     /\ UNCHANGED <<vars_vote, vars_config>>
         
HandleAppendLogResp(_node_id, message, _node_id_set, _check_safety, _enable_action) ==
    /\ message.dest = _node_id
    /\ message.name = AppendResponse
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll(_node_id_set)
           actions1 == ActionCheckState(_node_id)
           actions2 == Action(ActionInput, message)
       IN /\ _HandleAppendLogResponse(_node_id, from_node_id, payload, _node_id_set, _check_safety) 
          /\ SetAction(__action__, actions0, actions1 \o actions2, _enable_action)
    /\ UNCHANGED <<vars_vote, 
            v_config_committed,
            v_config_new,
            v_follower_config
        >>


    
RestartNode(i, _node_id, _enable_action) ==
    /\ v_state' = [v_state EXCEPT ![i] = Follower]
    /\ _ClearLeaderVar(i, _node_id)
    /\ LET _a == Action(ActionInput, MessageLocalNP(i, __ActionRestartNode))
            actions0 == ActionSeqSetupAll(_node_id)
       IN SetAction(__action__, actions0, _a, _enable_action)    
    /\ UNCHANGED <<
            v_current_term,
            v_log, 
            v_snapshot,
            v_voted_for,
            v_messages,
            v_history,
            v_acked_value,
            v_config_committed,
            v_config_new
         >>


LogCompaction(nid, _node_id, _enable_action) ==
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
            /\ LET  actions0 == ActionSeqSetupAll(_node_id)
                    actions1 == ActionCheckState(nid)
                    actions2 == Action(ActionInput, Message(nid, nid, __ActionLogCompaction, compact_log_index))
                IN SetAction(__action__, actions0, actions1 \o actions2, _enable_action)
           )
    /\ UNCHANGED <<
            v_state,
            v_current_term,
            v_voted_for,
            v_messages,
            v_history,
            vars_vote,
            vars_replicate,
            vars_config
            >>


ClientRequest(nid, v , _node_id_set, _check_safety, _enable_action) ==
    /\ v_state[nid] = Leader
    /\ ~LogHasValue(v_log[nid], v_snapshot[nid], v)
    /\  LET entry == [
                index |-> LastLogIndex(v_log[nid], v_snapshot[nid]) + 1,
                term  |-> v_current_term[nid],
                value |-> v]
        IN /\ v_log' = [v_log EXCEPT ![nid] = Append(v_log[nid], entry)]
    /\ LET  actions0 == ActionSeqSetupAll(_node_id_set)
            actions1 == ActionCheckState(nid)
            actions2 == Action(ActionInput, Message(nid, nid, __ActionClientRequest, v))
        IN SetAction(__action__, actions0, actions1 \o actions2, _enable_action)
    /\ IF NODE_ID = {nid} THEN
          _HandleAdvanceCommitIndex(v_match_index, v_log', v_snapshot,
                 v_config_committed, v_config_new,
                 nid, _node_id_set, _check_safety)
       ELSE
           UNCHANGED <<v_commit_index,v_acked_value>>
    /\ UNCHANGED <<
            v_history, v_current_term, v_state, 
            v_voted_for, v_snapshot, v_messages, 
            vars_vote,
            v_next_index, v_match_index, vars_config
            >> 



UpdateConfigReqMessages(
    _source, 
    _node_ids, 
    _current_term,
    _v_config_committed,
    _v_config_new,
    _v_follower_config
) ==
    LET f == [dest \in { 
                i \in (_node_ids \ {_source}) :
                  LET _conf == _v_follower_config[_source][i]
                  IN \/ _conf = NULL \* not set
                     \/ (/\ _conf /= NULL
                         /\ (\/ _conf.config_committed.term /= _v_config_committed[_source].term
                             \/ _conf.config_committed.version /= _v_config_committed[_source].version
                             \/ _conf.config_new.term /= _v_config_committed[_source].term
                             \/ _conf.config_new.version /= _v_config_committed[_source].version
                            )
                        )
              } |-> 
                MessageUpdateConfigReq(
                    _source, 
                    dest, 
                    _current_term[_source],
                    _v_config_committed[_source],
                    _v_config_new[_source]
                    )
             ]
    IN {f[id] : id \in DOMAIN f}



TickSendUpdateConfigToFollower(_nid, _nid_set, _enalbe_action) ==
    /\ v_state[_nid] = Leader
    /\ LET nid_set == v_config_committed[_nid].node \cup v_config_new[_nid].node 
           msgs == UpdateConfigReqMessages(_nid, nid_set, v_current_term, v_config_committed, v_config_new, v_follower_config)
           actions0 == ActionSeqSetupAll(_nid_set)
           actions1 == ActionCheckState(_nid)
           actions2 == Action(ActionInput, MessageLocalNP(_nid, __ActionSendUpdateConfig))
           actions3 == Actions(ActionOutput, msgs)
       IN /\ v_messages' = WithMessageSet(msgs, v_messages)
          /\ SetAction(__action__, actions0, actions1 \o actions2 \o actions3, _enalbe_action)    
    /\ UNCHANGED <<
            v_commit_index, 
            v_current_term, v_state, 
            v_voted_for, v_snapshot, v_log, 
            v_history,
            v_match_index,
            v_next_index,
            v_acked_value
            >>
    /\ UNCHANGED <<vars_vote, vars_config>>


_UpdateConfig(
    _node_id, _term, _config_committed, _config_new) ==
    CASE _term > v_current_term[_node_id] -> (
        [config_committed |-> _config_committed, config_new |-> _config_new, term |-> _term]
    )
    [] _term = v_current_term[_node_id] -> (
        LET c_c == IF _ConfigVersionLess(v_config_committed[_node_id], _config_committed) THEN
                _config_committed
            ELSE
                v_config_committed[_node_id]
            c_n == IF _ConfigVersionLess(v_config_new[_node_id], _config_new) THEN
                _config_new
            ELSE
                v_config_new[_node_id]
        IN 
        [config_committed |-> c_c, config_new |-> c_n, term |-> v_current_term[_node_id]]
    )
    [] OTHER -> (
        [
            config_committed |-> v_config_committed[_node_id], 
            config_new |-> v_config_new[_node_id],
            term |-> v_current_term[_node_id]
        ]
    )


_ConfigTermVersion(
    _config
) ==
    [term |-> _config.term, version |-> _config.version]

HandleUpdateConfigReq(_nid, _msg, _nid_set, _enable_action) ==
    /\ _msg.dest = _nid
    /\ _msg.name = UpdateConfigReq
    /\(LET config_committed == _msg.payload.config_committed
           config_new == _msg.payload.config_new
           term == _msg.payload.term
           result == _UpdateConfig(_nid, term, config_committed, config_new)
           term_context == _UpdateTerm(_nid, _msg.payload.term)
       IN /\ v_config_committed' = [v_config_committed EXCEPT ![_nid] = result.config_committed]
          /\ v_config_new' = [v_config_new EXCEPT ![_nid] = result.config_new]
          /\ v_state' = [v_state EXCEPT ![_nid] = term_context.state]
          /\ v_voted_for' = [v_voted_for EXCEPT ![_nid] = term_context.voted_for]
          /\ v_current_term' = [v_current_term EXCEPT ![_nid] = term_context.current_term]
          /\ LET resp == MessageUpdateConfigResp(_msg.dest, _msg.source, 
                result.term,
                _ConfigTermVersion(result.config_committed), 
                _ConfigTermVersion(result.config_new)
                ) 
                actions0 == ActionSeqSetupAll(_nid_set)
                actions1 == ActionCheckState(_nid)
                input_action == Action(ActionInput, _msg)
                output_action == Action(ActionOutput, resp)
             IN (/\ v_messages' = WithMessage(resp, v_messages)
                 /\ SetAction(__action__, actions0,   actions1 \o input_action \o output_action, _enable_action)
                ) 
      )
    /\ UNCHANGED <<v_log, v_snapshot, v_history, vars_leader, v_acked_value, v_commit_index>>



HandleUpdateConfigResp(_nid, _msg, _nid_set, _enable_action) ==
    /\ _msg.dest = _nid
    /\ _msg.name = UpdateConfigResp
    /\(LET config_committed == _msg.payload.config_committed
           config_new == _msg.payload.config_new
           term == _msg.payload.term
           source == _msg.source
       IN /\ v_current_term[_nid] = term
          /\ IF \/ v_follower_config[_nid][source] = NULL
                \/ v_follower_config[_nid][source].config_committed /= config_committed
                \/ v_follower_config[_nid][source].config_new /= config_new
             THEN
                v_follower_config' = [v_follower_config EXCEPT ![_nid][source] = [config_committed |-> config_committed, config_new |-> config_new]]
             ELSE
                UNCHANGED v_follower_config
       )
     /\ LET actions0 == ActionSeqSetupAll(_nid_set)
            actions1 == ActionCheckState(_nid)
            input_action == Action(ActionInput, _msg)
        IN SetAction(__action__, actions0,   actions1 \o input_action, _enable_action)  
     /\ UNCHANGED <<
            __action__, 
            v_current_term, v_history, v_log, v_messages, v_snapshot, v_voted_for,
            v_state,
            vars_vote, vars_replicate,
            v_follower_term_cindex,
            v_config_committed, v_config_new
        >>

_ConfigVersionEqual(
    _c1,
    _c2
) ==
    /\ _c1.term = _c2.term
    /\ _c2.version = _c2.version

LeaderReConfigBegin(_nid, _node_new, _nid_set, _enable_action) ==
    /\ v_state[_nid] = Leader
    /\ v_config_committed[_nid].node /= _node_new
    /\ _ConfigVersionEqual(v_config_committed[_nid], v_config_new[_nid]) \* already committed
    /\ v_config_new' = [v_config_new EXCEPT ![_nid] = 
            [
                version |-> v_config_new[_nid].version + 1, 
                term |-> v_current_term[_nid], 
                node |-> _node_new,
                commit_index |-> v_commit_index[_nid]
            ]
       ]
    /\ LET actions0 == ActionSeqSetupAll(_nid_set)
           actions1 == ActionCheckState(_nid)
           input_action == Action(ActionInput, MessageLocal(_nid, __ActionUpdateConfigBegin, [node |-> _node_new]))
       IN SetAction(__action__, actions0,   actions1 \o input_action, _enable_action)  
    /\ UNCHANGED <<v_state, v_current_term, v_log,  v_voted_for,
                    v_snapshot, v_commit_index, v_next_index, v_match_index,
                    v_vote_granted, v_messages, v_history, v_acked_value, 
                    v_config_committed, v_follower_config, v_follower_term_cindex
                  >>


    
LeaderReConfigCommit(_nid, _nid_set, _enable_action) ==
    /\ v_state[_nid] = Leader
    /\ ~_ConfigVersionEqual(v_config_committed[_nid], v_config_new[_nid])  \* not comitted yet
    /\ _ConfigQuorumCheck(_nid, v_config_committed[_nid], v_follower_config[_nid], FALSE)
    /\ _ConfigQuorumCheck(_nid, v_config_new[_nid], v_follower_config[_nid], TRUE)
    /\ _TermCommitIndexQuorumCheck(_nid, v_current_term[_nid], v_config_new[_nid], v_follower_term_cindex[_nid])
    /\ v_config_committed' = [v_config_committed EXCEPT ![_nid] = v_config_new[_nid]]
    /\ LET actions0 == ActionSeqSetupAll(_nid_set)
           actions1 == ActionCheckState(_nid)
           input_action == Action(ActionInput, MessageLocalNP(_nid, __ActionUpdateConfigCommit))
       IN SetAction(__action__, actions0,   actions1 \o input_action, _enable_action) 
    /\ UNCHANGED <<v_state, v_current_term, v_log,  v_voted_for,
                    v_snapshot, v_commit_index, v_next_index, v_match_index,
                    v_vote_granted, v_messages, v_history, v_acked_value, 
                    v_config_new, v_follower_config, v_follower_term_cindex
                 >>
                    
_CountLimit(_v_count, _type, _max_limit) ==
     \/ (/\ _max_limit = 0
         /\ _v_count' = _v_count
        )
     \/ (/\ _v_count[_type] < _max_limit
         /\ _v_count' = [_v_count EXCEPT ![_type] = _v_count[_type] + 1 ]  
        )
       
_Next(
    _node_id,
    _value,
    _max_term,
    _append_entries_max,
    _max_replicate,
    _max_vote,
    _max_client_req,
    _max_restert,
    _max_reconfig,
    _check_safety,
    _enable_action
) == 
    \/ \E i \in _node_id : 
        \/ (/\ (\/ (/\ _CountLimit(v_cnt_limit, CntAppendLog, _max_replicate)
                    /\ AppendLogEntries(i, _append_entries_max, _check_safety, _node_id, _enable_action)
                   )
                \/ (/\ _CountLimit(v_cnt_limit, CntLogCompaction, _max_replicate)
                    /\ LogCompaction(i, _node_id, _enable_action)
                   )
                \/ (\E m \in v_messages :
                    \/ ( /\ _CountLimit(v_cnt_limit, CntHandleAppendReq, _max_replicate)
                         /\ HandleAppendLogReq(i, m, _check_safety, _node_id, _enable_action)
                       )
                    \/ (/\ _CountLimit(v_cnt_limit, CntHandleAppendResp, _max_replicate)
                        /\ HandleAppendLogResp(i, m, _node_id, _check_safety, _enable_action)
                         
                       )
                    \/ ( /\ _CountLimit(v_cnt_limit, CntHandleAppendResp, _max_replicate)
                         /\ HandleApplySnapshotReq(i, m, _node_id, _enable_action)
                        )
                    )
               )
           )
           
        \/ (/\ (\/ (/\ _CountLimit(v_cnt_limit, CntVoteReq, _max_vote)
                    /\ VoteRequestVote(i, _max_term, _check_safety, _node_id, _enable_action)
                   )
                \/ (\E m \in v_messages :
                   \/ (/\ _CountLimit(v_cnt_limit, CntHandleVoteReq, _max_vote)
                       /\ HandleVoteReq(i, m, _node_id, _enable_action)
                      )
                   \/ ( /\ _CountLimit(v_cnt_limit, CntHandleVoteResp, _max_vote) 
                        /\ HandleVoteResp(i, m, _check_safety, _node_id, _enable_action))
                      )
               )
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntRestart, _max_restert) 
            /\ RestartNode(i, _node_id, _enable_action)
            )
        \/ (/\ _CountLimit(v_cnt_limit, CntClientReq, _max_client_req)
            /\ \E v \in _value:
                ClientRequest(i, v, _node_id, _check_safety,  _enable_action)
            )
        \/ (/\ _CountLimit(v_cnt_limit, CntTickUpConf, _max_reconfig)
            /\ TickSendUpdateConfigToFollower(i, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntTickUpConf, _max_reconfig)
            /\ \E nodes \in SUBSET(_node_id):
                /\ nodes /= {}
                /\ LeaderReConfigBegin(i, nodes, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntTickUpConf, _max_reconfig)
            /\ LeaderReConfigCommit(i, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntHandleUpConfReq, _max_reconfig)
            /\ \E m \in v_messages :
                HandleUpdateConfigReq(i, m, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntHandleUpConfResp, _max_reconfig)
            /\ \E m \in v_messages :
                HandleUpdateConfigResp(i, m, _node_id, _enable_action)
           )
           
Init == 
    _Init(
        NODE_ID,
        VALUE,
        DB_STATE_PATH = "",
        ENABLE_ACTION,
        DB_STATE_PATH
    )

Next == 
    _Next(
        NODE_ID,
        VALUE,
        MAX_TERM,
        APPEND_ENTRIES_MAX,
        REPLICATE,
        VOTE,
        CLIENT_REQUEST,
        RESTART,
        RECONFIG,
        CHECK_SAFETY,
        ENABLE_ACTION
    )

\* to Next.
Spec == 
    /\ Init
    /\ [][Next]_vars


InitP == 
    _Init(
        NODE_ID,
        VALUE,
        FALSE,
        FALSE,
        ""
    )

NextP == 
    _Next(
        NODE_ID,
        VALUE,
        0,
        3,
        0,
        0,
        0,
        0,
        0,
        TRUE,
        FALSE
    )
    
SpecP ==
    /\ InitP
    /\ [][NextP]_vars

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
        v_config_committed,
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


