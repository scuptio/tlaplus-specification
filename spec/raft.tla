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
CONSTANT DB_INIT_STATE_PATH
CONSTANT DB_SAVE_STATE_PATH
CONSTANT DB_ACTION_PATH
CONSTANT APPEND_ENTRIES_MAX


CONSTANT VOTE
CONSTANT REPLICATE
CONSTANT RESTART
CONSTANT RECONFIG
CONSTANT CLIENT_REQUEST

----


VARIABLE v_role
VARIABLE v_log
VARIABLE v_voted_for
VARIABLE v_snapshot
VARIABLE v_commit_index
VARIABLE v_acked_value
VARIABLE v_messages
VARIABLE v_current_term
VARIABLE v_conf_committed
VARIABLE v_conf_new
VARIABLE v_follower_vote_granted
VARIABLE v_follower_next_index
VARIABLE v_follower_match_index
VARIABLE v_follower_conf
VARIABLE v_follower_term_commit_index

VARIABLE v_history


VARIABLE __action__
VARIABLE v_cnt_limit




TERM_VALUE == Nat

vars_config == <<
    v_conf_committed,
    v_conf_new,
    v_follower_conf,
    v_follower_term_commit_index
>>

vars_leader == <<
    v_follower_vote_granted,
    v_follower_next_index,
    v_follower_match_index,
    v_follower_conf,
    v_follower_term_commit_index
>>

vars_control == <<v_cnt_limit>>

vars == <<
    v_role,
    v_current_term,
    v_log, 
    v_voted_for,
    v_snapshot,
    v_commit_index,
    v_follower_next_index,
    v_follower_match_index,
    v_follower_vote_granted,
    v_messages,
    v_history,
    v_acked_value,  
    v_conf_committed,
    v_conf_new,
    v_follower_conf,
    v_follower_term_commit_index, 
    __action__,
    vars_control
>>

vars_view == <<
    v_role,
    v_current_term,
    v_log, 
    v_voted_for,
    v_snapshot,
    v_commit_index,
    v_follower_next_index,
    v_follower_match_index,
    v_follower_vote_granted,
    v_conf_committed,
    v_conf_new,
    v_follower_conf,
    v_follower_term_commit_index, 
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
    v_role,
    v_commit_index,
    v_follower_next_index,
    v_follower_match_index,
    v_follower_vote_granted,
    v_messages,
    v_history,
    v_acked_value
>>

vars_except_action == <<
    vars_hard_state,
    v_role,
    v_commit_index,
    v_follower_next_index,
    v_follower_match_index,
    v_acked_value,
    v_follower_vote_granted,
    v_messages,
    v_history
>>

vars_vote == <<v_follower_vote_granted>>
vars_replicate == <<v_commit_index, v_follower_next_index, v_follower_match_index, v_acked_value>>



        
_RaftVariables(_nid) ==
    [
        role |-> v_role[_nid],
        current_term |-> v_current_term[_nid],
        log |-> v_log[_nid],
        snapshot |-> v_snapshot[_nid],
        voted_for |-> v_voted_for[_nid],
        commit_index |-> v_commit_index[_nid],
        conf_committed |-> v_conf_committed[_nid],
        conf_new |-> v_conf_new[_nid],
        follower_vote_granted |-> v_follower_vote_granted[_nid],        
        follower_next_index |-> v_follower_next_index[_nid],
        follower_match_index |-> v_follower_match_index[_nid],
        follower_term_commit_index |-> v_follower_term_commit_index[_nid],
        follower_conf |-> v_follower_conf[_nid]
    ]

               
ActionCheckState(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            {_node_id}, 
            ActionInput, 
            __ActionCheck
       )

       
InitActionSeqSetup(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            _node_id, 
            ActionInput, 
            __ActionInit
       )
       
ActionSeqSetupAll(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            _node_id, 
            ActionInput, 
            __ActionInit
       )

SaveVars ==
    [
        role |-> v_role,
        current_term |-> v_current_term,
        log |-> v_log,
        snapshot |-> v_snapshot,
        voted_for |-> v_voted_for,
        commit_index |-> v_commit_index,
        conf_committed |-> v_conf_committed,
        conf_new |-> v_conf_new        
    ]
    
SaveStates ==
    DB_SAVE_STATE_PATH /= "" =>
        SaveValue(SaveVars, DB_SAVE_STATE_PATH)

        
SaveActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)

SaveInitActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)



CntAppendLog == "App"
CntHandleAppendReq == "HAppReq"
CntHandleAppendResp == "HAppResp"
CntLogCompaction == "LogComp"
CntHandleApplyReq == "HAplReq"
CntHandleApplyResp == "HAplResp"

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
    CntAppendLog, 
    CntHandleAppendReq, 
    CntHandleAppendResp,  
    CntLogCompaction, 
    CntHandleApplyReq,
    CntHandleApplyResp,
    CntClientReq,
    CntRestart,
    CntVoteReq, 
    CntHandleVoteReq, 
    CntHandleVoteResp,
    CntTickUpConf,
    CntHandleUpConfReq,
    CntHandleUpConfResp,
    CntReConfBegin,
    CntReConfCommit
}




_ConfTermIndex(
    _term,
    _index
) ==
    [
        term |-> _term,
        index |-> _index
    ]

  
_Init(
    _node_id,
    _value,
    _enable_state_db,
    _enable_action,
    _state_db_path
)
 ==
    /\ IF _enable_state_db THEN
        \* read initial state from database
        LET all_state_set == QueryAllValues(_state_db_path)
        IN \E all_state \in all_state_set:
          (LET node_ids_has_state == DOMAIN all_state.role
               e == InitStateSetup(
                    _node_id \ node_ids_has_state, node_ids_has_state, all_state, _value)
           IN /\ v_role = e.role
                /\ v_current_term = e.current_term
                /\ v_log = e.log
                /\ v_snapshot = e.snapshot
                /\ v_voted_for = e.voted_for
                /\ v_commit_index = e.commit_index
                /\ v_conf_committed = e.conf_committed
                /\ v_conf_new = e.conf_new
           ) 
       ELSE
           \* build initial state
           LET e == InitStateSetup(_node_id, {}, NULL, _value)
           IN   /\ v_role = e.role
                /\ v_current_term = e.current_term
                /\ v_log = e.log
                /\ v_snapshot = e.snapshot
                /\ v_voted_for = e.voted_for
                /\ v_commit_index = e.commit_index
                /\ v_conf_committed = e.conf_committed
                /\ v_conf_new = e.conf_new 
    /\ v_messages = {}
    /\ v_history = <<>>
    /\ v_acked_value = {}
    /\ v_follower_next_index = [i \in _node_id |-> [j \in NODE_ID |-> 1]]
    /\ v_follower_match_index = [i \in _node_id |-> [j \in NODE_ID |-> 0]]
    /\ v_follower_vote_granted = [i \in _node_id |-> [j \in NODE_ID |-> 0]]
    /\ v_follower_conf = [i \in _node_id |-> [j \in _node_id |-> [conf_committed |-> _ConfVersion(0, 0, 0), conf_new |-> _ConfVersion(0, 0, 0)]]]
    /\ v_follower_term_commit_index = [i \in _node_id |-> [j \in _node_id |-> _ConfTermIndex(0, 0)]]
    /\ v_cnt_limit = [i \in CntLimitDomain |-> 0]
    /\ LET actions == InitActionSeqSetup(_node_id)
       IN __action__ = InitAction(
            actions,
            actions,
            _enable_action
        )


_ConfigQuorumCheck(
    _leader,
    _config_term,
    _config_version,
    _config_node,
    _follower_conf,
    _check_conf_new
) ==

    /\ _leader \in _config_node
    /\ \E Q \in QuorumOf(_config_node):
            /\ _leader \in Q
            /\ \A j \in Q \ {_leader}:
                /\ _follower_conf[j] /= NULL
                /\ IF _check_conf_new THEN
                        /\ _follower_conf[j].conf_new.version = _config_version
                        /\ _follower_conf[j].conf_new.term = _config_term
                   ELSE
                        /\ _follower_conf[j].conf_committed.version = _config_version
                        /\ _follower_conf[j].conf_committed.term = _config_term
                        
_TermCommitIndexQuorumCheck(
    _leader,
    _leader_term,
    _conf_new,
    _follower_term_cindex
) ==
    /\ _conf_new /= NULL
    /\ _leader \in _conf_new.nid_vote
    /\ \E Q \in QuorumOf(_conf_new.nid_vote):
           /\ _leader \in Q
           /\ \A j \in Q \ {_leader}:
                /\ _follower_term_cindex[j].term = _leader_term
                /\ _follower_term_cindex[j].index >= _conf_new.conf_version.index

           

_QuorumOverlapped(_node_set1, _node_set2) ==
    \A q1 \in QuorumOf(_node_set1), q2 \in QuorumOf(_node_set2):
        q1 \cap q2 /= {}


    
_ConfigNew(_conf_committed, _conf_new, _i) ==
     IF _conf_new[_i] /= NULL THEN
        _conf_committed[_i]
     ELSE
        _conf_new[_i]
        
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


_IndexTermOfSnapshotEntries(_entries) ==
        IF Cardinality(_entries) = 0 THEN 
            [begin_index |-> 0, end_index |-> 0, index |-> 0, term |-> 0]
        ELSE
            LET begin_e == CHOOSE e \in _entries:
                            ~(\E _e \in _entries:
                                _e.index < e.index
                             )
                end_e == CHOOSE e \in _entries:
                            ~(\E _e \in _entries:
                                _e.index > e.index
                             )
            IN \* [begin_index, end_index] , minimum, maximum index pair
                [begin_index |-> begin_e.index, end_index |-> end_e.index, index |-> end_e.index, term |-> end_e.term]



MessageApplySnapshot(
    _source,
    _dest,
    _term,
    _snapshot
) == 
    LET index_term == _IndexTermOfSnapshotEntries(_snapshot.entries)
    IN
     Message(_source, _dest, ApplyReq,
         [
            term     |-> _term,
            id       |-> "",
            begin_index |-> index_term.begin_index,
            end_index |-> index_term.end_index,
            snapshot |-> _snapshot
         ]
     )


\* TLA+ {D240422N-MsgUpdateConfReq}
MsgUpdateConfReq(
    _source,
    _dest,
    _term,
    _conf_committed,
    _conf_new
) ==
     Message(_source, _dest, UpdateConfigReq,
         [
            term     |-> _term,
            conf_committed |-> _conf_committed,
            conf_new |-> _conf_new
         ]
     )

\* TLA+ {D240422N-MsgUpdateConfResp}
MsgUpdateConfResp(
    _source,
    _dest,
    _term,
    _conf_committed,
    _conf_new
) ==
     Message(_source, _dest, UpdateConfigResp,
         [

            term     |-> _term,
            conf_committed |-> _conf_committed,
            conf_new |-> _conf_new
         ]
     )
          
_UpdateTerm(_node_id, _term) ==
    IF _term > v_current_term[_node_id] THEN
            [state |-> Follower, current_term |-> _term, voted_for |-> INVALID_NODE_ID]
    ELSE
            [state |-> v_role[_node_id], current_term |-> v_current_term[_node_id], voted_for |-> v_voted_for[_node_id]]


_ConfigVersionLess(_c1, _c2) ==
    \/ _c1.term < _c2.term
    \/ (/\ _c1.term = _c2.term 
        /\ _c1.version < _c2.version
       )

\* TLA+ {D240504N-MsgAppendRequest}    
MsgAppendRequest(
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
                append_message == MsgAppendRequest(
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
    _v_role,
    _v_follower_next_index,
    _v_follower_match_index,
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
    /\ v_role' = [v_role EXCEPT ![_node_id] = Leader]
    /\ LET last_log_index == LastLogIndex(_v_log[_node_id], _v_snapshot[_node_id])
        IN  _v_follower_next_index' = [_v_follower_next_index EXCEPT ![_node_id] = [j \in NODE_ID |-> last_log_index + 1]]
    /\ _v_follower_match_index' = [_v_follower_match_index EXCEPT ![_node_id] = [j \in NODE_ID |-> _v_snapshot[_node_id].index]]
    /\ _v_commit_index' = [_v_commit_index EXCEPT ![_node_id] = _v_snapshot[_node_id].index]


_ClearLeaderVar(_nid, _nid_set) ==
    /\ v_follower_vote_granted'   = [v_follower_vote_granted EXCEPT ![_nid] = [j \in _nid_set |-> 0]]
    /\ v_follower_next_index' = [v_follower_next_index EXCEPT ![_nid] = [j \in _nid_set |-> 1]]
    /\ v_follower_match_index' = [v_follower_match_index EXCEPT ![_nid] = [j \in _nid_set |-> 0]]
    /\ v_commit_index' = [v_commit_index EXCEPT ![_nid] = v_snapshot[_nid].index]
    /\ v_follower_term_commit_index' = [v_follower_term_commit_index EXCEPT ![_nid] = [j \in _nid_set |-> [term |-> 0, index |-> 0]]]
    /\ v_follower_conf' = [v_follower_conf EXCEPT ![_nid] = [j \in _nid_set |->
                [conf_committed |-> _ConfVersion(0, 0, 0), conf_new |-> _ConfVersion(0, 0, 0)]
            ]]

_UnchangedLeaderVar(_nid) ==
    /\ UNCHANGED <<v_follower_vote_granted, v_follower_match_index, v_commit_index, v_follower_term_commit_index, v_follower_conf>>
    

\* NODE_ID _node_id times out and starts a new election.
VoteRequestVote(_node_id, _max_term, _check_safety, _node_id_set, _enable_action) == 
    /\ _node_id \in v_conf_committed[_node_id].nid_vote
    /\ _node_id \in v_conf_new[_node_id].nid_vote
    /\ TermLE(_node_id, v_current_term, _max_term)
    /\ v_role[_node_id] = Follower
    /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = v_current_term[_node_id] + 1]
    /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _node_id]
    /\ LET nodes == v_conf_committed[_node_id].nid_vote \cup v_conf_new[_node_id].nid_vote
       IN  (
        /\ IF {_node_id} = nodes THEN
                _BecomeLeader(
                    _node_id,
                    v_current_term',
                    v_role,
                    v_follower_next_index,
                    v_follower_match_index,
                    v_commit_index,
                    v_log,
                    v_snapshot,v_history, _check_safety)
           ELSE /\ v_role' = [v_role EXCEPT ![_node_id] = Candidate]
                /\ UNCHANGED <<v_history, v_follower_match_index, v_follower_next_index, v_commit_index>>
        /\ v_follower_vote_granted'   = [v_follower_vote_granted EXCEPT ![_node_id][_node_id] = v_current_term'[_node_id]]
        /\  LET  payload == [
                    term            |-> v_current_term[_node_id] + 1,
                    last_log_term   |-> LastLogTerm(v_log[_node_id], v_snapshot[_node_id]),
                    last_log_index  |-> LastLogIndex(v_log[_node_id], v_snapshot[_node_id])
                ]  
                messages == MessageSet({_node_id}, nodes \ {_node_id}, VoteRequest,  payload)
                actions_input == Action(ActionInput, MessageNP(_node_id, _node_id, __ActionRequestVote))
                actions_output == Actions(ActionOutput, messages)
                actions0 == ActionCheckState(_node_id)
                actions == ActionSeqSetupAll(_node_id_set)
            IN /\ v_messages' = WithMessageSet(messages, v_messages)
               /\ SetAction(__action__, actions, actions0 \o actions_input \o actions_output, _enable_action)
        )
    /\ UNCHANGED <<
            v_log, 
            v_snapshot,
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
                vote_granted |-> grant
            ]
        a1 == action  
        reply ==  Message(_node_id, _from_node_id, VoteResponse, payload)
        a2 == Action(ActionOutput, reply)
        actions == ActionSeqSetupAll(_node_id_set)
    IN /\  (\/ (/\ grant
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = _from_node_id] 
                /\ v_role' = [v_role EXCEPT ![_node_id] = term_context.state]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]
               )
            \/ (/\ ~grant
                /\ v_role' = [v_role EXCEPT ![_node_id] = term_context.state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]
               )
           )
        /\ SetAction(__action__, actions, a1 \o a2, _enable_action)
        /\ v_messages' = WithMessage(reply, v_messages)   
        /\ UNCHANGED << 
                v_follower_vote_granted,
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
            /\ v_role[i] \in {Candidate, Leader} 
            /\ (\/( /\ _m.vote_granted
                    /\ v_follower_vote_granted' = [v_follower_vote_granted EXCEPT ![i][_from_node] = _m.term]    
                    /\ IF  /\ v_role[i] = Candidate
                           /\ LET granted_set == { j \in _node_id : v_follower_vote_granted'[i][j] = v_current_term[i] } \cup {i}
                              IN /\ granted_set \in  QuorumOf(v_conf_committed[i].nid_vote)
                                 /\ (\/ v_conf_new[i] = v_conf_committed[i]
                                     \/ granted_set \in QuorumOf(v_conf_new[i].nid_vote)
                                    )
                       THEN
                        (     _BecomeLeader(
                                    i,
                                    v_current_term,
                                    v_role,
                                    v_follower_next_index,
                                    v_follower_match_index,
                                    v_commit_index,
                                    v_log,
                                    v_snapshot,v_history, _check_safety)
                              /\ SetAction(__action__, actions,  _actions, _enable_action)
                              /\ UNCHANGED <<v_voted_for, v_current_term>>
                          )
                       ELSE   
                            /\ SetAction(__action__, actions, _actions, _enable_action)
                            /\ UNCHANGED <<
                                v_role, v_voted_for, v_current_term,
                                v_follower_next_index, v_follower_match_index, v_commit_index, v_history>>                   
                    )
                \/ ( /\ ~_m.vote_granted
                     /\ SetAction(__action__, actions,  _actions, _enable_action)
                     /\ UNCHANGED <<
                                v_role, v_voted_for, v_current_term, v_follower_vote_granted,  
                                v_follower_next_index, v_follower_match_index, v_commit_index, v_history>>
                    )
                )
             
        ELSE 
             /\ LET term_context == _UpdateTerm(i, _m.term)
                IN (/\ v_role' = [v_role EXCEPT ![i] = term_context.state]
                    /\ v_voted_for' = [v_voted_for EXCEPT ![i] = term_context.voted_for]
                    /\ v_current_term' = [v_current_term EXCEPT ![i] = term_context.current_term]   
                )
             /\ UNCHANGED <<v_follower_vote_granted,  v_follower_next_index, v_commit_index, v_follower_match_index, v_history>>
             /\ SetAction(__action__, actions,  _actions, _enable_action)
    /\ UNCHANGED <<v_log, v_snapshot, vars_config>>

                 
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendLogEntries(i, _append_entries_max, _check_safety, _node_id, _enalbe_action) ==
    /\ v_role[i] = Leader
    /\ LET node_ids == v_conf_committed[i].nid_log \cup v_conf_new[i].nid_log
           n == _append_entries_max 
           msgs == AppendRequestMessages(
                v_log, v_follower_next_index, 
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
            v_current_term, v_role, 
            v_voted_for, v_snapshot, v_log, 
            v_history,
            v_follower_match_index,
            v_follower_next_index,
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
                            term |-> current_term,
                            append_success |-> FALSE,
                            commit_index |-> 0,
                            match_index |-> 0,
                            next_index |-> next_index \* only when reject, tell leader the correct next index
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  /\ v_messages' = WithMessage(reply_message, v_messages)
                        /\ SetAction(__action__, _setup_action,   action_handle_append \o output_action, _enable_action)    
                /\ v_role' = [v_role EXCEPT ![_node_id] = current_state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = current_voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ UNCHANGED <<v_acked_value, v_log, v_snapshot,  v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_TO_FOLLOWER -> (
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ v_role' = [v_role EXCEPT ![_node_id] = Follower]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
                /\ SetAction(__action__, _setup_action,   action_handle_append, _enable_action)    
                /\ UNCHANGED <<v_acked_value, v_log, v_snapshot, v_messages, v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_ACCEPT -> (
                /\ 
                    LET \* TLA+ {D240524N- update commit index}
                        c_index == 
                        IF commit_index > v_commit_index[_node_id] THEN
                            IF commit_index <= result.match_index THEN
                                commit_index
                            ELSE
                                result.match_index
                        ELSE
                            v_commit_index[_node_id]
                        
                        reply_payload == [
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
                /\ v_role' = [v_role EXCEPT ![_node_id] = current_state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = current_voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = current_term]
                /\ UNCHANGED <<v_snapshot>>
            )
            [] OTHER  -> (
                FALSE
            )
        )
        /\ UNCHANGED << v_follower_next_index, v_follower_match_index>>

Agree(_match_index, _index, _node_id, _v_conf_committed, _v_conf_new) ==
    /\ LET _node_old == _v_conf_committed[_node_id].nid_vote
          IN {_node_id} \cup 
            {
                j \in _node_old :  
                    /\ j /= _node_id
                    /\ _match_index[_node_id][j] >= _index
            } \in QuorumOf(_node_old)
    /\ (\/ _v_conf_new[_node_id] = _v_conf_committed[_node_id]
        \/ LET _node_new == _v_conf_new[_node_id].nid_vote
           IN {_node_id} \cup 
                {
                    j \in _node_new :  
                        /\ j /= _node_id
                        /\ _match_index[_node_id][j] >= _index
                } \in QuorumOf(_node_new)
          )

AgreeIndex(_match_index, _v_log, _v_snapshot, _node_id, _v_conf_committed, _v_conf_new) ==
    LET index_set == {_v_log[_node_id][j].index: j \in DOMAIN  _v_log[_node_id]} \cup 1.._v_snapshot[_node_id].index
    IN {i \in index_set : Agree(_match_index, i, _node_id, _v_conf_committed, _v_conf_new) }
    
    
_HandleAdvanceCommitIndex(
    _match_index0, _v_log, _v_snapshot, 
    _v_conf_committed, _v_conf_new,
    _node_id, _node_id_set, _check_safety
) ==
    
    LET 
        \* the leader's last index is its match index
        _match_index == [_match_index0 EXCEPT ![_node_id][_node_id] = LastLogIndex(_v_log[_node_id], _v_snapshot[_node_id])]
        agree_indexes == AgreeIndex(_match_index, _v_log, _v_snapshot, _node_id,  _v_conf_committed, _v_conf_new)
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
                            /\ v_follower_next_index'  = [v_follower_next_index  EXCEPT ![_node_id][_source] = _payload.match_index + 1]
                            /\ v_follower_match_index' = [v_follower_match_index EXCEPT ![_node_id][_source] = _payload.match_index]
                            /\ _HandleAdvanceCommitIndex(v_follower_match_index', v_log, v_snapshot,
                                    v_conf_committed, v_conf_new,
                                 _node_id, _node_id_set, _check_safety)
                            /\ v_follower_term_commit_index' = [
                                v_follower_term_commit_index EXCEPT ![_node_id][_source] = 
                                    [term |-> _payload.term, index |-> _payload.commit_index] ]
                           )
                        \/ (/\ \lnot _payload.append_success
                            /\ IF _payload.next_index > 0 THEN
                                    LET last_log_index == LastLogIndex(v_log[_node_id], v_snapshot[_node_id])
                                        new_next_index == Min({last_log_index + 1, _payload.next_index})
                                    IN v_follower_next_index'  = [v_follower_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                               ELSE 
                                    LET new_next_index == Max({v_follower_next_index[_node_id][_source] - 1, 1})
                                    IN v_follower_next_index'  = [v_follower_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                            /\ UNCHANGED <<v_acked_value, v_commit_index, v_follower_match_index, v_follower_term_commit_index>>
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
                    v_follower_next_index,
                    v_follower_match_index,
                    v_follower_vote_granted,
                    v_messages,
                    v_follower_term_commit_index,
                    v_history
                    >>
            )
     /\ v_role' = [v_role EXCEPT ![_node_id] = term_context.state]
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
       IN __HandleVoteResponse(message.dest, message.source, 
            message.payload, actions1 \o actions2, 
            _check_safety, _node_id_set, _enable_action)
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
    
\* TLA+ {D240524N- update commit index}
HandleApplySnapshotReq(_node_id, message, _node_id_set, _enable_action) ==
    /\ message.dest = _node_id
    /\ message.name = ApplyReq
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll(_node_id_set)
           actions1 == ActionCheckState(_node_id)
           term_context == _UpdateTerm(_node_id, payload.term)
       IN  /\ (IF /\ payload.term = term_context.current_term 
                  /\ payload.begin_index < payload.end_index
                  /\ payload.end_index >= 1
                  /\ payload.end_index >= LastLogIndex(v_log[_node_id], v_snapshot[_node_id])
                  /\ payload.end_index > v_commit_index[_node_id]
               THEN
                  /\ v_snapshot' = [v_snapshot EXCEPT ![_node_id] = payload.snapshot]
                  /\ v_log' = [v_log EXCEPT ![_node_id] = <<>> ]
                  /\ LET resp_payload ==  [term |-> term_context.current_term, id |-> payload.id, match_index |-> payload.end_index]
                          resp == Message(_node_id, from_node_id, ApplyResp, resp_payload)  
                          actions3 == Action(ActionOutput, resp)
                          actions2 == Action(ActionInput, message)
                        
                     IN /\ SetAction(__action__, actions0, actions1 \o actions2 \o actions3, _enable_action)
                        /\ v_messages' = WithMessage(resp, v_messages)
               ELSE
                  /\ LET actions2 == Action(ActionInput, message)
                      IN SetAction(__action__, actions0, actions1 \o actions2, _enable_action)
                  /\ UNCHANGED <<v_snapshot, v_log, v_messages>>
              )
           /\ v_role' = [v_role EXCEPT ![_node_id] = term_context.state]
           /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
           /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]
           /\ UNCHANGED <<
                        v_commit_index,
                        v_follower_next_index,
                        v_follower_match_index,
                        v_history,
                        v_acked_value
                        >>
     /\ UNCHANGED <<vars_vote, vars_config>>

HandleApplySnapshotResp(_node_id, message, _node_id_set, _enable_action) ==
    /\ message.dest = _node_id
    /\ message.name = ApplyResp
    /\ LET _source == message.source
           payload == message.payload
       IN /\ payload.term = v_current_term[_node_id]
          /\ v_follower_next_index'  = [v_follower_next_index  EXCEPT ![_node_id][_source] = 
                Max({payload.match_index + 1, v_follower_next_index[_node_id][_source]})]
          /\ v_follower_match_index' = [v_follower_match_index EXCEPT ![_node_id][_source] = 
                Max({payload.match_index, v_follower_match_index[_node_id][_source]})]
    /\ LET  actions0 == ActionSeqSetupAll(_node_id_set)
            actions1 == ActionCheckState(_node_id)
            actions2 == Action(ActionInput, message)
       IN SetAction(__action__, actions0, actions1 \o actions2, _enable_action)
    /\ UNCHANGED <<
            v_role,
            v_current_term,
            v_log, 
            v_voted_for,
            v_snapshot,
            v_commit_index,
            v_follower_vote_granted,
            v_messages,
            v_history,
            v_acked_value,  
            v_conf_committed,
            v_conf_new,
            v_follower_conf,
            v_follower_term_commit_index
       >>
         
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
            v_conf_committed,
            v_conf_new,
            v_follower_conf
        >>


    
RestartNode(i, _node_id, _enable_action) ==
    /\ v_role' = [v_role EXCEPT ![i] = Follower]
    /\ _ClearLeaderVar(i, _node_id)
    /\ LET  a1 == ActionCheckState(i)
            a2 == Action(ActionInput, MessageLocalNP(i, __ActionRestartNode))
            actions0 == ActionSeqSetupAll(_node_id)
       IN SetAction(__action__, actions0, a1 \o a2, _enable_action)    
    /\ UNCHANGED <<
            v_current_term,
            v_log, 
            v_snapshot,
            v_voted_for,
            v_messages,
            v_history,
            v_acked_value,
            v_conf_committed,
            v_conf_new
         >>



_MergeSnapshotEntries(_snapshot_entries_1, _snapshot_entries_2) ==
    LET entries == _snapshot_entries_1 \cup _snapshot_entries_2
        entries_merged == \* left only one value with max index 
            {
                x \in entries:
                ~ (\E y \in entries:
                    /\ x.value = y.value
                    /\ x.term <= y.term
                    /\ x.index < y.index
                  )
            }
    IN entries_merged
       
LogCompaction(nid, _node_id, _enable_action) ==
    /\ v_snapshot[nid].index < v_commit_index[nid]
    /\ LET  last_log_index == LastLogIndex(v_log[nid], v_snapshot[nid])
            compact_log_index == Min({last_log_index, v_commit_index[nid]})
            offset == LogIndexToOffset(v_log[nid], v_snapshot[nid], compact_log_index)
            compact_log == SubSeq(v_log[nid], 1, offset)
       IN ( /\ offset > 0
            /\ LET entries1 == { compact_log[i]: i \in DOMAIN compact_log}
                   entries2 == _MergeSnapshotEntries(v_snapshot[nid].entries, entries1)              
                   index_term == _IndexTermOfSnapshotEntries(entries2)
               IN v_snapshot' = [v_snapshot EXCEPT  ![nid] = 
                    [index |-> index_term.index, term |-> index_term.term, entries |-> entries2] ]
            /\ v_log' = [v_log EXCEPT  ![nid] = SubSeq(v_log[nid], offset + 1, Len(v_log[nid]))]
            /\ LET  actions0 == ActionSeqSetupAll(_node_id)
                    actions1 == ActionCheckState(nid)
                    actions2 == Action(ActionInput, Message(nid, nid, __ActionLogCompaction, compact_log_index))
                IN SetAction(__action__, actions0, actions1 \o actions2, _enable_action)
           )
    /\ UNCHANGED <<
            v_role,
            v_current_term,
            v_voted_for,
            v_messages,
            v_history,
            vars_vote,
            vars_replicate,
            vars_config
            >>


ClientRequest(nid, v , _node_id_set, _check_safety, _enable_action) ==
    /\ v_role[nid] = Leader
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
          _HandleAdvanceCommitIndex(v_follower_match_index, v_log', v_snapshot,
                 v_conf_committed, v_conf_new,
                 nid, _node_id_set, _check_safety)
       ELSE
           UNCHANGED <<v_commit_index,v_acked_value>>
    /\ UNCHANGED <<
            v_history, v_current_term, v_role, 
            v_voted_for, v_snapshot, v_messages, 
            vars_vote,
            v_follower_next_index, v_follower_match_index, vars_config
            >> 



MsgsUpdateConfReq(
    _source, 
    _node_ids, 
    _current_term,
    _v_conf_committed,
    _v_conf_new,
    _v_follower_conf
) ==
    LET f == [dest \in { 
                i \in (_node_ids \ {_source}) :
                  LET _conf == _v_follower_conf[_source][i]
                  IN \/ _conf = NULL \* not set
                     \/ (/\ _conf /= NULL
                         /\ (\/ _conf.conf_committed.term /= _v_conf_committed[_source].conf_version.term
                             \/ _conf.conf_committed.version /= _v_conf_committed[_source].conf_version.version
                             \/ _conf.conf_new.term /= _v_conf_committed[_source].conf_version.term
                             \/ _conf.conf_new.version /= _v_conf_committed[_source].conf_version.version
                            )
                        )
              } |-> 
                MsgUpdateConfReq(
                    _source, 
                    dest, 
                    _current_term[_source],
                    _v_conf_committed[_source],
                    _v_conf_new[_source]
                    )
             ]
    IN {f[id] : id \in DOMAIN f}


\* TLA+ {D240422N-LeaderSendUpdateConfToFollower}
LeaderSendUpdateConfToFollower(_nid, _nid_set, _enalbe_action) ==
    /\ v_role[_nid] = Leader
    /\ LET nid_set == v_conf_committed[_nid].nid_log \cup v_conf_new[_nid].nid_log 
           msgs == MsgsUpdateConfReq(_nid, nid_set, v_current_term, v_conf_committed, v_conf_new, v_follower_conf)
           actions0 == ActionSeqSetupAll(_nid_set)
           actions1 == ActionCheckState(_nid)
           actions2 == Action(ActionInput, MessageLocalNP(_nid, __ActionSendUpdateConfig))
           actions3 == Actions(ActionOutput, msgs)
       IN /\ v_messages' = WithMessageSet(msgs, v_messages)
          /\ SetAction(__action__, actions0, actions1 \o actions2 \o actions3, _enalbe_action)    
    /\ UNCHANGED <<
            v_commit_index, 
            v_current_term, v_role, 
            v_voted_for, v_snapshot, v_log, 
            v_history,
            v_follower_match_index,
            v_follower_next_index,
            v_acked_value
            >>
    /\ UNCHANGED <<vars_vote, vars_config>>


\* TLA+ {D240422N-_UpdateConf}
_UpdateConf(
    _node_id, 
    _conf_committed, 
    _conf_new
) ==
        LET c_c == IF _ConfigVersionLess(v_conf_committed[_node_id].conf_version, _conf_committed.conf_version) THEN
                _conf_committed
            ELSE
                v_conf_committed[_node_id]
            c_n == IF _ConfigVersionLess(v_conf_new[_node_id].conf_version, _conf_new.conf_version) THEN
                _conf_new
            ELSE
                v_conf_new[_node_id]
        IN 
        [conf_committed |-> c_c, conf_new |-> c_n, term |-> v_current_term[_node_id]]



\* TLA+ {D240422N-HandleUpdateConfReq}
HandleUpdateConfReq(_nid, _msg, _nid_set, _enable_action) ==
    /\ _msg.dest = _nid
    /\ _msg.name = UpdateConfigReq
    /\(LET conf_committed == _msg.payload.conf_committed
           conf_new == _msg.payload.conf_new
           term == _msg.payload.term
           result == _UpdateConf(_nid, conf_committed, conf_new)
           term_context == _UpdateTerm(_nid, _msg.payload.term)
       IN \* only can update config when the term is equal to current term
          /\ v_current_term[_nid] = term 
          /\ v_conf_committed' = [v_conf_committed EXCEPT ![_nid] = result.conf_committed]
          /\ v_conf_new' = [v_conf_new EXCEPT ![_nid] = result.conf_new]
          /\ LET resp == MsgUpdateConfResp(_msg.dest, _msg.source, 
                result.term,
                result.conf_committed.conf_version, 
                result.conf_new.conf_version
                ) 
                actions0 == ActionSeqSetupAll(_nid_set)
                actions1 == ActionCheckState(_nid)
                input_action == Action(ActionInput, _msg)
                output_action == Action(ActionOutput, resp)
             IN (/\ v_messages' = WithMessage(resp, v_messages)
                 /\ SetAction(__action__, actions0,   actions1 \o input_action \o output_action, _enable_action)
                ) 
      )
    /\ UNCHANGED <<v_log, v_snapshot, v_history, vars_leader, v_acked_value, v_commit_index,
            v_role, v_voted_for, v_current_term
            >>


\* TLA+ {D240422N-HandleUpdateConfResp}
HandleUpdateConfResp(_nid, _msg, _nid_set, _enable_action) ==
    /\ _msg.dest = _nid
    /\ _msg.name = UpdateConfigResp
    /\(LET conf_committed == _msg.payload.conf_committed
           conf_new == _msg.payload.conf_new
           term == _msg.payload.term
           source == _msg.source
       IN /\ v_current_term[_nid] = term
          /\ v_role[_nid] = Leader
          /\ IF \/ v_follower_conf[_nid][source] = NULL
                \/ v_follower_conf[_nid][source].conf_committed /= conf_committed
                \/ v_follower_conf[_nid][source].conf_new /= conf_new
             THEN
                v_follower_conf' = [v_follower_conf EXCEPT ![_nid][source] = [conf_committed |-> conf_committed, conf_new |-> conf_new]]
             ELSE
                UNCHANGED v_follower_conf
       )
     /\ LET actions0 == ActionSeqSetupAll(_nid_set)
            actions1 == ActionCheckState(_nid)
            input_action == Action(ActionInput, _msg)
        IN SetAction(__action__, actions0,   actions1 \o input_action, _enable_action)  
     /\ UNCHANGED <<
            v_current_term, v_history, v_log, v_messages, v_snapshot, v_voted_for,
            v_role,
            vars_vote, vars_replicate,
            v_follower_term_commit_index,
            v_conf_committed, v_conf_new
        >>

_ConfigVersionEqual(
    _c1,
    _c2
) ==
    /\ _c1.term = _c2.term
    /\ _c2.version = _c2.version

\* TLA+ {D240422N-LeaderReConfBegin}
LeaderReConfBegin(_nid, _nid_vote, _nid_log, _nid_set, _enable_action) ==
    /\ v_role[_nid] = Leader
    /\(\/ v_conf_committed[_nid].nid_vote /= _nid_vote
       \/ v_conf_committed[_nid].nid_log /= _nid_log)
    /\ _ConfigVersionEqual(v_conf_committed[_nid].conf_version, v_conf_new[_nid].conf_version) \* already committed
    /\ v_conf_new' = [v_conf_new EXCEPT ![_nid] = 
            [
                conf_version |-> [
                    version |-> v_conf_new[_nid].conf_version.version + 1, 
                    term |-> v_current_term[_nid],
                    index |-> v_commit_index[_nid]
                ],
                nid_vote |-> _nid_vote,
                nid_log |-> _nid_log
            ]
       ]
    /\ LET actions0 == ActionSeqSetupAll(_nid_set)
           actions1 == ActionCheckState(_nid)
           input_action == Action(ActionInput, MessageLocal(_nid, __ActionUpdateConfigBegin, [nid_vote |-> _nid_vote, nid_log |-> _nid_log]))
       IN SetAction(__action__, actions0,   actions1 \o input_action, _enable_action)  
    /\ UNCHANGED <<v_role, v_current_term, v_log,  v_voted_for,
                    v_snapshot, v_commit_index, v_follower_next_index, v_follower_match_index,
                    v_follower_vote_granted, v_messages, v_history, v_acked_value, 
                    v_conf_committed, v_follower_conf, v_follower_term_commit_index
                  >>


\* TLA+ {D240423N-LeaderReConfCommit}
LeaderReConfCommit(_nid, _nid_set, _enable_action) ==
    /\ v_role[_nid] = Leader
    /\ ~_ConfigVersionEqual(v_conf_committed[_nid].conf_version, v_conf_new[_nid].conf_version)  \* not comitted yet
        \*old configuration was accepted and ACKed by old quorum set
        \*It is possible for old committed config was not ACKed by old quorum, the newly re-config cannot advance its commitment state
    /\   _ConfigQuorumCheck(_nid, v_conf_committed[_nid].conf_version.term, v_conf_committed[_nid].conf_version.version, v_conf_committed[_nid].nid_vote, v_follower_conf[_nid], FALSE)
        \*new configuration was accepted by old quorum set
    /\ _ConfigQuorumCheck(_nid, v_conf_new[_nid].conf_version.term, v_conf_new[_nid].conf_version.version, v_conf_committed[_nid].nid_vote, v_follower_conf[_nid], TRUE)
    /\ _ConfigQuorumCheck(_nid, v_conf_new[_nid].conf_version.term, v_conf_new[_nid].conf_version.version, v_conf_new[_nid].nid_vote, v_follower_conf[_nid], TRUE)
    /\ _TermCommitIndexQuorumCheck(_nid, v_current_term[_nid], v_conf_new[_nid], v_follower_term_commit_index[_nid])
    /\ v_conf_committed' = [
            v_conf_committed EXCEPT ![_nid] = 
                [
                    conf_version |-> v_conf_new[_nid].conf_version,
                    nid_vote |-> v_conf_new[_nid].nid_vote,
                    nid_log |-> v_conf_new[_nid].nid_log
                ]
           ]
    /\ LET actions0 == ActionSeqSetupAll(_nid_set)
           actions1 == ActionCheckState(_nid)
           input_action == Action(ActionInput, MessageLocalNP(_nid, __ActionUpdateConfigCommit))
       IN SetAction(__action__, actions0,   actions1 \o input_action, _enable_action) 
    /\ UNCHANGED <<v_role, v_current_term, v_log,  v_voted_for,
                    v_snapshot, v_commit_index, v_follower_next_index, v_follower_match_index,
                    v_follower_vote_granted, v_messages, v_history, v_acked_value, 
                    v_conf_new, v_follower_conf, v_follower_term_commit_index
                 >>
                    
_CountLimit(_v_count, _type, _max_limit) ==
    IF _max_limit > 100 THEN
        /\ _v_count' = _v_count
    ELSE
        (/\ _v_count[_type] < _max_limit
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
        \/ (/\ _CountLimit(v_cnt_limit, CntAppendLog, _max_replicate)
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
                \/ ( /\ _CountLimit(v_cnt_limit, CntHandleApplyReq, _max_replicate)
                     /\ HandleApplySnapshotReq(i, m, _node_id, _enable_action)
                    )
                \/ ( /\ _CountLimit(v_cnt_limit, CntHandleApplyResp, _max_replicate)
                     /\ HandleApplySnapshotResp(i, m, _node_id, _enable_action)
                    )
            )
        \/ (/\ _CountLimit(v_cnt_limit, CntVoteReq, _max_vote)
                /\ VoteRequestVote(i, _max_term, _check_safety, _node_id, _enable_action)
               )
        \/ (\E m \in v_messages :
                \/ (/\ _CountLimit(v_cnt_limit, CntHandleVoteReq, _max_vote)
                    /\ HandleVoteReq(i, m, _node_id, _enable_action)
                   )
                \/ (/\ _CountLimit(v_cnt_limit, CntHandleVoteResp, _max_vote) 
                    /\ HandleVoteResp(i, m, _check_safety, _node_id, _enable_action))
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntRestart, _max_restert) 
            /\ RestartNode(i, _node_id, _enable_action)
            )
        \/ (/\ _CountLimit(v_cnt_limit, CntClientReq, _max_client_req)
            /\ \E v \in _value:
                ClientRequest(i, v, _node_id, _check_safety,  _enable_action)
            )
        \/ (/\ _CountLimit(v_cnt_limit, CntTickUpConf, _max_reconfig)
            /\ LeaderSendUpdateConfToFollower(i, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntReConfBegin, _max_reconfig)
            /\ \E nid_log \in SUBSET(_node_id):
                 \E nid_vote \in SUBSET(nid_log):
                    /\ nid_vote /= {}
                    /\ nid_log /= {}
                    /\ LeaderReConfBegin(i, nid_vote, nid_log, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntReConfCommit, _max_reconfig)
            /\ LeaderReConfCommit(i, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntHandleUpConfReq, _max_reconfig)
            /\ \E m \in v_messages :
                HandleUpdateConfReq(i, m, _node_id, _enable_action)
           )
        \/ (/\ _CountLimit(v_cnt_limit, CntHandleUpConfResp, _max_reconfig)
            /\ \E m \in v_messages :
                HandleUpdateConfResp(i, m, _node_id, _enable_action)
           )
           
Init == 
    _Init(
        NODE_ID,
        VALUE,
        DB_INIT_STATE_PATH /= "",
        ENABLE_ACTION,
        DB_INIT_STATE_PATH
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
    /\ StateOK(
        v_role,
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
        v_conf_committed,
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
        v_role,
        v_current_term,
        v_log,
        v_snapshot
        )

                    
AssertSafty ==
    /\ AssertStateOK
    /\ AssertLogIndexTermGrow
    /\ AssertPrefixCommitted
    /\ AssertAtMostOneLeaderPerTerm
    /\ AssertFollowerAppend
    /\ AssertLeaderHasAllAckedValues
    
===============================================================================


