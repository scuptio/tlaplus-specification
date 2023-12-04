--------------------------------- MODULE raft ---------------------------------



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
CONSTANT DB_STATE_PATH
CONSTANT DB_ACTION_PATH
CONSTANT APPEND_ENTRIES_MAX
CONSTANT VOTE
CONSTANT REPLICATE
CONSTANT REASTART
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
    v_vote_granted,
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
    \*v_next_index,
    \*v_match_index,
    \*v_vote_granted,
    v_messages
    \*v_pc,
    \*v_pc_context
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
    /\ LET actions == InitActionSeqSetup
        IN InitAction(
            __action__,
            actions,
            actions
        )




\*
\*
\* used by (Abstract) Replicate
        
LogTerm(
    _log, 
    _snapshot, 
    _node_id, 
    _index
) ==
    IF _index <= _snapshot[_node_id].index THEN
        _snapshot[_node_id].term
    ELSE
        LET _i == _index - _snapshot[_node_id].index
        IN \* i > 0
            IF Len(_log[_node_id]) >= _i THEN
                _log[_node_id][_i].term
            ELSE
               \* cannot happen
               _log[_node_id][_i].term
               

LogEntries(
    _log, 
    _snapshot,
    _node_id,  
    _index, 
    maximum_entries
) ==
    IF _index <= _snapshot[_node_id].index THEN
        <<>>
    ELSE
        LET _i == _index - _snapshot[_node_id].index
        IN 
            IF  \/ Len(_log[_node_id]) = 0
                \/ _i > Len(_log[_node_id])
                THEN
                <<>>
            ELSE
                LET last_index == Min({_i + maximum_entries, Len(_log[_node_id])})
                    first_index == Min({_i, last_index})
                IN SubSeq(_log[_node_id], first_index, last_index)


LogPrevEntryOK(
    _log, 
    _snapshot, 
    _prev_log_index, 
    _prev_log_term
) ==
    \/ (/\ _prev_log_index = 0 
        /\ _snapshot.index = 0
        /\ Len(_log) = 0
        )
    \/ (IF _snapshot.index >= _prev_log_index THEN
            (/\ _snapshot.index = _prev_log_index
             /\ _snapshot.term = _prev_log_term)
           
        ELSE
            LET _i == _prev_log_index - _snapshot.index
            IN \* assert i  > 0
                /\ _i <= Len(_log)
                /\ _prev_log_term = _log[_i].term 
       )

RejectAppendLog(
    _current_term,
    _state,
    _term, 
    _log_ok
) ==
    \/ _current_term > _term
    \/(/\ _current_term = _term
       /\ _state = Follower
       /\ \lnot _log_ok)

CandidateBecomeFollower(_current_term, _state,  _term) ==
    /\ _current_term = _term
    /\ _state = Candidate

FollowerAcceptAppendLog(
    _current_term, 
    _state,
    _term,
    _log_ok
) ==
    /\ _current_term = _term
    /\ _state = Follower
    /\ _log_ok

LogEntryTermInconsistency(
    _log,
    _log_entry, 
    _index
) ==
   /\ Len(_log) >= _index
   /\ _log[_index].term # _log_entry.term
           
LogEntryExist(
    _log,
    _node_id,
    _log_entry, 
    _index
) ==
    /\ Len(_log[_node_id]) >= _index
    /\ _log[_node_id][_index].term = _log_entry.term
 
LogEntryCanAppend(
    _log,
    _node_id,
    _index
) ==
    /\ Len(_log[_node_id]) + 1 = _index


_LogEntryTruncateOrAppend(
    _log,
    _log_entries, 
    _log_offset_start
) ==
    LET _index == Min({Len(_log) - _log_offset_start, Len(_log_entries)})
        _inconsistency_index == {
            i \in 1.._index:
                LogEntryTermInconsistency(_log, _log_entries[i], _log_offset_start + i)
            }
    IN
        CASE _index = 0 -> ( 
            IF Len(_log) = _log_offset_start THEN
                [
                    log_entries |-> _log_entries,
                    index |-> _log_offset_start
                ]
            ELSE
                [
                    log_entries |-> <<>>,
                    index |-> _log_offset_start
                ]
        
        )
        [] _inconsistency_index #{} -> (
               LET min_offset == Min(_inconsistency_index)
               IN  
                    [
                        log_entries |-> SubSeq(_log_entries, min_offset, Len(_log_entries)),
                        index |-> _log_offset_start + min_offset - 1
                    ]
              )
        [] OTHER -> (
                [
                    
                    log_entries |-> SubSeq(_log_entries, _index + 1, Len(_log_entries)),
                    index |-> Len(_log)
                ]
        )
        
_LogEntriesAppendResult(
    _log,
    _log_entries, 
    _log_offset_start
) ==
    CASE Len(_log) >= _log_offset_start -> (
        _LogEntryTruncateOrAppend(_log, _log_entries, _log_offset_start)
    )
    [] OTHER -> ( 
        {} \* not possible
    )

ApplyReconfig(
    _v_node_vote,
    _v_node_replicate,
    _v_config,
    _reconfig_command,
    _new_commit_index,
    _prev_match_index,
    _id
) ==
    IF _reconfig_command = {} THEN
    TRUE
    ELSE 
        LET cmd == CHOOSE c \in _reconfig_command : TRUE
            index == cmd.index
            remove == cmd.remove
            add == cmd.add
        IN IF index + _prev_match_index < _new_commit_index THEN
                /\ _v_config' = [_v_config EXCEPT ![_id].add = _v_config[_id].add \cup add,
                                                  ![_id].remove = _v_config[_id].remove \cup remove
                                            ]
                /\ UNCHANGED <<_v_node_vote>>
           ELSE
                \* commit at once
                CASE Cardinality(_v_config[_id].add) =1 -> (
                    /\ _v_config' = [_v_config EXCEPT ![_id].vote = _v_config[_id].vote \cup _v_config[_id].add,
                                  ![_id].add = {},
                                  ![_id].remove = {}
                            ]
                )
                [] Cardinality(_v_config[_id].remove) =1 -> (
                    /\ _v_config' = [_v_config EXCEPT ![_id].vote = _v_config[_id].vote \ _v_config[_id].remove,
                                  ![_id].add = {},
                                  ![_id].remove = {}
                            ]
                )
                [] OTHER -> (
                    UNCHANGED <<_v_config>>
                )


\* return a collection contains at most one mapping
\* {[ value |-> V, index |-> I]}
\* V is \in value_set, and I is the first index of _entries
FirstCommandOf(
    _entries,
    _value
) ==
    {
        v \in [
            value : _value,
            index : DOMAIN(_entries)
        ] : /\ v.value = _entries[v.index].value
            /\ ~(\E i \in DOMAIN(_entries):
                    /\ _entries[v.index].value \in _value
                    /\ i < v.index
                )
    }


TruncateEntries(
    _entries,
    _value_index
) ==
    LET index == { 
            i \in DOMAIN(_entries) : 
                \/ \E x \in _value_index:
                     x.index = i
            }

    IN IF index = {} THEN
           _entries
       ELSE
            SubSeq(_entries, 1, Min(index))

ValueIndexLessLimit(
    _value_index,
    _index
) ==
    {vi \in _value_index: vi.index <= _index}

LogAfterAppendEntries(
    _node_id,
    _log,
    _recv_log_entries, 
    _log_offset_start,
    _reconfig_value
) ==
    LET _result == _LogEntriesAppendResult(_log,  _recv_log_entries, _log_offset_start)
        _index == _result.index \* new prev_index
        _to_append_entries == _result.log_entries
        _vi_reconfig == FirstCommandOf(_to_append_entries, _reconfig_value)
        _vi_reconfig_log == FirstCommandOf(_log, _reconfig_value)
        _entries == IF _vi_reconfig_log = {} THEN
                        \* when there is a compation command value in log
                        \* we must wait untill it commit and execute compation to append new log entries
                        TruncateEntries(_to_append_entries, _vi_reconfig)
                    ELSE <<>>
        reconfig_vi == ValueIndexLessLimit(_vi_reconfig, Len(_entries))
        _log_node== IF Len(_log) > 0 THEN 
                        SubSeq(_log, 1, Min({_index + Len(_entries), Len(_log)})) 
                    ELSE <<>>
        _log_index == 1..Len(_log_node)
        _log_index_to_update == IF Len(_entries) = 0 THEN
                    {}
                ELSE
                    \* Len(_entries) must >= 1
                    \* log offset [1..Len(_entries)]
                    _index + 1 .. _index + Len(_entries)
       __dump == [
                entries |-> _entries,
                new |-> _log_index_to_update,
                original |-> _log_index,
                node_id |-> _node_id,
                index |-> _index
            ]
    IN      [   
                prev_match_index |-> _index,
                match_index |->  _index + Len(_entries),
                log |-> (IF  _log_index \cup _log_index_to_update = {} THEN 
                            <<>>
                        ELSE
                            [
                                    i \in _log_index \cup _log_index_to_update |-> 
                                        IF i \in _log_index_to_update THEN
                                            IF i - _index \notin DOMAIN _entries THEN
                                                __dump.non_exist1
                                            ELSE 
                                               _entries[i - _index]
                                        ELSE
                                            IF i  \notin _log_index THEN
                                                __dump.non_exist2
                                            ELSE  
                                                _log_node[i]
                            ]),
                reconfig |-> reconfig_vi
           ]

APPEND_RESULT_REJECT == "reject_append"
APPEND_RESULT_TO_FOLLOWER == "to_follower"
APPEND_RESULT_ACCEPT == "accept_append"
APPEND_RESULT_STALE_INDEX == "stale_index" 

HandleAcceptAppend(
    _node_id, \* only used by checking invariants
    prev_log_index, 
    term, 
    log_entries,
    _v_log,
    _v_snapshot,
    _v_history,
    _reconfig_value_set
) ==
    CASE _v_snapshot.index > prev_log_index -> (
             [ append_result |-> APPEND_RESULT_STALE_INDEX ]
        ) 
    []OTHER -> (
        \* foreach log entry in log_entries seqneuce
           LET  _entries == log_entries
                snapshot_last_index == _v_snapshot.index
                snapshot_last_term == _v_snapshot.term
                prev_i == prev_log_index  - snapshot_last_index
                l == LogAfterAppendEntries(
                            _node_id, 
                            _v_log,
                            _entries, 
                            prev_i, 
                            _reconfig_value_set)
                match_index == l.match_index + snapshot_last_index
            IN [
                    append_result |-> APPEND_RESULT_ACCEPT,
                    log |-> l.log,
                    match_index |-> l.match_index + snapshot_last_index
               ] 
    )

 
HandleAppendLogInner(
    _node_id,
    _v_log,
    _v_snapshot,
    _v_current_term,
    _v_state,
    _v_history,
    _reconfig_value_set,
    _leader_node_id,
    _prev_log_index,
    _prev_log_term,
    _term,
    _log_entries
    ) ==
    LET log_ok == LogPrevEntryOK(
                    _v_log,
                    _v_snapshot,
                    _prev_log_index,
                    _prev_log_term)
    IN \* reject request
         CASE RejectAppendLog(_v_current_term, _v_state,  _term, log_ok) ->
              [
                append_result |-> APPEND_RESULT_REJECT
              ]
         
         \* to follower state
         [] CandidateBecomeFollower(_v_current_term, _v_state,  _term) ->
              [
                append_result |-> APPEND_RESULT_TO_FOLLOWER
              ]
         \* OK, append the log
         [] FollowerAcceptAppendLog(_v_current_term, _v_state,  _term, log_ok) ->
              HandleAcceptAppend(
                    _node_id,  _prev_log_index, _term, _log_entries, 
                    _v_log, _v_snapshot, _v_history, _reconfig_value_set
                )
         [] OTHER -> (
              [
                append_result  |-> "other"
              ]
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
            actions0 == ActionCheckState(_node_id)
            actions == ActionSeqSetupAll
        IN /\ v_messages' = WithMessageSet(messages, v_messages)
           /\ SetAction(__action__, actions, actions0 \o actions_input \o actions_output)
    /\ UNCHANGED <<
            v_log, 
            v_snapshot,
            v_history,
            v_pc,
            v_pc_context,
            vars_replicate
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
        /\ SetAction(__action__, actions, a1 \o a2)
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
    /\  LET term_context == _UpdateTerm(i, _m.term) 
           actions == ActionSeqSetupAll
        IN 
        IF term_context.current_term = v_current_term[i] THEN
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
                              /\ LET last_log_index == LastLogIndex(v_log[i], v_snapshot[i])
                                 IN  v_next_index' = [v_next_index EXCEPT ![i] = [j \in NODE_ID |-> last_log_index + 1]]
                              /\ v_match_index' = [v_next_index EXCEPT ![i] = [j \in NODE_ID |-> v_snapshot[i].index]]
                              /\ v_commit_index' = [v_commit_index EXCEPT ![i] = v_snapshot[i].index]
                              /\ LET check_new == ActionSeqCheckNew(i, [vote_granted |-> v_vote_granted, state |-> v_state]) 
                                 IN SetAction(__action__, actions,  _actions \o check_new)
                              /\ UNCHANGED <<v_voted_for, v_current_term>>
                          )
                       ELSE   
                            /\ LET check_new == ActionSeqCheckNew(i, [vote_granted |-> v_vote_granted])  
                               IN SetAction(__action__, actions, _actions \o check_new)
                            /\ v_state' = [v_state EXCEPT ![i] = term_context.state]
                            /\ v_voted_for' = [v_voted_for EXCEPT ![i] = term_context.voted_for]
                            /\ v_current_term' = [v_current_term EXCEPT ![i] = term_context.current_term] 
                            /\ UNCHANGED <<v_next_index, v_match_index, v_commit_index, v_history>>                   
                    )
                \/ ( /\ ~_m.vote_granted
                     /\ LET check ==  ActionCheckState(i)
                        IN SetAction(__action__, actions,  _actions \o check)
                     /\ v_state' = [v_state EXCEPT ![i] = term_context.state]
                     /\ v_voted_for' = [v_voted_for EXCEPT ![i] = term_context.voted_for]
                     /\ v_current_term' = [v_current_term EXCEPT ![i] = term_context.current_term] 
                     /\ UNCHANGED <<v_vote_granted,  v_next_index, v_match_index, v_commit_index, v_history>>
                    )
                )
             
        ELSE /\ v_state' = [v_state EXCEPT ![i] = term_context.state]
             /\ v_voted_for' = [v_voted_for EXCEPT ![i] = term_context.voted_for]
             /\ v_current_term' = [v_current_term EXCEPT ![i] = term_context.current_term]   
             /\ UNCHANGED <<v_vote_granted,  v_next_index, v_commit_index, v_match_index, v_history>>
             /\ SetAction(__action__, actions,  _actions)
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
    /\ UNCHANGED <<vars_vote>>
    


_HandleAppendLog(_node_id, _from_node_id, _payload, _setup_action, _input_action) ==
    LET term_context_updated == _UpdateTerm(_node_id, _payload.term)
        prev_log_index == _payload.prev_log_index
        prev_log_term ==_payload.prev_log_term
        log_ok == LogPrevEntryOK(
            v_log[_node_id], 
            v_snapshot[_node_id],
            prev_log_index, 
            prev_log_term)
        term == _payload.term
        log_entries == _payload.log_entries
        leader_commit_index == _payload.commit_index
        result == HandleAppendLogInner(
                _node_id,        
                v_log[_node_id],
                v_snapshot[_node_id],
                term_context_updated.current_term,
                term_context_updated.state,
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
                            term |-> v_current_term[_node_id],
                            append_success |-> FALSE,
                            match_index |-> 0,
                            next_index |-> next_index
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  /\ v_messages' = WithMessage(reply_message, v_messages)
                        /\ SetAction(__action__, _setup_action,   action_handle_append \o output_action)    
                /\ v_state' = [v_state EXCEPT ![_node_id] = term_context_updated.state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context_updated.voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context_updated.current_term]
                /\ UNCHANGED <<v_log, v_snapshot,  v_history, v_commit_index>>
            )
            [] result.append_result = APPEND_RESULT_TO_FOLLOWER -> (
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context_updated.current_term]
                /\ v_state' = [v_state EXCEPT ![_node_id] = Follower]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
                /\ UNCHANGED <<v_log, v_snapshot, v_messages, v_history, v_commit_index>>
                /\ SetAction(__action__, _setup_action,   action_handle_append)    
            )
            [] result.append_result = APPEND_RESULT_ACCEPT -> (
                /\ LET reply_payload == [
                            source_nid |-> _node_id,
                            term |-> term,
                            append_success |-> TRUE, 
                            match_index |-> result.match_index,
                            next_index |-> 0
                        ]
                       reply_message == Message(_node_id, _from_node_id, AppendResponse, reply_payload)
                       output_action == Action(ActionOutput, reply_message)
                    IN  (/\ v_messages' = WithMessage(reply_message, v_messages)
                         /\ SetAction(__action__, _setup_action,    action_handle_append \o output_action)) 
                /\ v_log' = [v_log EXCEPT ![_node_id] = result.log]
                /\ LET commit_index == Min({result.match_index, leader_commit_index})
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
                /\ v_state' = [v_state EXCEPT ![_node_id] = term_context_updated.state]
                /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context_updated.voted_for]
                /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context_updated.current_term]
                /\ UNCHANGED <<v_snapshot>>
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
    LET term_context == _UpdateTerm(_node_id, _payload.term)
    IN  /\ ( IF term_context.state = Leader 
              /\ _payload.term = v_current_term[_node_id]
              THEN (
                    /\ (\/ (/\ _payload.append_success
                            /\ v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = _payload.match_index + 1]
                            /\ v_match_index' = [v_match_index EXCEPT ![_node_id][_source] = _payload.match_index]
                            /\ _HandleAdvanceCommitIndex(v_match_index', _node_id)
                           )
                        \/ (/\ \lnot _payload.append_success
                            /\ IF _payload.next_index > 0 THEN
                                    LET last_log_index == LastLogIndex(v_log[_node_id], v_snapshot[_node_id])
                                        new_next_index == Min({last_log_index + 1, _payload.next_index})
                                    IN v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                               ELSE 
                                    LET new_next_index == Max({v_next_index[_node_id][_source] - 1, 1})
                                    IN v_next_index'  = [v_next_index  EXCEPT ![_node_id][_source] = new_next_index]
                            /\ UNCHANGED <<v_commit_index, v_match_index>>
                           )
                        )
                    /\ UNCHANGED <<v_log, v_acked_value,
                                    v_messages, v_snapshot,  v_history>>
                     )
             ELSE 
                UNCHANGED <<
                    v_log, 
                    v_snapshot,
                    v_commit_index,
                    v_next_index,
                    v_match_index,
                    v_vote_granted,
                    v_messages,
                    v_history,
                    v_acked_value
                    >>
            )
     /\ v_state' = [v_state EXCEPT ![_node_id] = term_context.state]
     /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = term_context.voted_for]
     /\ v_current_term' = [v_current_term EXCEPT ![_node_id] = term_context.current_term]

    



HandleVoteReq(node_id, message) ==
    /\ message.dest = node_id
    /\ message.name = VoteRequest
    /\ LET action == Action(ActionInput, message)
       IN __HandleVoteRequest(message.dest, message.source, message.payload, action)
    /\ UNCHANGED <<v_history, vars_replicate>>
    /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "next"]]
    /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = ContextNull]
    
HandleVoteResp(node_id, message) ==
    /\ message.dest = node_id
    /\ message.name = VoteResponse
    /\ LET action == Action(ActionInput, message)
       IN __HandleVoteResponse(message.dest, message.source, message.payload, action)
    /\ v_pc ' = [v_pc EXCEPT ![node_id] = [state |-> "next"]]
    /\ v_pc_context' = [v_pc_context EXCEPT ![node_id] = ContextNull]
    /\ UNCHANGED <<v_messages, v_acked_value>>
        

HandleAppendLogReq(_node_id, message) ==
    /\ message.dest = _node_id
    /\ message.name = AppendRequest
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
           actions1 == Action(ActionInput, message)
       IN /\ _HandleAppendLog(_node_id, from_node_id, payload, actions0, actions1) 
          /\ v_pc' = [v_pc EXCEPT ![_node_id] = [ state |-> "next"]]
          /\ v_pc_context' = [v_pc_context EXCEPT ![_node_id] = ContextNull]
    /\ UNCHANGED <<vars_vote>>
    

HandleApplySnapshotReq(_node_id, message) ==
    /\ message.dest = _node_id
    /\ message.name = ApplyReq
    /\ LET from_node_id == message.source
           payload == message.payload
           actions0 == ActionSeqSetupAll
           term_context == _UpdateTerm(_node_id, payload.term)
       IN  /\ (IF payload.term = v_current_term[_node_id] THEN
                 ( /\ IF /\ payload.snapshot.index > v_snapshot[_node_id].index 
                         /\ payload.snapshot.index > v_commit_index[_node_id]
                      THEN
                        /\ v_snapshot' = [v_snapshot EXCEPT ![_node_id] = payload.snapshot]
                        /\ v_log' = [v_log EXCEPT ![_node_id] = <<>> ]
                      ELSE
                        UNCHANGED <<v_snapshot, v_log>>
                   /\ LET resp_payload ==  [source_nid |-> _node_id, term |-> v_current_term[_node_id], id |-> payload.id, iter |-> <<>>]
                          resp == Message(_node_id, from_node_id, ApplyResp, resp_payload)  
                          action2 == Action(ActionOutput, resp)
                          action1 == Action(ActionInput, message)
                      IN SetAction(__action__, actions0, action1 \o action2)
                 )
             ELSE
                   /\ LET action1 == Action(ActionInput, message)
                      IN SetAction(__action__, actions0, action1)
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
           actions1 == Action(ActionInput, message)
       IN /\ _HandleAppendLogResponse(_node_id, from_node_id, payload) 
          /\ SetAction(__action__, actions0, actions1)
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
       IN SetAction(__action__, actions0, _a)    
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
                IN SetAction(__action__, actions0, actions1 \o actions2)
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
    /\ ~LogHasValue(v_log, v_snapshot, nid, v)
    /\  LET entry == [
                index |-> LastLogIndex(v_log[nid], v_snapshot[nid]) + 1,
                term  |-> v_current_term[nid],
                value |-> v]
        IN /\ v_log' = [v_log EXCEPT ![nid] = Append(v_log[nid], entry)]
    /\ LET  actions0 == ActionSeqSetupAll
            actions1 == ActionCheckState(nid)
            actions2 == Action(ActionInput, Message(nid, nid, __ActionClientRequest, v))
        IN SetAction(__action__, actions0, actions1 \o actions2)
    /\ UNCHANGED <<v_commit_index, v_history, v_current_term, v_state, 
            v_voted_for, v_snapshot, v_messages, 
            vars_vote, vars_replicate,
            v_pc, v_pc_context
            >> 

                          
Next == 
    \/ \E i \in NODE_ID : 
        \/ (/\ REPLICATE 
            /\ (\/ AppendLogEntries(i)
                \/ LogCompaction(i)
                \/ (\E m \in v_messages :
                    \/ HandleAppendLogReq(i, m)
                    \/ HandleAppendLogResp(i, m)
                    \/ HandleApplySnapshotReq(i, m))
               )
           )
        \/ (/\ VOTE 
            /\ (\/ VoteTimeoutRequestVote(i, MAX_TERM)
                \/ (\E m \in v_messages :
                   \/ HandleVoteReq(i, m)
                   \/ HandleVoteResp(i, m))
               )
           )
        \/ (REASTART /\ RestartNode(i))
        \/ (CLIENT_REQUEST
            /\ \E v \in VALUE:
                ClientRequest(i, v)
            )

          
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


