------------------------------ MODULE raft_replicate_common ------------------------------
EXTENDS  raft_common, history, Naturals, FiniteSets, Sequences, TLC

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
    _node_id, 
    _prev_log_index, 
    _prev_log_term
) ==
    \/ (/\ _prev_log_index = 0 
        /\ _snapshot[_node_id].index = 0
        /\ Len(_log[_node_id]) = 0
        )
    \/ (IF _snapshot[_node_id].index >= _prev_log_index THEN
             TRUE
        ELSE
            LET _i == _prev_log_index - _snapshot[_node_id].index
            IN \* assert i  > 0
                /\ _i <= Len(_log[_node_id])
                /\ _prev_log_term = _log[_node_id][_i].term 
       )

RejectAppendLog(
    _current_term,
    _state,
    _node_id, 
    _term, 
    _log_ok
) ==
    \/ _current_term[_node_id] > _term
    \/(/\ _current_term[_node_id] = _term
       /\ _state[_node_id] = Follower
       /\ \lnot _log_ok)

CandidateBecomeFollower(_current_term, _state, _node_id, _term) ==
    /\ _current_term[_node_id] = _term
    /\ _state[_node_id] = Candidate

FollowerAcceptAppendLog(
    _current_term, 
    _state,
    _node_id,
    _term,
    _log_ok
) ==
    /\ _current_term[_node_id] = _term
    /\ _state[_node_id] = Follower
    /\ _log_ok

LogEntryTermInconsistency(
    _log,
    _node_id,
    _log_entry, 
    _index
) ==
   /\ Len(_log[_node_id]) >= _index
   /\ _log[_node_id][_index].term # _log_entry.term
           
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
    _node_id,
    _log_entries, 
    _log_offset_start
) ==
    LET _index == Min({Len(_log[_node_id]) - _log_offset_start, Len(_log_entries)})
        _inconsistency_index == {
            i \in 1.._index:
                LogEntryTermInconsistency(_log, _node_id, _log_entries[i], _log_offset_start + i)
            }
    IN
        CASE _index = 0 -> ( 
            IF Len(_log[_node_id]) = _log_offset_start THEN
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
                    index |-> Len(_log[_node_id])
                ]
        )
        
_LogEntriesAppendResult(
    _log,
    _node_id,
    _log_entries, 
    _log_offset_start
) ==
    CASE Len(_log[_node_id]) >= _log_offset_start -> (
        _LogEntryTruncateOrAppend(_log, _node_id, _log_entries, _log_offset_start)
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
    _log,
    _node_id,
    _recv_log_entries, 
    _log_offset_start,
    _reconfig_value
) ==
    LET _result == _LogEntriesAppendResult(_log, _node_id, _recv_log_entries, _log_offset_start)
        _index == _result.index \* new prev_index
        _to_append_entries == _result.log_entries
        _vi_reconfig == FirstCommandOf(_to_append_entries, _reconfig_value)
        _vi_reconfig_log == FirstCommandOf(_log[_node_id], _reconfig_value)
        _entries == IF _vi_reconfig_log = {} THEN
                        \* when there is a compation command value in log
                        \* we must wait untill it commit and execute compation to append new log entries
                        TruncateEntries(_to_append_entries, _vi_reconfig)
                    ELSE <<>>
        reconfig_vi == ValueIndexLessLimit(_vi_reconfig, Len(_entries))
        _log_node== IF Len(_log[_node_id]) > 0 THEN 
                        SubSeq(_log[_node_id], 1, Min({_index + Len(_entries), Len(_log[_node_id])})) 
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
    dst, 
    src, 
    prev_log_index, 
    term, 
    log_entries,
    _v_log,
    _v_snapshot,
    _v_history,
    _reconfig_value_set
) ==
    CASE _v_snapshot[dst].index > prev_log_index -> (
             [ append_result |-> APPEND_RESULT_STALE_INDEX ]
        ) 
    []OTHER -> (
        \* foreach log entry in log_entries seqneuce
           LET  _entries == log_entries
                snapshot_last_index == _v_snapshot[dst].index
                snapshot_last_term == _v_snapshot[dst].term
                prev_i == prev_log_index  - snapshot_last_index
                l == LogAfterAppendEntries(
                            _v_log, 
                            dst, 
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
    _v_log,
    _v_snapshot,
    _v_current_term,
    _v_state,
    _v_history,
    _reconfig_value_set,
    _node_id,
    _leader_node_id,
    _prev_log_index,
    _prev_log_term,
    _term,
    _log_entries
    ) ==
    LET log_ok == LogPrevEntryOK(
                    _v_log,
                    _v_snapshot,
                    _node_id,
                    _prev_log_index,
                    _prev_log_term)
    IN \* reject request
         CASE RejectAppendLog(_v_current_term, _v_state, _node_id, _term, log_ok) ->
              [
                append_result |-> APPEND_RESULT_REJECT
              ]
         
         \* to follower state
         [] CandidateBecomeFollower(_v_current_term, _v_state, _node_id, _term) ->
              [
                append_result |-> APPEND_RESULT_TO_FOLLOWER
              ]
         \* OK, append the log
         [] FollowerAcceptAppendLog(_v_current_term, _v_state, _node_id, _term, log_ok) ->
              HandleAcceptAppend(
                    _node_id, _leader_node_id, _prev_log_index, _term, _log_entries, 
                    _v_log, _v_snapshot, _v_history, _reconfig_value_set
                )
         [] OTHER -> (
              [
                append_result  |-> "other"
              ]
         )


=============================================================================