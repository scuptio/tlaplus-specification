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

        

(*
    return record 
    [
        prev_index ->
        log_entries -> 
        seq_index_to_write -> index of log sequence started to write(stated from 1)
    ]
*)
_LogEntryTruncateOrAppend(
    _log,
    _log_entries, 
    _prev_index,
    _snapshot_last_index
) ==

    LET 
        _log_entries_skipped == _prev_index - _snapshot_last_index
        _inconsistency_index_of_log_entries == {
            i \in 1..Len(_log_entries):
                /\ i + _log_entries_skipped <= Len(_log)
                /\ _log_entries[i].term # _log[i + _log_entries_skipped].term
            }
    IN
        CASE  Len(_log) <= _log_entries_skipped -> (
                [
                    log_entries |-> _log_entries,
                    prev_index |-> _prev_index,
                    seq_index_to_write |-> _log_entries_skipped + 1,
                    truncate |-> FALSE
                ]
            )
        [] Len(_log_entries) = 0 -> (
                [
                    log_entries |-> <<>>,
                    prev_index |-> _prev_index,
                    seq_index_to_write |-> _log_entries_skipped + 1,
                    truncate |-> FALSE
                ]
        
           )
        [] _inconsistency_index_of_log_entries #{} -> (
               \* Ex:
               \*   _prev_index :          N - M
               \*   _prev_index + skpped : N
               \*   Log:                 M skipped ...,   <<index |-> N + 1, term |-> 2>>, <<index |-> N + 2, term |-> 2>>,
               \*   Entries to Append :                   <<index |-> N + 1, term |-> 2>>, <<index |-> N + 2, term |-> 3>>,
               \*
               \* min_offset == 2
               LET min_index == Min(_inconsistency_index_of_log_entries)
               IN  
                    [
                        log_entries |-> SubSeq(_log_entries, min_index, Len(_log_entries)),
                        min_index |-> min_index,
                        log_entries_skipped |-> _log_entries_skipped,
                        prev_index |-> _prev_index + min_index - 1,
                        seq_index_to_write |-> _log_entries_skipped + min_index,
                        truncate |-> TRUE
                    ]
              )
        [] OTHER -> (
                    LET _consistency_index_of_log_entries == { i \in 1..Len(_log_entries):
                            /\ i + _log_entries_skipped <= Len(_log)
                            /\ _log_entries[i ].term = _log[i + _log_entries_skipped].term
                         }
                         max_index == IF _inconsistency_index_of_log_entries = {} THEN 1 ELSE Max(_consistency_index_of_log_entries)
                    IN
                    [
                        max_index |-> max_index,
                        log_entries |-> SubSeq(_log_entries, max_index + 1, Len(_log_entries)),
                        prev_index |-> _prev_index + max_index,
                        seq_index_to_write |-> _log_entries_skipped + max_index + 1,
                        truncate |-> FALSE
                    ]
        )
       
_LogEntriesAppendResult(
    _log,
    _log_entries, 
    _prev_index,
    _snapshot_last_index
) ==
    CASE 
        /\ _prev_index >= _snapshot_last_index
        /\ Len(_log) >= _prev_index - _snapshot_last_index -> (
        _LogEntryTruncateOrAppend(_log, _log_entries, _prev_index, _snapshot_last_index)
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
    _prev_index,
    _snapshot_last_index
) ==
    LET _result == _LogEntriesAppendResult(_log,  _recv_log_entries, _prev_index, _snapshot_last_index)
        _index == _result.prev_index \* new prev_index
        _to_append_entries == _result.log_entries
        _seq_index_to_write == _result.seq_index_to_write \* index of _log sequence
        _entries == _to_append_entries     
        _log_index == IF _result.truncate THEN
                            1.. Min({Len(_log), _seq_index_to_write + Len(_entries) - 1})      
                      ELSE 
                            1..Len(_log)
        _log_index_to_update == IF Len(_entries) = 0 THEN
                    {}
                ELSE 
                    
                    
                    \* Len(_entries) must >= 1
                    \* log offset [1..Len(_entries)]
                    _seq_index_to_write .. _seq_index_to_write + Len(_entries) - 1
       __dump == [
                log |-> _log,
                seq_index_to_write |-> _seq_index_to_write,
                entries |-> _entries,
                new |-> _log_index_to_update,
                original |-> _log_index,
                node_id |-> _node_id,
                index |-> _index
            ]
    IN      [  
                match_index |->  _index + Len(_entries),
                log |-> (IF  _log_index \cup _log_index_to_update = {} THEN 
                            <<>>
                        ELSE
                            [
                                    i \in _log_index \cup _log_index_to_update |-> 
                                        IF i \in _log_index_to_update THEN
                                            IF i - _seq_index_to_write + 1 \notin DOMAIN _entries THEN
                                                __dump.non_exist1
                                            ELSE 
                                               _entries[i - _seq_index_to_write + 1]
                                        ELSE
                                            IF i  \notin _log_index THEN
                                                __dump.non_exist2
                                            ELSE  
                                                _log[i]
                            ])
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
    _v_history
) ==
    CASE _v_snapshot.index > prev_log_index -> (
             [ append_result |-> APPEND_RESULT_STALE_INDEX ]
        ) 
    []OTHER -> (
        \* foreach log entry in log_entries seqneuce
           LET  _entries == log_entries
                snapshot_last_index == _v_snapshot.index
                l == LogAfterAppendEntries(
                            _node_id, 
                            _v_log,
                            _entries,
                            prev_log_index, 
                            snapshot_last_index)
            IN [
                    append_result |-> APPEND_RESULT_ACCEPT,
                    log |-> l.log,
                    match_index |-> l.match_index
               ] 
    )

 
HandleAppendLogInner(
    _node_id,
    _v_log,
    _v_snapshot,
    _v_current_term,
    _v_state,
    _v_history,
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
                    _v_log, _v_snapshot, _v_history
                )
         [] OTHER -> (
              [
                append_result  |-> "other"
              ]
         )
         
    
_TestLogEntryTruncateOrAppend== 
    /\ LET r1 == _LogEntryTruncateOrAppend(
            <<[index |-> 1, term |-> 2, value |-> 1]>>, 
            <<[index |-> 2, term |-> 2, value |-> 2]>>, 
            1,
            0)
       IN /\ r1.prev_index = 1
           /\ r1.seq_index_to_write = 2
           /\ ~r1.truncate
           /\ Len(r1.log_entries) = 1
    /\ LET r2 == _LogEntryTruncateOrAppend(
            <<
                [index |-> 12, term |-> 2, value |-> 2], 
                [index |-> 13, term |-> 2, value |-> 2],
                [index |-> 14, term |-> 2, value |-> 2]
            >>, 
            <<
                [index |-> 13, term |-> 2, value |-> 2],
                [index |-> 14, term |-> 3, value |-> 4]
            >>, 
            12,
            11)
        IN /\ r2.prev_index = 13
           /\ r2.seq_index_to_write = 3
           /\ r2.truncate
           /\ Len(r2.log_entries) = 1
    /\ LET r3 == _LogEntryTruncateOrAppend(
            <<
                [index |-> 12, term |-> 2, value |-> 2], 
                [index |-> 13, term |-> 3, value |-> 3],
                [index |-> 14, term |-> 3, value |-> 4]
            >>, 
            <<  [index |-> 13, term |-> 3, value |-> 3] >>, 
            12,
            11)
       IN  /\ r3.prev_index = 13
           /\ r3.seq_index_to_write = 3
           /\ ~r3.truncate
           /\ Len(r3.log_entries) = 0
    /\ LET r4 == _LogEntryTruncateOrAppend(
            <<
                [index |-> 12, term |-> 2, value |-> 2], 
                [index |-> 13, term |-> 3, value |-> 3]
            >>, 
            <<  [index |-> 13, term |-> 3, value |-> 3],
                [index |-> 14, term |-> 3, value |-> 4],
                [index |-> 15, term |-> 3, value |-> 5]
            >>,
            12,
            11)
        IN /\ r4.prev_index = 13
           /\ r4.seq_index_to_write = 3
           /\ ~r4.truncate
           /\ Len(r4.log_entries) = 2
     /\ LET r5 == _LogEntryTruncateOrAppend(
            <<[index |-> 1, term |-> 2,  value |-> 1]>>, 
            <<[index |-> 1, term |-> 2,  value |-> 1], [index |-> 2, term |-> 2,  value |-> 2]>>,
            0,
            0)
         IN  /\ r5.prev_index = 1
             /\ r5.seq_index_to_write = 2
             /\ ~r5.truncate
             /\ Len(r5.log_entries) = 1      
       
__TestLogAfterAppendEntries ==
     /\ LET r == LogAfterAppendEntries(
                1,
                <<[index |-> 1, term |-> 2,  value |-> 1]>>,
                <<[index |-> 1, term |-> 2,  value |-> 1], [index |-> 2, term |-> 2,  value |-> 2]>>,
                0,
                0
                )
        IN  /\ r.match_index = 2
            /\ Len(r.log) = 2
     /\ LET r == LogAfterAppendEntries(
                1,
                <<[index |-> 1, term |-> 2,  value |-> 1]>>,
                <<>>,
                0,
                0
                )
        IN  /\ r.match_index = 0
            /\ Len(r.log) = 1
     /\ LET r == LogAfterAppendEntries(
                1,
                <<
                    [index |-> 1, term |-> 2,  value |-> 1], 
                    [index |-> 2, term |-> 2,  value |-> 2], 
                    [index |-> 3, term |-> 2,  value |-> 3]
                >>,
                <<
                    [index |-> 1, term |-> 2,  value |-> 1], 
                    [index |-> 2, term |-> 3,  value |-> 2]
                >>,
                0,
                0
                )
        IN  /\ r.match_index = 2
            /\ Len(r.log) = 2
    /\ LET r == LogAfterAppendEntries(
                1,
                <<
                    [index |-> 2, term |-> 2,  value |-> 2]
                >>,
                <<
                    [index |-> 2, term |-> 2,  value |-> 2]
                >>,
                1,
                1
                )
        IN  /\ r.match_index = 2
            /\ Len(r.log) = 1    
            
  
   

=============================================================================