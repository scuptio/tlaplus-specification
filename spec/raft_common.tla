------------------------------ MODULE raft_common ------------------------------
EXTENDS action, Naturals, FiniteSets, Sequences, TLC

----

CONSTANT INVALID_NODE_ID

\* raft role states.
Follower == "Follower"
Candidate == "Candidate"
Leader == "Leader"
PreCandidate == "PreCandidate"

\* message types
VoteRequest == "VoteReq"
VoteResponse == "VoteResp"
                 
AppendRequest == "AppendReq"
AppendResponse == "AppendResp"

PreVoteRequest == "PreVoteReq"
PreVoteResponse == "PreVoteResp"

ApplyReq == "ApplyReq"
ApplyResp== "ApplyResp"


__ActionInit == "DTMTesting::Setup"
__ActionCheck == "DTMTesting::Check"
__ActionHandleUpdateTerm == "DTMTesting::UpdateTerm"
__ActionRequestVote == "DTMTesting::RequestVote"
__ActionAppendLog == "DTMTesting::AppendLog"
__ActionBecomeLeader == "DTMTesting::BecomeLeader"
__ActionRestartNode == "DTMTesting::Restart"
__ActionHandleVoteRequest == "DTMTesting::HandleVoteReq"
__ActionHandleVoteResponse == "DTMTesting::HandleVoteResp"
__ActionHandleAppendLogRequest == "DTMTesting::HandleAppendReq"
__ActionHandleAppendLogResponse == "DTMTesting::HandleAppendResp"
__ActionClientRequest == "DTMTesting::ClientWriteLog"
__ActionAdvanceCommitIndex == "DTMTesting::AdvanceCommitIndex"
__ActionLogCompaction == "DTMTesting::LogCompaction"
__ActionRestart == "DTMTesting::Restart"
__ActionHandleApplySnapshotRequest == "DTMTesting::HandleApplyReq"

ReceiveMessageAction(_var, m) ==
    LET action == Action(ActionInput, m)
    IN _var \o action
       
SendMessageAction(_var, msg_set) ==
    LET output_actions == 
        [
            name : {"Send"},
            type : {ActionOutput},
            payload:msg_set
        ]       
    IN AppendActionSet(_var, output_actions)
    
StateSet == {
    PreCandidate, 
    Candidate, 
    Leader, 
    Follower
}

LogDomain(_max_term, _value_set) == [
    term  : 1.._max_term,
    value : _value_set
]

MessagesDomain(_max_term, _value_set, _node_ids) == 

    [
        (*
        @code {
            struct VoteRequest {
                term : u64,
                last_log_term : u64,
                last_log_index : u64,
            }
        }
        *)
        msg_type         : {VoteRequest},
        term         : 1.._max_term,
        last_log_term  : Nat,
        last_log_index : Nat,
        source       : _node_ids,
        dest         : _node_ids
    ]
    \cup
    [
        (*@action {
            struct VoteResponse {
                term        : u64,
                vote_granted : bool ,
            }
        }
        @action*)
        msg_type        : {VoteResponse},
        term        : 1.._max_term,
        vote_granted : BOOLEAN ,
        source      : _node_ids,
        dest        : _node_ids
    ]    
    \cup
    [
        (*@action
            type struct AppendRequest {
                term          : u64,
                prev_log_index  : u64,
                prev_log_term   : u64,
                commit_index   : u64,
                log_entries       : Sequence<type LogEntry>,
            }
            
            type enum RaftMessage {
                RMAppendRequest(type AppendRequest)
            }
            
            automaton handle_message {
                input action handle_append_request(
                    message: type RaftMessage,
                    from:type NodeId, 
                    to:type NodeId, 

                    name: unknown type TODO,
                ) -> unknown type XXXX
                ;
                action internal handle_append_request(message: type AppendRequest);
                action output handle_append_request(message: type AppendRequest);
            }
        @action*)     
        msg_type          : {AppendRequest},
        term          : 1.._max_term,
        prev_log_index  : Nat,
        prev_log_term   : Nat,
        log_entries       : Seq(LogDomain(_max_term, _value_set)),
        commit_index   : Nat,
        source        : _node_ids,
        dest          : _node_ids
    ]     
    \cup
    [
        msg_type           : {AppendResponse},
        term           : 1.._max_term,
        append_success : BOOLEAN,
        match_index     : Nat,
        source         : _node_ids,
        dest           : _node_ids
    ]
    \cup
    [   
        msg_type        : {PreVoteRequest},
        next_term       : 1.._max_term,
        last_log_term   : Nat,
        last_log_index  : Nat,
        source          : _node_ids,
        dest            : _node_ids
    ]
    \cup
     [
        msg_type            : {PreVoteResponse}, 
        term                : 1.._max_term,
        pv_granted    : BOOLEAN,
        source              : _node_ids,
        dest                : _node_ids
     ]       
    \cup 
     [
        msg_type            : {ApplyReq}, 
        term                : 1.._max_term,
        snapshot_term       : 1.._max_term,
        snapshot_index      : 1..Len(_value_set),
        snapshot_value      : {SUBSET(_value_set)},
        source              : _node_ids,
        dest                : _node_ids
     ]   
\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

InitCurrentTerm(_node_ids) ==
    [i \in _node_ids |-> 1]

InitState(_node_ids) ==
    [i \in _node_ids |-> Follower]
    
InitVotedFor(_node_ids) ==
    [i \in _node_ids |-> INVALID_NODE_ID]
    
InitLog(_node_ids) ==
    [i \in _node_ids |-> << >>]

InitCommitIndex(_node_ids) ==
    [i \in _node_ids |-> 0]


InitVoteGranted(_node_ids) ==
    [i \in _node_ids |-> {}]
    
\* The values NextIndex[i][i] and MatchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitNextIndex(_node_ids)  == [i \in _node_ids |-> [j \in _node_ids |-> 1]]

InitNextIndexRole(_node_ids, _state, _log)  == 
    [i \in _node_ids |-> 
        IF _state[i] = Leader THEN
            [j \in _node_ids |-> Len(_log[i]) + 1]
        ELSE
            [j \in _node_ids |-> 1]
    ]

InitMatchIndex(_node_ids) == [i \in _node_ids |-> [j \in _node_ids |-> 0]]
InitAckedValue == {}


\* helpers for debugging    
PrintVal(id, exp)  ==  Print(<<id, exp>>, TRUE)
PrintValIf(id, exp, cond)  ==  
    IF cond THEN
        Print(<<id, exp>>, TRUE)
    ELSE
        TRUE
\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
QuorumOf(_node_ids) == {i \in SUBSET(_node_ids) : Cardinality(i) * 2 > Cardinality(_node_ids)}


RECONFIG_ADD_LEANER == "AddLeaner"
RECONFIG_ADD_NODE == "Add"
RECONFIG_REMOVE_NODE == "Remove"

ElectionOP(
    _leader_node_id,
    _leader_term,
    _leader_log,
    _leader_snapshot
) == [
    election |-> 
        [
            leader |-> _leader_node_id,
            term |-> _leader_term,
            log |-> _leader_log,
            snapshot |-> _leader_snapshot
        ]
]

InitHistoryWithElection(
    _history,
    _state,
    _current_term,
    _log,
    _snapshot,
    _node_id
) ==
    \/ (\E i \in _node_id:
        /\ _state[i] = Leader 
        /\ LET op == ElectionOP(
                            i, 
                            _current_term[i], 
                            _log[i],
                            [
                                index |-> _snapshot[i].index,
                                term |->_snapshot[i].term
                            ])
           IN _history = <<op>>)
    \/ (/\ ~(\E i \in _node_id: /\ _state[i] = Leader)
        /\ _history = <<>>
        )

RECURSIVE ChooseFromSet(_, _)
ChooseFromSet(_set, _num) ==
    IF _num = 0 \/ _set = {} THEN
          {}
    ELSE
        LET item == CHOOSE _item \in _set: TRUE
        IN {item} \cup ChooseFromSet(_set \ {item}, _num - 1)

LastLogIndex(_log, _snapshot) == 
    IF Len(_log) = 0 THEN 
        _snapshot.index
    ELSE 
        _log[Len(_log)].index


\* return _log's offset index (started from 1)
\* return 0 value if the _index is invalid(too small, or too big)
LogIndexToOffset(_log, _snapshot, _index) ==
    IF _snapshot.index >= _index THEN
        0
    ELSE (LET n == _index - _snapshot.index
          IN (IF Len(_log) < n THEN \* index start from 1 , so not include =n here
                0
             ELSE
                n 
            )
         )  
LogTermOfIndex(_log, _snapshot, _index) ==
    LET offset == LogIndexToOffset(_log, _snapshot, _index)
    IN  (IF offset = 0 THEN 
            0
         ELSE 
            _log[offset].term
        )   
 

NewConfigNodeId(
    _node_id_set,
    _add_set,
    _remove_set
) ==
    CASE Cardinality(_add_set) = 1 -> (
        _node_id_set \cup _add_set
    )
    [] Cardinality(_remove_set) = 1 -> (
        _node_id_set \ _remove_set
    )
    [] Cardinality(_add_set) = 0 /\ Cardinality(_remove_set) = 0  -> (
        _node_id_set
    )
    [] OTHER -> (
        [
            add |-> _add_set,
            remove |-> _remove_set
        ].non_exist
    )
  

NewConfigVoteNodeId(
    _config
) ==
    NewConfigNodeId(
        _config.vote,
        _config.add,
        _config.remove
    )


    
VoteNodeIds(
    _config,
    _node_id
) ==
    LET new_node_ids == NewConfigVoteNodeId(
                        _config[_node_id])
    IN new_node_ids
        
\* compute overlapped quorum of old and new configuration
OverlappedQuorum(
    _node_id_set,
    _reconfig,
    _id
) == 
    IF _reconfig[_id] = {} THEN
        QuorumOf(_node_id_set)
    ELSE
        LET new_id_set == NewConfigNodeId(_node_id_set, TRUE, _reconfig)
            new_quorum == QuorumOf(new_id_set)
            old_quorum == QuorumOf(_node_id_set)
        IN new_quorum \cap old_quorum

        
LogHasValue(_log, _snapshot,   _value) ==
    \/ \E v \in _snapshot.value : v.value = _value
    \/  \E i \in DOMAIN _log: (
            /\ i <= Len(_log)
            /\ i >= 1
            /\ _log[i].value = _value
         )



LogAfterClientRequestValue(_log, _snapshot, _current_term, _value) ==
    /\  LET entry == [
                index |-> LastLogIndex(_log, _snapshot) + 1,
                term  |-> _current_term,
                value |-> _value]
        IN  Append(_log, entry)
        
\* The term of the last entry in a server log, or minimum term(0) if the log is empty.
LastLogTerm(_log, _snapshot) == 
    IF Len(_log) = 0 THEN 
        _snapshot.term
    ELSE 
        _log[Len(_log)].term




\* Used by PV and Vote

TermLimit(_term, _max_term) ==
    _term < _max_term


TermLE(_node_ids, _current_term, _max_term) ==
   TermLimit(_current_term[_node_ids], _max_term)

IsLastLogTermIndexOK(
    _log, 
    _snapshot,
    _last_log_term, 
    _last_log_index
) ==
    \/ _last_log_term > LastLogTerm(_log, _snapshot)
    \/ (/\ _last_log_term = LastLogTerm(_log, _snapshot)
        /\ _last_log_index >= LastLogIndex(_log, _snapshot)
       )

VoteCanGrant(
    _current_term, 
    _vote_log, 
    _snapshot,
    _voted_for, 
    _to_vote_for_node_id,
    _term, 
    _last_log_term, 
    _last_log_index
) ==
    /\ IsLastLogTermIndexOK(
        _vote_log, 
        _snapshot,
        _last_log_term, 
        _last_log_index)
    /\ (\/ _term > _current_term
        \/  (/\ _term = _current_term
            /\ (\/ _voted_for = INVALID_NODE_ID
                \/ _voted_for = _to_vote_for_node_id
                )
            )
        )


MinCommitIndex(
    _commit_index,
    _n1, _n2
) ==
    IF _commit_index[_n1] < _commit_index[_n2] THEN 
        _commit_index[_n1]
    ELSE 
        _commit_index[_n2]


_CommitLogConsistency(_entries1, _snapshot1, _entries2, _snapshot2, _commit_index, _enable_print) ==
    LET last_index1 == LastLogIndex(_entries1, _snapshot1)
        last_index2 == LastLogIndex(_entries2, _snapshot2)
    IN /\ _enable_print => PrintT(<<"_CommitLogConsistency, last index", last_index1, last_index2, _commit_index>>)
       /\ last_index1 >= _commit_index
       /\ last_index2 >= _commit_index
       /\ LET term1 == LogTermOfIndex(_entries1, _snapshot1, _commit_index)
              term2 == LogTermOfIndex(_entries2, _snapshot2, _commit_index)
          IN \* term > 0, => _commint_index <= snapshot.index
             CASE /\ term1 > 0 
                  /\ term2 > 0 -> (
                  LET term_equal == term1 = term2
                  IN /\ (~term_equal /\ _enable_print => PrintT(<<"_CommitLogConsistency, term non equal", term1, term2>>))
                     /\ term_equal
             )
             [] /\ term1 = 0 
                /\ term2 > 0  -> (
                  LET term_ok == term2 <= _snapshot1.term
                  IN /\ (~term_ok /\ _enable_print => PrintT(<<"_CommitLogConsistency, term error", term1, term2, _snapshot1.term>>))
                     /\ term_ok
                 )
             [] /\ term1 > 0 
                 /\ term2 = 0 -> (
                  LET term_ok == term1 <= _snapshot2.term
                  IN /\ (~term_ok /\ _enable_print => PrintT(<<"_CommitLogConsistency, term error", term1, term2, _snapshot2.term>>))
                     /\ term_ok
                )
             [] OTHER -> (
                term1 = 0 /\ term2 = 0
             )


\* _prefix_log in prefix of _total_log 
_IsPrefixLog(_prefix_log, _prefix_snapshot, _total_log, _total_snapshot) ==
    /\ _prefix_snapshot.index + Len(_prefix_log) <= _total_snapshot.index + Len(_total_log)
    /\ \A i \in 1..Len(_prefix_log):
            LET n == i + _prefix_snapshot.index
            IN IF n <= _total_snapshot.index THEN
                    TRUE
               ELSE _prefix_log[i] = _total_log[n - _total_snapshot.index]                                             


AllValuesLEIndex(_log, _snapshot, index, _value_set) ==
    {
        v \in _value_set:
            \/ \E i \in 1..Len(_log):
                /\ _log[i].value = v 
                /\ _log[i].index <= index
            \/ \E i_v \in _snapshot.value:
                 i_v.value = v
    }
    
RECURSIVE _LogSeq(_, _, _)

_LogSeq(_terms, _values, _seq) ==
    IF Cardinality(_terms) = 0 \/ Cardinality(_values) = 0 THEN 
        _seq
    ELSE
        LET v == CHOOSE v \in _values: TRUE
            t == Min(_terms)
        IN _LogSeq(_terms \ {t}, _values \ {v}, _seq \o <<[term |-> t, value |->  v]>>)

RECURSIVE _ToValidLogSeqSet(_, _)
_ToValidLogSeqSet(_values_terms, _log_seq_set) == 
    IF _values_terms = {} THEN
        _log_seq_set \cup {<<>>}
    ELSE
        LET vt == CHOOSE vt \in _values_terms : TRUE
            values == vt.values
            terms == vt.terms
            log_seq == _LogSeq(terms, values, <<>>)
        IN _ToValidLogSeqSet(_values_terms \ {vt}, _log_seq_set \cup {log_seq})


_ValidLogSeqSet(_max_log_size, _max_term, _value_set) ==
    LET values == SUBSET _value_set
        terms == SUBSET (1..Min({_max_term, Cardinality(values)}))
        values_terms == {
                x \in [
                    terms : terms,
                    values : values
                ]:
                /\ Cardinality(x.terms) <= _max_log_size
                /\ Cardinality(x.values) <= _max_log_size
                /\ Cardinality(x.terms) >= 1
                /\ Cardinality(x.values) >= 1
                /\ Cardinality(x.terms) <= Cardinality(x.values)
            }
        log_seq_set == _ToValidLogSeqSet(values_terms, {})
    IN log_seq_set

RECURSIVE _OneIdSet(_)
_OneIdSet(_node_ids) ==
    {
        s \in SUBSET _node_ids : Cardinality(s) <= 1 
    }

-------------------------------------------------
\* Invariants

\* Lemma 2. There is at most one leader per term:
InvAtMostOneLeaderPerTerm(_history) ==
    /\ LET index == {i \in 1..Len(_history): "election" \in DOMAIN _history[i]}
       IN ~(\E i, j \in index:
                /\ _history[i].election.term = _history[j].election.term
                /\ _history[i].election.leader # _history[j].election.leader
           )

        
\*Lemma 5. When a follower appends an entry to its log, its log after the append is a prefix of the leader's log 
\* at the time the leader sent the AppendEntries request
InvFollowerAppend(
    _history
) ==
    /\  IF  /\ Len(_history) > 1 
            /\ "follower_append" \in DOMAIN (_history[Len(_history)]) 
        THEN 
                LET action == _history[Len(_history)].follower_append
                    leader_log == action.leader_log
                    leader_snapshot == action.leader_snapshot
                    follower_log == action.follower_log
                    follower_snapshot == action.follower_snapshot
                IN _IsPrefixLog(follower_log, follower_snapshot, leader_log, leader_snapshot)
        ELSE TRUE

       
\* Lemma 6. A server current term is always at least as large as the terms in its log: 
InvTerm(
    _current_term,
    _log,
    _snapshot,
    _node_id
) ==
    /\ \A index \in DOMAIN _log[_node_id]:
        _log[_node_id][index].term <= _current_term[_node_id]
    /\ _snapshot[_node_id].term <= _current_term[_node_id]

\* Lemma 7. The terms of entries grow monotonically in each log:
_InvLogIndexTermGrow(
    _log,
    _snapshot
    ) ==
   /\ \A i, j \in DOMAIN _log:
     (
         i < j =>
               ( /\ i + 1 = j => _log[i].index <= _log[j].index  \* index grows
                 /\ _log[i].term <= _log[j].term \* term grows
               )
     )
   /\ \A i \in DOMAIN _log:
     (
        /\ i = 1 => (
             _snapshot.index + 1 = _log[i].index
            )
        /\_snapshot.term <= _log[i].term
     )
   /\ \A v \in _snapshot.value:
        v.index <= _snapshot.index

        
InvLogIndexTermGrow(
    _v_log,
    _v_snapshot,
    _node_ids
) ==
    /\ \A i \in _node_ids:
        /\ _InvLogIndexTermGrow(
            _v_log[i],
            _v_snapshot[i]
            )
    
        


\* Lemma 9.   Prefix committed entries are committed in the same term
             
MajorityCommit(
    _node_ids,
    _commit_index,
    _log,
    _snapshot,
    _enable_print
) ==             
    \E quorum \in QuorumOf(_node_ids):
       /\ \A n1, n2 \in quorum:
            /\ n1 # n2 => (
                \A i \in 1.._commit_index:
                    LET l1 == _log[n1]
                        l2 == _log[n2]
                        s1 == _snapshot[n1]
                        s2 == _snapshot[n2]
                        consistency == _CommitLogConsistency(l1, s1, l2, s2, i, _enable_print)
                    IN  /\ (~consistency /\ _enable_print) 
                            => PrintT(<<"MajorityCommit, Non Consistency", 
                                "commit index", i,
                                quorum, n1, l1, s1, n2, l2, s2>>)
                        /\ consistency
                )

                           
InvPrefixCommitted(
    _node_ids, 
    _commit_index,
    _log,
    _snapshot
) ==
    \A _node_id \in _node_ids:
        _commit_index[_node_id] > 0 =>
            LET commit_index == _commit_index[_node_id]
                majority_commit == MajorityCommit(
                    _node_ids,
                    commit_index,
                    _log,
                    _snapshot,
                    FALSE)
            IN /\ ~majority_commit =>
                    MajorityCommit(
                        _node_ids,
                        commit_index,
                        _log,
                        _snapshot,
                        TRUE)
               /\ majority_commit

_LeaderMissingValue(
    _node_ids,
    _v_state,
    _v_current_term,
    _v_log,
    _v_snapshot,
    _value
) ==
    \E i \in _node_ids :
        \* is a leader
        /\ _v_state[i] = Leader
        \* and which is the newest leader (aka not stale)
        /\ ~\E l \in _node_ids : 
            (/\ l # i
             /\ _v_current_term[l] > _v_current_term[i]
            )
        \* and that is missing the value
        /\ ~LogHasValue(_v_log[i], _v_snapshot[i], _value)


\* INV: LeaderHasAllAckedValues
\* A non-stale leader cannot be missing an acknowledged value
InvLeaderHasAllAckedValues(
    _node_ids,
    _value_set,
    _acked_value,
    _v_state,
    _v_current_term,
    _v_log,
    _v_snapshot
) ==
    \* for every acknowledged value
    \A value \in _acked_value:
        \* there does not exist a server that
        ~ _LeaderMissingValue(_node_ids,
                _v_state,
                _v_current_term,
                _v_log,
                _v_snapshot,
                value)


ValidTerm(_term, _max_term) ==
    /\ _term > 0
    /\ _term <= _max_term

LogEntryTypeOK(_entry, _max_term, _value_set) ==
    /\ ValidTerm(_entry.term, _max_term)
    /\ _entry.value \in _value_set

\* Log Entry value valid
LogEntriesOK(_log, _snapshot, _id, _max_term, _value_set) ==
    /\ Len(_log[_id]) + _snapshot[_id].index <= Cardinality(_value_set) 
    /\ LET _local_log == _log[_id]
        IN  \/ Len(_local_log) = 0
            \/ (/\ Len(_local_log) > 0
                /\ \A i \in 1..Len(_local_log):
                    /\ LogEntryTypeOK(_local_log[i], _max_term, _value_set)
                    /\ _local_log[i].index = _snapshot[_id].index + i
                /\ ~( \E i, j \in 1..Len(_local_log):
                        /\ i # j
                        /\ _local_log[i].value = _local_log[j].value
                    )
               )


VoteGrantOK(
    _current_term, 
    _log, 
    _snapshot,
    _voted_for,
    _to_vote_for_id
) ==
    LET last_log_index == LastLogIndex(_log, _snapshot)
        last_log_term == LastLogTerm(_log, _snapshot)
        term == _current_term
    IN  VoteCanGrant(
            _current_term, 
            _log, 
            _snapshot,
            _voted_for, 
            _to_vote_for_id,
            term, 
            last_log_term, 
            last_log_index
        )

VotedForOK(
    _current_term, 
    _log, 
    _snapshot,
    _voted_for,
    _id
) ==
    \/ _voted_for = INVALID_NODE_ID
    \/( /\ _voted_for /= INVALID_NODE_ID
        /\ LET _to_vote_for_id ==  _voted_for
           IN  \/ _id = _to_vote_for_id
                \/( /\ _id # _to_vote_for_id
                    /\ VoteGrantOK(
                        _current_term, 
                        _log, 
                        _snapshot,
                        _voted_for,
                        _to_vote_for_id)
                )
        )


AfterUpdateTermInner(
    _term,
    _current_term,
    _state,
    _voted_for,
    _invalid_node_id
) ==
    IF _term > _current_term THEN
        [
            changed |-> TRUE,
            term |-> _term,
            voted_for |-> _invalid_node_id,
            state |-> Follower
        ]
    ELSE
        [
            changed |-> FALSE,
            term |-> _current_term,
            voted_for |-> _voted_for,
            state |-> _state
        ]


BaseStateOK(
    _state,
    _current_term,
    _log,
    _snapshot,
    _voted_for,
    _node_ids,
    _value_set,
    _max_term
) ==
    /\ \A i \in _node_ids:
        (
        /\ ValidTerm(_current_term[i], _max_term)
        /\ InvTerm(
            _current_term,
            _log,
            _snapshot,
            i
            )
        /\ VotedForOK(_current_term[i], _log[i], _snapshot[i], _voted_for[i], i)
        )

LogOK( 
    _current_term,
    _log,
    _snapshot,
    _node_ids,
    _value_set,
    _max_term) ==
    /\ \A i \in _node_ids:
        /\ LogEntriesOK(_log, _snapshot, i, _max_term, _value_set)




InitSaftyStateTrival(
    _state,
    _current_term,
    _log,
    _snapshot,
    _voted_for,
    _node_ids,
    _value_set,
    _max_term,
    _max_entries,
    _max_snapshot_index
    ) ==
    /\ _state \in  [_node_ids -> {Follower} ]
    /\ _current_term \in [_node_ids -> {1} ]
    /\ _log \in [_node_ids -> {<<>>} ]
    /\ _voted_for \in [_node_ids -> {INVALID_NODE_ID} ]
    /\ _snapshot \in [_node_ids -> [term: {0}, index: {0}, value: {{}}] ]
    /\ BaseStateOK(
        _state,
        _current_term,
        _log,
        _snapshot,
        _voted_for,
        _node_ids,
        _value_set,
        _max_term 
        )
        
    
InitSaftyState(
    _state,
    _current_term,
    _log,
    _snapshot,
    _voted_for,
    _node_ids,
    _value_set,
    _max_term,
    _max_entries,
    _max_snapshot_index
    ) ==
    /\ _state \in  [_node_ids -> StateSet]
    /\ _current_term \in [_node_ids -> 1.._max_term ]
    /\ _log \in [_node_ids -> _ValidLogSeqSet(_max_entries, _max_term, _value_set) ]
    /\ _voted_for \in [_node_ids -> _node_ids \cup {INVALID_NODE_ID}]
    /\ _snapshot \in [_node_ids -> {
                        x \in [term : 0.._max_term, index : 0.._max_snapshot_index] : 
                            \/ (x.term = 0 /\ x.index = 0)
                            \/ (x.term # 0 /\ x.index # 0) 
                            }]
    /\ BaseStateOK(
        _state,
        _current_term,
        _log,
        _snapshot,
        _voted_for,
        _node_ids,
        _value_set,
        _max_term 
        )


InitSaftyStateDefault(
    _state,
    _current_term,
    _log,
    _snapshot,
    _voted_for,
    _node_ids,
    _value_set,
    _max_term
    ) == 
    InitSaftyState(
        _state,
        _current_term,
        _log,
        _snapshot,
        _voted_for,
        _node_ids,
        _value_set,
        _max_term,
        1,
        1
    )
    

 
=============================================================================