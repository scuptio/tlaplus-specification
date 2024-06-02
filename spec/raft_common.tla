------------------------------ MODULE raft_common ------------------------------
EXTENDS action, Naturals, FiniteSets, Sequences, TLC

----

CONSTANT NULL

INVALID_NODE_ID == NULL

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

UpdateConfigReq == "UpdateConfigReq"
UpdateConfigResp == "UpdateConfigResp"

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
__ActionSendUpdateConfig == "DTMTesting::SendUpdateConf"
__ActionUpdateConfigBegin == "DTMTesting::UpdateConfBegin"
__ActionUpdateConfigCommit == "DTMTesting::UpdateConfCommit"


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
    \/ \E v \in _snapshot.entries : v.value = _value
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
    \/ _term < _max_term
    \/ _max_term = 0

\* if _max_term = 0 , then term is no limitation
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
            \/ \E i_v \in _snapshot.entries:
                 i_v.value = v
    }



Election(_history) ==
    /\ LET index == {i \in 1..Len(_history): "election" \in DOMAIN _history[i]}
       IN { _history[i].election : i \in index }

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
   /\ \A v \in _snapshot.entries:
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

_CurrentNodeIdSet(
    _config_committed,
    _node_ids    
) ==
    LET node_has_latest_conf == 
        CHOOSE i \in _node_ids: 
            ~ \E j \in _node_ids:
                (\/ _config_committed[j].conf_version.term > _config_committed[i].conf_version.term
                 \/ (/\ _config_committed[j].conf_version.term = _config_committed[i].conf_version.term
                     /\ _config_committed[j].conf_version.version > _config_committed[i].conf_version.version)
                )
        current_nodes == _config_committed[node_has_latest_conf].nid_vote  
    IN current_nodes
                        
InvPrefixCommitted(
    _node_ids, 
    _config_committed,
    _commit_index,
    _log,
    _snapshot
) ==
    \A _node_id \in _node_ids:
        _commit_index[_node_id] > 0 =>
            LET commit_index == _commit_index[_node_id]
                current_nodes == _CurrentNodeIdSet(_config_committed, _node_ids)
                majority_commit == MajorityCommit(
                    current_nodes,
                    commit_index,
                    _log,
                    _snapshot,
                    FALSE)
            IN /\ ~majority_commit =>
                    MajorityCommit(
                        current_nodes,
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


StateOK(
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

\* TLA+ {D240508N-_ConfVersion}
_ConfVersion(
    _term,
    _version,
    _commit_index
) ==
    [
        version |-> _version,        
        term |-> _term,
        \* the commit index when the configuration was updated
        index |-> _commit_index
    ]

_ConfNode(
    _term,
    _version,
    _commit_index,
    _nid_vote,
    _nid_log
) ==
    [
        conf_version |-> _ConfVersion(_term, _version, _commit_index),
        nid_vote |-> _nid_vote,
        nid_log |-> _nid_log
    ]


InitStateSetup(
    _node_ids,
    _node_ids2,
    _state_all,
    _value_set
    ) ==
    LET ids == _node_ids \cup _node_ids2
        ids1 == _node_ids
    IN    
    [
        role |-> [
            i \in ids |-> 
                IF i \in ids1 THEN 
                    Follower
                ELSE
                    _state_all.role[i]
           ],
        current_term |-> [
            i \in ids |-> 
                IF i \in ids1 THEN 
                    1
                ELSE
                    _state_all.current_term[i]
            ],
        log |-> [
            i \in ids |-> 
                IF i \in ids1 THEN 
                    <<>>
                ELSE
                    _state_all.log[i]
            ],
        voted_for |-> [
            i \in ids |-> 
                IF i \in ids1 THEN 
                    INVALID_NODE_ID
                ELSE
                    _state_all.voted_for[i]
            ],
        snapshot |-> [
            i \in ids |-> 
                IF i \in ids1 THEN 
                    [term |-> 0, index |-> 0, entries|-> {}] 
                ELSE
                    _state_all.snapshot[i]
            
            ],
        commit_index |-> [
             i \in ids |-> 
                IF i \in ids1 THEN 
                    0
                ELSE
                    _state_all.commit_index[i]
             ],
        conf_committed |-> [
            i \in ids |-> 
                IF i \in ids1 THEN 
                    _ConfNode(0, 0, 0, _node_ids, _node_ids)
                ELSE
                    _state_all.conf_committed[i]
            ],
        conf_new |-> [
            i \in ids |-> 
                IF i \in ids1 THEN 
                    _ConfNode(0, 0, 0, _node_ids, _node_ids)
                ELSE
                    _state_all.conf_new[i]
            ]
    ]
        
=============================================================================