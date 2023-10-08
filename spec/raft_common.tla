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
VoteRequest == "RMsg::VoteReq"
VoteResponse == "RMsg::VoteResp"
                 
AppendRequest == "RMsg::AppendReq"
AppendResponse == "RMsg::AppendResp"

PreVoteRequest == "RMsg::PreVoteReq"
PreVoteResponse == "RMsg::PreVoteResp"

ApplySnapshot == "RMsg::ApplySnapshotReq"
ApplySnapshotResponse == "RMsg::ApplySnapshotResp"

__MsgInitRaft           == "DSMsg::InitRaft"
__MsgRequestPreVote     == "DSMsg::RequestPreVote"
__MsgRestartNode        == "DSMsg::RestartNode"
__MsgBecomeCandidate    == "DSMsg::BecomeCandidate"


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
        msg_type            : {ApplySnapshot}, 
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
    [i \in _node_ids |-> INVALID_NODE_ID]
    
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

\* Log entry <<_entry_index, _entry_term>> committed at term <<_term>>
LogEntryCommit(
    _entry_index, 
    _entry_term,
    _term,
    _history
) ==
    /\ LET index == {
            i \in 1..Len(_history): 
                /\ "election" \in DOMAIN _history[i]
                /\ _history[i].election.term > _term
            }
       IN \A i \in index:
            LET election == _history[i].election
            IN  IF _entry_index <= election.snapshot.index THEN
                    _entry_term <= election.snapshot.term
                ELSE
                    LET _ei == _entry_index - election.snapshot.index
                    IN   /\ _ei <= Len(election.log)
                         /\ _entry_term = election.log[_ei].term


LogEntryPrefixCommit(
    _log,
    _node_id,
    _entry_index, 
    _entry_term,
    _term,
    _history
) ==
    /\ \E i \in DOMAIN(_log[_node_id]):
        _log[_node_id][i].term = _entry_term
    /\ \E i \in DOMAIN(_log[_node_id]):
        /\ _entry_index < i
        /\ LogEntryCommit(
            i, 
            _log[_node_id][i].term,
            _term,
            _history
            )

\* Invariants

\* Lemma 2. There is at most one leader per term:
InvariantAtMostOneLeaderPerTerm(_history) ==
    /\ LET index == {i \in 1..Len(_history): "election" \in DOMAIN _history[i]}
       IN ~(\E i, j \in index:
                /\ _history[i].election.term = _history[j].election.term
                /\ _history[i].election.leader # _history[j].election.leader
           )

InvariantSnapshotCommit(_log, _snapshot, _node_ids) ==
    \A i \in _node_ids:
        _snapshot[i].index > 0 =>
            (\E quorum \in QuorumOf(_node_ids):
                \A j \in quorum:
                    \/ (/\ _snapshot[i].index = _snapshot[j].index
                        /\ _snapshot[i].term = _snapshot[j].term)
                    \/ (/\ _snapshot[i].index < _snapshot[j].index
                        /\ _snapshot[i].term <= _snapshot[j].term)
                    \/ (/\ _snapshot[i].index > _snapshot[j].index
                        /\ LET n == _snapshot[i].index - _snapshot[j].index
                           IN /\ n <= Len(_log[j])
                              /\ _snapshot[i].term = _log[j][n].term)
             )
  

_LogEntriesConsistency(_entries1, _entries2) ==
    \A i \in (1..Len(_entries1) \cap 1..Len(_entries2)):
        _entries1[i].term = _entries2[i].term
           => _entries1[i] = _entries2[i]

_LogSnapshotIndexLE(_entries1, _snapshot1, _entries2, _snapshot2) ==
    /\ _snapshot1.index < _snapshot2.index
    /\ _snapshot1.term <= _snapshot2.term
    /\ LET n == _snapshot2.index - _snapshot1.index
       IN /\ n <= Len(_entries1) => _entries1[n].term =  _snapshot2.term
          /\ LET sub1 == SubSeq(_entries1, n + 1, Len(_entries1))
             IN /\ _LogEntriesConsistency(sub1, _entries2)

_LogSnapshotConsistency(_entries1, _snapshot1, _entries2, _snapshot2) ==
    CASE _snapshot1.index < _snapshot2.index -> (
        _LogSnapshotIndexLE(_entries1, _snapshot1, _entries2, _snapshot2)
    )
    [] _snapshot1.index > _snapshot2.index -> (
        _LogSnapshotIndexLE(_entries2, _snapshot2, _entries1, _snapshot1)
    )
    [] OTHER -> (
        _LogEntriesConsistency(_entries1, _entries2)
    )
                                         
\* Lemma 4. An <<index,term>> pair identifies a log prefix
InvariantLogPrefix(_log, _snapshot, _node_ids) ==
    \A i, j \in _node_ids:
        \/ i = j
        \/ (/\ i # j
            /\  LET l == _log[i]
                    m == _log[j]
                    s_l == _snapshot[i]
                    s_m == _snapshot[j]
                IN _LogSnapshotConsistency(l, s_l, m, s_m)
            )

\* _prefix_log in prefix of _total_log 
_IsPrefixLog(_prefix_log, _prefix_snapshot, _total_log, _total_snapshot) ==
    /\ _prefix_snapshot.index + Len(_prefix_log) <= _total_snapshot.index + Len(_total_log)
    /\ \A i \in 1..Len(_prefix_log):
            LET n == i + _prefix_snapshot.index
            IN IF n <= _total_snapshot.index THEN
                    TRUE
               ELSE _prefix_log[i] = _total_log[n - _total_snapshot.index]
        
\*Lemma 5. When a follower appends an entry to its log, its log after the append is a prefix of the leader's log at the time the leader sent the AppendEntries request
InvariantFollowerAppend(
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
InvariantTerm(
    _current_term,
    _log,
    _snapshot,
    _node_id
) ==
    /\ \A index \in DOMAIN _log[_node_id]:
        _log[_node_id][index].term <= _current_term[_node_id]
    /\ _snapshot[_node_id].term <= _current_term[_node_id]

\* Lemma 7. The terms of entries grow monotonically in each log:
InvariantLogTermGrow(
    _log,
    _snapshot,
    _node_id
    ) ==
    /\ \A i, j \in DOMAIN _log[_node_id]:
        IF i < j THEN
            _log[_node_id][i].term <= _log[_node_id][j].term 
        ELSE
            TRUE
    /\ \A i \in DOMAIN _log[_node_id]:
        _snapshot[_node_id].term <= _log[_node_id][i].term

\* Lemma 8.  Immediately committed entries are committed.
InvariantImmediatelyCommitted(
    _immediately_committed,
    _history
) ==
    \A entry \in _immediately_committed:
        LogEntryCommit(
            entry.index, 
            entry.term,
            entry.term,
            _history
        )

\* Lemma 9.   Prefix committed entries are committed in the same term
InvariantPrefixCommitted(
    _log,
    _max_term,
    _node_ids,
    _history
) ==
    \A t \in 1.._max_term:
        \A n \in _node_ids:
            \A index \in DOMAIN(_log[n]):
                IF LogEntryPrefixCommit(
                        _log,
                        n,
                        index, 
                        _log[n][index].term,
                        t,
                        _history)
                THEN
                    LogEntryCommit(
                        index, 
                        _log[n][index].term,
                        t,
                        _history
                    )
                ELSE TRUE                



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

        
LogHasValue(_log, _id,  _value) ==
   \E i \in DOMAIN _log[_id]: (
        /\ i <= Len(_log[_id])
        /\ i >= 1
        /\ _log[_id][i].value = _value
   )

\* The term of the last entry in a server log, or minimum term(0) if the log is empty.
LastLogTerm(_log) == 
    IF Len(_log) = 0 THEN 
        0 
    ELSE 
        _log[Len(_log)].term


LastLogIndex(_log) == Len(_log)

\* Used by PV and Vote

TermLimit(_term, _max_term) ==
    _term < _max_term


TermLE(_node_ids, _current_term, _max_term) ==
   TermLimit(_current_term[_node_ids], _max_term)

IsLastLogTermIndexOK(
    _log, 
    _node_ids, 
    _last_log_term, 
    _last_log_index
) ==
    \/ _last_log_term > LastLogTerm(_log[_node_ids])
    \/ (/\ _last_log_term = LastLogTerm(_log[_node_ids])
        /\ _last_log_index >= Len(_log[_node_ids]))

VoteCanGrant(
    _current_term, 
    _vote_log, 
    _voted_for, 
    _to_vote_for, 
    _id, 
    _term, 
    _last_log_term, 
    _last_log_index
) ==
    /\ IsLastLogTermIndexOK(
        _vote_log, 
        _id, 
        _last_log_term, 
        _last_log_index)
    /\ (\/ _term > _current_term[_id]
        \/  (/\ _term = _current_term[_id]
            /\ (\/ _voted_for[_id] = INVALID_NODE_ID
                \/ _voted_for[_id] = _to_vote_for
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
    
\* INV: NoLogDivergence
\* The log index is consistent across all servers (on those
\* servers whose commitIndex is equal or higher than the index).
NoLogDivergence(
    _node_ids, 
    _commit_index,
    _log
) ==
    \A s1, s2 \in _node_ids :
        IF s1 = s2 THEN 
            TRUE
        ELSE
            LET lowest_common_ci == MinCommitIndex(_commit_index, s1, s2)
            IN IF lowest_common_ci > 0
               THEN \A index \in 1..lowest_common_ci : _log[s1][index] = _log[s2][index]
               ELSE TRUE


\* INV: LeaderHasAllAckedValues
\* A non-stale leader cannot be missing an acknowledged value
LeaderHasAllAckedValues(
    _value_set,
    _node_ids_set,
    _acked_value,
    _state,
    _current_term,
    _log
) ==
    \* for every acknowledged value
    \A v \in _value_set :
        IF v \in _acked_value
        THEN
            \* there does not exist a server that
            ~\E i \in _node_ids_set :
                \* is a leader
                /\ _state[i] = Leader
                \* and which is the newest leader (aka not stale)
                /\ ~\E l \in _node_ids_set : 
                    /\ l # i
                    /\ _current_term[l] > _current_term[i]
                \* and that is missing the value
                /\ ~\E index \in DOMAIN _log[i] :
                    _log[i][index].value = v
        ELSE TRUE

\* INV: CommittedEntriesReachMajority
\* There cannot be a committed entry that is not at majority quorum
\* Don't use this invariant when allowing data loss on a server.      
CommittedEntriesReachMajority(
    _node_ids_set,
    _commit_index,
    _state,
    _log
) ==
    IF \E i \in _node_ids_set : _state[i] = Leader /\ _commit_index[i] > 0
    THEN \E i \in _node_ids_set :
           /\ _state[i] = Leader
           /\ _commit_index[i] > 0
           /\ \E quorum \in QuorumOf(_node_ids_set):
                /\ i \in quorum
                /\ (\A j \in quorum \ {i}:
                        /\ Len(_log[j]) >= _commit_index[i]
                        /\ _log[j][_commit_index[i]] = _log[i][_commit_index[i]])
    ELSE TRUE

TypeOK ==
    TRUE

InvalidTerm(_term, _max_term) ==
    /\ _term > 0
    /\ _term <= _max_term

LogEntryTypeOK(_entry, _max_term, _value_set) ==
    /\ InvalidTerm(_entry.term, _max_term)
    /\ _entry.value \in _value_set

\* Log Entry value valid
LogEntriesOK(_log, _snapshot, _id, _max_term, _value_set) ==
    /\ Len(_log[_id]) + _snapshot[_id].index <= Cardinality(_value_set) 
    /\ LET _local_log == _log[_id]
        IN  \/ Len(_local_log) = 0
            \/ (/\ Len(_local_log) > 0
                /\ \A i \in 1..Len(_local_log):
                    /\ LogEntryTypeOK(_local_log[i], _max_term, _value_set)
                /\ ~( \E i, j \in 1..Len(_local_log):
                        /\ i # j
                        /\ _local_log[i].value = _local_log[j].value
                    )
               )


LogCommitIndexOK(
    _log, 
    _commit_index, 
    _id, 
    _node_ids
) ==
    LET c_index == _commit_index[_id]
    IN  \/ c_index = 0
        \/ (/\ c_index >= 1
            /\ Len(_log[_id]) >= c_index 
            /\ \E quorum \in QuorumOf(_node_ids):
                /\ _id \in quorum
                /\ \A other_n \in (quorum \ {_id}): 
                    /\ Len(_log[other_n]) >= c_index
                    /\ \A i \in 1..c_index: 
                            _log[other_n][i] = _log[_id][i]  
           )

VoteGrantOK(
    _current_term, 
    _log, 
    _voted_for,
    _id,
    _to_vote_for_id
) ==
    LET last_log_index == LastLogIndex(_log[_to_vote_for_id])
        last_log_term == LastLogTerm(_log[_to_vote_for_id])
        term == _current_term[_to_vote_for_id]
    IN  VoteCanGrant(
            _current_term, 
            _log, 
            _voted_for, 
            _to_vote_for_id, 
            _id, 
            term, 
            last_log_term, 
            last_log_index
        )

VotedForOK(
    _current_term, 
    _log, 
    _voted_for,
    _id
) ==
    \/ _voted_for[_id] = INVALID_NODE_ID
    \/( /\ _voted_for[_id] /= INVALID_NODE_ID
        /\ LET _to_vote_for_id ==  _voted_for[_id]
           IN  \/ _id = _to_vote_for_id
                \/( /\ _id # _to_vote_for_id
                    /\ VoteGrantOK(
                        _current_term, 
                        _log, 
                        _voted_for,
                        _id,
                        _to_vote_for_id)
                )
        )


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
        /\ InvalidTerm(_current_term[i], _max_term)
        /\ LogEntriesOK(_log, _snapshot, i, _max_term, _value_set)
        /\ VotedForOK(_current_term, _log, _voted_for, i)
        /\ InvariantTerm(
            _current_term,
            _log,
            _snapshot,
            i
            )
        /\ InvariantLogTermGrow(
            _log,
            _snapshot,
            i
            )

        )
    /\ InvariantLogPrefix(_log, _snapshot, _node_ids)
    /\ InvariantSnapshotCommit(_log, _snapshot, _node_ids)

CommitStateOK(
    _log,
    _commit_index,
    _node_ids
) ==
    \A i \in _node_ids:
        /\ LogCommitIndexOK(_log, _commit_index, i, _node_ids)


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
    /\ _snapshot \in [_node_ids -> [term: {0}, index: {0}] ]
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
    

(*
CONSTANT MAX_TERM
CONSTANT VALUE
CONSTANT NODE_ID

VARIABLE c_voted_for
VARIABLE c_vote_granted
VARIABLE c_state


VARIABLE c_log
VARIABLE c_current_term

VARIABLE __action__


c_vars == <<
    c_voted_for,
    c_vote_granted,
    c_state,
    c_log,
    c_current_term
>>

VarsC == <<
    c_vars
>>


InitC ==
    /\ InitSaftyStateDefault(
        c_state,
        c_current_term,
        c_log,
        c_voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM)
    /\ c_vote_granted = InitVoteGranted(NODE_ID)


NextC == 
    \/ \E i \in NODE_ID : TRUE /\ UNCHANGED <<VarsC>>

    
Spec == 
    InitC
    /\ [][NextC]_VarsC
*)    
=============================================================================