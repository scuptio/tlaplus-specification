--------------------------------- MODULE raft_replicate ---------------------------------


EXTENDS channel, history, raft_replicate_common,  Naturals, FiniteSets, Sequences, TLC

----

CONSTANT ENABLE_ACTION
CONSTANT ENABLE_CHECK_INVARIANTS
CONSTANT APPEND_ENTRIES_MAX
CONSTANT MAX_TERM
CONSTANT INIT_VALUE
CONSTANT APPEND_VALUE
CONSTANT RECONFIG_VALUE
CONSTANT COMPACTION_VALUE
CONSTANT INIT_NODE_ID

NODE_ID == INIT_NODE_ID

VARIABLE r_state
VARIABLE r_log
VARIABLE r_commit_index
VARIABLE r_next_index
VARIABLE r_match_index
VARIABLE r_acked_value

\* readonly
VARIABLE r_current_term
VARIABLE r_voted_for

VARIABLE r_history
VARIABLE r_imdt_committed
VARIABLE __action__


VARIABLE r_config

VARIABLE r_snapshot

r_vars_config == <<
    r_config
>>

r_vars_snapshot == <<
    r_snapshot
>>

r_vars_replicate == <<
    r_state,
    r_log,
    r_current_term,
    r_commit_index,
    r_next_index,
    r_match_index,
    r_acked_value,
    r_voted_for
>>

r_vars_helper == <<
    r_history,
    r_imdt_committed
>>
r_vars == <<
    r_state,
    r_log,
    r_current_term,
    r_commit_index,
    r_next_index,
    r_match_index,
    r_acked_value,
    r_voted_for,
    r_history,
    r_imdt_committed,
    r_vars_config,
    r_vars_snapshot
>>

VarsR == <<
    r_vars,
    VarsChannel,
    __action__
>>


InitR ==
    /\ InitSaftyStateDefault(
        r_state,
        r_current_term,
        r_log,
        r_snapshot,
        r_voted_for,
        NODE_ID,
        INIT_VALUE,
        MAX_TERM
        )
    /\ InitChannel
    /\ r_next_index = InitNextIndexRole(NODE_ID, r_state, r_log)
    /\ r_match_index = InitMatchIndex(NODE_ID)
    /\ r_acked_value = InitAckedValue
    /\ r_commit_index = InitCommitIndex(NODE_ID)
    /\ LET vars == [
                state |-> r_state,
                current_term |-> r_current_term,
                log |-> r_log,
                snapshot |-> r_snapshot,
                voted_for |-> r_voted_for,
                next_index |-> r_next_index,
                match_index |-> r_match_index
            ]
       IN __action__ = ActionFromVars(vars, NODE_ID, ActionInput, "Init", ENABLE_ACTION)
    /\ r_imdt_committed = {}
    /\ r_config = [i \in NODE_ID |-> [vote |-> INIT_NODE_ID, replicate |-> INIT_NODE_ID, add |-> {}, remove |->{}]]
    /\ InitHistoryWithElection(
            r_history, r_state,
            r_current_term,
            r_log,
            r_snapshot,
            NODE_ID)
----
\* Define initial values for all variables


MessageAppendResponse(
    _source,
    _dest,
    _term,
    _append_success,
    _match_index
) ==
    [
        msg_type        |-> AppendResponse,
        term            |-> _term,
        append_success  |-> _append_success,
        match_index     |-> _match_index,
        source          |-> _source,
        dest            |-> _dest
    ]
                                               
RECURSIVE AppendRequestMessages(_, _, _, _, _, _, _, _, _)

LastEntryIndex(_log, _next_index, i, j) ==
    Min({Len(_log[i]), _next_index[i][j]})

PrevLogIndex(_next_index, i, j) ==
    _next_index[i][j] - 1

LastOrCommitIndex(_log, _next_index, _commit_index, i, j) ==
    LET last_index == LastEntryIndex(_log, _next_index, i, j)
    IN Min({_commit_index[i], last_index})


MessageApplySnapshot(
    _source,
    _dest,
    _term,
    _snapshot_last_index,
    _snapshot_last_term
) == 
     [
        msg_type            |-> ApplySnapshot, 
        term                |-> _term,
        snapshot_term       |-> _snapshot_last_term,
        snapshot_index      |-> _snapshot_last_index,
        snapshot_value      |-> {},
        source              |-> _source,
        dest                |-> _dest
     ]

MessageAppendRequest(
    _source,
    _dest,
    _term,
    _prev_log_index,
    _prev_log_term,
    _log_entries,
    _commit_index,
    _leader_log,
    _leader_snapshot_last_index,
    _leader_snapshot_last_term,
    _aux_payload
) ==
    IF _aux_payload THEN
        [
            msg_type        |-> AppendRequest,
            term            |-> _term,
            prev_log_index  |-> _prev_log_index,
            prev_log_term   |-> _prev_log_term,
            log_entries     |-> _log_entries,
            commit_index    |-> _commit_index,
            source          |-> _source,
            dest            |-> _dest,
            __leader_log    |-> _leader_log,
            __leader_snapshot |-> 
                    [
                        index|-> _leader_snapshot_last_index,
                        term |-> _leader_snapshot_last_term
                    ]
        ]
    ELSE
        [
            msg_type        |-> AppendRequest,
            term            |-> _term,
            prev_log_index  |-> _prev_log_index,
            prev_log_term   |-> _prev_log_term,
            log_entries     |-> _log_entries,
            commit_index    |-> _commit_index,
            source          |-> _source,
            dest            |-> _dest
        ]          
                      
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
                        _snapshot[i].index,
                        _snapshot[i].term)
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
                        index == LastOrCommitIndex(_log, _next_index, _commit_index, i, j)
                        append_message == MessageAppendRequest(
                                i,                          \*_source,
                                j,                          \*_dest,
                                _current_term[i],           \* _term,
                                prev_log_index,             \* _prev_log_index,
                                prev_log_term,              \* _prev_log_term,
                                entries,                    \* _log_entries,
                                index,                      \* _commit_index,
                                _log[i],                    \* _leader_log,
                                _snapshot[i].index,    \* _leader_snapshot_last_index,
                                _snapshot[i].term,     \* _leader_snapshot_last_term,
                                ENABLE_CHECK_INVARIANTS     \* _aux_payload
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
AppendEntries(i) ==
    /\ r_state[i] = Leader
    /\ LET node_ids == VoteNodeIds(
                        r_config,
                        i)
            msgs == AppendRequestMessages(
                r_log, r_next_index, 
                r_commit_index, 
                r_current_term,
                r_snapshot,
                APPEND_ENTRIES_MAX,
                i, node_ids \ {i}, {})
       IN ChannelSend' = WithMessageSet(msgs, ChannelSend)
    /\ NewAction(__action__, i, i, "AppendEntries", ActionInternal, {}, ENABLE_ACTION)
    /\ UNCHANGED <<ChannelRecv, r_vars, r_history, r_imdt_committed,
            r_vars_config,
            r_vars_snapshot
        >>

AgreeIndex(node_ids, i, log, match_index) ==
\* The set of servers that agree up through index.
    LET Agree(index) == {i} \cup {k \in node_ids :
                                         match_index[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
        agree_indexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in QuorumOf(node_ids)}
    IN agree_indexes
    
LeaderCanAdvanceCommitIndex(i, current_term, state, log, agree_index) ==
    /\ state[i] = Leader
    /\ agree_index /= {}
    /\ log[i][Max(agree_index)].term = current_term[i]

ImmediatelyCommit(
    _immediately_commit,
    _node_log,
    _node_snapshot,
    _commit_index,
    _enable
) == 
    IF _enable THEN
        LET  ic == {
                l \in 
                [   
                    term : 1..MAX_TERM,
                    index: 1.._commit_index
                ]:
                \E i \in 1..Len(_node_log):
                    /\ l.index = i + _node_snapshot.index
                    /\ l.term = _node_log[i].term    
            }
        IN _immediately_commit \cup ic
    ELSE
       _immediately_commit
    
\* r_commit_index CHANGED/UNCHANGED 
__LeaderAdvanceCommitIndex(node_ids, i, match_index, _value_set) ==
    CASE r_state[i] = Leader -> (
       LET  agree_index == AgreeIndex(node_ids, i, r_log, r_match_index)
            ok == LeaderCanAdvanceCommitIndex(i, r_current_term, r_state, r_log, agree_index)
       IN  IF ok
            THEN
              LET new_commit_index ==  Max(agree_index)
              IN \* update new value for r_commit_index'[i]
                (/\ r_commit_index' = [r_commit_index EXCEPT ![i] = new_commit_index]
                 /\ r_acked_value' = r_acked_value \cup {v \in _value_set : 
                        \E index \in 1..Len(r_log[i]):
                            /\ v = r_log[i][index].value 
                            /\ index \in r_commit_index[i]+1..new_commit_index 
                    }
                 /\ r_imdt_committed' = ImmediatelyCommit(r_imdt_committed, r_log[i], r_snapshot[i], 
                                                new_commit_index,
                                                ENABLE_CHECK_INVARIANTS
                                            )
               )
           ELSE
              UNCHANGED <<r_commit_index, r_acked_value, r_imdt_committed>>
    )
    [] OTHER -> (
        UNCHANGED <<r_commit_index, r_acked_value, r_imdt_committed>>
    )

----


        
FollowerAppendHistory(
    _history,
    _follower_node_id,
    _new_follower_log,
    _new_follower_snapshot,
    _append_entries_msg,
    _enable_check
) ==
    IF _enable_check THEN 
        LET leader_log == _append_entries_msg.__leader_log
            leader_snapshot == _append_entries_msg.__leader_snapshot
            op == [
                follower_append |-> [
                    node_id |-> _follower_node_id,
                    leader_log |-> leader_log,
                    leader_snapshot |-> leader_snapshot,
                    follower_log |-> _new_follower_log,
                    follower_snapshot |-> _new_follower_snapshot
                ]
            ]
        IN AppendHistory(_history, op, _enable_check)
    ELSE
        _history

\* NODE_ID i receives an AppendEntries request from server j with
\* m.term <= r_commit_index[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
__HandleAppendRequest(i, j, m) ==
    LET 
        prev_log_index == m.prev_log_index
        prev_log_term == m.prev_log_term
        log_ok == LogPrevEntryOK(
            r_log, 
            r_snapshot,
            i, prev_log_index, prev_log_term)
        term == m.term
        log_entries == m.log_entries

    IN  
    /\  ( \/ ( \* reject request
                /\ RejectAppendLog(r_current_term, r_state, i, term, log_ok)
                /\ LET reply_no == 
                        MessageAppendResponse(
                                i,      \* _source
                                j,      \* _dest
                                term,   \* _term
                                FALSE,  \* _append_success
                                0       \* _match_index
                            )
                   IN ChannelSend' = WithMessage(reply_no, ChannelSend)
                /\ UNCHANGED <<
                        r_voted_for,
                        r_state, 
                        r_commit_index,
                        r_log,
                        r_history,
                        r_imdt_committed,
                        r_vars_snapshot
                    >>
               )
            \/ (\* return to follower replicate_state
                /\ CandidateBecomeFollower(r_current_term, r_state, i, term)
                /\ r_state' = [r_state EXCEPT ![i] = Follower]
                /\ r_voted_for' = [r_voted_for EXCEPT ![i] = {}]
                /\ UNCHANGED <<
                        ChannelSend,
                        r_commit_index,
                        r_log,
                        r_history,
                        r_imdt_committed,
                        r_vars_snapshot
                    >>
               )
            \/ (\* accept request
                /\ FollowerAcceptAppendLog(r_current_term, r_state, i, term, log_ok)
                /\  (   CASE r_snapshot[i].index > prev_log_index -> (
                               /\ LET reply_yes == MessageAppendResponse(
                                                i,                      \* _source
                                                j,                      \* _dest
                                                r_current_term[i],      \* _term
                                                TRUE,                   \* _append_success
                                                r_snapshot[i].index       \* _match_index
                                            )
                                 IN ChannelSend' = WithMessage(reply_yes, ChannelSend)
                              /\ UNCHANGED <<r_vars_snapshot, r_log, r_commit_index,
                                        r_history, r_imdt_committed
                                    >>
                        ) 
                        []OTHER -> (
                            \* foreach log entry in log_entries seqneuce
                            /\ LET  _entries == log_entries
                                    snapshot_last_index == r_snapshot[i].index
                                    snapshot_last_term == r_snapshot[i].term
                                    prev_i == prev_log_index  - snapshot_last_index
                                    l == LogAfterAppendEntries(
                                                r_log, 
                                                i, 
                                                _entries, 
                                                prev_i, 
                                                RECONFIG_VALUE)
                                    match_index == l.match_index + snapshot_last_index
                                    reply_yes ==  MessageAppendResponse(
                                                i,                      \* _source
                                                j,                      \* _dest
                                                r_current_term[i],      \* _term
                                                TRUE,                   \* _append_success
                                                match_index             \* _match_index
                                                )
                                IN 
                                    /\ r_log' = [r_log EXCEPT ![i] = l.log]
                                    /\ ChannelSend' = WithMessage(reply_yes, ChannelSend)
                                    /\ IF r_log[i] = l.log THEN
                                            /\ UNCHANGED <<r_history, r_imdt_committed>>
                                       ELSE
                                            /\ r_history' = FollowerAppendHistory(
                                                            r_history, i, l.log, 
                                                            [
                                                                term |-> snapshot_last_term,
                                                                index |-> snapshot_last_index
                                                            ],
                                                            m, ENABLE_CHECK_INVARIANTS)
                            /\ r_commit_index' = [r_commit_index EXCEPT ![i] = m.commit_index]
                            /\ UNCHANGED <<r_vars_snapshot>>
                        ) 
                    )
                /\ UNCHANGED <<r_voted_for, r_state>>
            )
        )
    /\ UNCHANGED <<
            r_match_index, 
            r_next_index, 
            r_current_term, 
            r_acked_value
        >> 

           
\* NODE_ID i receives an AppendEntries response from server j with
\* m.term = r_commit_index[i].
__HandleAppendResponse(i, j, m, _node_ids, _value_set) ==
    /\ m.term = r_current_term[i]
    /\ CASE m.append_success ->
         (  /\ m.append_success \* successful
            /\ r_next_index'  = [r_next_index  EXCEPT ![i][j] = m.match_index + 1]
            /\ (LET new_match_index == [r_match_index EXCEPT ![i][j] = m.match_index]
                  IN /\ r_match_index' = new_match_index
                     /\ __LeaderAdvanceCommitIndex(_node_ids, i, new_match_index, _value_set))
                 
              )
      [] OTHER -> \* not successful
          ( /\ r_next_index' = [r_next_index EXCEPT ![i][j] =
                               Max({r_next_index[i][j] - 1, 1})]
            /\ UNCHANGED <<
                    r_match_index, 
                    r_commit_index, 
                    r_acked_value,
                    r_imdt_committed
               >>
          )
    /\ UNCHANGED <<r_state, r_current_term, r_log, r_voted_for>>

__HandleNope == 
    UNCHANGED <<r_vars, r_vars_snapshot, r_vars_helper, ChannelSend>>
    
HandleAppendRequest(msg) ==
    /\ msg.msg_type = AppendRequest
    /\ ClearRecvMessage(msg)
    /\ (\/ __HandleAppendRequest(msg.dest, msg.source, msg)
        \/ ( /\ __HandleNope 
             /\ UNCHANGED <<r_history, 
                    r_vars_snapshot>>))
    /\ NewAction(__action__, msg.dest, msg.dest, "HandleAppendRequest", ActionInternal, msg, ENABLE_ACTION)
    /\ UNCHANGED <<r_imdt_committed,
            r_vars_config
        >>

HandleAppendResponse(msg,  _value_set) ==
    LET node_ids == VoteNodeIds(
                        r_config,
                        msg.dest)
    IN                    
    /\ msg.msg_type = AppendResponse
    /\ ClearRecvMessage(msg)    
    /\ ( \/ __HandleAppendResponse(msg.dest, msg.source, msg, node_ids, _value_set)
         \/ __HandleNope /\ UNCHANGED <<r_imdt_committed>> )
    /\ NewAction(__action__, msg.dest, msg.dest, "HandleAppendResponse", ActionInternal, msg, ENABLE_ACTION)
    /\ UNCHANGED <<ChannelSend, r_history,
            r_vars_config,
            r_vars_snapshot
        >>

LogCompaction(i) ==
    LET first_cmd == FirstCommandOf(r_log[i], COMPACTION_VALUE)
    IN  /\ first_cmd # {}
        /\ LET index_and_value == CHOOSE x \in  first_cmd: TRUE
             compact_last_index == index_and_value.index
             compact_last_term == r_log[i][compact_last_index].term
           IN   /\ r_commit_index[i] >= compact_last_index
                /\ r_snapshot' = [r_snapshot EXCEPT ![i] = [index |-> compact_last_index, term |-> compact_last_term]]
                /\ r_log' = [r_log EXCEPT ![i] = SubSeq(r_log[i], compact_last_index + 1, Len(r_log[i]))]
                /\ NewAction(
                        __action__, i, i, 
                        "LogCompaction", 
                        ActionInternal,
                        [
                            index |-> compact_last_index,
                            term |-> compact_last_term
                        ], 
                        ENABLE_ACTION)
                /\ UNCHANGED <<
                    VarsChannel,
                        r_state,
                        r_current_term,
                        r_commit_index,
                        r_next_index,
                        r_match_index,
                        r_acked_value,
                        r_voted_for,
                        r_vars_helper,
                        r_vars_config
                    >>


HandleApplySnapshot(m) ==
    /\ m.msg_type = ApplySnapshot
    /\ ClearRecvMessage(m)
    /\ NewAction(
        __action__, m.dest, m.dest, 
        "HandleApplySnapShot", 
        ActionInternal,
        [
            snapshot |->
            [
                snapshot_index |-> m.snapshot_index,
                snapshot_term |-> m.snapshot_term,
                snapshot_value |-> {}
            ]
        ], 
        ENABLE_ACTION)
    /\ \/ __HandleNope
       \/ ( LET i == m.dest
            IN
                /\ r_state[i] = Follower
                /\ m.term = r_current_term[i]
                /\ r_snapshot[i].index + Len(r_log[i]) <= m.snapshot_index
                /\ LET new_snapshot == [index|->m.snapshot_index, term |->m.snapshot_term ]
                   IN /\ r_snapshot[i] # new_snapshot
                      /\ r_snapshot' = [r_snapshot EXCEPT ![i] = new_snapshot]
                /\ r_log' = [r_log EXCEPT ![i] = <<>>]
                /\ r_commit_index' = [r_commit_index EXCEPT ![i] = m.snapshot_index]
                /\ UNCHANGED <<
                    r_state,
                    r_current_term,
                    r_next_index,
                    r_match_index,
                    r_acked_value,
                    r_voted_for,
                    r_vars_helper
                    >>       
            )
      /\ UNCHANGED <<ChannelSend, r_vars_config>>
                                
ReplicateRecvMessage(m) ==
    /\ m.msg_type \in {AppendRequest, AppendResponse, ApplySnapshot}
    /\ RecvMessage(m) 
    /\ NewAction(__action__, m.source, m.dest, "ReplicateRecvMessage", ActionInput, m, ENABLE_ACTION)
    /\ UNCHANGED <<r_vars, ChannelSend, r_history, r_imdt_committed,
            r_vars_config,
            r_vars_snapshot
        >>

\* Network v_state transitions
ReplicateUpdateTerm(msg) ==
    /\ msg.msg_type \in {AppendRequest, AppendResponse, ApplySnapshot}
    /\ "term" \in DOMAIN msg
    /\  LET  term == msg.term
             i == msg.dest
        IN
        /\ r_current_term[i] < term
        /\ r_current_term' = [r_current_term EXCEPT ![i] = term]
        /\ r_state' = [r_state EXCEPT ![i] = Follower]
        /\ r_voted_for' = [r_voted_for EXCEPT ![i] = {}]
        /\ NewAction(__action__, i, i, "ReplicateUpdateTerm", ActionInternal, [term |-> term], ENABLE_ACTION)
        /\ UNCHANGED <<
                ChannelSend, 
                ChannelRecv,
                r_log,
                r_commit_index,
                r_next_index,
                r_match_index,
                r_acked_value,
                r_history,
                r_imdt_committed,
                r_vars_config,
                r_vars_snapshot
            >>


ReplicateRestart(i) ==
    LET node_ids == VoteNodeIds(
                        r_config,
                        i)
    IN
    /\ r_state' = [r_state EXCEPT ![i] = Follower]
    /\ r_next_index' = [r_next_index EXCEPT ![i] = [j \in node_ids |-> 1]]
    /\ r_match_index' = [r_match_index EXCEPT ![i] = [j \in node_ids |-> 0]]
    /\ LET  old == [state |-> r_state]
            new == [state |-> r_state']
            actions == ActionFromChangedVars(
                old,
                new,
                node_ids,
                "ReplicateRestart", ActionInternal ,
                ENABLE_ACTION
            )
       IN ActionPrime(__action__, actions, ENABLE_ACTION)
    /\ UNCHANGED <<
            VarsChannel,
            r_current_term, 
            r_log,
            r_voted_for,
            r_acked_value,
            r_commit_index,
            r_history,
            r_imdt_committed,
            r_vars_config,
            r_vars_snapshot
       >>

        
\* TODO, refinement is violated!
\* RefinementR == MappingAR!SpecAR

FollowerAppendLogOK ==
    InvariantFollowerAppend(r_history, ENABLE_CHECK_INVARIANTS)

TermOK ==
    \A i \in NODE_ID:
        InvariantTerm(r_current_term, r_log, r_snapshot, i)

LogTermGrowOK ==
    \A i \in NODE_ID:
        InvariantLogTermGrow(r_log, r_snapshot, i)
        
ImmediatelyCommittedOK ==
   InvariantImmediatelyCommitted(
        r_imdt_committed,
        r_history,
        ENABLE_CHECK_INVARIANTS)


CommitIndexOK ==
    \A i \in NODE_ID:
        r_commit_index[i] <= Len(r_log[i]) + r_snapshot[i].index
        
PrefixCommittedOK ==
    InvariantPrefixCommitted(
        r_log,
        MAX_TERM,
        NODE_ID,
        r_history,
        ENABLE_CHECK_INVARIANTS)
        
NextR ==
    \/ \E m \in ChannelSend : ReplicateRecvMessage(m)
    \/ \E m \in ChannelRecv : ReplicateUpdateTerm(m)
    \/ \E m \in ChannelRecv : HandleAppendResponse(m, INIT_VALUE \cup APPEND_VALUE)
    \/ \E m \in ChannelRecv : HandleAppendRequest(m)
    \/ \E m \in ChannelRecv : HandleApplySnapshot(m)
    \/ \E i \in NODE_ID : LogCompaction(i)
    \/ \E i \in NODE_ID : ReplicateRestart(i)
    \/ \E i, j \in NODE_ID : AppendEntries(i)


SpecR == 
    /\ InitR 
    /\ [][NextR]_VarsR

===============================================================================


