--------------------------------- MODULE raft_abstract ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.


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
CONSTANT ENABLE_STATE_DB
----


VARIABLE state
VARIABLE current_term
VARIABLE log
VARIABLE snapshot
VARIABLE voted_for
VARIABLE event
VARIABLE history
VARIABLE __action__

vars == <<
    state,
    current_term,
    log, 
    snapshot,
    voted_for,
    event,
    history,
    __action__
>>

vars_view == <<
    state,
    current_term,
    log, 
    snapshot,
    voted_for,
    event
>>


_RaftVariables(_nid) ==
    [
        state |-> state[_nid],
        current_term |-> current_term[_nid],
        log |-> log[_nid],
        snapshot |-> snapshot[_nid],
        voted_for |-> voted_for[_nid]
    ]

__ActionInit == "DTMTesting::Setup"
__ActionCheck == "DTMTesting::Check"
__ActionRequestVote == "DTMTesting::RequestVote"
__ActionHandleRequestVote == "DTMTesting::HandleRequestVote"
__ActionBecomeLeader == "DTMTesting::BecomeLeader"
__ActionAppendLog == "DTMTesting::AppendLog"
__ActionHandleAppendLog == "DTMTesting::HandleAppendLog"
__ActionClientRequest == "DTMTesting::ClientRequest"
__ActionUpdateTerm == "DTMTesting::UpdateTerm"


SaveVars ==
    [
        state |-> state,
        current_term |-> current_term,
        log |-> log,
        snapshot |-> snapshot,
        voted_for |-> voted_for
    ]


InitStateDB == 
    ENABLE_STATE_DB => DBOpen("/tmp/state.db")
    
SaveState ==
    ENABLE_STATE_DB => Put(SaveVars)
        
Init ==
    /\ InitStateDB
    /\ InitSaftyStateTrival(
        state,
        current_term,
        log,
        snapshot,
        voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM,
        1, 
        1
        )
    /\ event = {}
    /\ history = <<>>
    /\ LET actions == ActionsFromHandle(
            _RaftVariables,
            NODE_ID, 
            ActionInput, 
            __ActionInit 
            ) 
        IN InitAction(
            __action__,
            actions
        )
    /\ Put(SaveVars)
    
RequestVote(nid) ==
    /\ TermLE(nid, current_term, MAX_TERM)
    /\ state[nid] = Follower
    /\ state' = [state EXCEPT ![nid] = Candidate]
    /\ current_term' = [current_term EXCEPT ![nid] = current_term[nid] + 1]
    /\ event' = event \union 
            {[
                event_type  |-> "RequestVote",
                term |-> current_term[nid] + 1,
                last_log_term |-> LastLogTerm(log[nid]),
                last_log_index |-> Len(log[nid]),
                node_id |-> nid
             ]}
    /\ voted_for' = [voted_for EXCEPT ![nid] = nid]
	/\ LET actions1 == ActionsFromHandle(
                _RaftVariables,
                NODE_ID, 
                ActionInput, 
                __ActionCheck 
                )
	       actions2 == Action(ActionInput, Message(nid, nid, __ActionRequestVote, {})) 
       IN SetAction(__action__, actions1 \o actions2)
    /\ UNCHANGED <<
            history,
             log,
             snapshot
            >>   
    
HandleRequestVote(src, dst) ==
    \E e \in event:
        /\ e.event_type = "RequestVote"
        /\ src = e.node_id
        /\ LET _term == e.term 
               _last_log_term == e.last_log_term
               _last_log_index == e.last_log_index
               _voted_for_node == e.node_id
               _current_term == current_term[dst]
               _granted == VoteCanGrant(
                        current_term,
                        log,
                        voted_for,
                        _voted_for_node,
                        dst,
                        _term, 
                        _last_log_term, 
                        _last_log_index)
           IN /\ current_term[dst] = _term
              /\ _granted 
              /\ voted_for' = [voted_for EXCEPT ![dst] = _voted_for_node]
              /\ event' = event \union 
                    {[
                        event_type  |-> "HandleRequestVote",
                        term |-> _term,
                        voted_for |-> src,
                        node_id |-> dst
                     ]}
              /\ LET m == [
                               term |-> _term,
                               last_log_term |-> _last_log_term,
                               last_log_index |-> _last_log_index
                          ]
                 IN LET actions1 == ActionsFromHandle(
                            _RaftVariables,
                            NODE_ID, 
                            ActionInput, 
                            __ActionCheck 
                            )
                        actions2 == Action(ActionInput, Message(src, dst, __ActionHandleRequestVote, m))       
                    IN SetAction(__action__, actions1 \o actions2)
                        /\ UNCHANGED <<history, state, current_term, log, snapshot>>


BecomeLeader(nid) == 
    /\ \E quorum \in QuorumOf(NODE_ID):
        /\ \A vote_granted_nid \in quorum: 
            \/ vote_granted_nid = nid
            \/ (\E e \in event:
                    /\ e.event_type = "HandleRequestVote"
                    /\ e.voted_for = nid
                    /\ e.node_id = vote_granted_nid
                    /\ e.term = current_term[vote_granted_nid]
                )
        /\ state[nid] = Candidate
        /\ state' = [state EXCEPT ![nid] = Leader]
        /\ UNCHANGED <<current_term, log, snapshot, voted_for, event>>
    /\ LET  actions1 == ActionsFromHandle(
                            _RaftVariables,
                            NODE_ID, 
                            ActionInput, 
                            __ActionCheck 
                            )
            actions2  == Action(ActionInput, Message(nid, nid, __ActionBecomeLeader, {}))
        IN SetAction(__action__, actions1 \o actions2)
    /\ LET o == 
        [
            election |-> 
            [
               leader |-> nid,
               term |-> current_term[nid],
               log |-> log[nid],
               snapshot |-> snapshot[nid]
            ]
        ] 
        IN history' = AppendHistory(history, o, CHECK_SAFETY)


UpdateTerm(src, dst) ==
    \E e \in event:
        /\ e.node_id = src
        /\ e.term > current_term[dst]
        /\ e.event_type \in { "RequestVote", "AppendLog" }
        /\ state' = [state EXCEPT ![dst] = Follower]
        /\ current_term' = [current_term EXCEPT ![dst] = e.term]
        /\ voted_for' = [voted_for EXCEPT ![dst] = INVALID_NODE_ID]
        /\ UNCHANGED <<history, log, snapshot, event>>
        /\ LET actions1 == ActionsFromHandle(
                            _RaftVariables,
                            NODE_ID, 
                            ActionInput, 
                            __ActionCheck 
                            )
                actions2 == Action(ActionInput, Message(src, dst, __ActionUpdateTerm, e.term))
            IN SetAction(__action__, actions1 \o actions2)


AppendLog(nid) ==
    /\ state[nid] = Leader
    /\ \E i \in 1..Len(log[nid]):
        /\ event' = event \cup 
                            {[
                                event_type  |-> "AppendLog",
                                term |-> current_term[nid],
                                log_entries |-> <<log[nid][i]>>,
                                node_id |-> nid,
                                prev_log_index |-> i - 1,
                                prev_log_term |-> LogTerm(
                                                    log,
                                                    snapshot,
                                                    nid, 
                                                    i - 1),
                                leader_log |-> IF CHECK_SAFETY THEN log[nid] ELSE <<>>,
                                leader_snapshot |-> IF CHECK_SAFETY THEN snapshot[nid] ELSE {}
                                                    
                            ]}
        /\ UNCHANGED <<log, snapshot, state, voted_for, current_term, history>>
        /\ LET actions1 == ActionsFromHandle(
                            _RaftVariables,
                            NODE_ID, 
                            ActionInput, 
                            __ActionCheck 
                            )
                actions2 == Action(ActionInput, Message(nid, nid, __ActionAppendLog, {}))
            IN SetAction(__action__, actions1 \o actions2)


HandleAppendLog(src, dst) ==
    /\ \E e \in event:                               
        /\ e.event_type = "AppendLog"
        /\ e.node_id = src
        /\ LET  
                prev_log_index == e.prev_log_index
                prev_log_term == e.prev_log_term
                log_ok == LogPrevEntryOK(
                    log, 
                    snapshot,
                    dst, 
                    prev_log_index, 
                    prev_log_term)
                term == e.term
                log_entries == e.log_entries
                msg_payload == [
                            term          |-> term,
                            prev_log_index  |-> prev_log_index,
                            prev_log_term   |-> prev_log_term,
                            log_entries       |-> log_entries,
                            commit_index   |-> 0

                    ]
           IN(\/ ( \* reject request
                    /\ RejectAppendLog(current_term, state, dst, term, log_ok)
                    /\ UNCHANGED <<current_term, state, voted_for, log, snapshot, event, history>>
                    )
                \/ (\* return to follower replicate_state
                    /\ CandidateBecomeFollower(current_term, state, dst, term)
                    /\ state' = [state EXCEPT ![dst] = Follower]
                    /\ voted_for' = [voted_for EXCEPT ![dst] = INVALID_NODE_ID]
                    /\ UNCHANGED <<current_term, log, snapshot, event, history>>
                   )
                \/ (\* accept request
                    /\ FollowerAcceptAppendLog(current_term, state, dst, term, log_ok)
                    /\  (CASE snapshot[dst].index > prev_log_index -> (
                               /\ LET _e == [
                                    event_type |-> "HandleAppendLog",
                                    term |-> term,
                                    node_id |-> dst,
                                    leader_node_id |-> src,
                                    append_success |-> TRUE,
                                    match_index |-> snapshot[dst].index
                                  ]
                                  IN event' = event \cup {_e}
                                /\ UNCHANGED <<log, history>>
                            ) 
                         []OTHER -> (
                                \* foreach log entry in log_entries seqneuce
                                /\ LET  _entries == log_entries
                                        snapshot_last_index == snapshot[dst].index
                                        snapshot_last_term == snapshot[dst].term
                                        prev_i == prev_log_index  - snapshot_last_index
                                        l == LogAfterAppendEntries(
                                                    log, 
                                                    dst, 
                                                    _entries, 
                                                    prev_i, 
                                                    RECONFIG_VALUE)
                                        match_index == l.match_index + snapshot_last_index
                                        _e == [
                                                event_type |-> "HandleAppendLog",
                                                term |-> term,
                                                node_id |-> dst,
                                                leader_node_id |-> src,
                                                append_success |-> TRUE, 
                                                match_index |-> match_index
                                              ]
                                    IN 
                                        /\ event' = event \cup {_e}
                                        /\ log' = [log EXCEPT ![dst] = l.log]
                                        /\ IF CHECK_SAFETY THEN
                                                LET leader_log == e.leader_log
                                                   leader_snapshot == e.leader_snapshot
                                                   op == [
                                                        follower_append |-> [
                                                            node_id |-> dst,
                                                            leader_log |-> leader_log,
                                                            leader_snapshot |-> leader_snapshot,
                                                            follower_log |-> l.log,
                                                            follower_snapshot |-> snapshot[dst]
                                                        ]
                                                    ]
                                                 IN history' = AppendHistory(history, op, CHECK_SAFETY)
                                            ELSE UNCHANGED <<history>>

                            ) 
                        )
                     /\ UNCHANGED <<current_term, state, voted_for, snapshot>>
                   )
          /\ LET actions1 == ActionsFromHandle(
                            _RaftVariables,
                            NODE_ID, 
                            ActionInput, 
                            __ActionCheck 
                            )
                actions2 == Action(ActionInput, Message(src, dst, __ActionHandleAppendLog, msg_payload))
             IN SetAction(__action__, actions1 \o actions2)
               )

ClientRequest(nid, v) ==
    /\ state[nid] = Leader
    /\ ~LogHasValue(log, nid, v)
    /\  LET entry == [
                index |-> Len(log[nid]) + 1,
                term  |-> current_term[nid],
                value |-> v]
        IN /\ log' = [log EXCEPT ![nid] = Append(log[nid], entry)]
    /\ UNCHANGED <<history, current_term, state, voted_for, snapshot, event>>
    /\ LET actions1 == ActionsFromHandle(
                            _RaftVariables,
                            NODE_ID, 
                            ActionInput, 
                            __ActionCheck 
                            )
            actions2 == Action(ActionInput, Message(nid, nid, __ActionClientRequest, v))
        IN SetAction(__action__, actions1 \o actions2)
     
       
Next == 
    \/ \E nid \in NODE_ID:
        \E value \in VALUE:   
            /\ ClientRequest(nid, value)
            /\ SaveState
    \/ \E nid \in NODE_ID:  
            /\ RequestVote(nid)
            /\ SaveState
    \/ \E nid1, nid2 \in NODE_ID:  
            /\ UpdateTerm(nid1, nid2)
            /\ SaveState
    \/ \E nid \in NODE_ID:  
            /\ BecomeLeader(nid)
            /\ SaveState
    \/ \E nid \in NODE_ID:  
            /\ AppendLog(nid)
            /\ SaveState
    \/ \E nid1, nid2 \in NODE_ID:  
            /\ HandleRequestVote(nid1, nid2)
            /\ SaveState
    \/ \E nid1, nid2 \in NODE_ID:  
            /\ HandleAppendLog(nid1, nid2)   
            /\ SaveState
            
\* The specification must start with the initial state and transition according
\* to Next.
Spec == 
    /\ Init 
    /\ [][Next]_vars
----


Invariant ==
    /\ BaseStateOK(
        state,
        current_term,
        log,
        snapshot,
        voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM)
    /\ InvariantPrefixCommitted(
        log,
        MAX_TERM,
        NODE_ID,
        history)
    /\ InvariantAtMostOneLeaderPerTerm(
          history)
    /\ InvariantSnapshotCommit(
        log,
        snapshot,
        NODE_ID)
    /\ InvariantLogPrefix(
        log,
        snapshot,
        NODE_ID)
    /\ InvariantFollowerAppend(
        history)
    /\ InvariantPrefixCommitted(
        log,
        MAX_TERM,
        NODE_ID,
        history)

===============================================================================


