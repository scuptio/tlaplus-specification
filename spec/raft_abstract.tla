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
CONSTANT DB_STATE_PATH
CONSTANT DB_ACTION_PATH
----


VARIABLE state
VARIABLE current_term
VARIABLE log
VARIABLE snapshot
VARIABLE voted_for
VARIABLE event
VARIABLE history
VARIABLE commit_index
VARIABLE __action__

vars == <<
    state,
    current_term,
    log, 
    snapshot,
    voted_for,
    commit_index,
    event,
    history,
    __action__
>>

vars_view == <<
    state,
    current_term,
    log, 
    snapshot,
    commit_index,
    voted_for,
    event
>>


_RaftVariables(_nid) ==
    [
        state |-> state[_nid],
        current_term |-> current_term[_nid],
        log |-> log[_nid],
        snapshot |-> snapshot[_nid],
        voted_for |-> voted_for[_nid],
        \* ignore the following
        vote_granted |-> {},
        commit_index |-> 0,
        match_index |-> {},
        next_index |-> [n \in NODE_ID |-> 1]
    ]

ActionSeqCheck(_node_id) ==
    ActionsFromHandle(
            _RaftVariables,
            {_node_id}, 
            ActionCheck, 
            __ActionCheck
       )

ActionSeqSetupAll ==
    ActionsFromHandle(
            _RaftVariables,
            NODE_ID, 
            ActionSetup, 
            __ActionInit
       )
       
InitActionSeqSetup ==
    ActionsFromHandle(
            _RaftVariables,
            NODE_ID, 
            ActionSetup, 
            __ActionInit
       )
                                   
SaveVars ==
    [
        state |-> state,
        current_term |-> current_term,
        log |-> log,
        snapshot |-> snapshot,
        voted_for |-> voted_for
    ]


SaveActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__', DB_ACTION_PATH)

InitStateDB == 
    /\ DB_STATE_PATH /= "" => 
        SaveValue(SaveVars, DB_STATE_PATH)
    /\ DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)

SaveState ==
    DB_STATE_PATH /= "" => 
        SaveValue(SaveVars, DB_STATE_PATH)
        
Init ==
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
    /\ commit_index = 0
    /\ history = <<>>
    /\ LET actions == InitActionSeqSetup
        IN InitAction(
            __action__,
            actions,
            actions
        )
    /\ InitStateDB


RequestVote(nid) ==
    /\ TermLE(nid, current_term, MAX_TERM)
    /\ state[nid] = Follower
    /\ state' = [state EXCEPT ![nid] = Candidate]
    /\ current_term' = [current_term EXCEPT ![nid] = current_term[nid] + 1]
    /\ event' = event \union 
            {[
                event_type  |-> "RequestVote",
                term |-> current_term[nid] + 1,
                last_log_term |-> LastLogTerm(log[nid], snapshot[nid]),
                last_log_index |-> Len(log[nid]),
                node_id |-> nid
             ]}
    /\ voted_for' = [voted_for EXCEPT ![nid] = nid]
	/\ LET actions0 == ActionSeqSetupAll
           actions1 == ActionSeqCheck(nid)
	       actions2 == Action(ActionInput, MessageNP(nid, nid, __ActionRequestVote)) 
       IN SetAction(__action__,  actions0, actions1 \o actions2)
    /\ UNCHANGED <<
             commit_index,
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
                        snapshot,
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
                               last_log_index |-> _last_log_index,
                               source_nid |-> src
                          ]
                 IN LET actions0 == ActionSeqSetupAll
                        actions1 == ActionSeqCheck(dst)
                        actions2 == Action(ActionInput, Message(src, dst, __ActionHandleVoteRequest, m))       
                    IN SetAction(__action__,  actions0, actions1 \o actions2)
                        /\ UNCHANGED <<
                            commit_index, history, state, current_term, log, snapshot
                        >>


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
    /\ LET  actions0 == ActionSeqSetupAll
            actions1 == ActionSeqCheck(nid)
            actions2  == Action(ActionInput, MessageNP(nid, nid, __ActionBecomeLeader))
        IN SetAction(__action__, actions0, actions1 \o actions2)
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
     /\ UNCHANGED <<commit_index, current_term, log, snapshot, voted_for, event>>

UpdateTerm(src, dst) ==
    /\ (\E e \in event:
            /\ e.node_id = src
            /\ e.term > current_term[dst]
            /\ e.event_type \in { "RequestVote", "AppendLog" }
            /\ state' = [state EXCEPT ![dst] = Follower]
            /\ current_term' = [current_term EXCEPT ![dst] = e.term]
            /\ voted_for' = [voted_for EXCEPT ![dst] = INVALID_NODE_ID]
    
            /\ LET actions0 == ActionSeqSetupAll
                    actions1 == ActionSeqCheck(dst)
                    actions2 == Action(ActionInput, Message(src, dst, __ActionHandleUpdateTerm, e.term))
                IN SetAction(__action__, actions0, actions1 \o actions2)
        )
     /\ UNCHANGED <<commit_index, history, log, snapshot, event>>

AppendLog(nid) ==
    /\ state[nid] = Leader
    /\ \E i \in 1..Len(log[nid]):
        /\ event' = event \cup 
                            {[
                                event_type  |-> "AppendLog",
                                term |-> current_term[nid],
                                log_entries |-> <<log[nid][i]>>,
                                node_id |-> nid,
                                prev_log_index |-> IF i <= 1 THEN snapshot[nid].index ELSE log[nid][i - 1].index ,
                                prev_log_term |-> IF i <= 1 THEN snapshot[nid].term ELSE log[nid][i - 1].term,
                                leader_log |-> IF CHECK_SAFETY THEN log[nid] ELSE <<>>,
                                leader_snapshot |-> IF CHECK_SAFETY THEN snapshot[nid] ELSE {}
                                                    
                            ]}
        /\ LET  actions0 == ActionSeqSetupAll
                actions1 == ActionSeqCheck(nid)
                actions2 == Action(ActionInput, MessageNP(nid, nid, __ActionAppendLog))
            IN SetAction(__action__, actions0, actions1 \o actions2)
   /\ UNCHANGED <<commit_index, log, snapshot, state, voted_for, current_term, history>>
   

_HandleRejectRequest ==
    UNCHANGED <<voted_for>>
            
_HandleCandidateBecomeFollower(_node_id) ==
    /\ state' = [state EXCEPT ![_node_id] = Follower]
    /\ voted_for' = [voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
    /\ UNCHANGED <<current_term, log, snapshot, event, history>>



_HANDLE_APPEND_TO_LOG ==
    UNCHANGED <<voted_for>>

    
    
HandleAppendLog(src, dst) ==
    /\ \E e \in event:                               
        /\ e.event_type = "AppendLog"
        /\ e.node_id = src
        /\ e.node_id /= dst
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
                            \* ignore commit_index
                            commit_index   |-> 0,
                            source_nid |-> src

                    ]
                result == HandleAppendLogInner(
                        log,
                        snapshot,
                        current_term,
                        state,
                        history,
                        RECONFIG_VALUE,
                        dst,
                        src,
                        prev_log_index,
                        prev_log_term,
                        term,
                        log_entries
                     )
          IN /\ (CASE  result.append_result = APPEND_RESULT_REJECT -> (
                      UNCHANGED <<current_term, state, voted_for, log, snapshot, event, history>>
                 )
                 [] result.append_result = APPEND_RESULT_TO_FOLLOWER -> (
                      /\ state' = [state EXCEPT ![dst] = Follower]
                      /\ voted_for' = [voted_for EXCEPT ![dst] = INVALID_NODE_ID]
                      /\ UNCHANGED <<current_term, log, snapshot, event, history>>
                 )
                 [] result.append_result = APPEND_RESULT_STALE_INDEX -> (
                      /\ LET _e == [
                                event_type |-> "HandleAppendLog",
                                term |-> term,
                                node_id |-> dst,
                                leader_node_id |-> src,
                                append_success |-> TRUE,
                                match_index |-> snapshot[dst].index
                              ]
                              IN event' = event \cup {_e} 
                                
                      /\ UNCHANGED <<current_term, state, voted_for, log, snapshot, history>>                         
                 )
                 [] result.append_result = APPEND_RESULT_ACCEPT -> (
                        /\ LET _e == [
                                event_type |-> "HandleAppendLog",
                                term |-> term,
                                node_id |-> dst,
                                leader_node_id |-> src,
                                append_success |-> TRUE, 
                                match_index |-> result.match_index
                              ]
                              
                            IN event' = event \cup {_e}
                        /\ log' = [log EXCEPT ![dst] = result.log]
                        /\ IF CHECK_SAFETY THEN
                                LET leader_log == e.leader_log
                                   leader_snapshot == e.leader_snapshot
                                   op == [
                                        follower_append |-> [
                                            node_id |-> dst,
                                            leader_log |-> leader_log,
                                            leader_snapshot |-> leader_snapshot,
                                            follower_log |-> result.log,
                                            follower_snapshot |-> snapshot[dst]
                                        ]
                                    ]
                                 IN history' = AppendHistory(history, op, CHECK_SAFETY)
                            ELSE UNCHANGED <<history>>
                       /\ UNCHANGED <<current_term, state, voted_for, snapshot>>
                 )
                 [] OTHER  -> (
                    FALSE
                 )
                )
              /\ LET actions0 == ActionSeqSetupAll 
                    actions1 == ActionSeqCheck(dst)
                    actions2 == Action(ActionInput, Message(src, dst, __ActionHandleAppendLogRequest, msg_payload))
                 IN SetAction(__action__,  actions0, actions1 \o actions2)
    /\ UNCHANGED <<commit_index>>


ClientRequest(nid, v) ==
    /\ state[nid] = Leader
    /\ ~LogHasValue(log, snapshot, nid, v)
    /\  LET entry == [
                index |-> Len(log[nid]) + 1,
                term  |-> current_term[nid],
                value |-> v]
        IN /\ log' = [log EXCEPT ![nid] = Append(log[nid], entry)]
    /\ LET  actions0 == ActionSeqSetupAll
            actions1 == ActionSeqCheck(nid)
            actions2 == Action(ActionInput, Message(nid, nid, __ActionClientRequest, v))
        IN SetAction(__action__, actions0, actions1 \o actions2)
    /\ UNCHANGED <<commit_index, history, current_term, state, voted_for, snapshot, event>> 

LeaderAdvanceCommitIndex(nid) ==
    /\ state[nid] = Leader
    /\  LET indexes == { 
            i \in 1..LastLogIndex(log[nid], snapshot[nid]) :
                /\ \E quorum \in QuorumOf(NODE_ID):
                    /\ \A _n \in quorum: 
                        \/ _n = nid
                        \/ (\E e \in event:
                                /\ e.event_type = "HandleAppendLog"
                                /\ e.node_id = _n
                                /\ e.leader_node_id = nid
                                /\ e.term = current_term[nid]
                                /\ e.append_success
                                /\ e.match_index >= i
                            )
                }
           
       IN ( /\ Cardinality(indexes) > 0
            /\  LET max_commit_index == Max(indexes)
                IN (/\ max_commit_index > commit_index
                    /\ commit_index' = max_commit_index
                    /\ LET  actions0 == ActionSeqSetupAll 
                        actions1 == ActionSeqCheck(nid)
                        actions2 == Action(ActionInput, Message(nid, nid, __ActionAdvanceCommitIndex, max_commit_index))
                     IN SetAction(__action__, actions0, actions1 \o actions2)
                   )
           )
    /\   UNCHANGED << state,
                current_term,
                log, 
                snapshot,
                voted_for,
                event,
                history
            >>

LogCompaction(nid) ==
    /\ snapshot[nid].index < commit_index
    /\ LET last_log_index == LastLogIndex(log[nid], snapshot[nid])
            compact_log_index == Min({last_log_index, commit_index})
            offset == LogIndexToOffset(log[nid], snapshot[nid], compact_log_index)
            term == LogTermOfIndex(log[nid], snapshot[nid], compact_log_index)
            compact_log == SubSeq(log[nid], 1, offset)
            
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
               IN snapshot' = [snapshot EXCEPT  ![nid] = [index |-> compact_log_index, term |-> term, value |-> snapshot[nid].value \cup snapshot_values] ]
            /\ log' = [log EXCEPT  ![nid] = SubSeq(log[nid], offset + 1, Len(log[nid]))]
            /\ LET  actions0 == ActionSeqSetupAll
                    actions1 == ActionSeqCheck(nid)
                    actions2 == Action(ActionInput, Message(nid, nid, __ActionLogCompaction, compact_log_index))
                    
                IN SetAction(__action__, actions0, actions1 \o actions2)
           )
    /\ UNCHANGED <<
            state,
            current_term,
            voted_for,
            commit_index,
            event,
            history>>

Restart(nid) ==
    /\ state' = [state EXCEPT ![nid] = Follower]
    /\ LET  actions0 == ActionSeqSetupAll
        actions1 == ActionSeqCheck(nid)
        actions2 == Action(ActionInput, MessageNP(nid, nid, __ActionRestart))
       IN SetAction(__action__, actions0, actions1 \o actions2)
    /\ UNCHANGED <<
        current_term,
        log, 
        snapshot,
        voted_for,
        commit_index,
        event,
        history>>
    
Next == 
    \/ \E nid \in NODE_ID:
        \E value \in VALUE:   
            /\ ClientRequest(nid, value)
            /\ SaveState
            /\ SaveActions
    \/ \E nid \in NODE_ID:  
            /\ RequestVote(nid)
            /\ SaveState
            /\ SaveActions
    \/ \E nid1, nid2 \in NODE_ID:  
            /\ nid1 /= nid2
            /\ UpdateTerm(nid1, nid2)
            /\ SaveState
            /\ SaveActions
    \/ \E nid \in NODE_ID:  
            /\ BecomeLeader(nid)
            /\ SaveState
            /\ SaveActions
    \/ \E nid \in NODE_ID:  
            /\ AppendLog(nid)
            /\ SaveState
            /\ SaveActions
    \/ \E nid1, nid2 \in NODE_ID:
            /\ nid1 /= nid2  
            /\ HandleRequestVote(nid1, nid2)
            /\ SaveState
            /\ SaveActions
    \/ \E nid1, nid2 \in NODE_ID:  
            /\ HandleAppendLog(nid1, nid2)   
            /\ SaveState
            /\ SaveActions
    \/ \E nid \in NODE_ID:  
            /\ LeaderAdvanceCommitIndex(nid)
            /\ SaveState
            /\ SaveActions
    \/ \E nid \in NODE_ID:
            /\ LogCompaction(nid)
            /\ SaveState
            /\ SaveActions
    \/ \E nid \in NODE_ID:
            /\ Restart(nid)
            /\ SaveState
            /\ SaveActions
            
\* The specification must start with the initial state and transition according
\* to Next.
Spec == 
    /\ Init 
    /\ [][Next]_vars


StateOK ==
    BaseStateOK(
        state,
        current_term,
        log,
        snapshot,
        voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM)
   

LogTermGrowOK ==
    LogTermGrow(log, snapshot, NODE_ID)
            
        
PrefixCommitted ==
    InvariantPrefixCommitted(
        log,
        MAX_TERM,
        NODE_ID,
        history)
        
AtMostOneLeaderPerTerm ==  
    InvariantAtMostOneLeaderPerTerm(
          history)
    
SnapshotCommit ==    
    InvariantSnapshotCommit(
        log,
        snapshot,
        NODE_ID)
    
LogPrefixOK ==    
    InvariantLogPrefix(
        log,
        snapshot,
        NODE_ID)
    
FollowerAppend ==    
    InvariantFollowerAppend(
        history)
        
LogStateOK == 
    LogOK( 
        current_term,
        log,
        snapshot,
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


