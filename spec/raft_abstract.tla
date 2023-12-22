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


VARIABLE v_state
VARIABLE v_current_term
VARIABLE v_log
VARIABLE v_snapshot
VARIABLE v_voted_for
VARIABLE v_event
VARIABLE v_history
VARIABLE v_commit_index
VARIABLE __action__

vars == <<
    v_state,
    v_current_term,
    v_log, 
    v_snapshot,
    v_voted_for,
    v_commit_index,
    v_event,
    v_history,
    __action__
>>

vars_view == <<
    v_state,
    v_current_term,
    v_log, 
    v_snapshot,
    v_commit_index,
    v_voted_for,
    v_event
>>


_RaftVariables(_nid) ==
    [
        state |-> v_state[_nid],
        current_term |-> v_current_term[_nid],
        log |-> v_log[_nid],
        snapshot |-> v_snapshot[_nid],
        voted_for |-> v_voted_for[_nid],
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
        state |-> v_state,
        current_term |-> v_current_term,
        log |-> v_log,
        snapshot |-> v_snapshot,
        voted_for |-> v_voted_for
    ]


SaveActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)

InitStateDB == 
    /\ DB_STATE_PATH /= "" => 
        SaveValue(SaveVars, DB_STATE_PATH)
    /\ DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)

SaveStates ==
    DB_STATE_PATH /= "" => 
        SaveValue(SaveVars, DB_STATE_PATH)
        
Init ==
    /\ InitSaftyStateTrival(
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
    /\ v_event = {}
    /\ v_commit_index = 0
    /\ v_history = <<>>
    /\ LET actions == InitActionSeqSetup
        IN InitActionT(
            __action__,
            actions,
            actions
        )


RequestVote(nid) ==
    /\ TermLE(nid, v_current_term, MAX_TERM)
    /\ v_state[nid] = Follower
    /\ v_state' = [v_state EXCEPT ![nid] = Candidate]
    /\ v_current_term' = [v_current_term EXCEPT ![nid] = v_current_term[nid] + 1]
    /\ v_event' = v_event \union 
            {[
                event_type  |-> "RequestVote",
                term |-> v_current_term[nid] + 1,
                last_log_term |-> LastLogTerm(v_log[nid], v_snapshot[nid]),
                last_log_index |-> Len(v_log[nid]),
                node_id |-> nid
             ]}
    /\ v_voted_for' = [v_voted_for EXCEPT ![nid] = nid]
	/\ LET actions0 == ActionSeqSetupAll
           actions1 == ActionSeqCheck(nid)
	       actions2 == Action(ActionInput, MessageNP(nid, nid, __ActionRequestVote)) 
       IN SetAction(__action__,  actions0, actions1 \o actions2, ENABLE_ACTION)
    /\ UNCHANGED <<
             v_commit_index,
             v_history,
             v_log,
             v_snapshot
        >>   
    
HandleRequestVote(dst) ==
    \E e \in v_event:
        /\ e.node_id # dst
        /\ e.event_type = "RequestVote"
        /\ LET src == e.node_id
               _term == e.term 
               _last_log_term == e.last_log_term
               _last_log_index == e.last_log_index
               _voted_for_node == e.node_id
               _current_term == v_current_term[dst]
               
               _granted == VoteCanGrant(
                        v_current_term[dst],
                        v_log[dst],
                        v_snapshot[dst],
                        v_voted_for[dst],
                        _voted_for_node,
                        _term, 
                        _last_log_term, 
                        _last_log_index)
           IN /\ v_current_term[dst] = _term
              /\ _granted 
              /\ v_voted_for' = [v_voted_for EXCEPT ![dst] = _voted_for_node]
              /\ v_event' = v_event \union 
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
                    IN SetAction(__action__,  actions0, actions1 \o actions2, ENABLE_ACTION)
                        /\ UNCHANGED <<
                            v_commit_index, v_history, v_state, v_current_term, v_log, v_snapshot
                        >>


BecomeLeader(nid) == 
    /\ \E quorum \in QuorumOf(NODE_ID):
        /\ \A _node_id \in quorum: 
            /\ _node_id = nid => 
                   (\E e \in v_event:
                        /\ e.event_type = "RequestVote"
                        /\ e.term = v_current_term[nid]
                        /\ e.node_id = _node_id
                   )
            /\ _node_id # nid => 
                (\E e \in v_event:
                    /\ e.event_type = "HandleRequestVote"
                    /\ e.voted_for = nid
                    /\ e.node_id = _node_id
                    /\ e.term = v_current_term[nid]
                )
        /\ v_state[nid] = Candidate
        /\ v_state' = [v_state EXCEPT ![nid] = Leader]
    /\ LET  actions0 == ActionSeqSetupAll
            actions1 == ActionSeqCheck(nid)
            actions2  == Action(ActionInput, MessageNP(nid, nid, __ActionBecomeLeader))
        IN SetAction(__action__, actions0, actions1 \o actions2, ENABLE_ACTION)
    /\ LET o == 
        [
            election |-> 
            [
               leader |-> nid,
               term |-> v_current_term[nid],
               log |-> v_log[nid],
               snapshot |-> v_snapshot[nid]
            ]
        ] 
        IN v_history' = AppendHistory(v_history, o, CHECK_SAFETY)
     /\ UNCHANGED <<v_commit_index, v_current_term, v_log, v_snapshot, v_voted_for, v_event>>

UpdateTerm(dst) ==
    /\ (\E e \in v_event:
            /\ e.node_id # dst
            /\ e.term > v_current_term[dst]
            /\ e.event_type \in { "RequestVote", "AppendLog" }
            /\ v_state' = [v_state EXCEPT ![dst] = Follower]
            /\ v_current_term' = [v_current_term EXCEPT ![dst] = e.term]
            /\ v_voted_for' = [v_voted_for EXCEPT ![dst] = INVALID_NODE_ID]
            /\ LET  src == e.node_id
                    actions0 == ActionSeqSetupAll
                    actions1 == ActionSeqCheck(dst)
                    actions2 == Action(ActionInput, Message(src, dst, __ActionHandleUpdateTerm, e.term))
                IN SetAction(__action__, actions0, actions1 \o actions2, ENABLE_ACTION)
        )
     /\ UNCHANGED <<v_commit_index, v_history, v_log, v_snapshot, v_event>>

AppendLog(nid) ==
    /\ v_state[nid] = Leader
    /\ \E i \in 1..Len(v_log[nid]):
        /\ v_event' = v_event \cup 
                            {[
                                event_type  |-> "AppendLog",
                                term |-> v_current_term[nid],
                                log_entries |-> <<v_log[nid][i]>>,
                                node_id |-> nid,
                                prev_log_index |-> IF i <= 1 THEN v_snapshot[nid].index ELSE v_log[nid][i - 1].index ,
                                prev_log_term |-> IF i <= 1 THEN v_snapshot[nid].term ELSE v_log[nid][i - 1].term,
                                leader_log |-> IF CHECK_SAFETY THEN v_log[nid] ELSE <<>>,
                                leader_snapshot |-> IF CHECK_SAFETY THEN v_snapshot[nid] ELSE {}
                                                    
                            ]}
        /\ LET  actions0 == ActionSeqSetupAll
                actions1 == ActionSeqCheck(nid)
                actions2 == Action(ActionInput, MessageNP(nid, nid, __ActionAppendLog))
            IN SetAction(__action__, actions0, actions1 \o actions2, ENABLE_ACTION)
   /\ UNCHANGED <<v_commit_index, v_log, v_snapshot, v_state, v_voted_for, v_current_term, v_history>>
   

_HandleRejectRequest ==
    UNCHANGED <<v_voted_for>>
            
_HandleCandidateBecomeFollower(_node_id) ==
    /\ v_state' = [v_state EXCEPT ![_node_id] = Follower]
    /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
    /\ UNCHANGED <<v_current_term, v_log, v_snapshot, v_event, v_history>>



_HANDLE_APPEND_TO_LOG ==
    UNCHANGED <<v_voted_for>>

    
    
HandleAppendLog(_node_id) ==
    /\ \E e \in v_event:                               
        /\ e.event_type = "AppendLog"
        /\ e.node_id /= _node_id
        /\ LET  
                src == e.node_id
                prev_log_index == e.prev_log_index
                prev_log_term == e.prev_log_term
                log_ok == LogPrevEntryOK(
                    v_log[_node_id], 
                    v_snapshot[_node_id],
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
                        _node_id,
                        v_log[_node_id],
                        v_snapshot[_node_id],
                        v_current_term[_node_id],
                        v_state[_node_id],
                        v_history,
                        RECONFIG_VALUE,
                        src,
                        prev_log_index,
                        prev_log_term,
                        term,
                        log_entries
                     )
          IN /\ (CASE  result.append_result = APPEND_RESULT_REJECT -> (
                      UNCHANGED <<v_current_term, v_state, v_voted_for, v_log, v_snapshot, v_event, v_history>>
                 )
                 [] result.append_result = APPEND_RESULT_TO_FOLLOWER -> (
                      /\ v_state' = [v_state EXCEPT ![_node_id] = Follower]
                      /\ v_voted_for' = [v_voted_for EXCEPT ![_node_id] = INVALID_NODE_ID]
                      /\ UNCHANGED <<v_current_term, v_log, v_snapshot, v_event, v_history>>
                 )
                 [] result.append_result = APPEND_RESULT_ACCEPT -> (
                        /\ LET _e == [
                                event_type |-> "HandleAppendLog",
                                term |-> term,
                                node_id |-> _node_id,
                                leader_node_id |-> src,
                                append_success |-> TRUE, 
                                match_index |-> result.match_index
                              ]
                              
                            IN v_event' = v_event \cup {_e}
                        /\ v_log' = [v_log EXCEPT ![_node_id] = result.log]
                        /\ IF CHECK_SAFETY THEN
                                LET leader_log == e.leader_log
                                   leader_snapshot == e.leader_snapshot
                                   op == [
                                        follower_append |-> [
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
                                 IN v_history' = AppendHistory(v_history, op, CHECK_SAFETY)
                            ELSE UNCHANGED <<v_history>>
                       /\ UNCHANGED <<v_current_term, v_state, v_voted_for, v_snapshot>>
                 )
                 [] OTHER  -> (
                    FALSE
                 )
                )
              /\ LET actions0 == ActionSeqSetupAll 
                    actions1 == ActionSeqCheck(_node_id)
                    actions2 == Action(ActionInput, Message(src, _node_id, __ActionHandleAppendLogRequest, msg_payload))
                 IN SetAction(__action__,  actions0, actions1 \o actions2, ENABLE_ACTION)
    /\ UNCHANGED <<v_commit_index>>


ClientRequest(nid, v) ==
    /\ v_state[nid] = Leader
    /\ ~LogHasValue(v_log[nid], v_snapshot[nid], v)
    /\  LET entry == [
                index |-> LastLogIndex(v_log[nid], v_snapshot[nid]) + 1,
                term  |-> v_current_term[nid],
                value |-> v]
        IN /\ v_log' = [v_log EXCEPT ![nid] = Append(v_log[nid], entry)]
    /\ LET  actions0 == ActionSeqSetupAll
            actions1 == ActionSeqCheck(nid)
            actions2 == Action(ActionInput, Message(nid, nid, __ActionClientRequest, v))
        IN SetAction(__action__, actions0, actions1 \o actions2, ENABLE_ACTION)
    /\ UNCHANGED <<v_commit_index, v_history, v_current_term, v_state, v_voted_for, v_snapshot, v_event>> 

LeaderAdvanceCommitIndex(nid) ==
    /\ v_state[nid] = Leader
    /\  LET indexes == { 
            i \in 1..LastLogIndex(v_log[nid], v_snapshot[nid]) :
                /\ \E quorum \in QuorumOf(NODE_ID):
                    /\ \A _n \in quorum: 
                        \/ _n = nid
                        \/ (\E e \in v_event:
                                /\ e.event_type = "HandleAppendLog"
                                /\ e.node_id = _n
                                /\ e.leader_node_id = nid
                                /\ e.term = v_current_term[nid]
                                /\ e.append_success
                                /\ e.match_index >= i
                            )
                }
           
       IN ( /\ Cardinality(indexes) > 0
            /\  LET max_commit_index == Max(indexes)
                IN (/\ max_commit_index > v_commit_index
                    /\ v_commit_index' = max_commit_index
                    /\ LET  actions0 == ActionSeqSetupAll 
                        actions1 == ActionSeqCheck(nid)
                        actions2 == Action(ActionInput, Message(nid, nid, __ActionAdvanceCommitIndex, max_commit_index))
                     IN SetAction(__action__, actions0, actions1 \o actions2, ENABLE_ACTION)
                   )
           )
    /\   UNCHANGED << v_state,
                v_current_term,
                v_log, 
                v_snapshot,
                v_voted_for,
                v_event,
                v_history
            >>

LogCompaction(nid) ==
    /\ v_snapshot[nid].index < v_commit_index
    /\ LET last_log_index == LastLogIndex(v_log[nid], v_snapshot[nid])
            compact_log_index == Min({last_log_index, v_commit_index})
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
                    actions1 == ActionSeqCheck(nid)
                    actions2 == Action(ActionInput, Message(nid, nid, __ActionLogCompaction, compact_log_index))
                    
                IN SetAction(__action__, actions0, actions1 \o actions2, ENABLE_ACTION)
           )
    /\ UNCHANGED <<
            v_state,
            v_current_term,
            v_voted_for,
            v_commit_index,
            v_event,
            v_history>>

Restart(nid) ==
    /\ v_state' = [v_state EXCEPT ![nid] = Follower]
    /\ LET  actions0 == ActionSeqSetupAll
        actions1 == ActionSeqCheck(nid)
        actions2 == Action(ActionInput, MessageNP(nid, nid, __ActionRestart))
       IN SetAction(__action__, actions0, actions1 \o actions2, ENABLE_ACTION)
    /\ UNCHANGED <<
        v_current_term,
        v_log, 
        v_snapshot,
        v_voted_for,
        v_commit_index,
        v_event,
        v_history>>
    
Next == 
    \/ \E nid \in NODE_ID:
        \/ \E value \in VALUE:   
            ClientRequest(nid, value)
        \/ LeaderAdvanceCommitIndex(nid)
        \/ LogCompaction(nid)
        \/ Restart(nid)
        \/ RequestVote(nid)
        \/ BecomeLeader(nid)
        \/ AppendLog(nid)
        \/ HandleAppendLog(nid)  
        \/ HandleRequestVote(nid)
        \/ UpdateTerm(nid)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == 
    /\ Init 
    /\ [][Next]_vars



AssertStateOK ==
    /\ BaseStateOK(
        v_state,
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
        [i \in NODE_ID |-> v_commit_index],
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
        {},
        v_state,
        v_current_term,
        v_log,
        v_snapshot
        )



===============================================================================


