--------------------------------- MODULE raft_log_compaction ---------------------------------



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
CONSTANT APPEND_ENTRIES_MAX
----



VARIABLE v_state
VARIABLE v_log
VARIABLE v_voted_for
VARIABLE v_snapshot
VARIABLE v_commit_index
VARIABLE v_next_index
VARIABLE v_match_index
VARIABLE v_acked_value
VARIABLE v_messages

\* readonly
VARIABLE v_current_term

VARIABLE v_history


VARIABLE v_pc

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
    v_messages,
    v_pc,
    
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
    v_next_index,
    v_match_index,
    v_messages,
    v_pc
>>


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
                    /\ v_commit_index = e.v_commit_index
               )   
    /\ v_messages = {}
    /\ v_commit_index = [i \in NODE_ID |-> 0]
    /\ v_next_index = [i \in NODE_ID |-> 
            IF v_state[i] = Leader THEN
                [j \in NODE_ID |-> Len(v_log[i]) + 1]
            ELSE 
                [j \in NODE_ID |-> 1]
            ]
    /\ v_match_index = [i \in NODE_ID |-> [j \in NODE_ID |-> 0]]

    /\ v_history = <<>>
    /\ v_acked_value = {}
    /\ v_pc = [i \in NODE_ID |-> [state |-> "next"]]
    /\ LET actions == ActionSeqSetup
        IN InitAction(
            __action__,
            actions,
            actions
        )
    /\ SaveInitActions

            
Next == 
    \/ \E m \in v_messages: 
        /\ RecvMessage(m)
        /\ SaveActions
    \/ \E i \in NODE_ID : 
        /\ AppendLogEntries(i)
        /\ SaveActions


\* to Next.
Spec == 
    /\ Init 
    /\ [][Next]_vars
----



===============================================================================


