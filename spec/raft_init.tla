--------------------------------- MODULE raft_init ---------------------------------


EXTENDS raft_common, Naturals, FiniteSets, Sequences, TLC, StateStore


CONSTANT MAX_TERM
CONSTANT VALUE
CONSTANT NODE_ID


VARIABLE init_current_term
VARIABLE init_log
VARIABLE init_snapshot
VARIABLE init_voted_for
VARIABLE init_state

Vars == <<
    init_current_term,
    init_state,
    init_log,
    init_voted_for,
    init_snapshot
>>



InitV ==
    /\ StoreOpen("/tmp/store.db")
    /\ InitSaftyStateDefault(
        init_state,
        init_current_term,
        init_log,
        init_snapshot,
        init_voted_for,
        NODE_ID,
        VALUE,
        MAX_TERM
        )
    /\ StoreValue([
        state |-> init_state, 
        current_term |-> init_current_term, 
        log |-> init_log,
        voted_for |-> init_voted_for,
        snapshot |-> init_snapshot
       ])

Spec == InitV

===============================================================================
