------------------------ MODULE 2pc ------------------------

EXTENDS Naturals, FiniteSets, TLC, action, StateDB

CONSTANTS
    XID,            (* collection of transaction ids *)
    NODE_ID,        (* collection of server nodes *)
    ENABLE_ACTION,
    LIMIT_RESTART,
    LIMIT_TIMEOUT,
    DB_ACTION_PATH
    
VARIABLES
    v_tm_state,            (* transaction manager's state *)
    v_tm_rm_collection,    (* transaction manager's collection of rm_state *)
    v_pc_state,            (* transaction manager's soft state *)
    v_rm_state,            (* resource manager's state *)
    v_message,             (* collection of all messages *)
    v_limit_timeout,
    v_limit_restart,
    __action__
    
variables == <<
    v_tm_state,
    v_pc_state,
    v_rm_state,
    v_message,

    v_tm_rm_collection,
    v_limit_timeout,
    v_limit_restart,
    __action__
>>

vars_rm == <<v_rm_state>>
vars_tm == <<v_tm_state,  v_tm_rm_collection>>
vars_limit == <<v_limit_timeout, v_limit_restart>>

vars_view == <<
    v_tm_state,
    v_pc_state,
    v_rm_state,
    v_message,
    v_tm_rm_collection
>>

\* constant string definition
_TM_ABORTING == "TMAborting"
_TM_COMMITTING == "TMCommiting"
_TM_INVALID == "TMInvalid"
_TM_RUNNING == "TMRunning"
_TM_PREPARING == "TMPreparing"
_TM_COMMITTED == "TMCommitted"
_TM_ABORTED == "TMAborted"

_RM_INVALID == "RMInvalid"
_RM_RUNNING == "RMRunning"
_RM_PREPARED == "RMPrepared"
_RM_COMMITTED == "RMCommitted"
_RM_ABORTED == "RMAborted"

_PC_INVALID == "Invalid"
_PC_TM_COMMITTING == _TM_COMMITTING
_PC_TM_PREPARING == _TM_PREPARING
_PC_TM_ABORTING == _TM_ABORTING
_PC_TM_ABORTED == _TM_ABORTED
_PC_TM_COMMITTED == _TM_COMMITTED

(*@begin@
enum TMState {
    TMInvalid,
    TMRunning, 
    TMPreparing,
    TMCommitting,
    TMAborting, 
    TMCommitted, 
    TMAborted
}
@end@*)

TM_STATE == 
{
    _TM_INVALID,
    _TM_RUNNING, 
    _TM_PREPARING,
    _TM_COMMITTING,
    _TM_ABORTING, 
    _TM_COMMITTED, 
    _TM_ABORTED
}

(*@begin@
enum RMState {
    RMInvalid,
    RMRunning, 
    RMPrepared, 
    RMCommitted, 
    RMAborted
}
@end@*)



RM_STATE ==
{   
    _RM_INVALID,
    _RM_RUNNING, 
    _RM_PREPARED, 
    _RM_COMMITTED, 
    _RM_ABORTED
}


(*@begin@

struct Tx {
    xid:unknown XID
}

enum MsgTx {
    Prepare(Tx), 
    PreparedACK(Tx), 
    Commit(Tx), 
    CommittedACK(Tx), 
    Abort(Tx), 
    Aborted(Tx)
}
@end@*)


M_TM_PREPARE == "TMMsg::Prepare"
M_TM_COMMIT == "TMMsg::Commit"
M_TM_ABORT == "TMMsg::Abort"
M_RM_ABORTED_ACK == "RMMsg::AbortedACK"
M_RM_PREPARE_RESP == "RMMsg::PrepareResp"
M_RM_COMMITTED_ACK == "RMMsg::CommittedACK"


M_D_TM_PREPARE == "DTMTesting::TMPrepare"
M_D_TM_TIMEOUT == "DTMTesting::TMTimeout"
M_D_RM_ABORT == "DTMTesting::RMAbort"
M_D_RESTART == "DTMTesting::Restart"
M_D_RM_TIMEOUT == "DTMTesting::RMTimeout"

M_D_TM_COMMITED == "TMCommitted"
M_D_TM_ABORTED == "TMAborted"
M_D_TM_SEND_PREPARE == "TMSendPrepare"
M_D_TM_SEND_COMMIT == "TMSendCommit"
M_D_TM_SEND_ABORT == "TMSendAbort"
M_D_SETUP == "DTMTesting::Setup"
M_D_CHECK == "DTMTesting::Check"

M_D_TM_ACCESS == "DTMTesting::TMAccess"
M_D_RM_ACCESS == "DTMTesting::RMAccess"
M_D_TX_BEGIN == "DTMTesting::TxBegin"

MESSAGE_TYPE == 
{
    M_TM_PREPARE, 
    M_RM_PREPARE_RESP, 
    M_TM_COMMIT, 
    M_RM_COMMITTED_ACK, 
    M_TM_ABORT, 
    M_RM_ABORTED_ACK
}


(*@begin@

struct __ATxRMState {
    xid: unknown XID,
    state: RMState,
}

struct __ATxTMState {
    xid: unknown XID,
    state: RMState
}

struct __ATxInit {
    v_rm_state: Set<__ATxRMState>,
    v_tm_state: Set<__ATxTMState>
}

enum __Action {
    Init(__ATxInit),
    Receive(MsgTx),
    Send(MsgTx),
    Prepare(Tx),
    TMCommit(Tx),
    TMAbort(Tx),
    TMPrepare(Tx),
    RMAbort(Tx),
    Restart
}

automaton TxCoordCommit {
    input init_state(v_message: __ATxInit, source:NodeId, dest:NodeId)
    input receive_message(v_message: MsgTx, source:NodeId, dest:NodeId)
    output send_message(v_message:MsgTx, source:NodeId, dest:NodeId)
    internal tm_prepare(v_message:Tx, source:NodeId, dest:NodeId)
    internal tm_commit(v_message:Tx, source:NodeId, dest:NodeId)
}M_D_TM_SEND_PREPARE


automaton TestTxCoordCommit {
    input incoming_action(v_message:Message<__Action>)
}

@end@*)



            
_TypeInvariant == 
    /\ \A _n \in NODE_ID:
        (\A _x \in XID:
            ( /\ v_tm_state[_n][_x].state \in TM_STATE
              /\ v_rm_state[_n][_x].rm_id \in SUBSET(NODE_ID)
            )
        )
    /\ \A _n \in NODE_ID:
        (\A _x \in XID:
            ( /\ v_rm_state[_n][_x].state \in RM_STATE
              /\ v_rm_state[_n][_x].rm_id \in SUBSET(NODE_ID)   
            )
        )
 
    /\ \A _n1 \in NODE_ID:
        \A _x \in XID:
            \A _n2 \in NODE_ID:
                /\ v_tm_rm_collection[_n1][_x][_n2] \in RM_STATE

    
__RMNode(_tm_rm_collection) ==
    {n \in DOMAIN _tm_rm_collection:
        _tm_rm_collection[n] \in (RM_STATE \ {_RM_INVALID})
    }
        




_RMNodeAtState(_tm_rm_collection, _states) ==
    { 
        id \in NODE_ID:
            \E nid \in DOMAIN _tm_rm_collection : 
                /\ nid = id
                /\ _tm_rm_collection[nid] \in _states
    }
            


_StateCorrect(
    _xid, 
    _tm_nid, 
    _rm_nids,
    _tm_state,
    _rm_state
) ==
    /\ _tm_state[_tm_nid][_xid].state = _TM_COMMITTED =>
       (    LET ok == \A n \in _rm_nids: 
                        _rm_state[n][_xid].state = _RM_COMMITTED
            IN /\ ~ok => PrintT(<<"state error, tm committed", _tm_state, _rm_state>>)
               /\ ok
       ) 
    /\ (_tm_state[_tm_nid][_xid].state = _TM_ABORTED =>
            LET ok == \A n \in _rm_nids: 
                        _rm_state[n][_xid].state = _RM_ABORTED
            IN /\ ~ok => PrintT(<<"state error, tm aborted", _tm_state, _rm_state>>)
               /\ ok
        )
   /\ (_tm_state[_tm_nid][_xid].state = _TM_COMMITTING =>
            LET ok == /\ \A n \in _rm_nids: 
                            _rm_state[n][_xid].state \in {_RM_COMMITTED, _RM_PREPARED}
            IN /\ ~ok => PrintT(<<"state error, tm committing", _tm_state, _rm_state>>)
               /\ ok
        )
   /\ (_tm_state[_tm_nid][_xid].state = _TM_ABORTING =>
            LET ok == ~(\E n \in _rm_nids: 
                        _rm_state[n][_xid].state = _RM_COMMITTED)
            IN /\ ~ok => PrintT(<<"state error, tm aborting", _tm_state, _rm_state>>)
               /\ ok
        )
   /\ (_tm_state[_tm_nid][_xid].state = _TM_PREPARING =>
            LET ok == \A n \in _rm_nids: 
                        _rm_state[n][_xid].state \in {_RM_PREPARED, _RM_RUNNING, _RM_ABORTED}
            IN /\ ~ok => PrintT(<<"state error, tm preparing", _tm_state, _rm_state>>)
               /\ ok        
      )
   /\ \A _tm \in NODE_ID \ {_tm_nid}, _rm \in NODE_ID \ _rm_nids:  
        LET ok == (/\ _tm_state[_tm][_xid].state = _TM_INVALID
                   /\ _rm_state[_rm][_xid].state = _RM_INVALID)
        IN /\ ~ok => PrintT(<<"state error, all invalid", _tm_state, _rm_state>>)
           /\ ok  

_ValidState(_tm_state, _rm_state, _tm_rm_collection) ==
    \A x \in XID, tm_n \in NODE_ID:
        LET rm_n_ids == _tm_state[tm_n][x].rm_id
        IN Cardinality(rm_n_ids) > 0 
            => _StateCorrect(x, tm_n, rm_n_ids, _tm_state, _rm_state)

_TranStateInvariant == 
    _ValidState(v_tm_state, v_rm_state, v_tm_rm_collection)

__RMState(_rm_state) ==
    {
        x \in [
            xid : DOMAIN _rm_state,
            state : RM_STATE 
        ]: 
        _rm_state[x.xid] = x.state
    }

__TMState(_tm_state, _tm_rm_collection) ==
    { 
        x \in [
            xid : DOMAIN _tm_state,
            state : TM_STATE, 
            rm_nids : SUBSET(NODE_ID)
        ]: 
        /\ _tm_state[x.xid] = x.state
        /\ __RMNode(_tm_rm_collection[x.xid]) = x.rm_nids
    }
        
_HandleNodePayload(_nid) ==
    [
        v_rm_state |-> __RMState(v_rm_state[_nid]),
        v_tm_state |-> __TMState(v_tm_state[_nid], v_tm_rm_collection[_nid])
    ]





_ALLRMAtState(_collection, _states) ==
    \A n \in DOMAIN _collection:
        _collection[n] \in _states


State2PC(_nid) == 
    [
        v_tm_state |-> v_tm_state[_nid],
        v_rm_state |-> v_rm_state[_nid]
    ]

ActionSeqSetupAll ==
    ActionsFromHandle(
            State2PC,
            NODE_ID, 
            ActionSetup, 
            M_D_SETUP
       )

ActionCheckState(_node_id) ==
    ActionsFromHandle(
            State2PC,
            {_node_id}, 
            ActionCheck, 
            M_D_CHECK
       )
              
Init == 
    /\ v_tm_state = [n \in NODE_ID |-> [x \in XID |-> [state |-> _TM_INVALID, rm_id |-> {}]]]
    /\ v_rm_state = [n \in NODE_ID |-> [x \in XID |-> [state |-> _RM_INVALID, rm_id |-> {}]]]
    /\ v_pc_state = [n \in NODE_ID |-> [state |-> _PC_INVALID]]
    /\ v_message = {}
    /\ v_tm_rm_collection = [n \in NODE_ID |-> [x \in XID |-> [_n \in NODE_ID |-> _RM_INVALID]]]
    /\ v_limit_timeout = 0
    /\ v_limit_restart = 0
    /\  LET actions == ActionSeqSetupAll
        IN InitActionT(__action__, actions, actions) 
        
TxBegin(_nid, _xid) ==
    /\ v_pc_state[_nid].state = _PC_INVALID
    /\ \A nid \in NODE_ID:
        /\ v_tm_state[nid][_xid].state = _TM_INVALID
        /\ v_rm_state[nid][_xid].state = _RM_INVALID
    /\ v_tm_state' = [v_tm_state EXCEPT ![_nid][_xid] = [state |-> _TM_RUNNING, rm_id |-> {}]]
    /\ LET a0 == ActionSeqSetupAll
                a1 == ActionCheckState(_nid)
                m == MessageLocal(_nid, M_D_TX_BEGIN, [xid |-> _xid])
                a2 == Action(ActionInput, m)
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
    /\ UNCHANGED <<
        vars_rm,
        vars_limit,
        v_message,
        v_pc_state,
        v_tm_rm_collection
        >>

TxAccess(_nid, _xid, _rm_nid) ==
    /\ v_pc_state[_nid].state = _PC_INVALID
    /\ v_pc_state[_rm_nid].state = _PC_INVALID
    /\ v_tm_state[_nid][_xid].state = _TM_RUNNING
    /\ v_rm_state[_rm_nid][_xid].state \in {_RM_RUNNING, _RM_INVALID}
    /\ v_tm_rm_collection' = [v_tm_rm_collection EXCEPT ![_nid][_xid][_rm_nid] = _RM_RUNNING]
    /\ v_tm_state' = [v_tm_state EXCEPT ![_nid][_xid].rm_id = v_tm_state[_nid][_xid].rm_id \cup {_rm_nid} ]
    /\ v_rm_state' = [v_rm_state EXCEPT ![_rm_nid][_xid].state = _RM_RUNNING]
    /\ LET a0 == ActionSeqSetupAll
                a1 == ActionCheckState(_nid)
                m_tm == MessageLocal(_nid, M_D_TM_ACCESS, [xid |-> _xid])
                a2 == Action(ActionInput, m_tm)
                a3 == ActionCheckState(_rm_nid)
                m_rm == MessageLocal(_rm_nid, M_D_TM_ACCESS, [xid |-> _xid])
                a4 == Action(ActionInput, m_rm)
       IN SetAction(__action__, a0, a1 \o a2 \o a3 \o a4, ENABLE_ACTION)
    /\ UNCHANGED <<
        vars_limit,
        v_pc_state,
        v_message
        >>
    
TMTimeout(n, x) ==
    /\ v_pc_state[n].state = _PC_INVALID
    /\ CASE v_tm_state[n][x].state \in {_TM_RUNNING, _TM_PREPARING, _TM_ABORTING} -> (
            /\ v_tm_state' = [v_tm_state EXCEPT ![n][x].state = _TM_ABORTING] 
            /\ v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_TM_ABORTING, xid |-> x]]
       )
       [] v_tm_state[n][x].state \in {_TM_COMMITTING} -> (
            /\ v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_TM_COMMITTING, xid |-> x]]
            /\ UNCHANGED <<v_tm_state>>
       )
       [] OTHER -> (
            FALSE
       )
    /\ LET msg == Message(n, n, M_D_TM_TIMEOUT, [xid |-> x])
           a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInput, msg) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION) 
    /\ UNCHANGED <<
        v_rm_state,
        v_message,
        v_tm_rm_collection
       >>


                     
TMPrepare(n, x) == 
    /\ v_pc_state[n].state = _PC_INVALID
    /\ v_tm_state[n][x].state \in {_TM_RUNNING, _TM_PREPARING}
    /\ Cardinality(v_tm_state[n][x].rm_id) >= 1
    /\ LET  rm_node_id == v_tm_state[n][x].rm_id
            rm_nids == _RMNodeAtState(v_tm_rm_collection[n][x], {_RM_RUNNING})
            need_coord == Cardinality(rm_node_id) > 1
            msgs == IF need_coord THEN
                        MessageSet({n}, rm_nids, M_TM_PREPARE, [xid |-> x, rm_id |-> rm_node_id])
                    ELSE
                        MessageSet({n}, rm_nids, M_TM_COMMIT, [xid |-> x])
            m_a == Message(n, n, M_D_TM_SEND_PREPARE, [xid |-> x])  
       IN /\ v_message' = v_message \union msgs
          /\ LET state == IF need_coord THEN
                            _TM_PREPARING
                          ELSE
                            _TM_INVALID
             IN v_tm_state' = [v_tm_state EXCEPT ![n][x].state = state]
          /\ LET a0 == ActionSeqSetupAll
                a1 == ActionCheckState(n)
                a2 == Action(ActionInternal, m_a)
                a3 == Actions(ActionOutput, msgs)
             IN SetAction(__action__, a0, a1 \o a2 \o a3, ENABLE_ACTION)
    /\ UNCHANGED <<v_pc_state, v_rm_state, v_tm_rm_collection>>

_TMStateAdvance(_n, _x, _rm_collection, _pc_state) ==
    LET aborted_set == _RMNodeAtState(_rm_collection[_n][_x], {_RM_ABORTED})
           prepared_set == _RMNodeAtState(_rm_collection[_n][_x], {_RM_PREPARED})
           node_set == _RMNodeAtState(_rm_collection[_n][_x], {_RM_ABORTED, _RM_PREPARED, _RM_RUNNING})
    IN CASE ( 
             /\ node_set = prepared_set 
             /\ aborted_set = {}) ->  (
            /\ _pc_state' = [_pc_state EXCEPT ![_n] = [xid |-> _x, state |-> _PC_TM_COMMITTING]]
       )
       [] ( 
           /\ aborted_set \cup prepared_set = node_set 
           /\ aborted_set # {})
           -> (
                /\ _pc_state' = [_pc_state EXCEPT ![_n] = [xid |-> _x, state |-> _PC_TM_ABORTING]]
            )
       [] OTHER -> (  
            UNCHANGED <<_pc_state>>
       )

TMReceivePrepared(n, x, m) == 
    /\ v_pc_state[n].state = _PC_INVALID
    /\ m.name = M_RM_PREPARE_RESP
    /\ m.payload.xid = x
    /\ m.payload.success
    /\ m.dest = n
    /\ v_tm_state[n][x].state = _TM_PREPARING
    /\ LET a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInput, m) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
    /\ (LET _rm_collection  == [v_tm_rm_collection EXCEPT ![n][x][m.source] =_RM_PREPARED]
        IN /\ v_tm_rm_collection' = _rm_collection
           /\ _TMStateAdvance(n, x,  _rm_collection, v_pc_state)
        )
    /\ UNCHANGED <<v_tm_state, v_rm_state, v_message>>
    

TMSendCommit(n, x) == 
    /\ v_pc_state[n].state = _PC_TM_COMMITTING
    /\ v_pc_state[n].xid = x
    /\ v_tm_state[n][x].state \in {_TM_PREPARING, _TM_COMMITTING}
    /\ LET rm_nids == _RMNodeAtState(v_tm_rm_collection[n][x], {_RM_PREPARED})
            msgs == MessageSet({n}, rm_nids, M_TM_COMMIT, [xid |-> x])
            a == Message(n, n, M_D_TM_SEND_COMMIT, [xid |-> x])
       IN /\ v_message' = v_message \union  msgs
          /\ LET 
                a0 == ActionSeqSetupAll
                a1 == ActionCheckState(n)
                a2 == Action(ActionInternal, a) 
                a3 == Actions(ActionOutput, msgs)
             IN SetAction(__action__, a0, a1 \o a2 \o a3, ENABLE_ACTION) 
    /\ v_tm_state' = [v_tm_state EXCEPT ![n][x].state = _TM_COMMITTING]
    /\ v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_INVALID]]
    /\ UNCHANGED <<v_rm_state, v_tm_rm_collection>>

TMReceiveCommittedACK(n, x, m) == 
    /\ v_pc_state[n].state = _PC_INVALID
    /\ m.name = M_RM_COMMITTED_ACK
    /\ m.dest = n
    /\ m.payload.xid = x
    /\ v_tm_state[n][x].state = _TM_COMMITTING
    /\ LET a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInput, m) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
    /\ v_tm_rm_collection' = [v_tm_rm_collection EXCEPT ![n][x][m.source] = _RM_INVALID]
    /\ LET can_end == _ALLRMAtState(v_tm_rm_collection'[n][x], {_RM_INVALID})
       IN  IF can_end THEN 
                v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_TM_COMMITTED, xid |-> x]]
           ELSE 
                UNCHANGED <<v_pc_state>>
    /\ UNCHANGED <<v_tm_state, v_rm_state, v_message>>

TMReceiveAbortedACK(n, x, m) == 
    /\ v_pc_state[n].state = _PC_INVALID
    /\ m.name = M_RM_ABORTED_ACK
    /\ m.dest = n
    /\ m.payload.xid = x
    /\ v_tm_state[n][x].state = _TM_ABORTING
    /\ LET a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInput, m) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
    /\ v_tm_rm_collection' = [v_tm_rm_collection EXCEPT ![n][x][m.source] = _RM_INVALID]
    /\ LET can_end == _ALLRMAtState(v_tm_rm_collection'[n][x], {_RM_INVALID})
       IN  IF can_end THEN 
                v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_TM_ABORTED, xid |-> x]]
           ELSE 
                UNCHANGED <<v_pc_state>>
    /\ UNCHANGED <<v_tm_state, v_rm_state, v_message>>
        
TMSendAbort(n, x) == 
    /\ v_pc_state[n].state = _PC_TM_ABORTING
    /\ v_pc_state[n].xid = x
    /\ (\/ v_tm_state[n][x].state = _TM_RUNNING 
        \/ v_tm_state[n][x].state = _TM_PREPARING
        \/ v_tm_state[n][x].state = _TM_ABORTING
       )
    /\ LET rm_nids == _RMNodeAtState(v_tm_rm_collection[n][x], {_RM_RUNNING, _RM_PREPARED, _RM_ABORTED})
           msgs == MessageSet({n}, rm_nids, M_TM_ABORT, [xid |-> x])
           a == Message(n, n, M_D_TM_SEND_ABORT, [xid |-> x])   
       IN /\ v_message' = v_message \union msgs
          /\ LET 
                a0 == ActionSeqSetupAll
                a1 == ActionCheckState(n)
                a2 == Action(ActionInternal, a) 
                a3 == Actions(ActionOutput, msgs)
             IN SetAction(__action__, a0, a1 \o a2 \o a3, ENABLE_ACTION) 
    /\ v_tm_state' = [v_tm_state EXCEPT ![n][x].state = _TM_ABORTING]
    /\ v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_INVALID]]
    /\ UNCHANGED <<v_rm_state, v_tm_rm_collection>>

TMReceivePrepareAbort(n, x, m) == 
    /\ m.name = M_RM_PREPARE_RESP
    /\ m.dest = n
    /\ m.payload.xid = x
    /\ ~ m.payload.success
    /\ v_pc_state[n].state = _PC_INVALID
    /\ v_tm_state[n][x].state = _TM_PREPARING
    /\ LET a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInput, m) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
    /\ (LET _rm_collection  == [v_tm_rm_collection EXCEPT ![n][x][m.source] =  _RM_ABORTED]
        IN /\ v_tm_rm_collection' = _rm_collection
           /\ _TMStateAdvance(n, x,  _rm_collection, v_pc_state)
        )
    /\ UNCHANGED <<v_tm_state, v_rm_state, v_message>>

TMAborted(n, x) ==
    /\ v_pc_state[n].state = _PC_TM_ABORTED
    /\ v_pc_state[n].xid = x
    /\ v_tm_state' = [v_tm_state EXCEPT ![n][x].state = _TM_ABORTED]
    /\ v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_INVALID]]
    /\ LET a == Message(n, n, M_D_TM_ABORTED, [xid |-> x])
           a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInternal, a) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION) 
    /\ UNCHANGED <<
        v_tm_rm_collection,
        v_rm_state, 
        v_message
       >>

TMCommitted(n, x) ==
    /\ v_pc_state[n].state = _PC_TM_COMMITTED
    /\ v_pc_state[n].xid = x
    /\ v_tm_state' = [v_tm_state EXCEPT ![n][x].state = _TM_COMMITTED]
    /\ v_pc_state' = [v_pc_state EXCEPT ![n] = [state |-> _PC_INVALID]]
    /\ LET m == Message(n, n, M_D_TM_COMMITED, [xid |-> x])
           a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInput, m) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
    /\ UNCHANGED <<
        v_tm_rm_collection,
        v_rm_state, 
        v_message
       >>

RMAbort(n, x) ==
    /\ v_pc_state[n].state = _PC_INVALID
    /\ v_rm_state[n][x].state = _RM_RUNNING
    /\ v_rm_state' = [v_rm_state EXCEPT ![n][x].state = _RM_ABORTED]
    /\ LET m == Message(n, n, M_D_RM_ABORT, [xid |-> x])
           a0 == ActionSeqSetupAll
           a1 == ActionCheckState(n)
           a2 == Action(ActionInput, m) 
       IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
    /\ UNCHANGED <<v_tm_state, v_pc_state, v_message, v_tm_rm_collection>>

RMReceivePrepare(n, x, m) == 
    /\ v_pc_state[n].state = _PC_INVALID
    /\ m.name = M_TM_PREPARE
    /\ m.dest = n
    /\ m.payload.xid = x
    /\  (\/ ( /\ v_rm_state[n][x].state \in {_RM_RUNNING, _RM_PREPARED, _RM_COMMITTED}
                /\ (IF v_rm_state[n][x].state \in {_RM_INVALID, _RM_RUNNING} THEN
                        v_rm_state' = [v_rm_state EXCEPT ![n][x] = [state |-> _RM_PREPARED, rm_id |-> m.payload.rm_id]]
                    ELSE 
                        UNCHANGED <<v_rm_state>>
                    )
                /\ LET msg == Message(n, m.source, M_RM_PREPARE_RESP, [xid|-> x, success |-> TRUE])
                   IN /\ LET a0 == ActionSeqSetupAll
                                   a1 == ActionCheckState(n)
                                   a2 == Action(ActionInput, m) 
                                   a3 == Action(ActionOutput, msg) 
                         IN SetAction(__action__, a0, a1 \o a2 \o a3, ENABLE_ACTION)
                      /\ v_message' = v_message \union {msg}
               )
           \/ ( /\ v_rm_state[n][x].state \in  {_RM_ABORTED, _RM_INVALID}
                /\ UNCHANGED <<v_rm_state>>
                /\ LET msg == Message(n, m.source, M_RM_PREPARE_RESP, [xid|-> x, success |-> FALSE])
                   IN /\ LET a0 == ActionSeqSetupAll
                                   a1 == ActionCheckState(n)
                                   a2 == Action(ActionInput, m)
                                   a3 == Action(ActionOutput, msg)  
                         IN SetAction(__action__, a0, a1 \o a2 \o a3, ENABLE_ACTION)
                      /\ v_message' = v_message \union {msg}
               )
           )
    /\ UNCHANGED <<v_tm_state, v_pc_state, v_tm_rm_collection>>


RMReceiveCommit(n, x, m) == 
    /\ v_pc_state[n].state = _PC_INVALID
    /\ m.name = M_TM_COMMIT
    /\ m.dest = n
    /\ m.payload.xid = x
    /\ v_rm_state[n][x].state \in {_RM_INVALID, _RM_PREPARED, _RM_COMMITTED}
    /\ IF v_rm_state[n][x].state = _RM_PREPARED THEN
            v_rm_state' = [v_rm_state EXCEPT ![n][x].state = _RM_COMMITTED]
       ELSE 
            UNCHANGED <<v_rm_state>>
    /\ LET msg == Message(n, m.source, M_RM_COMMITTED_ACK, [xid |-> x])
       IN /\ LET a0 == ActionSeqSetupAll
                       a1 == ActionCheckState(n)
                       a2 == Action(ActionInput, m)
                       a3 == Action(ActionOutput, msg)  
             IN SetAction(__action__, a0, a1 \o a2 \o a3, ENABLE_ACTION)
          /\ v_message' = v_message \union {msg}     
    /\ UNCHANGED <<v_tm_state, v_pc_state, v_tm_rm_collection>>

RMReceiveAbort(n, x, m) == 
    /\ v_pc_state[n].state = _PC_INVALID
    /\ m.name = M_TM_ABORT
    /\ m.dest = n
    /\ m.payload.xid = x
    /\ v_rm_state[n][x].state \in {_RM_INVALID, _RM_RUNNING, _RM_PREPARED, _RM_ABORTED}
    /\ IF v_rm_state[n][x].state \in {_RM_PREPARED, _RM_RUNNING} THEN
            v_rm_state' = [v_rm_state EXCEPT ![n][x].state = _RM_ABORTED]
       ELSE
            UNCHANGED <<v_rm_state>>
    /\ LET msg == Message(n, m.source, M_RM_ABORTED_ACK, [xid |-> x])
       IN /\ LET a0 == ActionSeqSetupAll
                       a1 == ActionCheckState(n)
                       a2 == Action(ActionInput, m)
                       a3 == Action(ActionOutput, msg)  
             IN SetAction(__action__, a0, a1 \o a2 \o a3, ENABLE_ACTION)
          /\ v_message' = v_message \union {msg} 
    /\ UNCHANGED <<v_tm_state, v_pc_state, v_tm_rm_collection>>


Restart(n) ==
    /\ v_pc_state[n].state = _PC_INVALID
    /\ v_rm_state' = [v_rm_state EXCEPT ![n] =
            [
                x \in DOMAIN v_rm_state[n] |-> 
                   (IF v_rm_state[n][x].state = _RM_RUNNING THEN
                        \* lost running state
                        [state |-> _RM_ABORTED, rm_id |-> {}]
                    ELSE
                        \* state unchanged
                        v_rm_state[n][x]
                   )
            ]
        
        ]
    /\ v_tm_state' = [v_tm_state EXCEPT ![n] =
            [
                x \in DOMAIN v_tm_state[n] |-> 
                    CASE v_tm_state[n][x].state \in {_TM_ABORTING, _TM_PREPARING} -> (
                        \* aborting tx
                        [state |-> _TM_ABORTING, rm_id |-> v_tm_state[n][x].rm_id]
                    )
                    [] v_tm_state[n][x].state = _TM_RUNNING -> (
                         \* lost running state
                         [state |-> _TM_INVALID, rm_id |-> {}]
                    )
                    [] OTHER -> (
                        \* state unchanged
                        v_tm_state[n][x]
                    )
            ]
        
        ]
    /\ v_tm_rm_collection' = [
            v_tm_rm_collection EXCEPT ![n] =             
            [
                x \in DOMAIN v_tm_rm_collection[n] |->
                    IF v_tm_state[n][x].state \in {_TM_ABORTING, _TM_PREPARING, _TM_COMMITTING} THEN
                        \* need to advance 2PC
                            LET rm_nids == __RMNode(v_tm_rm_collection[n][x])
                            IN [_nid \in NODE_ID |-> 
                                    IF _nid \in rm_nids THEN
                                        _RM_RUNNING
                                    ELSE
                                        v_tm_rm_collection[n][x][_nid]
                                    ]

                    ELSE
                        v_tm_rm_collection[n][x]

            ]
        ]
     /\ LET a0 == ActionSeqSetupAll
            a1 == ActionCheckState(n)
            m == Message(n, n, M_D_RESTART, {})
            a2 == Action(ActionSetup, m)
        IN SetAction(__action__, a0, a1 \o a2, ENABLE_ACTION)
     /\ UNCHANGED <<v_pc_state, v_message>>
                                
Next == 
    \E n \in NODE_ID, x \in XID: 
       \/( /\(  \/ TxBegin(n, x)
                \/ \E _rm_id \in NODE_ID:
                    TxAccess(n, x, _rm_id)
                \/ TMPrepare(n, x)
                \/ RMAbort(n, x)
                \/ TMAborted(n, x)
                \/ TMCommitted(n, x) 
                \/ TMSendAbort(n, x)  
                \/ TMSendCommit(n, x)
                \/ \E m \in v_message: 
                       (\/ TMReceivePrepared(n, x, m)
                        \/ TMReceiveCommittedACK(n, x, m)
                        \/ TMReceiveAbortedACK(n, x, m)
                        \/ TMReceivePrepareAbort(n, x, m)
                        \/ RMReceivePrepare(n, x, m)
                        \/ RMReceiveCommit(n, x, m) 
                        \/ RMReceiveAbort(n, x, m)
                       )
            )
           /\ UNCHANGED <<vars_limit>>
         )
        \/ (/\ v_limit_timeout + 1 <= LIMIT_TIMEOUT
            /\ TMTimeout(n, x)
            /\ v_limit_timeout' = v_limit_timeout + 1
            /\ UNCHANGED <<v_limit_restart>>
           )
        \/ (/\ v_limit_restart + 1 <= LIMIT_RESTART
            /\ Restart(n)
            /\ v_limit_restart' = v_limit_restart + 1
            /\ UNCHANGED <<v_limit_timeout>>
           )


    
\* The specification must start with the initial state and transition according to Next.
Spec == Init /\ [][Next]_variables

AssertStateInvariant == _TranStateInvariant
AssertTypeInvariant == _TypeInvariant


SaveActions ==
    DB_ACTION_PATH /= "" =>
        SaveValue(__action__, DB_ACTION_PATH)

=============================================================================
