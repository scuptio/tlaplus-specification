--------------------------------- MODULE action ---------------------------------

EXTENDS message, GenID, StateDB, Sequences, SequencesExt, FiniteSets, Naturals


ActionInternal  ==  "T"
ActionInput     ==  "I"
ActionOutput    ==  "O"
ActionSetup     ==  "S"
ActionCheck     ==  "C"


    
Action(
    _action_type, 
    _payload
) == 
    <<[
            t |-> _action_type,
            p |-> _payload
    ]>>


Actions(
    _action_type,
    _payload_set
) ==
    LET _action_set == [
        t : {_action_type},
        p : _payload_set
    ]
    IN SetToSeq(_action_set)


    
CheckAction(_action, _node_id) ==
    \A i \in DOMAIN _action:
        /\ _action[i].t \in {ActionInternal, ActionInput, ActionOutput}
        /\ _action[i].source \in _node_id
        /\ _action[i].dest \in _node_id
        
        
AppendActionSeq(_var, _action_seq) ==
    _var \o _action_seq


AppendActionSet(_var, _action_set) ==
    _var \o SetToSeq(_action_set)


_NodeVariable(
    _var,
    _id,
    _node_ids
) ==
    [x \in DOMAIN _var |-> _var[x][_id]]  

_NodeChangedVariable(
    _old_var, 
    _new_var,
    _id,
    _node_ids
) ==
    LET changed == {x \in DOMAIN _old_var: _old_var[x][_id] # _new_var[x][_id]}
    IN  [x \in changed |-> _new_var[x][_id]]    


RECURSIVE ActionFromChangedVars(_, _, _, _, _)

ActionFromChangedVars(
    _old_var, 
    _new_var,
    _node_ids,
    _action_name,
    _action_type
) ==
    IF _node_ids = {} THEN
        {}
    ELSE 
        LET id == CHOOSE x \in _node_ids : TRUE
            changed_var == _NodeChangedVariable(_old_var, _new_var, id, _node_ids)
            action_set == { [
                        source |-> id,
                        dest |-> id,
                        name |-> _action_name,
                        type |-> _action_type, 
                        payload |-> changed_var
            ] }
        IN action_set \cup ActionFromChangedVars(
                _old_var, _new_var, _node_ids \ {id}, 
                _action_type, _action_name)
            

RECURSIVE __ActionSeqOfEachNodeHandle(_, _, _, _)

__ActionSeqOfEachNodeHandle(
    _handle_node_id(_),
    _node_ids,
    _action_type,
    _action_name
) ==
    IF _node_ids = {} THEN
        <<>>
    ELSE 
        LET id == CHOOSE x \in _node_ids : TRUE
            payload == _handle_node_id(id)
            msg == Message(id, id, _action_name, payload)
            action == Action(_action_type, msg)
        IN __ActionSeqOfEachNodeHandle(
                _handle_node_id,
                _node_ids \ {id}, 
                _action_type, 
                _action_name
                ) \o action

ActionsFromHandle(
    _handle_node_id(_),
    _node_ids,
    _action_type,
    _action_name
) ==
    __ActionSeqOfEachNodeHandle(
        _handle_node_id,
        _node_ids,
        _action_type,
        _action_name)


RECURSIVE __ActionSeqOfEachNodeHandleEx(_, _, _, _, _)

__ActionSeqOfEachNodeHandleEx(
    _handle_node_id(_, _),
    _node_ids,
    _action_type,
    _action_name,
    _context
) ==
    IF _node_ids = {} THEN
        <<>>
    ELSE 
        LET id == CHOOSE x \in _node_ids : TRUE
            payload == _handle_node_id(id, _context)
            msg == Message(id, id, _action_name, payload)
            action == Action(_action_type, msg)
        IN __ActionSeqOfEachNodeHandleEx(
                _handle_node_id,
                _node_ids \ {id}, 
                _action_type, 
                _action_name,
                _context
                ) \o action

ActionsFromHandleContext(
    _handle_node_id(_, _),
    _node_ids,
    _action_type,
    _action_name,
    _context
) ==
    __ActionSeqOfEachNodeHandleEx(
        _handle_node_id,
        _node_ids,
        _action_type,
        _action_name,
        _context
      )
        
PrevIdOfAction(
    _action
) ==
    _action.p
    
IdOfAction(
    _action
) ==
    _action.i



ContinuousAction(
    _action, 
    _pc) == 
    /\ "id" \in DOMAIN _pc
    /\ _pc.id = PrevIdOfAction(_action)


InitAction(
    _action_variable,
    _action_sequence1,
    _action_sequence2,
    _enable
) ==
    IF _enable THEN
        _action_variable = [
            p |-> _action_variable.i,
            i |-> NextID,
            s |-> _action_sequence1,
            a |-> _action_sequence2 
        ]
    ELSE
        _action_variable = [
            p |-> GetID,
            i |-> GetID,
            s |-> <<>>,
            a |-> <<>> 
        ]


SetAction(
    _action_variable,
    _action_sequence1,
    _action_sequence2,
    _enable
) ==
    IF _enable THEN
        _action_variable' = [
            p |-> _action_variable.i,
            i |-> NextID,
            s |-> _action_sequence1,
            a |-> _action_sequence2 
        ]
    ELSE
        _action_variable' = [
            p |-> GetID,
            i |-> GetID,
            s |-> <<>>,
            a |-> <<>> 
        ]

    
InitActionT(
    _action_variable,
    _action_sequence1,
    _action_sequence2
) ==
    _action_variable = [
        p |-> NextID,
        i |-> NextID,
        s |-> _action_sequence1,
        a |-> _action_sequence2 
    ]

SetActionT(
    _action_variable,
    _action_sequence1,
    _action_sequence2
) ==
    _action_variable' = [
        p |-> _action_variable.i,
        i |-> NextID,
        s |-> _action_sequence1,
        a |-> _action_sequence2 
    ]


                
InitActionEmpty == {}

===============================================================================