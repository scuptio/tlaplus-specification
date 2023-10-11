--------------------------------- MODULE action ---------------------------------

EXTENDS message, UUID, StateDB, Sequences, FiniteSets, Naturals


ActionInternal  ==  "T"
ActionInput     ==  "I"
ActionOutput    ==  "O"


IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

SetToSeq(S) == 
  (**************************************************************************)
  (* Convert a set to some sequence that contains all the elements of the   *)
  (* set exactly once, and contains no other elements.                      *)
  (**************************************************************************)
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
    
Action(
    _action_type, 
    _payload
) == 
    <<[
            t |-> _action_type, 
            p |-> _payload
    ]>>


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
            
SetAction(
    _action_variable,
    _action_sequence
) ==
    _action_variable' = [
        p |-> _action_variable.i,
        i |-> UUID,
        a |-> _action_sequence 
    ]

InitAction(
    _action_variable,
    _action_sequence
) ==
    _action_variable = [
        p |-> "",
        i |-> UUID,
        a |-> _action_sequence 
    ]

    
InitActionEmpty == {}

===============================================================================