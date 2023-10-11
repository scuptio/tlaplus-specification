------------------------------ MODULE StateDB ------------------------------

LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

DBOpen(path) ==
    TRUE

DBClose ==
    TRUE

CreateState(state) ==
  (*************************************************************************)
  (* NewState would store state to a give database if it not exist         *)
  (*************************************************************************)
  TRUE

QueryAllStates ==
  (*************************************************************************)
  (* QueryAllStates would load a set of state from the given database.     *)
  (*************************************************************************)
  CHOOSE val : TRUE


StoreValue(name, value) ==
  (*************************************************************************)
  (* StoreValue would store a named value to a give database.              *)
  (*************************************************************************)
  TRUE
    

LoadValue(name) ==
  (*************************************************************************)
  (* LoadValue would load a named value from a give database.              *)
  (*************************************************************************)
  CHOOSE val: TRUE


============================================================================
