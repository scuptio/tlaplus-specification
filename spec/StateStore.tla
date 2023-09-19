------------------------------ MODULE StateStore ------------------------------

LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
  (*************************************************************************)
  (* Imports the definitions from the modules, but doesn't export them.    *)
  (*************************************************************************)

StoreOpen(path) ==
    TRUE

StoreClose ==
    TRUE

StoreValue(val) ==
  (*************************************************************************)
  (* StoreValue store a value to the given database.                       *)
  (* The value will be serialized as a JSON string                         *)
  (*************************************************************************)
  TRUE

LoadValue ==
  (*************************************************************************)
  (* LoadValue load a value from the given database                        *)
  (* The JSON string would be deserialized to a value                      *)
  (*************************************************************************)
  CHOOSE val : TRUE



============================================================================
