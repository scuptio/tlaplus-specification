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

Put(val) ==
  (*************************************************************************)
  (* Put would store a tuple of values to the given file as (plain) JSON.  *)
  (* Records will be serialized as a JSON objects, and tuples as arrays.   *)
  (*************************************************************************)
  TRUE

QueryAll ==
  (*************************************************************************)
  (* QueryAll would load a set of value from the given file. JSON objects  *)
  (* will be deserialized to records, and arrays will be deserialized to   *)
  (* tuples.   															   *)
  (*************************************************************************)
  CHOOSE val : TRUE



============================================================================
