

--------------------------------- MODULE index_out_of_bound ---------------------------------

EXTENDS UUID

    
VARIABLE id1, id2, id3, id4, id5, id6

vars == <<id1, id2, id3, id4, id5, id6>>

Init == 
    /\ id1 = UUID
    /\ id2 = UUID
    /\ id3 = UUID
    /\ id4 = UUID
    /\ id5 = UUID
    /\ id6 = UUID                        

Next == 
    /\ id1' = UUID
    /\ id2' = UUID
    /\ id3' = UUID
    /\ id4' = UUID
    /\ id5' = UUID
    /\ id6' = UUID

Spec == 
    /\ Init 
    /\ [][Next]_vars
    
===============================================================================


