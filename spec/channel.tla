------------------------------ MODULE channel ------------------------------

EXTENDS action, Sequences



----


\* Channel Utility

FilterMessage(source, dest, channel) ==
    {m \in channel : m.source = source /\ m.dest = dest}


WithMessage(m, channel) ==
    channel \cup {m}

WithoutMessage(m, channel) ==
    channel \ {m}

WithMessageSet(m_set, channel) ==
    channel \cup m_set


    



RECURSIVE _MessageSet(_, _, _)

_MessageSet(msg, msg_set, node_ids) ==
    IF node_ids = {} THEN
        msg_set
    ELSE
        LET i == CHOOSE i \in node_ids : TRUE
            m == [msg EXCEPT !["dest"] = i ]
        IN _MessageSet(msg, msg_set \cup {m}, node_ids \ {i})

BuildMessageSet(msg, dest_node_ids) ==
    _MessageSet(msg, {}, dest_node_ids)
            



    

=============================================================================
\* Modification History
\* Last modified Thu Oct 12 12:01:40 CST 2023 by ybbh
\* Created Thu Jan 26 12:28:51 CST 2023 by ybbh
