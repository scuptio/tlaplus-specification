--------------------------------- MODULE message ---------------------------------

Message(
    _from,
    _to,
    _message_name,
    _payload) ==
    [
        source |-> _from,
        dest |-> _to,
        name |-> _message_name,
        payload |-> _payload
    ]
    
LocalMessage(
    _local_nid,
    _message_name,
    _payload) ==
    [
        source |-> _local_nid,
        dest |-> _local_nid,
        name |-> _message_name,
        payload |-> _payload
    ]
===============================================================================