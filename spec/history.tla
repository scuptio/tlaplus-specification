--------------------------------- MODULE history ---------------------------------

EXTENDS Sequences

InitHistory ==
    <<>>

AppendHistory(_history, _e, _enable) ==
    IF _enable THEN
        _history \o <<_e>>
    ELSE
        _history
        


===============================================================================