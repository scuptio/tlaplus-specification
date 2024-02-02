------------------------ MODULE blink_tree ------------------------

EXTENDS SequencesExt, Naturals, FiniteSets, TLC, action, StateDB

CONSTANTS KEY_INIT
CONSTANTS KEY_OPER
CONSTANTS KEY_MAX
CONSTANTS PAGE_NUM
CONSTANTS FAN_OUT_NUM
CONSTANTS SESSION_NUM
CONSTANTS NULL

CONSTANTS ENABLE_ACTION

VARIABLES
    v_root_id,
    v_tree_level,
    v_page,
    v_latch,
    v_stack,
    v_depth,
    v_command,
    v_operation,
    __action__
    
variables == <<
    v_root_id,
    v_tree_level,
    v_page,
    v_latch,
    v_stack,
    v_depth,
    v_command,
    v_operation,
    __action__
>>

vars_view == <<
    v_root_id,
    v_tree_level,
    v_page,
    v_latch,
    v_stack,
    v_depth,
    v_command,
    v_operation
>>

AI == "AccessIntent"
ND == "NodeDelete"
RL == "ReadLock"
WL == "WriteLock"
PM == "ParentModification"

PAGE_ID == 1..PAGE_NUM
SESSION == 1..SESSION_NUM

S_IDLE == "IDLE"
S_SEARCH_NON_LEAF == "SEARCH_NON_LEAF"
S_SEARCH_LEAF == "SEARCH_LEAF"
S_READ_WRITE == "READ_WRITE"
S_COMMAND == "COMMAND"
S_SCAN_LEAF == "SCAN_LEAF"
S_DONE == "DONE"

C_INSERT_KEY_VALUE == "INSERT_KEY_VALUE"
C_SPLIT_PAGE == "SPLIT_PAGE"
C_SEARCH_KEY == "SEARCH_KEY"
C_CONSOLIDATE_PAGE == "CONSOLIDATE_PAGE"
C_DELETE_PAGE == "DELETE_PAGE"
C_DELETE_SLOT == "DELETE_SLOT"
C_UPDATE_SLOT == "UPDATE_SLOT"
C_INSERT_SLOT_GUT == "INSERT_SLOT_GUT"
C_UPDATE_SLOT_GUT == "UPDATE_SLOT_GUT"
C_DELETE_SLOT_GUT == "DELETE_SLOT_GUT"
C_LATCH_ACQUIRE == "LATCH_ACQUIRE"
C_LATCH_RELEASE == "LATCH_RELEASE"
C_INSERT_SLOT == "INSERT_SLOT"
C_SEARCH_KEY_LEAF == "SEARCH_KEY_LEAF"
C_VISIT_PARENT == "VISIT_PARENT"
C_UPDATE_SLOT_PAGE_ID == "UPDATE_SLOT_PAGE_ID"

OP_SEARCH_KEY == "SEARCH_KEY"
OP_INSERT_KEY == "INSERT_KEY"
OP_UPDATE_KEY == "UPDATE_KEY"
OP_DELETE_KEY == "DELETE_KEY"

D_SETUP == "SETUP"
D_LATCH_ACQUIRE == "LATCH_ACQUIRE"
D_LATCH_RELEASE == "LATCH_RELEASE"
D_LATCH_ACQUIRED == "LATCH_ACQUIRED"
D_SEARCH_RESULT == "SEARCH_RESULT"
D_DELETE_RESULT == "DELETE_RESULT"
D_INSERT_RESULT == "INSERT_RESULT"
D_UPDATE_RESULT == "UPDATE_RESULT"
D_SPLIT_PAGE == "SPLIT_PAGE"
D_SEARCH_TOP_DOWN == "SEARCH_TOP_DOWN"

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

RECURSIVE __SeqRemoveIndex(_, _, _)


__SeqRemoveIndex(_seq_in, _seq_out, index) ==
    IF Cardinality(index) = 0 THEN
        _seq_out
    ELSE
         LET min_index == Min(index)
         IN _seq_out \o <<_seq_in[min_index]>>


_SeqSelectAllInSeq(seq, Test(_)) ==
  (*************************************************************************)
  (* Selects the index of the first element such that Test(seq[i]) is true *)
  (* Equals 0 if Test(seq[i]) is FALSE for all elements.                   *)
  (*************************************************************************)
  LET I == { i \in 1..Len(seq) : Test(seq[i]) }
  IN I
  
_SeqRemoveMatch(_seq, _test(_)) ==
    LET index == _SeqSelectAllInSeq(_seq, _test)
    IN __SeqRemoveIndex(_seq,<<>>,  index)
    
_HalfCeiling(_n) ==
    LET v == _n \div 2
    IN 
        IF _n % 2 = 0 THEN
            v 
        ELSE
            v + 1
            
_StateBLink(_id) == 
    [
        task_id |-> _id,
        root_id |-> v_root_id,
        page |-> v_page,
        stack |-> v_stack[_id],
        latch |-> v_latch,
        operation |-> v_operation[_id]
    ]

_ActionSetup ==
    ActionsFromHandle(
            _StateBLink,
            SESSION, 
            ActionSetup, 
            D_SETUP
       )

    
_KeyLess(key1, key2) ==
    CASE key1 = KEY_MAX -> (
        FALSE
    )
    [] key2 = KEY_MAX -> (
        TRUE
    )
    [] OTHER -> (
        key1 < key2
    )

_KeyGreat(key1, key2) ==
    _KeyLess(key2, key1)
    
_ChoosePageId(_page_id) ==
    CHOOSE _p \in _page_id: TRUE

_HighKey(
    _page
) == 
    IF Len(_page.slot) = 0 THEN
        NULL 
    ELSE
        _page.slot[Len(_page.slot)].key

RECURSIVE _ConstructSlotNonLeaf(_, _)
_ConstructSlotNonLeaf(_slot_array, _page_children) ==
    LET _t == PrintT(<<_slot_array, _page_children>>)
    IN
    IF Cardinality(_page_children) = 0 THEN
        _slot_array
    ELSE
        LET page == 
             CHOOSE s1 \in _page_children:
                \A s2 \in _page_children \ {s1}:
                    _KeyLess(_HighKey(s1), _HighKey(s2))
            slot == [key |-> _HighKey(page), page_id |-> page.page_id] 
        IN _ConstructSlotNonLeaf(_slot_array \o <<slot>>, _page_children \ {page})
        

RECURSIVE _ConstructSlotLeaf(_, _)
_ConstructSlotLeaf(_slot_array, _slot_set) ==
    IF Cardinality(_slot_set) = 0 THEN
        _slot_array
    ELSE
        LET slot == 
             CHOOSE s1 \in _slot_set:
                \A s2 \in _slot_set \ {s1}:
                    _KeyLess(s1.key, s2.key)
        IN _ConstructSlotLeaf(_slot_array \o <<slot>>, _slot_set \ {slot})

_SelectLevel(_page_set, _level) ==
    {p \in _page_set: p.level = _level}

RECURSIVE _ConstructTreeNonLeaf(_, _, _, _, _, _)
_ConstructTreeNonLeaf(_page_set_l1, _page_set, _page_ids,  _current_page_id, _level, _fan_out) ==
    LET page_id ==
            IF _current_page_id = NULL THEN 
                CHOOSE _p \in _page_ids: TRUE
            ELSE
                _current_page_id
    IN CASE Cardinality(_page_set)  = 0 -> (
          _page_set_l1
       )
       []  Cardinality(_page_set) < _fan_out -> (
            LET pages == _page_set
                slot == _ConstructSlotNonLeaf(<<>>, pages)
                page == [
                            page_id |-> page_id,
                            level |-> _level, 
                            right_id |-> NULL, 
                            slot |-> slot
                        ]
            IN _page_set_l1 \cup {page}
        )
        [] OTHER -> (
            LET pages == CHOOSE pages \in SUBSET(_page_set):
                                /\ Cardinality(pages) = _fan_out
                                /\ \A p1 \in pages:
                                    \A p2 \in _page_set \ pages:
                                        _KeyLess(_HighKey(p1),  _HighKey(p2))
                slot == _ConstructSlotNonLeaf(<<>>, pages)
                right_page_id == IF Cardinality(_page_set) = _fan_out THEN 
                                    \* no page left, no right siblings
                                    NULL
                                 ELSE
                                    CHOOSE id \in _page_ids : id /= page_id           
                page == [
                            page_id |-> page_id,
                            level |-> _level, 
                            right_id |-> right_page_id, 
                            slot |-> slot
                        ]
           IN _ConstructTreeNonLeaf(
                    _page_set_l1 \cup {page}, 
                    _page_set \ pages, 
                    _page_ids \ {page_id, right_page_id}, 
                    right_page_id, _level, _fan_out)
          )
          
RECURSIVE _ConstructTreeLeaf(_, _, _, _, _)
_ConstructTreeLeaf(page_set, _keys, _page_ids,  _current_page_id, _fan_out) ==
   LET page_id == IF _current_page_id = NULL THEN 
                            CHOOSE _p \in _page_ids: TRUE
                       ELSE
                          _current_page_id
   IN                       
    IF Cardinality(_keys) < _fan_out THEN
        LET 
            slot == _ConstructSlotLeaf(<<>>, [key : _keys, value : {NULL}]) \o <<[key |-> KEY_MAX, value |-> NULL]>>
            page == [
                        level |-> 0, 
                        page_id |-> page_id,
                        right_id |-> NULL, 
                        slot |-> slot
                    ]
        IN page_set \cup {page}
    ELSE
        LET key_page ==
                IF Cardinality(_keys) < _fan_out THEN
                    _keys 
                ELSE
                    CHOOSE key_page \in SUBSET(_keys):
                        /\ Cardinality(key_page) = _fan_out
                        /\ \A k1 \in key_page:
                            \A k2 \in _keys \ key_page:
                                _KeyLess(k1,  k2)

            right_page_id == CHOOSE id \in _page_ids : id /= page_id
            slot == _ConstructSlotLeaf(<<>>, [key : key_page, value : {NULL}])
            page == [
                        page_id |-> page_id,
                        level |-> 0, 
                        right_id |-> right_page_id, 
                        slot |-> slot
                    ]
        IN _ConstructTreeLeaf(page_set \cup {page}, _keys \ key_page, _page_ids \ {page_id, right_page_id}, right_page_id, _fan_out)

_PageIdSet(_page_set) ==
    { p.page_id : p \in _page_set}

RECURSIVE _ConstructTreeGut(_, _, _, _, _)
_ConstructTreeGut(_page, _keys, _page_ids, _level, _fan_out)  ==
    IF _level = 0 THEN
        LET pages == _ConstructTreeLeaf(_page, _keys, _page_ids, NULL, _fan_out)
        IN _ConstructTreeGut(pages \cup _page, _keys, _page_ids \ _PageIdSet(pages \cup _page), 1, _fan_out)
    ELSE
        LET pages_l0 == _SelectLevel(_page, _level - 1)
        IN     IF Cardinality(pages_l0) = 1 THEN
                    _page
               ELSE
                  LET pages_l1 == _ConstructTreeNonLeaf({}, pages_l0, _page_ids, NULL, _level, _fan_out)
                  IN _ConstructTreeGut(pages_l1 \cup _page, _keys, _page_ids \ _PageIdSet(pages_l1 \cup _page), _level + 1, _fan_out)
            
_ConstructTree(_keys, _page_ids, _fan_out) ==
    LET pages == _ConstructTreeGut({}, _keys, _page_ids, 0, _fan_out)
        root_page == 
            CHOOSE p0 \in pages:
                \A p1 \in pages \ {p0}:
                    p0.level > p1.level
        root_id == root_page.page_id            
        level == root_page.level + 1
    IN [root_id |-> root_id, page |-> pages, level |-> level]

_TestConstructTreeLeaf ==
    LET pages == _ConstructTreeLeaf({}, 1..4, {"p1", "p2", "p3"}, NULL, 2)
    IN /\ pages =
            {
                [slot |-> <<[key |-> KEY_MAX, value |-> NULL]>>, page_id |-> "p3", level |-> 0, right_id |-> NULL], 
                [slot |-> <<[key |-> 1, value |-> NULL], [key |-> 2, value |-> NULL]>>, page_id |-> "p1", level |-> 0, right_id |-> "p2"], 
                [slot |-> <<[key |-> 3, value |-> NULL], [key |-> 4, value |-> NULL]>>, page_id |-> "p2", level |-> 0, right_id |-> "p3"]
            }
      /\ LET non_leaf_pages == _ConstructTreeNonLeaf({}, pages, {"p4", "p5", "p6", "p7"}, NULL, 1, 2)
           IN non_leaf_pages =  {
                [slot |-> <<[key |-> KEY_MAX, page_id |-> "p3"]>>, page_id |-> "p5", level |-> 1, right_id |-> NULL], 
                [slot |-> <<[key |-> 2, page_id |-> "p1"], 
                [key |-> 4, page_id |-> "p2"]>>, page_id |-> "p4", level |-> 1, right_id |-> "p5"]
             }


_TestConstructTree ==
    LET tree == _ConstructTree(1..4, {"p1", "p2", "p3", "p4", "p5", "p6", "p7"}, 2)
    IN /\ tree.root_id = "p6"
       /\ tree.level = 3
       /\ tree.page = {
                [
                    page_id |-> "p1", level |-> 0, right_id |-> "p2", 
                    slot |-> <<[key |-> 1, value |-> NULL], [key |-> 2, value |-> NULL]>>
                ], 
                [
                    page_id |-> "p2", level |-> 0, right_id |-> "p3",
                    slot |-> <<[key |-> 3, value |-> NULL], [key |-> 4, value |-> NULL]>>
                ],
                [
                    page_id |-> "p3", level |-> 0, right_id |-> NULL,
                    slot |-> <<[key |-> KEY_MAX, value |-> NULL]>>
                ],
                [
                    page_id |-> "p4", level |-> 1, right_id |-> "p5",
                    slot |-> <<[key |-> 2, page_id |-> "p1"], [key |-> 4, page_id |-> "p2"]>>
                ], 
                [
                    page_id |-> "p5", level |-> 1, right_id |-> NULL,
                    slot |-> <<[key |-> KEY_MAX, page_id |-> "p3"]>>
                ],
                [
                    page_id |-> "p6", level |-> 2, right_id |-> NULL,
                    slot |-> <<[key |-> 4, page_id |-> "p4"], [key |-> KEY_MAX, page_id |-> "p5"]>>
                ]
         }
     
    
Init == 
    LET tree == _ConstructTree(KEY_INIT, PAGE_ID, FAN_OUT_NUM)
    IN  
        /\ v_root_id = tree.root_id
        /\ v_tree_level = tree.level
        /\ v_page =  [ id \in {page.page_id: page \in tree.page} |-> CHOOSE page \in tree.page: page.page_id = id]
        /\ v_operation = [s \in SESSION |-> [operation |-> NULL]]
        /\ v_depth = [s \in SESSION |-> 0]
        /\ v_latch = [s \in PAGE_ID |-> {}]  
        /\ v_stack = [s \in SESSION |-> <<>>]
        /\ v_command = [s \in SESSION |-> <<>>]
        /\ InitActionT(__action__, _ActionSetup, _ActionSetup)




(*
                                    Latch Requested
                            AI      ND      RL      WL      PM
    E AccessIntent          Y       N       Y       Y       Y
    X NodeDelete            N/A     N/A     Y       Y       Y
    I ReadLock              Y       Y       Y       N       Y
    S WriteLock             Y       Y       N       N       Y
    T ParentModification    Y       Y       Y       Y       N
*)


       
_First(
    _command_seq
    ) ==
    _command_seq[1]

_Last(
    _command_seq
    ) ==
    _command_seq[Len(_command_seq)]

_FirstCommandType(
    _command_seq
    ) ==
    _command_seq[1].command_type
    
_LastCommandType(
    _command_seq
    ) ==
    _command_seq[Len(_command_seq)].command_type

_PopLast(
    _command_seq
) ==
    IF Len(_command_seq) <= 1 THEN
        <<>>
    ELSE
        SubSeq(_command_seq, 1, Len(_command_seq) - 1)


    
_PopFirst(
    _command_seq
) ==
    IF Len(_command_seq) <= 1 THEN
        <<>>
    ELSE
        SubSeq(_command_seq, 2, Len(_command_seq))


_CommandExcluded(_cmd_seq, _cmd_type_set, _page_id_set) ==
    [
        i \in DOMAIN _cmd_seq |-> 
            /\ _cmd_seq[i].command_type \in _cmd_type_set
            /\ _cmd_seq[i].page_id \in _page_id_set
    ]
    
             
_LatchCapatible(
    _latch_existing, 
    _latch_request
) ==
    CASE _latch_existing = AI -> (
        _latch_request \in {AI, RL, WL, PM}
    )
    [] _latch_existing = ND -> (
        IF _latch_request \in {AI, ND} THEN
            \* since all referencesto it have previouslybeen removed from the tree
            "AcesssIntent, NodeDelete latch requesting cannot happend when existing NodeDelete"
        ELSE
            _latch_request \in {RL, WL, PM}
    )
    [] _latch_existing = RL -> (
        _latch_request \in {AI, ND, RL, PM}
    )
    [] _latch_existing = WL -> (
        _latch_request \in {AI, ND, PM}
    )
    [] _latch_existing = PM -> (
        _latch_request \in {AI, ND, RL, WL}
    )
    [] OTHER -> (
        "unknown latch type"
    )


_PopLastLevel(_stack) ==
    IF Len(_stack) = 0 THEN
        <<>>
    ELSE
        LET last_depth == _stack[Len(_stack)].depth
            index == CHOOSE i \in 1..Len(_stack): 
                        /\ \A j \in 1..i - 1:
                            _stack[j].depth < last_depth
                        /\ \A k \in i .. Len(_stack):
                            _stack[k].depth = last_depth
        IN SubSeq(_stack, 1, index - 1)


_ParentLevelPageId(_stack) ==
    IF Len(_stack) <= 1 THEN
        NULL
    ELSE
        LET s == _PopLastLevel(_stack)
        IN _stack[Len(s)].page_id
    
_LatchCanAcquire(_s, _existing_latch, mode) ==
    \A l \in _existing_latch:
        \/ l.task_id = _s
        \/ _LatchCapatible(l.mode, mode)


_LatchAcquireCommand(_page_id, _mode) ==
    [command_type |-> C_LATCH_ACQUIRE, page_id |-> _page_id, latch_mode |-> _mode]

_LatchReleaseCommand(_page_id, _mode) ==
    [command_type |-> C_LATCH_RELEASE, page_id |-> _page_id, latch_mode |-> _mode]

           
\* search the index I, where:
\*      the first index _slot[i] >= _k  
_SearchKey(_slot_seq, _key) ==    
    CASE Len(_slot_seq) = 0 -> (
        0
    )
    [] OTHER -> ( 
        LET set == 
                {
                    idx \in 1..Len(_slot_seq):
                       /\ ( \A i \in 1..idx - 1:
                                _KeyLess(_slot_seq[i].key,  _key)
                          )
                       /\ (\/ (/\ _slot_seq[idx].key = _key
                               /\ ( ~\E i \in idx + 1 .. Len(_slot_seq):
                                      _KeyLess(_slot_seq[i].key, _key)
                                  )
                               )
                           \/ (/\ _KeyGreat(_slot_seq[idx].key, _key)
                               /\ ( ~\E i \in idx + 1 .. Len(_slot_seq):
                                      ~_KeyGreat(_slot_seq[i].key, _key)
                                  )
                               )
                           )

                }
            
        IN CASE Cardinality(set) = 1 ->
            CHOOSE index \in set: TRUE
           [] Cardinality(set) = 0 -> 
             0
           [] OTHER -> {
                <<"_SearchKey error, more than one item", set, _slot_seq, _key>>
           }
     )

_TestSearchKey ==
    LET slot == <<[key |-> 3], [key |-> 4], [key |-> 4], [key |-> 6], [key |-> 8]>>
        slot2 == <<>>
        slot3 == <<[key |-> 10]>>
    IN  /\ 2 = _SearchKey(slot, 4)
        /\ 4 = _SearchKey(slot, 5)
        /\ 5 = _SearchKey(slot, 8)
        /\ 0 = _SearchKey(slot, 10)
        /\ 1 = _SearchKey(slot, 1)
        /\ 1 = _SearchKey(slot3, 10)
        /\ 1 = _SearchKey(slot3, 1) 

\* search the next in the same depth
_PageRightLink(_page, _key) ==
        CASE /\ _HighKey(_page) /= NULL 
             /\ (/\ _HighKey(_page) /= KEY_MAX 
                 /\ _key /= KEY_MAX
                 /\ _HighKey(_page) < _key) -> (
            _page.right_id
        )
        [] OTHER -> (
            NULL
        )
    
_NonLeafRightOrChild(_page, _key) ==
    CASE  _PageRightLink(_page, _key) /= NULL -> (
        _PageRightLink(_page, _key)
    )
    [] OTHER -> (
        LET index == _SearchKey(_page.slot, _key)
        IN IF index = 0 \/ index > Len(_page.slot) THEN
            NULL
        ELSE
            _page.slot[index].page_id
        )
 
        
_TestSearchPageNonLeaf ==
     /\ LET page == 
                [
                    level |-> 1, 
                    right_id |-> "right", 
                    slot |-> <<
                        [key |-> 2, page_id |-> "p1"],
                        [key |-> 3, page_id |-> "p3"],  
                        [key |-> 6, page_id |-> "p6"], 
                        [key |-> 8, page_id |-> "p8"]
                    >>
                ]
        IN /\ _NonLeafRightOrChild(page, 3) = "p3"
           /\ _NonLeafRightOrChild(page, 4) = "p6"
           /\ _NonLeafRightOrChild(page, 7) = "p8"
           /\ _NonLeafRightOrChild(page, 8) = "p8"
           /\ _NonLeafRightOrChild(page, 2) = "p1"
           /\ _NonLeafRightOrChild(page, 1) = "p1"
           /\ _NonLeafRightOrChild(page, 11) = "right"
     /\ LET page == 
                [
                    level |-> 1, 
                    right_id |-> "right", 
                    slot |-> <<[key |-> 3, page_id |-> "p1"],  [key |-> 6, page_id |-> "p2"], [key |-> 8, page_id |-> "p3"]>>
                ]  
         IN _NonLeafRightOrChild(page, 1) = "p1"
     /\ LET page == 
                [
                    level |-> 1, 
                    right_id |-> NULL, 
                    slot |-> <<[key |-> KEY_MAX, page_id |-> "p1"]>>
                ]  
         IN _NonLeafRightOrChild(page, 1) = "p1"

_PrevAccessed(_stack) ==
    IF Len(_stack) = 0 THEN
        NULL
    ELSE
        LET last_index == Len(_stack)
            stack_top == _stack[last_index]
        IN stack_top
        
_PrevAccessedPageId(_stack) ==
    _PrevAccessed(_stack).page_id

_PrevAccessedDepth(_stack) ==
    _PrevAccessed(_stack).depth

        
_LatchAdd(
    _latch, 
    _task_id,
    _latch_mode,
    _page_id) ==
        [_latch EXCEPT 
            ![_page_id] = _latch[_page_id] \cup {[mode |-> _latch_mode, task_id |-> _task_id]}        
        ]
             
_LatchRemove(
    _latch, 
    _task_id,
    _latch_mode,
    _page_id) ==
        [_latch EXCEPT 
            ![_page_id] = _latch[_page_id] \ {[mode |-> _latch_mode, task_id |-> _task_id]}
        ]

_LatchHold(
    _latch,
    _session,
    _latch_mode,
    _page_id) ==
     \E s \in _latch[_page_id]:
        /\ s.task_id = _session
        /\ s.mode = _latch_mode 


__CommandSearchPageLeafForOperation(_v_command, _v_operation, _s, _key, _page_id) ==
             CASE _v_operation[_s].operation = OP_SEARCH_KEY -> ( 
                [_v_command EXCEPT ![_s] = 
                                <<[command_type |-> C_SEARCH_KEY_LEAF, page_id |-> _page_id, key |-> _key]
                                        >> \o _PopFirst(_v_command[_s])]
             ) 
             [] _v_operation[_s].operation = OP_INSERT_KEY -> (
                [_v_command EXCEPT ![_s] = 
                                <<[command_type |-> C_INSERT_SLOT, page_id |-> _page_id, slot |-> [key |-> _key, value |-> _s]]
                                        >> \o _PopFirst(_v_command[_s])]
             )
             [] _v_operation[_s].operation = OP_UPDATE_KEY -> (
                [_v_command EXCEPT ![_s] = 
                                <<[command_type |-> C_UPDATE_SLOT, page_id |-> _page_id, slot |-> [key |-> _key, value |-> _s], 
                                    slot_new |-> [key |-> _key, value |-> _s]]
                                        >> \o _PopFirst(_v_command[_s])]
             )
             [] _v_operation[_s].operation = OP_DELETE_KEY -> (
                [_v_command EXCEPT ![_s] = 
                                <<[command_type |-> C_DELETE_SLOT, page_id |-> _page_id, slot |-> [key |-> _key, value |-> _s]]
                                        >> \o _PopFirst(_v_command[_s])]
             )
             [] OTHER -> (
                <<"error, unknown operation type", _v_operation[_s].operation>>
             )


_ActionLatchAcquire(_s, _page_id, _latch_mode) ==
    Action(ActionInternal, MessageLocal(_s, D_LATCH_ACQUIRE, [task_id |-> _s, page_id |->  _page_id, latch_mode |-> _latch_mode]))

_ActionLatchAcquired(_s, _page_id, _latch_mode) ==
    Action(ActionInternal, MessageLocal(_s, D_LATCH_ACQUIRED, [task_id |-> _s, page_id |->  _page_id, latch_mode |-> _latch_mode]))


_ActionLatchRelease(_s, _page_id, _latch_mode) ==
    Action(ActionInternal, MessageLocal(_s, D_LATCH_RELEASE, [task_id |-> _s, page_id |->  _page_id, latch_mode |-> _latch_mode]))

_ActionSearchResult(_s, _page_id, _index, _success) ==
    Action(ActionOutput, MessageLocal(_s, D_SEARCH_RESULT, [task_id |-> _s, page_id |->  _page_id, index |-> _index, success |-> _success]))

_ActionDeleteResult(_s, _page_id, _index, _success) ==
    Action(ActionOutput, MessageLocal(_s, D_DELETE_RESULT, [task_id |-> _s, page_id |->  _page_id, index |-> _index, success |-> _success]))

_ActionUpdateResult(_s, _page_id, _index, _success) ==
    Action(ActionOutput, MessageLocal(_s, D_UPDATE_RESULT, [task_id |-> _s, page_id |->  _page_id, index |-> _index, success |-> _success]))
    
_ActionInsertResult(_s, _page_id, _index, _success) ==
    Action(ActionOutput, MessageLocal(_s, D_INSERT_RESULT, [task_id |-> _s, page_id |->  _page_id, index |-> _index, success |-> _success]))

_ActionSearchPage(_s, _page_id) ==
    Action(ActionInternal, MessageLocal(_s, D_SEARCH_TOP_DOWN, [task_id |-> _s, page_id |->  _page_id]))



SearchPageTopDown(_s) == 
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_SEARCH_KEY
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           key == cmd.key
           page == v_page[page_id]
           mode == IF \/(/\ "is_root" \in DOMAIN cmd 
                         /\ cmd.is_root
                         /\ cmd.tree_level = 1
                         /\ v_operation[_s].operation \in {OP_INSERT_KEY, OP_DELETE_KEY, OP_UPDATE_KEY}
                        )
                   THEN WL ELSE RL        
       IN 
        /\ IF ~ _LatchHold( v_latch, _s, mode, page_id)  THEN (
                /\ LET a == _ActionLatchAcquire(_s,  page_id,  mode)
                   IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
                /\ v_command' = [v_command EXCEPT ![_s] = 
                        <<_LatchAcquireCommand(page_id, mode)>> \o
                        <<cmd>> \o
                        <<_LatchReleaseCommand(page_id, mode)>> \o
                         _PopFirst(v_command[_s])]
                /\ UNCHANGED <<v_stack, v_depth>>
           ) ELSE ( 
                IF page.level /= 0 THEN \* not a leaf node
                    LET next_page_id == _NonLeafRightOrChild(page, key)
                        is_sibling == next_page_id /= NULL /\ next_page_id = page.right_id
                        inc_depth == IF is_sibling THEN 0 ELSE 1
                        current_depth == v_depth[_s] + inc_depth 
                    IN 
                    IF next_page_id /= NULL THEN
                        (LET next_mode == 
                                IF /\ ~is_sibling 
                                   /\ page.level = 1 
                                   /\ v_operation[_s].operation \in {OP_INSERT_KEY, OP_DELETE_KEY, OP_UPDATE_KEY}
                                THEN WL ELSE RL
                        IN
                            /\ v_stack' = [v_stack EXCEPT ![_s] = v_stack[_s] \o << [depth |-> v_depth[_s], page_id |-> page_id]>>]
                            /\ v_command' = [v_command EXCEPT ![_s] = 
                                <<_LatchAcquireCommand(next_page_id, AI),
                                    _LatchAcquireCommand(next_page_id, next_mode),
                                    _LatchReleaseCommand(page_id, mode),
                                    _LatchReleaseCommand(next_page_id, AI),
                                    [command_type |-> C_SEARCH_KEY, key |-> key, page_id |-> next_page_id],
                                    _LatchReleaseCommand(next_page_id, next_mode)
                                >> \o _PopFirst(v_command[_s])]
                            /\ IF ~is_sibling THEN 
                                    v_depth' = [v_depth EXCEPT ![_s] = v_depth[_s] + 1]
                               ELSE
                                    /\ UNCHANGED <<v_depth>>
                            /\ LET a == _ActionSearchPage(_s, page_id)
                               IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
                        )
                    ELSE
                        /\ PrintT(<<page, key>>)
                        /\ "SearchPageTopDown, error"
                ELSE
                    /\ v_stack' = [v_stack EXCEPT ![_s] = v_stack[_s] \o << [depth |-> v_depth[_s], page_id |-> page_id]>>]
                    /\ v_depth' = [v_depth EXCEPT ![_s] = v_depth[_s] + 1]
                    /\ v_command' = __CommandSearchPageLeafForOperation(v_command, v_operation, _s, key, page_id)
                    /\ UNCHANGED << __action__>>
                    
           )
    /\ UNCHANGED <<v_latch, v_operation,  v_page, v_root_id, v_tree_level>>

_InsertIntoPage(
    _page,
    _index,
    _slot
) ==
    LET s0 == _page.slot
        s == IF _index >= 1 THEN
                    LET s1 == SubSeq(s0, 1, _index - 1)
                        s2 == SubSeq(s0, _index, Len(s0))
                    IN s1 \o <<_slot>> \o s2
             ELSE
                 <<_slot>> \o s0    
    IN [_page EXCEPT !.slot = s]

\* delte _page.slot[_index], _index = 0 for invalid index, _page would be return
_DeleteFromPage(
    _page,
    _index
) ==
    LET s0 == _page.slot
        s == IF _index >= 1 THEN
                    LET s1 == SubSeq(s0, 1, _index - 1)
                        s2 == SubSeq(s0, _index + 1, Len(s0))
                    IN s1 \o  s2
             ELSE
                s0   
    IN [_page EXCEPT !.slot = s]

_UpdatePage(
    _page,
    _index,
    _slot
) ==
    LET s0 == _page.slot
        s == IF _index >= 1 THEN
                    LET s1 == SubSeq(s0, 1, _index - 1)
                        s2 == SubSeq(s0, _index + 1, Len(s0))
                    IN s1 \o <<_slot>> \o s2
             ELSE
                 <<_slot>> \o s0    
    IN [_page EXCEPT !.slot = s]
        
_TestInsertIntoPage ==
   /\ LET _page == [slot |-> <<[key |-> 3, page_id |-> 3], [key |-> 6, page_id |-> 6], [key |-> 9, page_id |-> 9]>>]
      IN /\ _InsertIntoPage(_page, 1, [key |-> 1, page_id |-> 1]).slot = 
                <<[key |-> 1, page_id |-> 1], [key |-> 3, page_id |-> 3], [key |-> 6, page_id |-> 6], [key |-> 9, page_id |-> 9]>>
         /\ _InsertIntoPage(_page, 2, [key |-> 4, page_id |-> 4]).slot = 
                <<[key |-> 3, page_id |-> 3], [key |-> 4, page_id |-> 4], [key |-> 6, page_id |-> 6], [key |-> 9, page_id |-> 9]>>
   /\ LET _page == [slot |-> <<>>]
      IN _InsertIntoPage(_page, 0, [key |-> 1, page_id |-> 1]).slot = <<[key |-> 1, page_id |-> 1]>>

_TestDeleteFromPage ==
   /\ LET _page == [slot |-> <<[key |-> 3, page_id |-> 3], [key |-> 6, page_id |-> 6], [key |-> 9, page_id |-> 9]>>]
      IN /\ _DeleteFromPage(_page, 1).slot = 
                <<[key |-> 6, page_id |-> 6], [key |-> 9, page_id |-> 9]>>
         /\ _DeleteFromPage(_page, 2).slot = 
                <<[key |-> 3, page_id |-> 3], [key |-> 9, page_id |-> 9]>>

SearchKeyLeaf(_s) ==
    /\ Len(v_command[_s]) > 0 
    /\ _FirstCommandType(v_command[_s]) =  C_SEARCH_KEY_LEAF
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           key == cmd.key
           page == v_page[page_id]
           next_page_id == _PageRightLink(page, key)
       IN IF ~_LatchHold(v_latch, _s, RL, page_id) THEN
              /\ v_command' = [v_command EXCEPT ![_s] = 
                            <<_LatchAcquireCommand(page_id, RL)>> \o
                            <<cmd>> \o
                            <<_LatchReleaseCommand(page_id, RL)>> \o 
                            _PopFirst(v_command[_s])] 
              /\ UNCHANGED <<__action__>>
          ELSE 
            IF next_page_id = NULL THEN
                LET index == _SearchKey(page.slot, key)
                IN
                  /\ index /= 0
                  /\ LET a == _ActionSearchResult(_s,  page_id,  index, page.slot[index].key = key)
                     IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
                  /\ v_command' = [v_command EXCEPT ![_s] = <<_LatchReleaseCommand(page_id, RL)>> \o _PopFirst(v_command[_s])] 
            ELSE
                IF ~_LatchHold(v_latch, _s, AI, next_page_id) THEN
                        /\ v_command' = [v_command EXCEPT ![_s] = 
                            <<_LatchAcquireCommand(next_page_id, AI)>> \o
                            <<_LatchAcquireCommand(next_page_id, RL)>> \o
                            <<_LatchReleaseCommand(page_id, RL)>> \o
                            <<_LatchReleaseCommand(next_page_id, AI)>> \o
                            <<[cmd EXCEPT !.page_id = next_page_id]>> \o 
                            <<_LatchReleaseCommand(next_page_id, RL)>> \o
                             _PopFirst(v_command[_s])] 
                        /\ UNCHANGED <<__action__>>
                ELSE /\ v_command' = [v_command EXCEPT ![_s] = 
                              <<[cmd EXCEPT !.page_id = next_page_id]>> \o _PopFirst(v_command[_s])] 
                        /\ UNCHANGED <<__action__>>                  
    /\ UNCHANGED <<v_page, v_operation, v_root_id, v_stack, v_depth, v_latch, v_tree_level>>
      
DoWriteSlot(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) \in {C_DELETE_SLOT, C_INSERT_SLOT, C_UPDATE_SLOT}
    /\ LET cmd == _First(v_command[_s])
           cmd_type == cmd.command_type
           page_id == cmd.page_id
           slot == cmd.slot
           key == slot.key
           page == v_page[page_id]
           next_page_id == _PageRightLink(page, key)
       IN /\ IF ~_LatchHold(v_latch, _s, WL, page_id) THEN
                 LET release_read == IF _LatchHold(v_latch, _s, RL, page_id) THEN 
                                        <<_LatchReleaseCommand(page_id, RL)>> 
                                     ELSE <<>>
                 IN
                 /\ v_command' = [v_command EXCEPT ![_s] = 
                            <<_LatchAcquireCommand(page_id, WL)>> \o
                            release_read \o
                            <<cmd>> \o 
                            <<_LatchReleaseCommand(page_id, WL)>> \o
                            _PopFirst(v_command[_s])] 
                 /\ UNCHANGED <<__action__>>
             ELSE

               \*/\ v_stack' = [v_stack EXCEPT ![_s] = v_stack[_s] \o << [depth |-> v_depth[_s], page_id |-> page_id]>>]
                 IF next_page_id = NULL THEN \* exactly in this page
                    CASE cmd_type = C_DELETE_SLOT -> (
                        /\ v_command' = [v_command EXCEPT ![_s] = <<[cmd EXCEPT !.command_type = C_DELETE_SLOT_GUT] >> \o _PopFirst(v_command[_s])]
                        /\ UNCHANGED <<__action__>>
                    )
                    [] cmd_type = C_INSERT_SLOT -> (
                        /\ v_command' = [v_command EXCEPT ![_s] = <<[cmd EXCEPT !.command_type = C_INSERT_SLOT_GUT] >> \o _PopFirst(v_command[_s])]
                        /\ UNCHANGED <<__action__>>
                    )
                    [] cmd_type = C_UPDATE_SLOT -> (
                        /\ v_command' = [v_command EXCEPT ![_s] = <<[cmd EXCEPT !.command_type = C_UPDATE_SLOT_GUT] >> \o _PopFirst(v_command[_s])]
                        /\ UNCHANGED <<__action__>>
                    )
                  ELSE \* search next page
                    IF ~_LatchHold(v_latch, _s, AI, next_page_id) THEN
                        /\ v_command' = [v_command EXCEPT ![_s] = 
                            <<_LatchAcquireCommand(next_page_id, AI)>> \o
                            <<_LatchAcquireCommand(next_page_id, WL)>> \o
                            <<_LatchReleaseCommand(page_id, WL)>> \o
                            <<_LatchReleaseCommand(next_page_id, AI)>> \o
                            <<[cmd EXCEPT !.page_id = next_page_id]>> \o 
                            <<_LatchReleaseCommand(next_page_id, WL)>> \o
                             _PopFirst(v_command[_s])] 
                        /\ UNCHANGED <<__action__>>
                    ELSE 
                        /\ v_command' = [v_command EXCEPT ![_s] = 
                              <<[cmd EXCEPT !.page_id = next_page_id]>> \o _PopFirst(v_command[_s])] 
                        /\ UNCHANGED <<__action__>>

     /\ UNCHANGED <<v_latch, v_stack, v_page, v_operation, v_depth, v_root_id, v_tree_level>>


LatchAcquire(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_LATCH_ACQUIRE
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           latch_mode == cmd.latch_mode
       IN /\ _LatchCanAcquire(_s, v_latch[page_id], latch_mode)
          /\ v_latch' = _LatchAdd(v_latch, _s, latch_mode, page_id)
          /\ LET a == _ActionLatchAcquired(_s,  page_id,  latch_mode)
             IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
    /\ v_command' = [v_command EXCEPT ![_s] = _PopFirst(v_command[_s])]
    /\ UNCHANGED <<v_page, v_root_id, v_stack, v_depth, v_operation, v_tree_level>>
        
LatchRelease(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_LATCH_RELEASE
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           latch_mode == cmd.latch_mode
       IN /\ v_latch' = _LatchRemove(v_latch, _s, latch_mode, page_id)
          /\ LET a == _ActionLatchRelease(_s,  page_id,  latch_mode)
             IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
    /\ v_command' = [v_command EXCEPT ![_s] = _PopFirst(v_command[_s])]

    /\ UNCHANGED <<v_page, v_root_id, v_stack, v_depth, v_operation, v_tree_level>>
    
InsertSlotGut(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_INSERT_SLOT_GUT
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           slot == cmd.slot
           key == cmd.slot.key
           page == v_page[page_id]
           is_leaf == page.level = 0
           duplicate == v_operation[_s].duplicate /\ is_leaf
           index == _SearchKey(page.slot, key)
       IN /\ _LatchHold(v_latch, _s, WL, page_id)
          /\ index /= NULL
          /\ LET insert_failed == page.slot[index].key = key /\ ~duplicate
             IN /\ IF /\ Len(page.slot) = FAN_OUT_NUM 
                      /\ ~ insert_failed THEN
                        /\ v_command' = [v_command EXCEPT ![_s] = <<[cmd EXCEPT !.command_type = C_SPLIT_PAGE] >> \o _PopFirst(v_command[_s])]
                        /\ UNCHANGED <<v_page>>
                   ELSE  IF insert_failed THEN
                            /\ page.level > 0 => <<"Insert Slot Gut Error", page, _s>>
                            /\ v_command' = [v_command EXCEPT ![_s] = _PopFirst(v_command[_s])]
                            /\ UNCHANGED <<v_page>>
                         ELSE
                            LET page_new == _InsertIntoPage(page, index, slot)
                                parent_id == _ParentLevelPageId(v_stack[_s])
                            IN /\ v_page' = [v_page EXCEPT ![page_id] = page_new]
                               /\ parent_id = page_id => <<parent_id, v_stack[_s]>>
                               \*/\ PrintT(<<"after insert", _s, page_new, key, index>>)
                               /\ IF parent_id /= NULL /\ _HighKey(page_new) /= _HighKey(page) THEN
                                    /\ v_command' = [v_command EXCEPT ![_s] = 
                                        <<_LatchReleaseCommand(page_id, WL),
                                          [command_type |-> C_VISIT_PARENT, page_id |-> parent_id],
                                          [command_type |-> C_UPDATE_SLOT, page_id |-> parent_id, slot |-> [page_id |-> page_id, key |-> key],
                                                    slot_new |-> [page_id |-> page_id, key |-> _HighKey(page_new)]]
                                        >> \o _PopFirst(v_command[_s])]
                                  ELSE
                                    /\ v_command' = [v_command EXCEPT ![_s] = 
                                            <<_LatchReleaseCommand(page_id, WL)>> \o
                                            _PopFirst(v_command[_s])]
               /\ IF page.level = 0 THEN
                     LET a == _ActionInsertResult(_s,  page_id, index, ~insert_failed)
                     IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
                  ELSE 
                     UNCHANGED <<__action__>>
          /\ UNCHANGED <<v_latch, v_stack, v_operation, v_depth, v_root_id, v_tree_level>>

UpdateSlotGut(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_UPDATE_SLOT_GUT
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           slot == cmd.slot
           slot_new == cmd.slot_new
           key == cmd.slot.key
           page == v_page[page_id]
           index == _SearchKey(page.slot, key)
       IN /\ _LatchHold(v_latch, _s, WL, page_id)
          /\ index = 0 => <<"DeleteSlotGut error", index, page, key>>
          /\ index /= 0
          /\ IF page.slot[index].key = key THEN (
              /\ LET page_new == _UpdatePage(page, index, slot_new)
                 IN /\ v_page' = [v_page EXCEPT ![page_id] = page_new]
                    /\ v_command' = [v_command EXCEPT ![_s] = 
                                        <<_LatchReleaseCommand(page_id, WL)>> \o
                                         _PopFirst(v_command[_s])]
                    /\ IF page.level = 0 THEN
                            /\ v_command' = [v_command EXCEPT ![_s] = 
                                        <<_LatchReleaseCommand(page_id, WL)>> \o
                                         _PopFirst(v_command[_s])]
                            /\ LET a == _ActionUpdateResult(_s,  page_id, index, TRUE)
                                IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
                       ELSE
                            /\ UNCHANGED <<__action__>>
            )
            ELSE 
                /\ UNCHANGED <<v_page>>
                /\ IF page.level = 0 THEN 
                      /\ v_command' = [v_command EXCEPT ![_s] = 
                                        <<_LatchReleaseCommand(page_id, WL)>> \o
                                         _PopFirst(v_command[_s])]
                      /\ LET a == _ActionUpdateResult(_s,  page_id, index, FALSE)
                         IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
                   ELSE
                    <<"UpdateSlotGut error, no such slot", slot>>
     /\ UNCHANGED <<v_latch, v_stack, v_operation, v_depth, v_root_id, v_tree_level>>
               
DeleteSlotGut(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_DELETE_SLOT_GUT
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           slot == cmd.slot
           key == cmd.slot.key
           page == v_page[page_id]
           index == _SearchKey(page.slot, key)
       IN /\ ~_LatchHold(v_latch, _s, WL, page_id) => <<"Delete Slot Gut Error">>
          /\ _LatchHold(v_latch, _s, WL, page_id)
          /\ index = 0 => <<"DeleteSlotGut error", index, page, key>>
          /\ index /= 0
          /\ (IF page.slot[index].key = key THEN (
                  /\ LET page_new == _DeleteFromPage(page, index)
                     IN    IF Len(page_new.slot) < _HalfCeiling(FAN_OUT_NUM) THEN
                               /\ UNCHANGED <<v_page>>
                               /\ v_command' = [v_command EXCEPT ![_s] = <<[command_type |-> C_CONSOLIDATE_PAGE, page_id |-> page_id, index |-> index]>> \o _PopFirst(v_command[_s])]
                           ELSE
                               /\ v_page' = [v_page EXCEPT ![page_id] = page_new]
                               /\ IF index = Len(page.slot) THEN
                                    LET parent_id == _ParentLevelPageId(v_stack[_s])
                                    IN IF parent_id /= NULL THEN
                                            v_command' = [v_command EXCEPT ![_s] = 
                                                        <<_LatchReleaseCommand(page_id, WL),
                                                          [command_type |-> C_VISIT_PARENT, page_id |-> parent_id],
                                                          [command_type |-> C_UPDATE_SLOT, page_id |-> parent_id, 
                                                                slot |-> [page_id |-> page_id, key |-> key],
                                                                slot_new |-> [page_id |-> page_id, key |-> _HighKey(page_new)]]
                                                        >> \o _PopFirst(v_command[_s])]
                                       ELSE 
                                            v_command' = [v_command EXCEPT ![_s] = <<_LatchReleaseCommand(page_id, WL) >> \o _PopFirst(v_command[_s])]    
                                  ELSE
                                       v_command' = [v_command EXCEPT ![_s] = 
                                            <<_LatchReleaseCommand(page_id, WL)>> \o
                                             _PopFirst(v_command[_s])]
              )
              ELSE (
                    /\ v_command' = [v_command EXCEPT ![_s] = 
                                  <<_LatchReleaseCommand(page_id, WL)>> \o
                                      _PopFirst(v_command[_s])]
                    /\ UNCHANGED <<v_page>>
               )
             )
          /\ IF page.level = 0 THEN 
                     LET a == _ActionDeleteResult(_s,  page_id, index, page.slot[index].key /= key)
                     IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
                ELSE
                     /\ page.slot[index].key /= key => <<"DeleteSlotGut error, no such slot", slot, page, _s>>
                     /\ UNCHANGED <<__action__>>
     /\ UNCHANGED <<v_latch, v_stack, v_operation, v_depth, v_root_id, v_tree_level>>

_ConsolidateTwoPage(_left, _right, _to_delete_index) == 
    LET left_page1 == _DeleteFromPage(_left, _to_delete_index)
        half_size == _HalfCeiling(FAN_OUT_NUM)
        move_size == Min({half_size - Len(left_page1.slot), Len(_right.slot)})
        right_page == [_right EXCEPT !.slot = SubSeq(_right.slot, move_size + 1, Len(_right.slot))]
        left_page2 == [left_page1 EXCEPT !.slot = left_page1.slot \o IF Len(_right.slot) = 0 THEN <<>> ELSE SubSeq(_right.slot, 1, move_size)] 
    IN [left_page |-> left_page2, right_page |-> right_page]


_TestConsolidateTwoPage ==
    LET l == [slot |-> <<[key |-> 40, value |-> NULL]>>, page_id |-> "p2", level |-> 0, right_id |-> "p3"]
        r == [slot |-> <<[key |-> KEY_MAX, value |-> NULL]>>, page_id |-> "p3", level |-> 0, right_id |-> NULL]
        con_l == [slot |-> <<[key |-> KEY_MAX, value |-> NULL]>>, page_id |-> "p2", level |-> 0, right_id |-> "p3"]    
        con_r == [slot |-> <<>>, page_id |-> "p3", level |-> 0, right_id |-> NULL]
        con == _ConsolidateTwoPage(l, r, 1)
    IN /\ con.left_page = con_l  
       /\ con.right_page = con_r 


DeletePage(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_DELETE_PAGE
    /\ LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           index == cmd.index
           page == v_page[page_id]
       IN /\ page.right_id = NULL 
          /\ v_page' = [id \in (DOMAIN v_page) \ {page_id} |->  v_page[id]]
    /\ v_command' = [v_command EXCEPT ![_s] = _PopFirst(v_command[_s])] 
    /\ UNCHANGED <<__action__, v_latch, v_tree_level, v_root_id, v_stack, v_depth, v_operation>>
    
ConsolidatePage(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_CONSOLIDATE_PAGE
    /\(LET cmd == _First(v_command[_s])
           page_id == cmd.page_id
           index == cmd.index
           page == v_page[page_id]
       IN IF page.right_id = NULL THEN (
              LET page_new == _DeleteFromPage(page, index)
              IN  /\ v_page' = [
                                    i \in (DOMAIN v_page) |->  
                                        IF i = page_id THEN 
                                            page_new
                                        ELSE
                                            v_page[i]
                               ]      
                  /\  IF /\ Len(page_new.slot) = 1
                          /\ page_new.level + 1 = v_tree_level
                          /\ page_new.page_id = v_root_id 
                          
                      THEN
                          /\ v_root_id' = page_new.slot[1].page_id
                          /\ v_tree_level' = v_tree_level - 1    
                          /\ v_command' = [v_command EXCEPT ![_s] = 
                                <<_LatchAcquireCommand(page_id, ND)>> \o
                                <<[command_type |-> C_DELETE_PAGE, page_id |-> page_id]>> \o
                                <<_LatchReleaseCommand(page_id, ND)>> \o
                                _SeqRemoveMatch(_PopFirst(v_command[_s]),   
                                        LAMBDA c : c.page_id = page_id)] 
                      ELSE
                          /\ UNCHANGED <<v_root_id, v_tree_level>>
                          /\ v_command' = [v_command EXCEPT ![_s] = _PopFirst(v_command[_s])]
          ) ELSE (
              /\(CASE ~_LatchHold(v_latch, _s, WL, page_id) -> (
                    /\ v_command' = [v_command EXCEPT ![_s] = 
                        <<_LatchAcquireCommand(page_id, WL)>> \o 
                        <<cmd>> \o
                        <<_LatchReleaseCommand(page_id, WL)>> \o
                        _PopFirst(v_command[_s])] 
                    /\ UNCHANGED <<v_page>>
                 )
                 [] /\ _LatchHold(v_latch, _s, WL, page_id)
                    /\ ~_LatchHold(v_latch, _s, WL, page.right_id) -> (
                     /\ v_command' = [v_command EXCEPT ![_s] = 
                            <<_LatchAcquireCommand(page.right_id, WL)>> \o 
                            <<cmd>> \o
                            <<_LatchReleaseCommand(page.right_id, WL)>> \o
                             _PopFirst(v_command[_s])]
                     /\ UNCHANGED <<v_page>>
                 )
                 [] /\ _LatchHold(v_latch, _s, WL, page_id)
                    /\ _LatchHold(v_latch, _s, WL, page.right_id)
                    /\ ~ _LatchHold(v_latch, _s, PM, page_id) -> (
                       /\ v_command' = [v_command EXCEPT ![_s] = 
                            <<_LatchAcquireCommand(page_id, PM)>> \o
                            <<cmd>> \o
                            <<_LatchReleaseCommand(page_id, PM)>> \o
                            _PopFirst(v_command[_s])]
                       /\ UNCHANGED <<v_page>>
                 )
                 [] /\ _LatchHold(v_latch, _s, WL, page_id)
                    /\ _LatchHold(v_latch, _s, WL, page.right_id)
                    /\ _LatchHold(v_latch, _s, PM, page_id) -> (
                    LET page_id_right == page.right_id
                        page_right0 == v_page[page_id_right]
                        r == _ConsolidateTwoPage(page, page_right0, index)
                        page_left1 == r.left_page
                        page_right1 == r.right_page
                        parent_id == _ParentLevelPageId(v_stack[_s])
                    IN 
                       /\ IF Len(page_right1.slot) = 0 THEN ( \* need delete this page
                            LET page_left2 == [page_left1 EXCEPT !.right_id = page_right1.right_id]
                            IN /\ v_page' = [v_page EXCEPT 
                                    ![page_id] = page_left2, 
                                    ![page_id_right] = page_right1]
                               /\ v_command' = [v_command EXCEPT ![_s] = <<
                                        _LatchReleaseCommand(page_id, WL), 
                                        _LatchReleaseCommand(page.right_id, WL),
                                        [command_type |-> C_VISIT_PARENT, page_id |-> parent_id],
                                        [command_type |-> C_DELETE_SLOT, page_id |-> parent_id, slot |-> [key |-> _HighKey(page), page_id |-> page_id]],
                                        [command_type |-> C_UPDATE_SLOT, page_id |-> parent_id, key |-> _HighKey(page), 
                                              slot |-> [page_id |-> page_id_right, key |-> _HighKey(page_right0)],
                                              slot_new |-> [page_id |-> page_id, key |-> _HighKey(page_left1)]
                                        ],
                                        _LatchReleaseCommand(page_id, PM),
                                        _LatchReleaseCommand(page_id_right, PM)
                                     >> \o _PopFirst(v_command[_s])]
    
                         ) ELSE (    
                            LET consolidate_right_page ==
                                IF Len(page_right1.slot) < _HalfCeiling(FAN_OUT_NUM) THEN
                                    <<[command_type |-> C_CONSOLIDATE_PAGE, page_id |-> page_id_right, index |-> 0]>>
                                ELSE
                                    <<>>
                            IN  
                                /\ v_page' = [v_page EXCEPT 
                                    ![page_id] = page_left1, 
                                    ![page_id_right] = page_right1]
                                /\ v_command' = [v_command EXCEPT ![_s] = <<
                                    _LatchReleaseCommand(page_id, WL), 
                                    _LatchReleaseCommand(page.right_id, WL),
                                    [command_type |-> C_VISIT_PARENT, page_id |-> parent_id],
                                    [command_type |-> C_UPDATE_SLOT, page_id |-> parent_id, key |-> _HighKey(page), 
                                          slot |-> [page_id |-> page_id, key |-> _HighKey(page)],
                                          slot_new |-> [page_id |-> page_id, key |-> _HighKey(page_left1)]
                                    ],
                                    _LatchReleaseCommand(page_id, PM),
                                    _LatchReleaseCommand(page_id_right, PM)
                                 >> \o consolidate_right_page \o _PopFirst(v_command[_s])]
                         )
                 )
                 [] OTHER -> (
                    "ConsolidatePage error, not possible"
                 )
                )
               /\ UNCHANGED <<v_root_id, v_tree_level>>
             )
       ) 
       /\ UNCHANGED <<__action__, v_depth, v_latch, v_operation, v_stack>>
                                        
_GenNewPageId(_page_ids) == 
    CHOOSE id \in PAGE_ID: ~(id \in _page_ids)


_SplitSlot(_slot) ==
    [
        lower |-> SubSeq(_slot, 1, Len(_slot) - (Len(_slot) \div 2)),  
        upper |-> SubSeq(_slot, Len(_slot) - (Len(_slot) \div 2) + 1,  Len(_slot))
    ]

_TestSplitSlot ==
    LET slot == <<[key |-> 1], [key |-> 2], [key |-> 3]>>
    IN _SplitSlot(slot) = [lower |-> <<[key |-> 1], [key |-> 2]>>, upper |-> <<[key |-> 3]>>]

    
SplitPage(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_SPLIT_PAGE
    /\ LET command == _First(v_command[_s])
           left_page_id == command.page_id
           page == v_page[left_page_id]
           right_page_id == _GenNewPageId(DOMAIN v_page)
           inserted_slot == command.slot
           slot_split == _SplitSlot(page.slot)
           slot_lower == slot_split.lower
           slot_upper == slot_split.upper
           right_page == [ 
                    page_id |-> right_page_id,                   
                    level |-> page.level,
                    right_id |-> page.right_id, 
                    slot |-> slot_upper
                    ]
           left_page == [
                    page_id |-> page.page_id,
                    level |-> page.level,
                    right_id |-> right_page_id,
                    slot |-> slot_lower
                    ]
       IN /\ Len(page.slot) = FAN_OUT_NUM
          /\ CASE ~_LatchHold(v_latch, _s, WL, left_page_id) -> (
                 /\ v_command' = [v_command EXCEPT ![_s] = 
                        <<_LatchAcquireCommand(left_page_id, WL)>> \o 
                        <<command>> \o
                        <<_LatchReleaseCommand(left_page_id, WL)>> \o
                        _PopFirst(v_command[_s])] 
                 /\ UNCHANGED <<v_page, v_root_id, v_tree_level, __action__>>
             )
             [] /\ _LatchHold(v_latch, _s, WL, left_page_id)
                /\ ~_LatchHold(v_latch, _s, WL, right_page_id) -> (
                 /\ v_command' = [v_command EXCEPT ![_s] = <<
                         _LatchAcquireCommand(right_page_id, WL)>> \o
                         <<command>> \o
                         <<_LatchReleaseCommand(right_page_id, WL)>> \o
                         _PopFirst(v_command[_s])]
                 /\ UNCHANGED <<v_page, v_root_id, v_tree_level, __action__>>
             )
             [] /\ _LatchHold(v_latch, _s, WL, left_page_id)
                /\ _LatchHold(v_latch, _s, WL, right_page_id)
                /\ ~ _LatchHold(v_latch, _s, PM, left_page_id) -> (
                /\ v_command' = [v_command EXCEPT ![_s] = <<
                           _LatchAcquireCommand(left_page_id, PM)>> \o 
                           <<command>> \o
                           <<_LatchReleaseCommand(left_page_id, PM)>> \o
                           _PopFirst(v_command[_s])]
                /\ UNCHANGED <<v_page, v_root_id, v_tree_level , __action__>>
             )
             [] /\ _LatchHold(v_latch, _s, WL, left_page_id)
                /\ _LatchHold(v_latch, _s, WL, right_page_id)
                /\ _LatchHold(v_latch, _s, PM, left_page_id)
                /\ ~ _LatchHold(v_latch, _s, PM, right_page_id) -> (
                /\ v_command' = [v_command EXCEPT ![_s] = <<
                            _LatchAcquireCommand(right_page_id, PM)>> \o 
                            <<command>> \o
                            <<_LatchReleaseCommand(right_page_id, PM)>> \o
                            _PopFirst(v_command[_s])]
                /\ UNCHANGED <<v_page, v_root_id, v_tree_level, __action__>>
             )
             [] /\ _LatchHold(v_latch, _s, WL, left_page_id)
                /\ _LatchHold(v_latch, _s, WL, right_page_id)
                /\ _LatchHold(v_latch, _s, PM, left_page_id)
                /\ _LatchHold(v_latch, _s, PM, right_page_id) ->  (
                      LET update_root == v_root_id = left_page_id
                          parent_id == 
                                   IF update_root THEN 
                                        _GenNewPageId(DOMAIN v_page \cup {right_page_id}) 
                                   ELSE 
                                        _ParentLevelPageId(v_stack[_s])
                          root_id_set == IF update_root THEN {parent_id} ELSE {}
                          updated_page == 
                                   IF _KeyLess(inserted_slot.key, _HighKey(left_page)) THEN
                                      LET index == _SearchKey(left_page.slot, inserted_slot.key)
                                          _left_page == _InsertIntoPage(left_page, index, inserted_slot)
                                      IN [left_page |-> _left_page, right_page |-> right_page]
                                   ELSE 
                                      LET index == _SearchKey(right_page.slot, inserted_slot.key)
                                         _right_page == _InsertIntoPage(right_page, index, inserted_slot)
                                      IN [left_page |-> left_page, right_page |-> _right_page]
                      IN
                      /\ v_page' = [
                                        id \in (DOMAIN v_page) \cup {right_page_id} \cup root_id_set |->
                                            CASE right_page_id = id -> (
                                                updated_page.right_page
                                            )
                                            [] left_page_id = id -> (
                                                updated_page.left_page
                                            )
                                            [] update_root /\ parent_id = id -> ( \*split root
                                                [
                                                    level |-> left_page.level + 1, 
                                                    right_id |-> NULL, 
                                                    slot |-> <<[key |-> KEY_MAX, page_id |-> right_page_id]>>
                                                ]
                                            )
                                            [] OTHER -> (
                                                 v_page[id]
                                            )
                                   ]
                      /\ v_command' = [v_command EXCEPT ![_s] = 
                                    <<  
                                        _LatchReleaseCommand(right_page_id, WL),
                                        _LatchReleaseCommand(left_page_id, WL),
                                        [command_type |-> C_VISIT_PARENT, page_id |-> parent_id],
                                        [command_type |-> C_INSERT_SLOT,page_id |-> parent_id, 
                                            slot |-> [page_id |-> left_page_id, key |-> _HighKey(updated_page.left_page)]],
                                        [command_type |-> C_UPDATE_SLOT, page_id |-> parent_id, key |-> _HighKey(page), 
                                            slot |-> [page_id |-> left_page_id, key |-> _HighKey(page)],
                                            slot_new |-> [page_id |-> right_page_id, key |-> _HighKey(updated_page.right_page)]
                                        ],
                                        _LatchReleaseCommand(left_page_id, PM),
                                        _LatchReleaseCommand(right_page_id, PM)
                                    >> \o _PopFirst(v_command[_s])]
                        /\ (IF update_root THEN
                                /\ v_root_id' = parent_id
                                /\ v_tree_level' = v_tree_level + 1
                             ELSE 
                                UNCHANGED <<v_root_id, v_tree_level>>
                           )
                        /\ LET a == Action(ActionInternal, MessageLocal(_s,  D_SPLIT_PAGE, [page_id |-> left_page_id]))
                             IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)

               )
             [] OTHER -> (
                "SplitPage error, not possible"
             )
        /\ UNCHANGED <<v_latch, v_operation, v_depth, v_stack>>
              
_RangePredicateFilter(
    _value,
    _range_min, 
    _range_min_open,
    _range_max, 
    _range_max_open
) ==
    /\ (\/_range_min = NULL
        \/ (/\ _range_min /= NULL
            /\ IF _range_min_open THEN _value > _range_min ELSE _value >= _range_min
           )
        )
    /\ (\/ _range_max = NULL
        \/ (/\ _range_max /= NULL
            /\ IF _range_max_open THEN _value < _range_max ELSE _value >= _range_max
           )
       )
       
ScanLeaf(
    _s, 
    _id, 
    _range_min, 
    _range_min_open,
    _range_max, 
    _range_max_open,
    _reverse
) ==

    /\ v_page[_id].level = 0 
    /\ LET page == v_page[_id]
           set == 
                    {
                        i \in 1..Len(page.slot): 
                            _RangePredicateFilter(page.slot[i].key,     
                                        _range_min, 
                                        _range_min_open,
                                        _range_max, 
                                        _range_max_open) 
                    }
           found == 
                    {
                        page.slot[i].key: i \in set
                    }
       IN  IF ~ _reverse THEN
              IF set /= {} /\ Max(set) = Len(page.slot) /\ page.right_id /= NULL THEN
                    v_command' = [v_command EXCEPT ![_s].id = page.right_id]              
              ELSE
                    v_command' = [v_command EXCEPT ![_s] = [state |-> S_DONE]]
                
           ELSE
              IF set /= {} /\ Min(set) = Len(page.slot) /\ page.left_id /= NULL THEN
                    v_command' = [v_command EXCEPT ![_s].id = page.left_id]              
              ELSE
                    v_command' = [v_command EXCEPT ![_s] = [state |-> S_DONE]]

VisitParentPage(_s) ==
    /\ Len(v_command[_s]) > 0
    /\ _FirstCommandType(v_command[_s]) = C_VISIT_PARENT
    /\ v_command' = [v_command EXCEPT ![_s] =  _PopFirst(v_command[_s])]
    /\ v_stack' = [v_stack EXCEPT ![_s] = _PopLastLevel(v_stack[_s])]
    /\ IF v_depth[_s] > 0 THEN 
            v_depth' = [v_depth EXCEPT ![_s] = v_depth[_s] - 1]
       ELSE
            UNCHANGED <<v_depth>>
    /\ UNCHANGED <<__action__, v_operation, v_page, v_latch, v_root_id, v_tree_level>>
            
Search(_s, _k) ==
    /\ v_operation[_s].operation = NULL
    /\ v_command' = [v_command EXCEPT ![_s] = 
            <<[command_type |-> C_SEARCH_KEY, key |-> _k, page_id |-> v_root_id, 
            is_root |-> TRUE, tree_level |-> v_tree_level]>>]
    /\ v_depth' = [v_depth EXCEPT ![_s] = 0]
    /\ v_operation' = [v_operation EXCEPT ![_s] = [operation |-> OP_SEARCH_KEY, key |-> _k]]
    /\ LET a ==  Action(ActionInput, MessageLocal(_s, OP_SEARCH_KEY, [key |-> _k]))
       IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
    /\ UNCHANGED <<v_page, v_stack, v_latch, v_root_id, v_tree_level>>

Insert(_s, _k, _dup) ==
    /\ v_operation[_s].operation = NULL
    /\ v_command' = [v_command EXCEPT ![_s] = <<[
            command_type |-> C_SEARCH_KEY, key |-> _k, page_id |-> v_root_id,
            is_root |-> TRUE, tree_level |-> v_tree_level
                    ]>>]
    /\ v_depth' = [v_depth EXCEPT ![_s] = 0]
    /\ v_operation' = [v_operation EXCEPT ![_s] = [operation |-> OP_INSERT_KEY, key |-> _k, duplicate |-> _dup]]
    /\ LET a == Action(ActionInput, MessageLocal(_s, OP_INSERT_KEY, [key |-> _k]))
       IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
    /\ UNCHANGED <<v_page, v_stack, v_latch, v_root_id, v_tree_level>>

Update(_s, _k) ==
    /\ v_operation[_s].operation = NULL
    /\ v_command' = [v_command EXCEPT ![_s] = <<[command_type |-> C_SEARCH_KEY, key |-> _k, page_id |-> v_root_id,
                    is_root |-> TRUE, tree_level |-> v_tree_level
                ]>>]
    /\ v_depth' = [v_depth EXCEPT ![_s] = 0]
    /\ v_operation' = [v_operation EXCEPT ![_s] = [operation |-> OP_UPDATE_KEY, key |-> _k]]
    /\ LET a == Action(ActionInput, MessageLocal(_s, OP_UPDATE_KEY, [key |-> _k])) 
       IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
    /\ UNCHANGED <<v_page, v_stack, v_latch, v_root_id, v_tree_level>>

Delete(_s, _k) ==
    /\ v_operation[_s].operation = NULL
    /\ v_command' = [v_command EXCEPT ![_s] = <<[command_type |-> C_SEARCH_KEY, key |-> _k, page_id |-> v_root_id,
                        is_root |-> TRUE, tree_level |-> v_tree_level
                        ]>>]
    /\ v_depth' = [v_depth EXCEPT ![_s] = 0]
    /\ v_operation' = [v_operation EXCEPT ![_s] = [operation |-> OP_DELETE_KEY, key |-> _k]]
    /\ LET a ==  Action(ActionInput, MessageLocal(_s, OP_DELETE_KEY, [key |-> _k]))
       IN SetAction(__action__, _ActionSetup, a, ENABLE_ACTION)
    /\ UNCHANGED <<v_page, v_stack, v_latch, v_root_id, v_tree_level>>


RECURSIVE _DedupOp(_, _)


_DedupOp( _in, _out) ==
    IF Cardinality(_in) = 0 THEN
        _out
    ELSE     
        LET i == CHOOSE i \in _in: TRUE
        IN _DedupOp(_in \ {i}, {ToSet(i)} \cup _out)
                
Next == 
   LET s == [key : KEY_OPER, type : {"Search", "Insert", "Update", "Delete"}]
   IN \E op \in s:
        \E _s \in SESSION:
            LET _k == op.key
                _t == op.type
            IN
                \/ (_t = "Search" /\ Search(_s, _k))
                \/ (_t = "Insert" /\ Insert(_s, _k, FALSE))
                \/ (_t = "Update" /\ Update(_s, _k))
                \/ (_t = "Delete" /\ Delete(_s, _k))
                \/ SearchPageTopDown(_s)
                \/ LatchAcquire(_s)
                \/ LatchRelease(_s)
                \/ SearchKeyLeaf(_s)
                \/ DoWriteSlot(_s)
                \/ DeleteSlotGut(_s)
                \/ InsertSlotGut(_s)
                \/ UpdateSlotGut(_s)
                \/ SplitPage(_s)
                \/ ConsolidatePage(_s)
                \/ VisitParentPage(_s)
                \/ DeletePage(_s)

FinalAllLatchReleased ==
    ~(ENABLED Next)  => 
    (\A l \in DOMAIN v_latch:
            v_latch[l] = {}
    ) 

EventuallyAllLatchReleased ==    
    <>[] (\A l \in DOMAIN v_latch:
            v_latch[l] = {}
         ) 
     
\* The specification must start with the initial state and transition according to Next.
Spec == Init /\ [][Next]_variables



=============================================================================
