## Raft Consensus Protocol

### How to start

#### 1. Model checker setting

*Model overview -> what is the model?*

**NODE_ID**: node id set 

```
    {A_n1, A_n2, A_n3}
```


**VALUE**: value set

```
    {A_v1, A_v2, A_v3}
```

**MAX_TERM**: maximum term value

```
    3
```

**RECONFIG_VALUE** ejnable reconfig value

**CHECK_SAFETY** check safety property

**ENABLE_ACTION** eanble output action trace, used to generate trace

**ENABLE_STATE_DB** enable save states to DB, used to generate initialized state of concreate specification


*Model overview -> What is the behaviour? -> Temporal formula*

```Spec```


*Additional TLC Option -> Parameters -> TLC command line parameter* ->

```-dump dot abstract_raft.dot```

#### 2.Click *Runs TLC on the model* Button

After finishing running the model checker, in */[xxxx]/abstract_raft/abstract_raft.toolbox/Model_[xxxx]* folder