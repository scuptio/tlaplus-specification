## Raft Consensus Protocol

### How to start

#### 1. Model checker setting

*Model overview -> What is the model?*

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

**RECONFIG_VALUE** Enable config value

**DB_STATE_PATH** DB path to read the initial state

**DB_ACTION_PATH** DB path to write action output

**APPEND_ENTRIES_MAX** Max log entries size append in one invocation

**VOTE** Max limitation of voting

**REPLICATE** Max limitation of replicating

**RESTART** Max limitation of restarting

**CLIENT_REQUEST** Max limitation of the client sending a request

**CHECK_SAFETY** Check safety property

**ENABLE_ACTION** Enable output action trace, used to generate trace



*Model overview -> What is the behavior? -> Temporal formula*

```Spec```


