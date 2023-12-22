## Two-Phase Commit Protocol

### How to start

#### 1. Model checker setting

*Model overview -> What is the model?*

**NODE_ID**: node id set 

```
    {A_n1, A_n2, A_n3}
```

**XID**: transaction id set
```
    {A_x1}
```

**DB_ACTION_PATH** DB path to write action output


**CHECK_SAFETY** Check safety property

**ENABLE_ACTION** Enable output action trace, used to generate trace

**LIMIT_TIMEOUT** Max limitation of a TM or RM timeout

**LIMIT_RESTART** Max limitation of restarting


*Model overview -> What is the behavior? -> Temporal formula*

```Spec```


