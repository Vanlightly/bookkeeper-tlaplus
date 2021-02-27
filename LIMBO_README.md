# Use of ledger limbo status to protect protocol from arbitrary failure

Note this work is describing and modelling work by Ivan Kelly (@ivankelly).

When a bookie runs with the WAL, any crash could mean that acknowledged entries are lost as they may not have been flushed to disk at the time of the crash. Likewise, when a bookie is restarted with the same identity but with all data wiped (and no boot-up sequence check prevents start-up), acknowledged entries are lost.

This introduced the risk of data loss during ledger recovery even though the entry still exists on other bookies and the under-replicated ledger could be repaired by auto recovery.

## Arbitrary reads

The current protocol is not built to be correct in the face of arbitrary read responses (non-malign byzantine failures). 

Bookie client actions are only safe when read responses are correct. Introduction of arbitrary read responses makes bookie client
decisions unsafe. The following is an example (paste into https://sequencediagram.org/):

```
title Arbitrary failure (E,WQ,AQ=2)

participant w2
participant b1
participant b2
participant zk

note over w2,zk: Original writer, w1, is dead. 100 entries in b1,b2 ensemble\nb1 lac=90, b2 lac=90. Bookies running without WAL.
b1--xb1: b1 crashes, loses all entries (0-100)
w2->zk: Place in-recovery
w2->b1: LAC Read
w2->b2: LAC Read
b1->w2: -1
note over w2,zk: w2 has enough fenced LAC responses to continue. Starts read phase at e0.
w2->b1:Read e0
w2->b2:Read e0
b1->w2:NoSuchEntry e0 (arbitrary response)
w2->zk:Close ledger as empty
note over w2,zk: All entries lost.\nThe response is arbitrary because it is like saying "I don't have it and that is ok",\nwhen the real answer is "Hey I don't have it but I should! BIG PROBLEM!"
```

Either we make the protocol handle arbitrary LAC and recovery reads, or we avoid arbitrary responses. This is where the ledger limbo status comes in:

```
title Limbo status avoids arbitrary failure (E,WQ,AQ=2)

participant w2
participant b1
participant b2
participant zk

note over w2,zk: Original writer, w1, is dead. 100 entries in b1,b2 ensemble\nb1 lac=90, b2 lac=90Bookies running without WAL.
b1--xb1: b1 crashes, loses all entries (0-100)\nOpen ledger now in limbo
w2->zk: Place in-recovery
w2->b1: LAC Read
w2->b2: LAC Read
b1->w2: Unknown
b2->w2: e90
note over w2,zk: w2 forced to wait for b2 as b1 responded with Unknown
w2->b1:Recovery read e0
w2->b2:Recovery read e0
b1->w2:Unknown e0
b2->w2:e0
w2->b1:add e0
note over w2,zk: Recovery reads and writes continue until reaching e100.\nLedger fully repaired.\nThis sequence does not include the clearing of the limbo status\n(which does happen as this limbo status is temporary).
```

Bookie clients only make decisions that can affect data loss, such as closing a ledger based on explicit positive/negative responses and excludes other responses (time outs, Unknown etc).

## Setting and clearing the limbo status on a ledger

The limbo status was originally intended for making bookies resilient to crashes when running without the WAL. There would likely be acknowledged entries that had not yet been flushed to disk. When a bookie starts-up without the WAL enabled, it sets the limbo status on all open ledgers. It then starts a repair mechanism:

1. Recovers all open ledgers. This is able to repair entries of the current ensemble only.
2. Repair process where it identifies all entries that it does not have but that ZK says it should have, sourcing them from peer bookies. This is similar to the existing auto-recovery but more efficient. Once the bookie has repaired the ledger (if required), it clears the limbo status of that ledger.

The ledger is available for reads during this repair, but responds with an Unknown response code to reads when it doesn't have the requested entry.

## Reproducing

See the README.md but use the BookKeeperWithLimbo.tla (and cfg). This is preliminary work, it only demonstrates that the limbo status avoids data loss during ledger recovery. The clearing of the status is not modelled.

Set the UseLimboStatus constant to FALSE to see the data loss scenario when the limbo status is not used.