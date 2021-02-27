# BookKeeper Replication Protocol TLA+ Specification

This spec models the life of a single ledger with a writer, multiple bookies
and a second writer that can perform a recovery + close.

Notes:

- TLA+ sequences are base 1 not 0. So in order to work more easily in TLA+:
    - entry ids start at 1 not 0.
    - LAC starts at 0 not -1.
- Not modelled:
    - Readers
    - Auto-recovery (a higher level spec would be required to specifically model that)
- Deviations:
    - The recovery reads and writes in the implementation are concurrent, for performance. This specification however splits them up into separate phases. The reason for this is to reduce the state space. Whether they are concurrent or in two phases does not affect correctness.


Terminology:

- The word "committed" is used to refer to an entry that the writer has acknowledged back to its own client.

## Opening the specification with the ToolBox

An existing model called Safety is included which has parameters already configured.

## Defects Found or Confirmed in December 2020 BookKeeper version 4.11

### Defect 1: Existing Fencing Not Enough to Prevent Data Loss
Discovered by this TLA+ specification. The defect can be found with the following commands:

```bash
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
wget https://github.com/tlaplus/CommunityModules/releases/download/202102040137/CommunityModules.jar
java -cp tla2tools.jar:CommunityModules.jar tlc2.TLC BookKeeperProtocol.tla -tool -modelcheck -deadlock -config BookKeeperProtocol.cfg -workers auto
```

In detail, the BookKeeper protocol defect found with this spec is that fencing of LAC reads is not enough to prevent committing an add:

The below example involves the loss of a fencing request. However, the same is achievable if one fencing LAC req is delivered after a Recovery Read Req, for example due to some network delay and a connection failure between the requests.

Paste into https://sequencediagram.org/ or use link https://sequencediagram.org/index.html#initialData=A4QwTgLglgxloDsIAIDuBGAUKSt4iTQCZtxo5EUAjLHc-QqkuvS5KgZlNwoJQC8A1pgwBaUQA8aALmQBTAAwiiogHxDZAW3CDkIAM7IoCZGDkwA9gDc5YAJ7K1M5ADM5CGHMw01qIrIAbEBhkAF5kUSwxVSZZRW8VVQw4hTQwKAgId0cY-1d3TwTfPKCQ8MjHSU5ZNw8vBAss5GtbNHQAGg18uuR9AFcYT31DCxN0ZAaAEzlkYFbg3QBHPoswPs0AHQRSo0NIrYAxArlJ2QBvGnamAF925ABRJHS5fVkAHjeaZGlVZDPb9hEb6-M6KAGcYF-a6qVQ5ZxmECTeRKPxOPIIpHxVExDiyDHI7zoYqyAByFgAygMABaPCD2bwcYnIMmUmA0p4ObFdGABCz6GYBE4Ac3mhjkmmAEE5RJxslQ6Sa8U4vnQKTSGSyCBEMuSehgggaqEFkxFyK2yAgFmQMBAAUFYEwDSaLTAbU6glkAEF9YbjSKkfKMjNFLt5C43DBoDYAnZkLz9CgDEYUKgk3S+h4QFkkVRY5o5BBEVmQEA

```
participant w1
participant w2
participant b1
participant b2
participant b3
participant zk
w1--xb1: e0
w2->zk: mark as in recovery
w2->b1: fence
b1->w2: lac = -1
w1->b2: e0
b2->w1: e0 written
w2->b2: fence
b2->w2: lac = -1
w2--xb3: fence
note over w1,zk: fence success on 1 node per ack quorum\nlac is -1\nFenced: {b1,b2}, Entries: <<b1 :> {}, b2 :> {e0}, b3 :> {}>>
w2->b1: read e0
w2->b2: read e0
w2->b3: read e0
b1->w2: NoSuchEntry
b3->w2: NoSuchEntry
w2->zk: close ledger as empty
w1->b3: write e0
b3->w1: e0 written
w1->w1: acknowledge e0\n to caller
note over w1,zk: Acknowledged write e0 is effectively lost as it was truncated by metadata
```

Data loss!

The issue is that it is possible to reach AckQuorum even after enough bookies are fenced.

It derives from the combination of a couple of things (using Qw 3, Qa 2 as an example):

1. Ledger recovery (by w2) can begin when an entry is already at Qa-1 and the original writer (w1) is still alive. In this case, w1 only needs one more positive response from a bookie for the entry to be committed.

2. Recovery consists of 3 phases:
    1. Fencing (LAC reads)
    2. Recovery read and write back
    3. Ledger close

   Phase 2 begins once one bookie in every ack quorum is fenced. This allows for Phase 2 and 3 to execute when a single bookie has not responded to the LAC read. If say, one LAC read request was lost, this leaves a single bookie unfenced which means that the ensemble as a whole still permits a single write to get through. This single write is enough for w1 to reach Qa after Phase 3 has completed (aka the ledger being closed).

3. Recovery reads succeed as long as (Qw-Qa)+1 bookies do not explicitly respond with a NoSuchEntry/Ledger code. Because it is possible for a single bookie to not be fenced during Phase 2, recovery reads are not monotonic, in the sense that once an answer is received, later information may invalidate that answer. Basically a NoSuchEntry response might later turn into a successful response (if w2 were to ask again) because w1 was able to write to an unfenced bookie.

The fix is to make recovery reads monotonic (in the sense that once a read is negative, it is guaranteed to remain negative). We achieve this by adding fencing to recovery reads also. Once a bookie has responded with a NoSuchEntry code to a recovery read, it will not accept a write for that entry because it is fenced.

For that reason we have a new constant RecoveryReadsFence to test that. The invariant violation no longer occurs when set to TRUE.

### Defect 2: Invalid fragments
Discovered by Jack Vanlightly, confirmed by this spec.

When a second writer performs recovery, it can end up trying to create an invalid fragment which will cause recovery to fail.

```
participant w1
participant w2
participant b1
participant b2
participant b3
participant b4
participant b5
participant b6
participant zk

note over w1,zk:Ensembles: 0:{b1,b2}, 1000:{b2,b3}
w1->b1: e1999
w1->b2: e1999
b1->w1: ack e1999
b2->w1: ack e1999
w1--xb1: e2000
w1--xb2: e2000
w1->zk:Add ensemble 2000:{b4,b5}
w2->zk:Start recovery
w2->b4: Read LAC
w2->b5: Read LAC
b4->w2: LAC -1
b5->w2: LAC -1
w2->b1: Read e0
w2->b2: Read e0
b1->w2:e0
b2->w2:e0
w2->b4:e0
w2--xb5:e0
b4->w2:ack e0
w2->zk:Add ensemble 0:{b4,b6}
note over w2,zk:INVALID FRAGMENT
```

The fix is to not use -1 (or 0 in the TLA+ spec) as the minimum but to take the `first entry id` of the current fragment - 1 as the minimum. This ensures we only try to recover the current fragment. Previously fragments, if any, have already been committed and so recovery reads/writes of those fragments is unnecessary. If a failure occurs during recovery of the current fragment, then updating that fragment is a legal operation.

This specification uses this new minimum value and so the spec will not currently reach this illegal state.