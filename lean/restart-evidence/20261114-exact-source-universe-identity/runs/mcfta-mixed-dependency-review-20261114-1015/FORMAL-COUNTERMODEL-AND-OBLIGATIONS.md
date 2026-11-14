# Two-slot model for the weaker cache and selection facts

Status: source-only model. No compiler or evaluator checked this model. It is not a supported reachable runtime example and establishes no Haskell defect.

Use the actual Symbol literals `F` and `var1`. Let h be the encoded handle of the actual computed closed type universe whose constructor catalog includes unary F. The universe admits the finite leaf var1. No new graph or worker is needed. The separate core below is an arbitrary formal state over that native heap; this packet does not claim that source initialization reaches it.

```text
sc.trie = EqualityTrie.Trie.branch [(0, .terminal)]
sc.var = 1
bucket = [sc]
fragment = Fragment.node F [.hole 0]

before.counter = 2
before.representatives = UnionFind.withInitialValues [0, 1]
before.values = [ .unenumerated (some h) bucket, .enumerated fragment ]
before.obligations = []
before.recursionAncestry slot = if slot=0 then [recursionKey h bucket] else []
before.expansionAncestry = []

cached.core = before
cached.expandable slot = if slot=0 then true else false
cached.waiting slot = if slot=1 then some 1 else none
roots slot = slot
level slot = if slot=0 then 1 else 0
frontier = 1
preference _ = none

after = { before with values := before.values.set 0 (.unenumerated (some h) []) }
```

The intended checks are precise:

1. Storage is aligned and bounded; both live stored slots are roots. The forest and roots map agree. The only canonical suspended count is1 at slot1. The actual native candidate for slot0 is true because its bucket is nonempty; slot1 and absent slots are false. These are the same cache/selection invariants. Pure selection offers slot0 because its waiting count is absent.
2. This core also permits the existing Stratified invariant. Set frontier=1, level0=1 and level1=0. Slot1's fragment points to the strictly later-level slot0. Thus dependency levels alone do not reject the model.
3. If lookupNode heap h is the resident recursive universe, the actual checkRepeated at fuel1 on slot0/h/bucket reads its root0, sees its literal preloaded recursionKey and performs exactly the written clear. Native heap and other slots stay unchanged. This is an actual-operation equation to check; no alternate evaluator is proposed.
4. Before satisfaction under ANY language forces assignment0.atPath[0]=some assignment1 from the suspended trie, and assignment1=F(assignment0) from the enumerated slot. The finite Term.height inequality is impossible.
5. After clearing, ONE joint finite assignment exists: assignment0=var1; assignment1=F(var1); all other slots=var1. It satisfies the forest equalities, the remaining native universe restriction, the enumerated equation and the empty residual list. For the genuine native-language instance, derive var1 membership from the computed universe's existing finite membership law; do not replace it with an assumed whole-state witness. This packet does not discharge that native-language transport.
6. PendingReferences fails at slot1 immediately: slot1 is enumerated, while slot0's sc.var=1 belongs to its class. This is the exact barrier supplied by the real history invariant. The source-only model therefore cannot show a reachable violation when that invariant is derived.

The explicit proof obligations above remain uncompiled. The new path candidate proves the positive separation statement from the existing history invariant rather than asking callers to accept a new completion gate. The model explains why Safe, canonical cache correctness, selection and even Stratified alone are insufficient. It does not refute the stronger reachable-state invariant.
