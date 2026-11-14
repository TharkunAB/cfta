# Explicit witnesses in the incoming bucket receipt

Status: UNCOMPILED CANDIDATE. The root owns validation and publication.

Source SHA256:
`c1cd495d8a10fd124fdb986da9f43f204062c0db475160215d4d2a61c52b41a9`

The frozen `e638...` candidate failed at a case-rewritten lookup equation.
The root's `0d6968...` repair fixed that result field. Its next strict check
failed because placeholder existential witnesses did not elaborate. The log
is `20261114-shared-bucket-and-fresh-goal-check/shared-bucket-history-1.txt`.
Those failed declarations receive no proof credit.

This new packet replaces only the public theorem's proof body. Both theorem
headers and the complete private helper are byte-identical to the root's
lookup repair. The public statement and all endpoints remain unchanged.

The proof first derives a finite operational receipt with explicit witnesses:
the actual found target, old payload, old bucket, encoded handle, replacement,
read Core and pure finish singleton. It names these values in the actual
first-write and native-merge branches. It then applies the unchanged pure
write helper and the original slot bound. No existential placeholder is used
for a payload, bucket or handle.

The receipt preserves the complete old bucket as the ordered suffix of
`incomingScs ++ oldScs`. It derives ancestry membership from the old active and
target histories. It assumes no old-bucket, ancestry-origin, semantic model,
native-capacity or future-result provider.

The source audit and full objective remain in the original packet. The MAIN
target still needs ONE finite accepted completion of the SAME actual emitted
original-root partial term, under ONE assignment satisfying all retained and
historical removed obligations. The actual earlier-entry/child/clear relation
remains open. This repair does not replace it with a postModel implication.
No Haskell fix or accepted-source failing trace was established.

```lean
#print axioms MicroCFTA.SourcePruningEnumerationSharedIncomingNode.singleton_bucket_history
```

Strict elaboration and standard-axiom checks remain pending. No compiler,
live source, Git, board, Haskell or temporary data changed.
