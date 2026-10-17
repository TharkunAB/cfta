# Finite union and self-filter reconstruction checks

No counterexample was found in the four kernel cases in this package.
This result is finite evidence. It proves no general fusion theorem.
This package changes no production source and records no Haskell defect.

The tests use closed source construction from empty.
They select an actual stored used Mu and run repaired stored substitution twice.
The first run replaces the stored self in the body.
The second replaces the ordinary marker in the ordinary probe.
The second run starts at the first returned heap and uses the same replacement.

Four kernel pairs prove complete Value equality:

1. A root union contains duplicate bare-self alternatives and an ordinary node.
   The node has duplicate live rows and one dead row with an empty child.
   The normalized stored body has exactly one row.
   The replacement is the selected ordinary reference.
2. The source is a raw outer binder over a union of self and a raw inner binder.
   The inner body is a union of inner self and outer self.
   The outer usesLocal result is true and the inner result is false.
   Both identity/self reconstructions reduce to the literal outer self reference.
3. A root union contains self, an ordinary node, and a nested used raw Mu.
   The selected outer Mu has an empty replacement.
4. The same nested-used union source selects the open inner Mu.
   Its replacement aliases the captured outer self.

The first two kernels also derive Ready, replacement availability, source-started
publication history, the retained original Mu, and exact warm replay at the final heap.
The latter two compute actual successful source and reconstruction calls and usesLocal=true.
They compare the complete returned Values, not only their reference keys.
They do not package separate Ready or History conclusions.
All four selected proofs have only standard axioms.

The used-local decision does not guarantee an ordinary-row result after reconstruction.
Case 2 has no ordinary nodes. A raw unused inner wrapper makes outer self deep.
Smart reconstruction removes that wrapper and returns the self reference.
A general origin relation must allow this reference or epsilon case.

The initial buffered eight-case evaluator timed out at five minutes with no result.
A smaller streamed evaluator was stopped after the kernel checks replaced it.
Neither evaluator attempt is counted as evidence of equality or inequality.
A failed type-qualification attempt is also retained and excluded.

The missing theorem remains normalization and substitution fusion through arbitrary
nested used binders and actual earlier warm winners.
It must compare two repaired results and retain exact selected probes and payloads.
Original ordinary and reserved marker freshness must follow from actual construction.
Depth can alias a capture. A replacement need not be fresh: these cases use aliases.
The earlier inequality against an unreconstructed raw ordinary probe remains compatible.
