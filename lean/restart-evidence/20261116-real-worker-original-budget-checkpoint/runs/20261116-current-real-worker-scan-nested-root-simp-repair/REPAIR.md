UNCOMPILED single local proof replacement after98316.

The prior dsimp left literal record.limit and record.own below protected nodePlan
and tuplePlan. Replace only rootSeed's dsimp/rfl block with simp only on the root
rowSeed, root projections and the exact local forecast aliases. The simplifier
uses congruence to normalize the nested arguments. The scalar function remains
opaque. The symbolic capacity and all computed forecast functions stay protected.

RootShapes is exactly the accepted prior proof. The accepted row proof and the
entire remaining scan proof stay byte-exact. Full de7a/public5493/probes stay exact.
The original2M checking limit and all algorithm fuel arguments stay unchanged.
All previous packets/logs remain immutable. Root owns strict checking/publication.
