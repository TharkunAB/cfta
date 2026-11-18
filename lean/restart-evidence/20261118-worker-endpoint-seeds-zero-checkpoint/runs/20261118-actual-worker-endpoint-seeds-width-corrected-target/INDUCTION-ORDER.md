# Dependency order for the endpoint proof

1. Prove Outer0 with the literal zero-depth resume equations.
2. Assume Outer n to construct Outer(n+1).
3. Inside that successor, prove task endpoint preservation at callback depth n
   by strong induction on task.work. Recover resource transitions internally.
4. Captured task callbacks invoke OuterIH n at their unchanged actual depth n.
   Selected returns and tuple/ordinary descendants use smaller task.work atn.
5. Finish Outer(n+1), including every emitted output and actual optional endpoint.
6. After all outer depths are proved, derive the global task theorem at each n
   from the already proved Outer n. Its final contract takes no outside IH.

Do not subtract one from an actual task callback's parameter. Its decrease is
from the enclosing outer(n+1) call. Preserve all original work fuels, the SAME
source root, actual metadata/cache, supplied decision and operational receipt.
