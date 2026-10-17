# Controlled vector length review

Reviewed on 2026-10-17 at 08:50 CEST. The frozen production source has 190
lines and SHA256
`a98abdc7880f17c9de7b6f3aa78a963aa9a7e6f3c22e52858d46af0b345f86a4`.
Strict direct attempt three has an empty log. The canonical single target
completed three jobs with no diagnostic. No older source was changed.

## Statement and numeric computation

`iterate` applies a numeric function a fixed number of times (lines 14–16).
The complete initial majorant is a computable definition (lines 45–48):

```text
F(0,q) = q
F(d+1,q) = iterate (x -> g(F(d,x))) (q+1) q
```

The function `g` must be monotone and strictly increase every natural input.
`majorant_ge` and `majorant_mono` prove initial growth and initial-control
monotonicity (lines 59–81). The latter proof increases both the iteration
seed and its count. It does not assume a later digit ceiling.

`Path` (lines 84–94) records a finite actual path. Vectors use natural-index
functions with only coordinates below `dimension` active. This is the same
finite order as `HeightOrder.VectorBelow`: unfold that definition and apply
`HeightOrder.extend` to each finite vector. Coordinates beyond dimension are
irrelevant. Every path state has its own coordinate bound. A step requires
strict vector descent, a strictly increased control number, and an upper
bound of `g` applied to the preceding control. The final state is bounded by
the terminal reflexive constructor.

`Path.elapsed_le` proves initialControl + length <= finalControl (lines
105–110). It uses the strict control increase at every actual step. The
conclusion does not rely on counting a chosen successful fuel witness.

## Block proof

The private `blocks` theorem (lines 112–133) scans the actual finite path.
Either all steps descend within the lower dimension, or it isolates the
first highest-coordinate drop. The preceding part is a complete controlled
lower-dimensional path. The boundary has its actual next-control upper
bound. The remaining highest coordinate is strictly smaller than the
original highest coordinate. Lower coordinates at that boundary can be
larger than all original coordinates.

`top_bound` (lines 135–163) inducts on an arbitrary bound on the initial
highest coordinate. In a whole lower-dimensional block, its endpoint is at
most F(d,q). One extra application of g safely bounds the end of that block.
At a strict highest-coordinate drop, the lower block followed by its actual
boundary has control at most g(F(d,q)). The induction hypothesis applies to
the remaining path with one fewer possible highest-coordinate level. The
majorant's q+1 iterations include the final block. No bound from the initial
state is reused as a bound on future lower coordinates.

`Path.final_le` applies this argument by dimension and uses the actual
initial highest coordinate <= initialControl (lines 166–179). Dimension zero
has no strict vector step. `Path.length_le` combines the resulting final
control bound with the actual elapsed-length inequality (lines 182–188).
The proof takes neither a future vector bound nor an assumed path-length
bound. The candidate recurrence is proved unchanged.

## Imported validation

All 11 public declarations have explicit signature and axiom pairs. Both
integration theorems construct their own controlled paths. They do not take
a path or its desired bound as an input.

The first uses g(q)=2*q+1. It starts at coordinates (1,1), control 1. One
lower step reaches (0,1), control 3. The highest coordinate then drops and
the lower coordinate becomes 7, control 7. Seven lower steps end at (0,0),
control 1023. This is nine steps, which exceeds the initial fixed-radix
allowance (1+1)^2=4. The theorem derives both finalControl <= F(2,1) and
length <= F(2,1).

The second uses any monotone strictly growing g and initial q>=1. A highest
coordinate drop refills the lower coordinate to g(q)>q. It constructs the
entire g(q)-step countdown at the actual growing controls. Both endpoint
and length g(q)+1 are bounded by F(2,q). This exercises the parametric
control rule rather than a concrete precomputed endpoint only.

All final imported logs are free of warnings, errors, proof holes, and
truncated signatures. Only standard Lean axioms occur. Earlier parser/name
errors and integration attempts remain immutable snapshots and logs.

## Scope

This is the generic controlled-descent theorem. The reader must separately
produce its own strict measure steps, coordinate bounds, and monotone
control growth from physical invariants. It must reconstruct a successful
read from its consumed finite path before advertising sufficient read fuel.
This theorem makes no source-fragment, future inventory, completion, word
range, or fixed-radix assumption. It is a mathematical majorant, not a
practical runtime, solver-cost, payload-byte, or full-library convergence
claim.
