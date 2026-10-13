# Generated nested unary equality carrier

Checkpoint: 2026-10-13 17:06 Europe/Stockholm.

## Result

The concrete projected endpoint loop terminates for a finite nested ordinary
fragment. Each endpoint is a set of unary `f` rows. Each unary row has Top
at its parent and one canonical nullary `a` child. The child constraint is
an admitted source residual generated from the original outer guard atoms.
The atom basis has length at most two.

`EqualityNestedUnaryTermination.termination` proves a bound of
`4 * (leftOccurrences + rightOccurrences) + 2`. This includes the final
identity test. The worker uses actual physical caches and complete values.
It reads both projections before it changes an endpoint. Each projection
executes the actual union constructor and current target merge. Each edit
executes the physical nested intersection. The stopping condition compares
numeric node identities at each original occurrence position.

The bound does not assume a finite universe. The source guard atom basis
generates the row inventory. Its length is at most four. Canonical node
readback and physical row injectivity bound the actual stored endpoint
rows by that inventory. Thus the current target merger returns each such
endpoint and cache unchanged. This result also applies after intersection
and projection; it does not assume one-pass target idempotence in general.

## Proof files

- `EqualityNestedUnaryCarrier.lean`: generated residual inventory, source
  conjunction, initial nested compiler, and finite indexed row measure.
- `EqualityNestedUnaryChild.lean`: actual singleton child intersection,
  complete constraint keys, identity shortcut, and operand orientation.
- `EqualityNestedUnaryProduct.lean`: physical unary row composition and
  complete source symbol hash join. The product executes child requests
  before the parent edge and final node requests.
- `EqualityNestedUnaryMeet.lean`: exact numeric identity condition and
  source whole-node shortcut. Empty operands return Empty without effects.
- `EqualityNestedUnaryBound.lean`: canonical row count and exact runtime
  target merge for every represented nested endpoint.
- `EqualityNestedUnaryUnion.lean`: actual projection union and current
  target merge preserve the exact generated row predicate.
- `EqualityNestedUnarySchedule.lean`: cache-threaded snapshot projections
  and ordered edits at the original finite occurrence indices.
- `EqualityNestedUnaryTermination.lean`: physical identity agrees with
  generated row equality. The concrete endpoint loop refines the bounded
  row execution.
- `EqualityNestedUnaryCompile.lean`: actual source requests construct
  the complete endpoint representation invariant in the returned cache.

`EqualityNestedUnaryCompile.compileGroup_complete` supplies the initial
physical endpoint invariant. It does not replace the runtime input with a
proof-prepared cache. `Extension` retains cache growth, issued history,
Facts, and Prepared across every executed stage.

## Source correspondence boundary

The proved runtime worker is the projected endpoint schedule. Its inputs
retain every original endpoint occurrence at a fixed finite index.
Ancestor reconstruction, duplicate ancestor normalization, required-path
admission, and comparison with the forest-level source identity test need
an additional lift. The source fixture uses paths `0.0 = 1.0` and unary
ancestors. The endpoint proof alone is not a theorem for the complete
`reduceEqConstraints` implementation.

The parent row hash join uses the source symbol key. It then takes the
arity branch before it zips actual children. This fragment derives equal
unary arities, so the mismatch branch is unreachable. Complete parent
constraints remain Top. Complete child constraints use actual canonical
source conjunction. Admitted residuals exclude the constructor rejection
cases. The physical identity condition derives from retained coherent
records and exact readback; it is not a semantic language comparison.

The current loop covers one fixed reciprocal binary class. It does not
cover arbitrary intervening classes, wider generated carriers that can
activate the large-group merge branch, or recursive Mu paths. The earlier
multi-pass target normalization counterexample remains valid. No source
repair follows from this restricted positive result.

## Checks

Pinned Lean build:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.EqualityNestedUnaryCompile
```

All 393 dependency jobs passed. The focused axiom audit checked 68 theorem
declarations in these nine modules. It found only `propext`,
`Classical.choice`, and `Quot.sound`. There are no admitted obligations,
custom axioms, or native decisions.

Audit input: `/tmp/mcfta-equality-nested-unary-axioms-20261013.lean`.
Audit log: `/tmp/mcfta-equality-nested-unary-axioms-20261013.log`.

`lean/repro/NestedUnaryTwoAtom.hs` retains the native source comparison.
It checks all 256 pairs of singleton endpoint masks and 4,096 deterministic
pairs of groups with three original occurrences per side. Every completed
source pass agrees with the generated row transition. Every represented
target is unchanged by the current merger. The maximum observed number
of changing passes is two. This finite execution check supports source
alignment; it is not a replacement for the remaining ancestor lift.

The Nix result is in `/tmp/mcfta-nested-two-atom.log`:

```text
("nested-two-atom",4352,"maximum-changing-passes",2)
```

Run the retained source fixture with:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- ghc -O0 -package=microcfta lean/repro/NestedUnaryTwoAtom.hs -outputdir /tmp/mcfta-nested-unary-build -o /tmp/mcfta-nested-unary && /tmp/mcfta-nested-unary'
```
