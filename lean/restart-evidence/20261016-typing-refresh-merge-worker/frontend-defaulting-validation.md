# Current curried marker adapter validation

Source: MicroCFTA/SourceCurrentCurriedDefaulting.lean.
Frozen SHA256: `15efe7d98f967fee1c7683b6607aa1d487315fe7419ec55f7ed9b76f6de3733f`.

The literal source is Synthesis.hs:579–586 at ccebf0f7. The new module
reuses the historical exact leaf predicate and adds the current ?any-first
branch. It proves agreement with the older filter when ?any is absent,
all four branch laws with their actual guards, complete-record/order/
multiplicity retention, and idempotence. It does not retarget the old
Defaulting data or domain-map APIs.

The source-built counterexample sequentially executes makeEdge ?any and
makeEdge Int in the SAME constructor heap, starting empty. The checked
records have symbols ?any and Int, with identities 0 and 1. No arbitrary
physical records are supplied. The old no-open filter retains both; the
current filter retains only ?any. This is an exact source-adapter boundary,
not a Haskell bug.

Focused canonical command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentCurriedDefaulting
```

Terminal exit 0, 142 jobs, no warnings. The canonical slot was released to
root immediately. No further Lake build was run by this owner.

Independent imported probe command:

```
LEAN_PATH=lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-typing-refresh-merge-worker/frontend-defaulting-public.lean
```

Final raw log frontend-defaulting-public-4.log: exit 0, no errors or warnings.
All 12 public axiom checks and full signatures pass. Three external kernels
test precedence over head rejection, retention of repeated physical marker
occurrences, and an actually interned nonleaf marker name. The nonleaf test
is a raw local-filter input with an Empty child. It does not claim that a
node constructor retains an edge with an Empty child. All 15 axiom probes
use only propext, Classical.choice, and Quot.sound (or no axioms).
There are no sorryAx dependencies.

Logs 1–3 preserve probe-only elaboration failures. The first had an invalid
combined open declaration. A later more complex node-constructor fixture
was replaced by the smaller actual raw edge fixture. No proof source was
changed after the first canonical build. The clean final source is saved
as frontend-defaulting-source.lean.txt.

No earlier proof source, Haskell, Audit, docs, or Git state was edited by
this owner. The evidence contains no compiled artifacts. The model does not
prove Domain construction, bounded domainNodes approximation, GHC instance
selection or pruning, synthesis completeness, host Text/Symbol conversion,
HashMap behavior, or actual runtime identity allocation.
