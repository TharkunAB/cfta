# Native writer growth and actual filtered reconstruction

Starting checkpoint: 7b300b93. Proof commit: 0f995a42.
Source main remains c0cc8a05, merged at 896b0a1c.
The whole-library goal remains active.

## Exact native writer handles and retained heaps

SourceCurrentNativeEdgeWriterGrowth.Written records the exact captured
edge-owner handle. It retains the actual earlier body trace and protected
finish. Both the starting heap and completed-body heap grow into the current
reader heap. History starts with empty native tables. It follows actual
completed checked traces and exact physical advances with past growth.

History.writers derives Written for every returned cell. The proof follows
the actual fuel induction. Work and optional-binder steps supply their own
heap effects. A completed miss constructs the body and finish witness at
the same handle. A ready demand identifies the complete captured request
through its actual key checks. History.warm retains that exact handle.
History.forget projects the previous persistent-history result.

Grows retains the node and edge interning tables and both record tables.
It does not by itself retain the issued-reference ledger, prove counter
bounds, or establish domain growth. The generic advance constructor requires
past Grows. It does not assume a desired writer or guard law. A completed
trace is evidence about past execution, not a completion producer.

The constructed integration starts with its own source construction and
cold edge publication. An actual intervening allocation changes the heap.
The next demand is warm. It retains handle 0 and both writer-to-reader
growth facts.

## Initial inputs construct the history

SourceCurrentNativeCausalEntry.query applies the existing computed-budget
completion theorem to initial closed Original operands. It constructs the
actual physical receipt and derives the new History from that receipt's
trace. The caller supplies initial validity, semantic readiness, idle native
tables, available operands, stored mass, and the original numeric headroom.
It supplies no future trace, completion, or writer law.

The result retains the same exact receipt, bounded fuel, execution at the
computed bound, stored and result mass bounds, node and edge counter bounds,
and domain counter bound. It does not weaken the existing resource result.

The separate conjunction theorem constructs an actual memo call from initial
semantic readiness, cost facts, availability, and memo correctness. Its
returned physical effects derive the growth used by History.advance. It
retains the complete checked receipt, answer soundness, memo correctness,
and memo extension.

These two domains remain separate. The physical query receipt does not
supply the stronger SemanticReady and CostHeap premises for the conjunction
entry. No composed query-to-conjunction semantic pipeline is claimed.

The independent conjunction integration starts with a nonempty returned
native cell from its own cold source execution. The entry theorem constructs
a singleton productive-Mu conjunction call and its actual row read. The
returned heap retains handle 0 and its Written receipt. This integration
does not separately test the numeric query entry or assert that conjunction
must allocate.

## Actual reconstruction after literal filtering

SourceCurrentStoredFilterReconstruction.complete starts with Ready,
Available, and available replacements. It constructs the literal
withoutSelfReference result, the stored reconstruction of that result,
ordered reconstruction calls on retained original alternatives, and their
final union. All four actual heap steps retain Keeps. Both final values are
available and have the same exact literal atoms and complete ordinary rows.

The retained alternatives remove the literal self reference only at a union
root. A bare self reference remains. The proof replays all actual calls at
one derived final heap, then applies the existing union-fusion and literal
row laws. It assumes no future call or output relation. Nested Mu values
remain allowed.

The constructed test first reconstructs a bare self reference. It then
starts the union-self case at the actual first result heap. The second
source also has a nonempty ordinary leaf. The two cases retain the exact
reference and row distinction. Filtering after arbitrary replacement would
not supply the same behavior.

This theorem can apply to each raw callback and its filter from an actual
Mu writer. It does not yet align the retained alternatives from the body
callback with those from the ordinary-probe callback. That relation remains
the retained-Mu correspondence obligation.

## The same original node can occur as its returned child

SourceCurrentOuterOriginalRepeat builds plain productive pair recursion tau.
Let A be the class [[0,0],[0,1],[1]]. It builds C=pair^A(tau,tau) and
B=pair^A(C,C). The proof derives initial Ready, availability, closedness,
and Original from that source construction. Both outer result tables start
empty.

The root request uses B with empty inherited constraints. Its actual parent
edge call returns children [B,C]. The first child is the exact original B,
not only a value with the same guard. An exact Reached prefix reaches that
child while root owner 0 still evaluates.

The child's inherited class is [[0],[1]]. Its complete request key differs
from the root key. Its key is absent, and actual demand starts owner 1.
The actual local precheck reports empty children. The inherited-prefix
operation at the captured input also returns contradiction. The repeated
child call and the complete root call both return Empty. Their final cells
retain their distinct requests and returned Empty values. A later repeated
request is a warm hit.

This is an obstruction to strict descent by the whole physical node value.
It does not refute a measure based on properly tracked row occurrences.
B and C have the same raw guard and arity, so a row origin may still come
from C. Incoming inherited path height also increases from zero to one.
The constraint combination is essential to this stopping calculation.
The example does not exhibit a repeated physical key, an outer busy fault,
nontermination, or a Haskell defect.

## Remaining work and Haskell handoff

The largest mathematical gap remains general recursive outer progress and
all-active-ancestor exclusion. Repeated-pass convergence is separate.
The new writer-growth and initial-entry results provide provenance facts;
they do not supply a decreasing global call measure. Retained-Mu callback
alignment, frontend and runtime adapters, and public pipeline composition
also remain open. See notes-proof-status-20261017.md.

No Haskell behavior change or new production defect is added. Field-pool
repair b9219b9e remains merged and validated in source c0cc8a05. Keep FINDINGS
as the external repair handoff. Record every later fix with its failure,
reproducer, paths, commit, checks, and upstream status. Preserve all earlier
proofs, evidence, counterexamples, repairs, drafts, and optimized code.

## Validation

All four final strict source logs are empty. All four canonical builds pass.
Full Audit passes 3141 jobs and 69349 dependency checks. Sixteen public and
four constructed pairs pass in eight groups. Only propext, Classical.choice,
and Quot.sound occur. Full proof output has no omissions or printer failures.
Four component manifests verify 180 entries. The effective maximum and high
are 4294967296 bytes, with zero swap. Audit peak is 376 MiB.

Evidence is in restart-evidence/20261017-native-causal-growth/. It retains
all failed attempts and raw logs. The original-repeat integration also
checks inherited path height from zero to one and the final warm result at
every supplied fuel. It does not claim a general repeated-pass proof.
Unchanged Haskell source reuses its existing strict Nix and suite validation.
