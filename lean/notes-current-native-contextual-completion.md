# Contextual completion components for checked native execution

Source main is `d44b2a0f`, merged at `b09f4ebb`. The recursive intersection
source is unchanged. Proof commits are `1ce04615`, `dc64812b`, `43b910be`, and `06a73330`.
The full-library goal remains active.

## Recursive binder language

`SourceCurrentAllocatedNativeMuMeaning` connects an actual completed
`maybeMu` to its least language and unfolding equation. Soundness tests the
body at the fixed original operand intersection. Completeness uses strong
induction on the sum of original input derivation ranks. The induction derives
the fresh result-candidate containment needed by `CompletePairs` extension.
The original `RankedInput.body` law supplies strict descent for both-Mu,
left-Mu, and right-Mu branches.

Local unfolded-body soundness and completeness remain component premises.
They must come from the actual checked body trace. Neither the least-language
law nor the local rank proof establishes general checked request completion.

`SourceCurrentAllocatedNativeMuSource` derives the literal source adapter.
An actual checked Mu prefix returns the entered domain and the original body
request, with its actual optional-binder continuation. Original codecs identify
the physical and semantic pair. The actual domain-cache allocation supplies
the exact source binding list. Stored body readback and input validity derive
the child inputs. A contextual law for that literal child supplies both local
body laws. Child completion and its contextual law remain recursive obligations.

## Contextual returned cells

`SourceCurrentAllocatedNativeContextCache` fixes the original input model and
its ranks across heap changes. A returned node has one-sided `NodeLaw`;
a returned edge has the corresponding ordered-row `EdgeLaw`. Empty tables,
lookup, demand, and machine advance preserve these laws. Finish stores a
locally proved law for the literal original evaluating request.

Actual warm lookup and ready demand recover the law for the requested key.
Existing physical key validity supplies exact request identity. A stored
historical closed `NodeProduced` receipt alone does not establish `NodeLaw`.

`SourceCurrentAllocatedNativeContextExecution` preserves this invariant
through actual checked steps, edge bodies, and every finite execution outcome.
`FinishThrough` asks for local laws only at finish instructions that execute.
Fuel zero executes no instruction and has no finish obligation. The proof
uses actual returned native and equality-operation states. It assumes no
final native validity or old eager execution. Deriving `FinishThrough` from
initial invariants remains part of the recursive semantic proof.

## Physical checked code

`SourceCurrentAllocatedNativeCodeProgress` derives primitive operands for all
compiled node branches. Initial closed Original inputs derive an independent
semantic schedule bound, structural `Safe` and `Below`, physical `Operands`,
and static loaded-field checks. Initial resident loaded fields also derive an
actual checked edge prefix, with exact returned operation validity, growth,
fields, operand checks, and strict child request bounds. Rejected branches
retain the actual sentinel and skip child requests.

The old `Safe` and `Below` predicates are structural certificates. They do
not replay an old native interpreter. Original operand codecs turn conditional
word checks into the current input checks. An unresolved intersection
placeholder lies outside this Original domain; its direct bypass does not
refute original-input completion.

## Closed receipts

`SourceCurrentAllocatedNativeClosedReceipts.mu_node_law` connects the local
Mu result laws to the contextual cache interface. `node_closed_exact` erases
the original ranks at the empty domain and derives exact input intersection.
`source_models` derives the needed original physical language readback from
source facts, availability, Original syntax, and closed roots.

`node_produced` uses the actual checked body execution, before and after
states, physical extension, and returned availability. It constructs the
closed receipt without a final native-validity premise. Completion, physical
effects, and the local contextual result law remain explicit inputs.

`SourceCurrentAllocatedNativeContextQuery` reads actual ready and started
query traces. It recovers the literal requested law from the retained cells.
The finish-plan endpoint has no final native-validity premise. For a started
query, its plan includes the root finish instruction and therefore the root
result law itself. This is conditional readback and cache transfer. The
recursive body induction must establish that law before the finish step.
The endpoint does not discharge general root semantics. Its empty-domain
exactness uses fixed model languages. Physical input equality still needs
the independently derived original input readback.

## Remaining general proof

Combine these components in a paired induction on the independent request
measure. Derive actual node and edge body completion, physical result facts,
local contextual result laws, and the original running finish handle. Derive
the reached input and finish plans. Preserve loaded fields, semantic heaps,
cost observations, and contextual caches at the same returned state.
Then compose whole original allocation history, the new current class Scan,
and the actual constrained outer caller. Do not substitute an old eager
execution or historical Scan.

All other full-library targets and each separate Sized contract remain open
where their existing coverage rows say so. External runtime contracts remain
explicit. This checkpoint does not prove whole-library correctness.

## Validation and evidence

The full audit passes 2,265 jobs and 55,567 theorem dependency checks. Only
the three permitted foundations and the existing unused-input warning occur.
Focused public signatures, axiom checks, actual empty checked execution, and
the other recorded kernel examples pass. Independent reviews retain the
local-body and full-completion boundaries above.

New evidence is in `lean/restart-evidence/20261016-recursive/`.
The execution environment reset its temporary directory during this work.
Before that reset, 2,981 baseline files and nineteen external drafts were
verified. Their temporary snapshots and external draft bytes are unavailable
after the reset. No missing draft is reconstructed or claimed reverified.
All 2,981 tracked baseline files remain. Older non-Audit proof sources are
byte-identical. The new repository-local evidence records this limit.
