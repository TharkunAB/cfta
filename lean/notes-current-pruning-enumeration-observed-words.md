# Actual native observations and initial numeric room

Recorded trace word checks and target observations: `da28d95e2`.
Initial-room receipts and full caller posts: `1d8cdc3a7`.
Positive-width raw-versus-recorded boundary: `769fe467b`.
The goal stays ACTIVE. This checkpoint does not complete the formalization.
The initial pull was already up to date. A fresh main fetch confirms imported
main `153e1a211b56dd78bd22f6b427fb78e673041d55`.

## Correct the raw-observation target

The previous handoff requested range-free preservation from raw native done
observations. Bare raw success does not supply the missing physical checks.
Native lookup converts keys without testing KeySafe. Finish instructions do
not check the running-cell ownership and resident-value facts required by
PhysicalExecution.Inputs. Good and Fields for arbitrary control therefore
do not justify an automatic raw execution-to-physical-Trace lift.

Do not assume that lift in the recursive proof. The new positive theorems use
either an existing certified Trace or explicit CURRENT numeric room. This
does not replace initial recursive capacity with a future range receipt.

## A recorded trace already supplies its word checks

ObservedWords.inputs_words extracts RequestBounds.Words from the actual
PhysicalExecution.Inputs. Node and edge checks contain those exact key bounds.
Every other Words case is True.

trace_wordRanges starts from a COMPLETED rich physical Trace. It compares
every possible actual Steps prefix with that trace. Zero-length prefixes
use the recorded current instruction checks. Positive prefixes align both
the next control and the complete checked state by deterministic step
equality. At the final pure control, a further yielded prefix is impossible.
No readiness, semantic result or extra range hypothesis is needed.

TargetQuery.Step already wraps such a Trace. Step.wordRanges therefore derives
its range certificate. Step.verified_observed retains the ENTIRE existing
target Receipt with no separate WordRanges argument. It reuses the earlier
verified theorem. Its internally constructed finite witness is identified
with the supplied actual Step by exact completed-run uniqueness. This is
proof reuse. No future successful action is an admission premise.

Step is richer than raw execute.done. The new theorem must not be described
as a raw-done-to-trace lift. Existing runtime workers and earlier Step,
Receipt, finite and verified declarations remain exact.

## Current numeric room constructs the full target receipt

TargetQuery.finite_initial takes current Ready, inventory At, closed available
left and right operands, valid global memos and three explicit initial bounds.
For before : Checked(bits + 2), they are:

1. before.native.machine.heap.nodes.next < 2^bits.
2. before.native.machine.heap.edges.next ≤ 2^(bits + 2).
3. before.native.machine.domains.next +
   2^(nodes.next + nodes.next * nodes.next) < 2^(bits + 1).

The coherent current heap derives Original syntax from closed availability.
warm_initial_ranges derives WordRanges from these current counters and room.
The original target producer then returns its actual value, full checked
state, next inventory and complete Receipt. No future range, trace, cache,
successful callback or recursive result is an input.

raw_done_verified_initial uses the SAME initial facts and an actual supplied
execute result. It invokes finite_initial once. Its produced actual Step
gives a completed execution. Exact completed-run uniqueness identifies the
supplied value and EVERY checked-state field. The conclusion retains the
same full Receipt, next.source and next.roots equations.

These bounds admit one current closed query. They do not forecast all later
queries or reserve an entire recursive tree. More work fuel cannot provide
the missing machine width. Derive future room from the original input.

## Query receipts retain the full outer Caller

receipt_post combines the actual target Receipt with the original Context.
Its literal returned caller uses the actual checked state and retains the
original fourth and merge memos. It retains all eight Context fields:
readiness, inventory admission, partial-result soundness, stored merge data,
merge language coverage, fourth-memo correctness, globals and probe heap.
It retains physical effects and merge/fourth extension histories. Existing
advance retains both outer result-table families.

Step.caller_post derives this full Post and Receipt from the existing rich
Step with no extra range argument. raw_done_caller_initial derives the same
facts for an actual raw return under the explicit current numeric room.
These posts can feed Recursive.captured_post for the SAME captured sibling
cache. They do not prove a whole subtree's aggregate Post.

## Kernel-checked positive-width boundary

NativeWordBoundary.witness builds a closed ordinary root with a closed leaf
through the actual fresh constructor. The root's identity is one. Its tagged
reference code is four. At width two, this is outside the admitted safe range.
The empty-left request still publishes its key and returns Empty in four
native instructions. Its initial empty physical memo tables are valid.
The operation state is valid. NodeReady and closed operand availability hold.

The witness proves not KeySafe, not Words, not Inputs and absence of ANY rich
physical Trace for that complete return. The no-trace proof uses the new
trace_wordRanges theorem. All private decision instances are computable.
The proof uses kernel reduction, not native evaluation or a new axiom.

The witness makes no semantic Ready, inventory At, full Good or outer Context
claim. It establishes neither an incorrect result nor a Haskell output defect.
Do not treat it as a refutation under stronger initial numeric admission.
FINDINGS records this scope. No Haskell patch is proposed.

## Verification and retained attempts

Lean 4.34.1 checks all five new modules and Audit with warningAsError and
linter.all. Eight strict attempts have seven passes and one failure. The
failed trace proof used local names removed by dependent cases and omitted
the induction hypothesis's explicit prefix parameters. The final source
fixes those proof arguments. The failed source and raw log remain retained.
No linter is disabled, and no placeholder or new axiom is added.

Three serial helper builds and installed Audit pass. Audit checks 77138
theorem dependencies in 3794 jobs. Lake replays the existing unused inputs
warning in InternedFreshOrdinaryClosedCompletion. Its source stays unchanged.
Every new strict module has no warning. Independent review found no issue
with the input/output boundaries or the counterexample's stated scope.

Installed public readback covers 20 declarations and the complete Step and
Trace definitions. It retains 688 lines and 48890 bytes, SHA-256
`624c44345ecc4d639131c823487ed768298f7c9924a8f50d0a4051724dffa883`.
No ellipsis is present. Reported axioms are limited to propext, Classical.choice
and Quot.sound. Heavy jobs run serially with a 4G cap and five-minute limit.
Evidence is in `lean/restart-evidence/20261026-native-observed-words`.
Haskell stays unchanged. No Haskell suite or formatter is required for this change.

## Strongest theorem and next work

H6 remains SourceCurrentColdFiniteWarmCalls.constructed_node_calls. Covered
closed construction and valid initial constraint allocation history derive
a complete prescribed finite number of modeled node-processing rounds,
sufficient finite fuel and one mathematical word width chosen after
construction. With empty inherited payload, the final available value has
exactly the initial finite-tree language under the modeled guard/solver
interfaces. It does not prove full recursive typing/pruning enumeration.

The callback-to-next-prefix producer remains available with its common work
fuel and full invariant packet. Use the new native-call contracts for the
next captured-edge preservation layer. A certified actual Step can derive
its own word checks. A raw native return must use sufficient current room
or another proved admission certificate. Do not invent a general raw-success
physical trace or silently assume current key safety at later endpoints.

Derive sufficient room from INITIAL inputs for prescribed finite recursive
histories. The current instruction/computed budget theorems bound one query's
returned payload and counters. Extend the forecast through actual child
traversals, concrete callbacks, recursive subtrees and later siblings.
The old ordinary Ranges follows legacy endpoints and does not supply this.

Then prove subtree preservation by recursive-budget and edge-list induction.
Retain a native Post for the final endpoint and separate Posts/cache packets
for outputs at their OWN emission endpoints. Use actual Posts to transport
the SAME captured sibling cache. Keep safety for changed callback cores
separate from Frame. Preserve pending metadata bounds and dependency levels.

Whole-driver output language, terminal/nonordinary outer fallback, native
Graph correspondence, concrete solvers, physical containers, machine Ints,
extraction and arbitrary Haskell lazy demand remain open. No convergence or
practical resource bound is claimed. Preserve the optimized interned core,
older secondary constructor/equality proofs, all counterexamples and marked
drafts. Keep the six merged Haskell repairs and external Sized documentation
repair action in FINDINGS. The full goal stays incomplete.
