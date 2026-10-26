from pathlib import Path
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-observed-words-20261026')
block = '''## Native observations retain checked traces and explicit initial room

Recorded word checks: `da28d95e2`. Initial-room receipts: `1d8cdc3a7`.
Positive-width boundary: `769fe467b`. The goal stays ACTIVE.

A completed physical Trace already records each instruction's input checks.
It now derives WordRanges for every actual execution prefix. An existing
target Step therefore derives the complete target receipt and outer Caller
Post without a separate range premise. No raw-success-to-trace lift is claimed.

For raw execution, current readiness, inventory, closed available operands
and explicit initial node/edge/domain room derive the complete target receipt.
A supplied raw return is matched at its exact value and full checked state.
Its outer postcondition retains all Context fields and both outer memo tables.
The producer assumes no future trace, cache, result or range receipt.

A width-2 counterexample has a closed available operand, valid empty physical
tables and valid operations. It returns Empty despite an unsafe encoded key.
Words and Inputs fail; no rich checked Trace exists. The witness makes no
semantic Ready, At, full Good or Caller Context claim. This corrects the
earlier bare range-free raw-success target. It establishes no Haskell defect.

All five new modules and Audit pass strict checking. Public readback covers
20 declarations and both complete Step/Trace definitions. Audit checks 77138
theorem dependencies. Earlier runtime and proof interfaces stay unchanged.
H6 remains the strongest end-to-end language theorem. Next: use initial-room
admission for native edge preservation, then derive and retain enough room
from the original input across callbacks, recursive subtrees and siblings.
Whole-driver language, terminal fallback, Graph correspondence, extraction
and arbitrary lazy demand remain open. Haskell stays unchanged. Details:
`lean/notes-current-pruning-enumeration-observed-words.md`.

'''
findings = '''### Native numeric admission and raw successful observations

The finite-width native model converts memo keys without checking KeySafe
at execution. A Lean-checked width-2 witness builds a closed ordinary node
with identity one. An empty-left request returns Empty in four steps, while
the encoded key is unsafe. Its initial physical tables and operations are
valid, and both operands are available. Words and Inputs fail. No physical
Trace with recorded instruction checks can describe that complete execution.
The witness does not assert semantic Ready, At, full Good or caller Context.

This is a formal capacity boundary. No incorrect Haskell output or new Haskell
repair is established. External action: retain the numeric-room obligation.
No runtime patch is proposed. Keep the existing Sized documentation repair.

The positive proofs now separate the two valid contracts. A recorded Trace
derives its own range certificate. A raw return receives the full target
receipt and outer Post under explicit CURRENT node, edge and domain room.
No future trace, successful callback, valid cache or range receipt substitutes
for those initial facts. Room across recursive siblings remains to be proved.
Details: `lean/notes-current-pruning-enumeration-observed-words.md`.

'''
note = '''# Actual native observations and initial numeric room

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
'''
content = dict(block=block, findings=findings, note=note)
(area / 'handoff-content.json').write_text(json.dumps(content, indent=2) + '\n')
for rel in ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
            'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
            'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']:
    path = root / rel
    text = path.read_text()
    marker = '## Concrete callbacks derive the next prefix packet and common work fuel'
    assert marker in text and block.splitlines()[0] not in text, rel
    path.write_text(text.replace(marker, block + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Concrete callback invariants and next-prefix fuel'
assert marker in text
path.write_text(text.replace(marker, findings + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(block.splitlines()[0])
(root / 'lean/notes-current-pruning-enumeration-observed-words.md').write_text(note)
print('Updated nine status documents and the native-observation handoff.')
