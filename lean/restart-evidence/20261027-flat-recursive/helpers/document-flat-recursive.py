from pathlib import Path
import hashlib
import json
import re
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-flat-recursive-20261027')
head = (area / 'source-head.txt').read_text().strip()
base = (area / 'published-base.txt').read_text().strip()
aggregate = (area / 'build-aggregate/raw.log').read_text()
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', aggregate).group(1)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', aggregate).group(1)
public = json.loads((area / 'public-validation.json').read_text())
assert public['status'] == 'pass'
assert json.loads((area / 'source-validation.json').read_text())['status'] == 'pass'

prefix = f'''
## Actual flat recursive correspondence now holds at every finite depth

Source checkpoint: {head}.
Twenty-two new modules execute the full flat recursive driver and preserve
the original finite-depth completion and resource contract.
For each original admitted packet and finite recursive reservation, one
work bound and one stable original result are chosen before the flat input.
Every related initial flat cache executes to a related result at every
adequate work bound. Ordered outputs retain metadata, branch caches, Caller
and Queries. Explicit stops retain their observations and optional endpoints.
The result retains the entire original OutcomeResources certificate.

The depth induction executes actual callbacks and smaller-depth subtrees.
Each later sibling starts at the actual post-hook native Caller and full
Memos. Each sibling restores the same captured enumeration cache and metadata.
The public theorem has no recursive-completion or future-flat-success premise.
No semantic Canonical or Ranges assumption was added to the original contract.
It does not prove unbounded convergence or exclude explicit budget stops.

H6 remains the strongest global exact finite-tree language theorem.
Recursive output soundness, coverage, pruning-policy soundness, initial
admission histories and full Haskell correspondence remain open.
Audit passes {jobs} jobs and {dependencies} theorem dependency checks.
All twenty-two modules and Audit pass strict checks. No Haskell source changed.
FINDINGS retains all Haskell repair handoffs and the extraction-progress limit.

Next classify the actual recursive outputs and prove their language meaning.
Derive initial Canonical, semantic Ranges and allocation histories where
semantic consumers require them. The full goal stays ACTIVE and incomplete.
Details: `lean/notes-current-flat-recursive.md`.

'''

documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/API-COVERAGE.md',
    'lean/COVERAGE.md', 'lean/README.md', 'lean/SYSTEM.md',
    'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
records = []
for name in documents:
    path = root / name
    old = path.read_bytes()
    assert old == subprocess.check_output(['git', 'show', base + ':' + name], cwd=root)
    target = area / 'prior-documents' / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(old)
    first, rest = old.split(b'\n', 1)
    data = first + b'\n' + prefix.encode() + rest
    path.write_bytes(data)
    records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
        offset=len(first) + 1, inserted_bytes=len(prefix.encode())))

note = f'''# Actual flat recursive correspondence at every finite depth

Source checkpoint: {head}.
Published base: {base}.
Imported main: 82258094c2c32bb93e517427bc649a5c7077adac.
The initial formalize pull and main fetch succeeded. Main did not change.
The preceding goal turn made progress. It pushed ordinary and plain sibling
completion through 79da43a1b. This turn closes finite-depth recursive execution
correspondence. The whole formalization goal stays ACTIVE and incomplete.
Preserve the optimized interned core and every earlier proof, repair,
counterexample and marked draft. The preceding checkpoint is
`notes-current-flat-native-branches.md`.

## Target and strongest statements

The target remains whole-system source-connected correctness. It includes
exact finite-tree language preservation, enumeration soundness and coverage,
and explicit solver and pruning contracts.

SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains unchanged.
For covered closed construction and a valid original guard-allocation history,
each chosen finite budget and round count has derived mathematical width and
fuels. The actual formal node calls complete. The final node remains available.
Its accepted finite trees equal the original accepted finite trees in every
ambient environment. The inherited payload is empty. This theorem concerns
the formal model. It does not certify the whole Haskell implementation.

SourcePruningEnumerationCapturedEdge.diagonal_render_sound_current is unchanged.
Actual stable captured completion, its original current admission conditions,
structural discharge, successful rendering and checked residuals construct a
satisfying assignment. They derive original edge/parent acceptance and every
suspended constraint. Existence of discharge or successful rendering remains
a separate obligation.

The new SourceFlatPruningRecursive.run_finite_complete_resources theorem
covers the entire actual recursive driver at every chosen finite capacity.
Its depth induction is finite_complete. The Complete definition retains all
original inputs: Packet at the full native Memos, Fits, heap carrier, edge
selection membership and length bounds, initial suspended mass, and the
original finite reservation at bits + 2. It adds no semantic Canonical or
Ranges gate. The input Packet still requires native Context, Safe storage,
pending-reference discipline, valid native cache indexes, stratification and
allocated pending template variables. These initial facts need construction
histories. The theorem does not assume a desired final flat execution.

The quantifiers are significant. Original admission determines one work bound
and one stable old result. The old run equals that result at every larger work
bound. It retains the entire old OutcomeResources certificate. Then, for EVERY
related initial flat cache and every larger work bound, the actual flat run
returns a related result. The flat result can depend on that execution. This
is not one literal flat forest shared by every larger bound.

OutputRelated preserves output order through the heterogeneous ordered-list
relation. Each output has equal metadata, a related branch cache, and the
same actual native Caller and Queries. FailureRelated retains selected-prefix
observations, callback and entry raw results, exhaustion, processed receipts,
nested continuation failure and the exact optional native endpoint. The
global result relation preserves complete/stopped shape and emitted prefixes.
The old OutcomeResources certificate retains full Post/global Memos and
resource bounds for the reached endpoint and for each emitted output.

## Composition and resource history

ChildResources and TraversalResources retain the entire old resource packets.
Actual successful child caches feed the next child. Valid rejection keeps
its real stopping cache and native effects. It does not imply Safe.
SelectedResources composes actual own-class allocation and child traversal.
CapturedResources aligns the actual completed receipt and writes its captured
slot. NativeHeadResources covers arity rejection and unsupported projections.
No future flat observation or final flat invariant is an admission premise.

Recursive defines the actual flat Output, Failure, resume and run workers.
It executes the flat selected prefix, ordinary entry, ordered siblings and
the full fragment callback. RecursiveBase covers zero depth and all
nonexpanding decisions. ContinuationCorrespondence derives a successful
singleton continuation from the original callback Success witness.
ContinuationHead extracts the actual suffix after a handled head.
RecursiveAdmission derives actual callback rows and cache correctness at
their own native heap. Its completed_subtree theorem restores the captured
packet at the actual returned native endpoint and full Memos.

FiniteContract strengthens the original Complete contract with actual flat
correspondence. RecursiveCallbackResources first obtains the uniform old
callback result. A nonpruned callback uses the strong smaller-depth contract
at its actual returned cache. RecursiveReceiptResources obtains that packet
from the original completed receipt. RecursiveHeadResources combines the
same old head and callback result without discarding the old certificates.

RecursiveSiblingResources uses list induction. A completed hook runs BEFORE
the suffix. Its actual returned native Caller, Queries and full Memos supply
the suffix admission. Each sibling restores the SAME captured enumeration
cache and metadata. The proof does not infer post-hook admission from the
plain scan's earlier head endpoint. It retains processed receipt positions,
ordered outputs and stopped hook observations. Its finish theorem retains
the entire old finished OutcomeResources certificate.

RecursiveOrdinaryResources and RecursiveOrdinaryForecastResources compose
one actual successful entry with that sibling family. The entered flat core
is framed over the original captured indexes. The original entry packet,
support conditions, resource forecast and finished certificates remain.

RecursivePrefixShape extracts parked, rejected and accepted observations
from actual selected-prefix correspondence. RecursiveParkedResources runs
the smaller-depth worker at the actual callback cache. ExpansionResources
obtains the original uniform prefix checkpoint BEFORE choosing the flat
cache. It replays the SAME PrefixValid at the common work bound. Ordinary,
Empty, parked and explicit fallback cases retain their exact results.
RunStep includes every initial decision. FiniteResources closes Nat induction
and removes the smaller-depth completion premise from the public theorem.

Bounds use sums and maxima. Their choices precede the universal flat input.
The flat-first generic prefix producer cannot establish that uniform order.
The proof therefore uses the original uniform checkpoint and pointwise replay.
The old actual receipt supplies the entire old history once. Resource and
cache facts then apply at the receipt's actual native heap.

## Verification and preservation

Twenty-two new modules contain 3956 lines and 35 public theorems.
Audit adds only twenty-two imports. Every earlier proof source is unchanged.
All new modules and Audit pass Lean 4.34.1 with warningAsError and linter.all.
Every new module has empty strict compiler output. Aggregate Audit passes
{jobs} jobs and {dependencies} theorem dependency checks. Its replay retains
the earlier unused-input warning in InternedFreshOrdinaryClosedCompletion.
No sorry, admit, native_decide, new axiom or heartbeat increase was added.

Installed readback covers 37 theorem signatures and axiom lists, including
unchanged H6 and captured rendering, plus 11 complete definitions.
Only propext, Classical.choice and Quot.sound occur in those axiom lists.
No definition or signature is elided. Raw readback has {public['bytes']} bytes.
Its SHA256 is {public['sha256']}.
All heavy checks run serially with memory.max/high=4294967296 and swap=0.

The first RecursiveBase strict check found a missing included section
hypothesis. The correction explicitly includes related. Its failed source
and raw report are preserved. The earlier continuation proposal also remains.
Its simplified revision removes the unreachable diagnostic premise and
private helper. All final finite expansion drafts passed on their first check.

Exact drafts, failed checks, source review cuts, passing inputs, installed
sources, raw public readback and source commits are stored losslessly in
`restart-evidence/20261027-flat-recursive`. Its portable verify-evidence.py
checks payload hashes, decoded archives, literal source cuts, historical
source versions, installed sources and unchanged older document bytes.
Publication results are recorded outside the frozen temporary evidence area.

## Haskell repairs and remaining work

No Haskell source changed in this checkpoint. FINDINGS retains all existing
repair handoffs for external work. Main already includes the LPO fix and
later extraction fixes. Extraction progress and lexicographic starvation
remain open. This checkpoint supplies no new executable repair. Native
tests were not rerun for these Lean-only additions.

The largest remaining semantic task is recursive output soundness and
coverage. First classify actual stop-rule and done outputs. State their
assignment and original-language meaning. Compose the existing captured
rendering theorem only with its real discharge and residual-check gates.
Derive initial Canonical, semantic request Ranges and allocation histories
where those semantic consumers need them. Prove the pruning-policy contract.

Finite correspondence permits explicit exhaustion and unsupported stops.
It does not prove unbounded convergence, a complete search depth, existence
of every desired render, or acceptance of every emitted output. Concrete
solver behavior, physical Haskell containers, machine bounds and practical
resource limits also remain outside this result. Do not mark the goal complete.
'''
name = 'lean/notes-current-flat-recursive.md'
path = root / name
assert not path.exists()
path.write_text(note)
data = path.read_bytes()
documents.append(name)
records.append(dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
(area / 'document-paths.json').write_text(json.dumps(documents, indent=2) + '\n')
(area / 'document-validation.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(documents=len(documents), note_bytes=len(data), note_sha256=hashlib.sha256(data).hexdigest())))
