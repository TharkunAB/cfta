# Main Prefix integration: complete restart evidence

Source `9f17b74c13f66e363545ce7e9c60e14bb878f599`. Documentation `3957889e073be56874525be26a965741a8f7caa2`.
The full formalization objective remains ACTIVE on formalize.
Every sealed regular file is archived without a filter.
The manifest binds all 1,145 paths, byte counts and hashes.
Raw bytes: 47,438,827.
Compressed bytes: 11,132,201.
SHA256: `fc466fe8a06d43d6debbcc4525ae722ac896ab05a16953e3324499e0aad5b7f8`.

Verify or reconstruct from the repository root:

```sh
python3 lean/restart-evidence/20261030-main-prefix-integration/verify.py lean/restart-evidence/20261030-main-prefix-integration --extract /tmp/mcfta-main-prefix-integration-restored
```

Use a fresh destination. Omit --extract to verify only. The standard-library
verifier rejects duplicate, missing, extra, unsafe and non-regular members.
It executes no Lean or Haskell code. Keep reconstructed evidence immutable.
Continue in a new writable area. The original source area is sealed read-only.
The failed host-linker attempt and every source-only control plan remain.
Four inherited strict checks match unchanged Lean inputs. All95 native command
snapshots match the integrated sources. No new Lean theorem was added.
The note below states the result, admissions, failures and remaining gaps.

---

# Main Prefix integration and next model-independent control proof

Checkpoint2026-10-30. Source 9f17b74c13f66e363545ce7e9c60e14bb878f599 on formalize.
Integrated main bd5a406a6a3f84b7e3ae0906082783911509df83 with a normal merge. The full goal remains ACTIVE.

## Current result and full objective

The new public Prefix API and sized counting routes are integrated and tested.
This is a Haskell integration checkpoint. It adds no checked Lean theorem.
Every4675 existing Lean source and all476 protected identities remain exact.
The prior Audit result remains4675 jobs and82394 theorem axiom checks.
The prior public readback remains984 declarations and79 definitions.
Four inherited strict sources match current bytes exactly. The Lean toolchain
also remains exact. No Lean check was repeated without a changed input.

Conditional rendered soundness, proper dependency storage, exact local native
resource results, constructor progress and actual callback progress remain.
The chosen accepting extension survives constructor selection and recording,
with the full Packet, ProperState and strict original pendingSize bound.
Existing finite-round construction/pruning language results also remain.
They do not establish a convergence bound or withoutRedundantEdges.

The full objective retains soundness and intended finite-value coverage from
public inputs, original control and resources, unfolding, configured exact order
and partial stops, the optimized interned core and Haskell correspondence.
Keep exact accepted terms per node-count size and both rank/unrank inverse laws.
The new public APIs require correspondence proofs. Passing Haskell tests and
unchanged Lean files do not supply those proofs.

## Integrated behavior

Main PR102 adds Data.CFTA.Sized.Prefix and Prefix.QuickCheck.
A token is a term node's symbol and arity in preorder. It is not a subword token.
The API counts, lists, ranks and unranks completions within a node-size bound.
It offers next tokens, rejects impossible continuations and identifies complete
prefixes. The solver route retains Yes/No/Unknown. Unknown tokens are withheld
from offered tokens unless some completion is accepted. A Deciding walk caches
verdicts and asks only the questions required by the current prefix.
Symbol weights are nonnegative Rationals. A term's weight is their product.
The weight and sampling APIs operate on accepted completions.

Unconstrained rows use a count-table prefix index. Ambiguous rows first use
bottom-up deterministic rows, within the stated state limit. Equality or
unsupported cases use the exact reference/listing route. The deciding equality
walk can switch from a bounded filling search to an exact-size restricted
automaton whose enumeration solves the equalities. Existing tests compare the
immediate-product, one-filling and default routes.

Sized also adds shared per-state indexes. It returns nonempty indexes for the
states reached from the supplied initial state. Unreachable states intentionally
return empty classes. Do not state agreement with independently rerooting at
an unreachable state.

The new fast count routes preserve accepted size classes. Their within-class
order can differ from sizedReference for ambiguous rows and equal children.
The unconstrained unambiguous route retains the reference sequence.
Both sized and sized-sample checkpoint route versions advance from1 to2.
A future correspondence theorem must use the selected route's actual order.
It must not infer order agreement from unordered set tests.

## Haskell corrections for external pickup

These changes are already incorporated from upstream. No additional local
Haskell patch or newly reproduced final-merge defect was needed.

- 9b5181980 counts distinct terms of ambiguous unconstrained rows through
  bottom-up determinization. Distinct deterministic state languages remove
  duplicate accepting runs before counting and ranking.
- 289b99818 builds the intersection of ALL child states in an equality group.
  It uses one term choice for that group. The term size is counted once for
  each child position. Counting, selection and ranking use the same grouped
  product. Existing fixtures cover unequal child-state languages, empty and
  productive intersections, joined classes and nonadjacent positions.
- Sized.Checkpoint advances both route versions to2. Serialization expectations
  and examples now retain the new version and reject older route positions.

The preceding formalize base used the reference route for ambiguous and
constrained rows. Do not report these fast-route corrections as a newly
reproduced wrong count in that old base.

The1024 limit bounds resulting deterministic states or intersection keys.
It does not bound the intermediate Cartesian-product work. Determinization
can construct a full round before checking the next state count. Intersection
construction can inspect rejected tuples before it reaches the row cap.
The code documents exponential construction. This is a resource-proof boundary,
not a confirmed correctness defect or a measured performance regression.

## Verification

All checks ran serially through heavy-management in nix-shell. Each measured
scope has4GiB memory.max/high and zero swap with a five-minute cap.
The fixed seed is20261030. The checks used upstream tests.
No additional local test was added.

- Sized/Prefix:185 examples, zero failures,12.6690 seconds.
- Other generator tests, excluding the already checked Sized groups:230
  examples, zero failures,62.8860 seconds.
- Serialization/checkpoints:56 examples, zero failures,1.7029 seconds.
- Fourmolu0.20.1.0 checks all12 changed Haskell files. Cabal-gild1.8.4.2
  checks the changed generator Cabal file. Both pass.

The first Sized attempt ran no tests because the host linker could not find
-lgmp. Retain that failed log. The documented explicit library directory fixes
the environment:
/nix/store/szvrzng4wfxc9xljqjipxhrrayjfy0vj-gmp-6.3.0/lib
This is an environment correction, not a Haskell source repair.
The successful Cabal commands use --offline -j1 --test-show-details=direct and
--extra-lib-dirs with that directory. Exact argv, raw output and measured limits
remain in each run's command/report files.
Five native commands retain four passes and one environment failure.
All95 input snapshots verify. All831 premerge Haskell paths remain. Nine change
through the reviewed upstream merge,822 remain exact, and four new Haskell
modules/tests give the new835-input baseline. The entire optimized cfta core
is unchanged by this merge. Keep final-haskell.json as the new native baseline.

## Next proof: exact model-independent parked progress

The strongest immediate target is an append-only strengthening of actual parked
selection and restart. Use the existing measure, without a new count definition:

(EnumerationIndexSelection.candidates state).length

candidates is the allocated range filtered by the maintained expandable flag.
SourcePruningEnumerationSelection.offered already derives the original selected
index's bound and true flag from the producer's original .expand selection.
Ready alone does not derive that cached flag. Do not add a new top-level flag
or semantic-model assumption.

Reuse the SAME witnesses from ParkedRestart.selected_complete_with_order.
Its actual indexed-write receipt, decoded boundary, unchanged counter and
framing give exact off-slot flags. The proposed equation is:

after.candidates.length + 1 = before.candidates.length

This equation is NOT YET a checked new theorem. It is the next Root proof.
Use the existing full receipt once. Do not call two producers and equate their
existential caches. Follow the old selected_complete_with_restart proof to
retain every stop/order/metadata result, including its empty stuck case.
Complete source-only strengthened contracts are in
control-research/neutral-control/STRONGER_STATEMENTS.md.

The equation bounds a consecutive parked-only chain. It does not telescope
across siblings that reset the captured cache. Ordinary constructor and opaque
continuations still need a model-independent rank for unproductive branches.
The checked SourceEqualityPartialHeightBoundary.actual_heights example gives
(parent,original child,narrowed child)=(2,1,3). Native equality narrowing can
raise ordinary height. This rejects the naive original-parent height measure;
it does not establish nontermination, a coverage failure or a Haskell defect.
Keep Recursive and PreparedRecursive distinct when composing later control.

## Path-carrier proof after parked progress

The fixed-capacity forecast still suggests an original carrier P_D.
Path transport requires suffix closure and the actual projections of forecasted
conjoined guards. It needs no accepting term or trie Valid premise.
The next local interface can use HeadAdmission: its original stored slot gives
the inherited bucket, and its physical edge residency plus known annotation
heap puts the selected guard in the supplied original forecast.
CachedOwn.prepare allocates empty buckets and installs only projected tries.
Descended paths come from index::suffix even for an arbitrary trie.

The full proposed HeadAdmission.prepare_paths_of_forecast statement and writer
proof plan are in control-research/path-forecast/REPORT.md. The all-state proof
must cover stopped child candidates, empty-output callbacks and restart inputs.
Attach the path certificate at the actual head producer before filtering outputs.
ReceiptAt retains each processed head's precise stage forecast. Rich callback
history wrappers hide headSeed and retain rich histories only for outputs.
They are insufficient for the all-state claim by themselves.

Even complete transport in P_D does not prove a sufficient D exists. P_D still
depends on D. A uniform carrier or independent decreasing measure remains open.
The earlier suffix-only concrete draft remains failed/unproved in the previous
archive. It is not a checked full counterexample. Preserve all draft labels.

## Remaining full-system gaps

Uniform original control for earlier incompatible/unproductive branches and
neutral work remains the largest gap. A chosen finite model ranks its own
productive path. It does not rank every earlier alternative.
Recursive fuel uses1+max of continuation bounds across siblings. Native resources
compose in actual stage order. Configured stopping returns complete partial
output and permits later siblings. An earlier stopped hook is operational
failure; it stops the suffix and retains earlier output.
Initial_boundary_done still leaves recursive placeholders. DONE is not Discharged.
Unfolding/public finite-value coverage, exact public order/stops and Haskell
correspondence remain open. The new Prefix, determinization, intersection-table,
weighted grouping, prefix-index and sampling routes add explicit correspondence
obligations. No admitted all-capacity counterexample was established.

## Evidence and restart

Evidence area:/tmp/mcfta-main-prefix-integration-20261030/
Repository archive:lean/restart-evidence/20261030-main-prefix-integration/
Reconstruction:/tmp/mcfta-main-prefix-integration-restored-20261030/
The archive retains every sealed regular payload without filtering.
It includes all three complete frozen reports,105 pinned review payloads,
84 source scopes,6 recorded Root scopes and5 complete upstream diffs.
Root read all three reports and verified every scope and pin.
Count review covers the entire658-line Table in four bounded cuts. Sized and
tests remain scoped. Root reviewed selected Prefix construction, query, walk,
product, weight and memo bodies; its initial combined display was truncated
near the imports. No whole Prefix source review is claimed. Existing tests
supply the runtime evidence. Both control reports are source-only.
Path review conservatively uses2/4 whole-source equivalents; neutral review
uses4/4 old whole sources. All acquisition limits/corrections remain explicit.

control-research contains the complete frozen preceding investigation area.
Its831-path Haskell baseline is PREMERGE history. Use the enclosing835-input
final native manifest after integration. No Root Lean command ran in that
control investigation. Keep all source-only plans and failed old probes.
Continue in a fresh writable area. Do not alter sealed or reconstructed trees.
Pull formalize and fetch main before new work. Push remains explicitly authorized
for git@github.com:TharkunAB/cfta.git refs/heads/formalize. No force push.
The full goal remains ACTIVE; this checkpoint is not completion or a pause.
