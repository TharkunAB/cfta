# Current checked Scan global memos and selected required execution

Source main remains `8f85ddb6`. The preceding published checkpoint is
`ca0b8697`. Proof commits are `e715f34c`, `bc99fc26`, `2ce01ce2`, and
`aad5d624`. No Haskell implementation or test file changes.

## Actual current memo receipts

`SourceCurrentAllocatedNativeGlobalMemos` derives constructor event traces
for the actual checked step and physical Trace. Ordinary instructions reuse
their exact primitive execution. Checked edge publication and demand retain
the heap. The checked edge body changes equality operations without changing
the native heap. The complete checked trace therefore derives NoGlobal.
Its physical effects retain coherence of the same three global gate tables.
No old eager whole-engine execution substitutes for checked execution.

`SourceCurrentAllocatedSeededMemos` records the literal Forest projection
calls, the actual checked native trace, and the source head-projection,
tail-fold, native-query order. SeededReads retains `rest ++ [seed]`.
Initial physical invariants, selected support, and reached ranges derive
its final global table validity. Both query tables remain unchanged during
this fold. Earlier unfolding entries remain retained. No whole-forest
closedness or final table-validity premise is added.

`SourceCurrentConjunctionGlobalMemos` follows the CURRENT conjunction body.
Exposure, tuple filtering, equality allocation, generated requirements,
row-major projections, and the dynamic Worklist.Run retain their actual
order. Admitted work derives its closed resident projection inputs from
skip=false. Open and skipped work adds no call. Initial Ready and pending
availability derive all following physical inputs. The Boolean grow and
free-reference guard add no global call. A current fourth-memo hit skips
the body. A miss follows the actual current Decision before saving its
answer. Global unfolding entries are retained and both query tables stay
unchanged. This proof uses no historical emptiness Decision or Call.

`SourceCurrentConjunctionQueryGlobalMemos` connects actual secondary,
checked seeded, and current conjunction memo receipts. Its physical effects
retain the same full checked state and fourth memo. The actual query
completion and exact-state uniqueness derive its returned physical facts.

`SourceCurrentConjunctionClassScanGlobalMemos` follows all five actual
current Scan branches. Primary and secondary gates pass their returned
bundles to the next reached operation. Continued queries pass the actual
current call result to the next class. A stopped query needs no suffix
receipt or range plan. Initial global validity and reached ranges derive
final validity. The semantic verified endpoint uses the SAME Scan to derive
final Inventory.At and uniform original-class rejection soundness.

`SourceCurrentConjunctionAllocatedGlobalMemos.finite` derives its cold
native inventory laws, physical readiness, original values, proper paths,
and active classes from actual allocation History, source construction,
resident field lookup, and the live allocated precheck. The actual returned
precheck operations remain. Finite Scan, all global receipts, final At,
fourth-memo invariants, and stopped-class soundness are conclusions.
Initial legitimate global tables, fourth Correct, source History and origin
coverage, inherited stored readiness, and reached Ranges remain explicit.
This does not claim that production global caches start empty.

## Selected records and required execution

`SourceCurrentConjunctionSelectedRecords.Retained` follows original record
positions in the CURRENT checked Scan. Only a selected branch retains its
literal original head record. Order, duplicate occurrences, paths, and tries
are retained. The live accessor derives coherent ascending active fields.
No old Scan transfer or equality of equal-path record identities is assumed.

`SourceCurrentConjunctionRequired.selected_primary` replays each actual
selected primary certificate at the final Scan heap. Selected tip support
derives finite requireAll execution at that heap. Loaded fields use the
exact predicate FieldAvailable scanAfter.operations. Constructor effects
retain those fields in that same operation cache. They do not reset it or
replace it by normalized-only field coverage.

The Required Receipt exposes stable actual requireAll execution, final
Ready and At, physical Effects and machine Extension, the exact unchanged
native node and edge tables, domain cache, and equality operations. It
retains original and prepared Values. Every original selected path has a
closed projection domain in the prepared forest. The language is exactly
the original forest filtered by the required paths. Other original siblings
can remain open. No completed required worker is a public finite premise.

`SourceCurrentConjunctionRequiredGlobalMemos` consumes that derived stable
bound to obtain the literal done receipt. It derives RequireAllReads on the
same Scan-final heap and global bundle, final table validity, retained
unfolding entries, and unchanged global query tables during required work.
Its record endpoint retains the positional original selected records.

`SourceCurrentConjunctionAllocatedRequired.finite` constructs the Scan from
the actual live allocated entry. A stop retains the original-class refutation.
If its actual outcome is none, the result derives selected Retained records,
the required worker, all global receipts, final physical and input inventory
invariants, and fourth-memo Correct. The outcome condition is a source branch
case in the result. It supplies no future successful callback. Neither a
completed Scan nor completed requireAll is a premise.

## Validation and preservation

The pinned Lean 4.34.1 full Audit passes 2337 jobs and checks dependencies
of 56426 theorems. Only propext, Classical.choice, and Quot.sound occur.
Only the preexisting unused-input warning remains. Public axiom reports,
full signatures, kernel integrations, independent source reviews, and raw
logs are in restart-evidence/20261016-current-scan-memos/.

All 3712 starting files remain. All 2326 older non-Audit proof sources
retain identical bytes. All earlier frozen manifests, stashes, other worktree
records, and the root Haskell repair registry remain. Earlier unavailable
external drafts are not claimed recovered or reverified. Reuse unchanged
Haskell source validation: strict Nix build, 777 examples plus golden,
five-file Fourmolu, and four-package Cabal-gild.

## Next proof target

Port the actual shared class targets and edits to the CURRENT checked state.
The older MemoDemandTarget Fold and SharedTargetLeaf use unchecked
SourceEqualityNativeScoped.Step. Their native state carries no current
live equality operations or Inventory.At. Their completed proofs therefore
do not establish checked class-edit execution. Preserve all those proofs.
Use InventoryState.query_complete for actual closed native intersections,
and retain the returned inventory, physical effects, and global receipts.
Capture the forest returned by the preceding tail in the actual class fold.
Keep target slots and the merge memo distinct. Other original siblings may
remain open.

Merged edges also need FieldAvailable for their actual same-cache guard.
Top is not an unconditional old-cache field premise. Derive its field from
actual empty-field allocation only on branches that allocate it. Memo hits
and small groups must retain their literal source branches. Read
restart-evidence/20261016-current-scan-memos/next-class-edit-boundary.md
for exact source and theorem paths.

Then compose the class pass, final empty propagation, inherited constraints,
and the general constrained outer caller. Derive remaining recursive
completion and progress obligations from actual execution.

Every other full-library and separate Sized contract stays active. The
explicit-map Sized algorithmic contract is already proved. Newer frontend
adapters, runtime-family wiring, concrete containers, GHC forcing and memo
publication, allocation order, concurrency, machine capacity, solver IO,
random draws, and codecs retain explicit boundaries. Keep the optimized
interned core and all older constructor and equality work. The full goal
remains active. This checkpoint is verified progress.
