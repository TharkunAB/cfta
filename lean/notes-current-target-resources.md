# Initial Target resources and universal reached capacity

Updated: 2026-10-16. Audited main is `c0cc8a05`, merged at `896b0a1c`.
This checkpoint starts at published `db01dbc3` on `formalize`.
Proof commits are `41da8919`, `9602c246`, and `8a66a2be`.
Root FINDINGS keeps the external Haskell repair handoff first.

## Full objective and current boundary

Prove that the current Haskell library implements its intended constrained
tree languages and generators. Each public operation must satisfy its
contract on its stated domain. Finite operations must construct terminating
executions. Keep solver, callback, codec, machine, and host assumptions explicit.
There is no completed whole-library theorem.

Keep language, transformation, exact size, count, enumeration order, both
rank inverses, generator multiplicity, and probability contracts separate.
Exact ranks use the original sorted explicit graph rows. Keep the optimized
interned core and the older constructor and equality proof targets.
Read `notes-current-merge-reservations.md` for the wider proof map.
Its open Target constructor resource stage is closed by this checkpoint.

## Constructed Target execution

Six additive modules extend the checked Operand resource proof.
OperandNativeStores proves that the same complete operand receipt retains
both native certificate families and idle cells. Its native result tables
stay equal to the original tables. The actual Merge retains its profile table.

QueryWorkTrace follows the actual checked yielded Steps. Each Work records
its exact job, initial heap, result heap, and observed requests. Other
supported instructions preserve the entire constructor heap. The returned
journal is exactly requestsThrough for that checked prefix. Equality-field
operations can change their separate operation state.

TargetQueryResources derives word ranges from initial supply bounds.
It constructs one full query receipt. The same actual checked trace derives
the result profile, both height bounds, native certificate families,
constructor Work trace, request bounds, and final supplies. No future
profile, returned capacity, or completed query is an initial premise.

For original forest limits R,A,C,D,H, let Q be the Operand output row
envelope and B = max(A,1). Let O_N and O_E be the Operand request bounds.
The seed-only fold has row bound Q and costs O_N,O_E. Each added operand
uses the following recurrences, with the original forest retained:

```
T(0) = Q
T(k+1) = max(Q,T(k)) * max(Q,T(k))
F_N(0) = O_N
F_E(0) = O_E
F_N(k+1) = O_N + F_N(k) + NativeN(max(Q,T(k)),B,H)
F_E(k+1) = O_E + F_E(k) + NativeN(max(Q,T(k)),B,H)
```

The native bound counts all constructor Work. Each supply uses that
conservative bound separately. TargetBudgetNumbers proves monotonicity
in every original limit and in the number of added operands.

TargetResources.fold_complete constructs the head Operand, the tail fold,
and their checked intersection in that order. Each stage uses the preceding
actual state, saved Merge table, inventory, and global memo bundle.
Actual prefix supplies and the initial total headroom derive tail and query
headroom internally. All Work traces join at their literal intermediate heaps.

TargetResources.target_complete includes an empty Target with zero requests
and the unchanged complete state. A nonempty Target uses one seed plus the
remaining paths. The result contains its own actual Target, stable literal
worker execution, TargetReads, full existing Receipt, stored certificates,
output profile, height bound, Work trace, and final supply capacity.
The receipt retains its existing proper-path common-subtree inclusion.
This is not unconditional exact language equality for Target.

## Existing capacity plan discharged

TargetInitialCapacity first proves uniqueness of stable literal returns.
It identifies every returned value, complete checked state, and Merge table.
Each raw completed Operand and Fold derives such stable execution.

The initial resource theorem constructs an Operand and a shorter tail.
Uniqueness identifies any raw completed prefix with those same returns.
Induction on the remaining paths therefore derives the existing universal
FoldCapacity and TargetCapacity. Neither plan is an initial assumption.
This covers all raw earlier prefixes in those plans, not one selected run.
The existing Target word-range adapter can consume the derived plan.

The complete outer root still takes its numeric reached-parent plan.
Target is one stage of that root. Next compose shared edits, class passes,
local calls, parent calls, and outer recursive calls. Derive their generated
profiles and cumulative resources from initial inputs. Other resource
families, general Mu/reference/union progress, repeated-pass convergence,
current frontend adapters, concrete Haskell, and full-pipeline composition
remain open. The full-library goal stays active.

The next shared-target stage needs certificates for actual memo slots.
One class computes at most one target per distinct path. Every reached
leaf occurrence still runs its native query. Empty leaves count as such
occurrences. The earlier ordinary constructor-occurrence count omits Empty
and cannot alone bound those queries. Read `next-edits-resources.md` in
the evidence directory before extending the numeric plan.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2599 jobs and 60278 dependency checks.
All 47 declared public axiom/full-signature pairs and 13 integration pairs
pass. Component kernels
include two constructed full queries and two constructed three-path Targets.
Their second calls use only initial total headroom and first returned facts.
The capacity kernel checks the old universal plan and word-range adapter.
Only propext, Classical.choice, and Quot.sound occur. Final imported probes
have no diagnostics or placeholders. The old unused-input dependency
warning remains. Independent reviews retain the exact proof and host boundaries.

Preservation retains 7315 starting files and 2592 older non-Audit sources.
Forty-five frozen manifests check 356 module entries. All 234 starting
Haskell files retain their bytes. Older repairs, counterexamples, drafts,
stashes, other worktrees, and the optimized interned core remain.
Evidence is in `lean/restart-evidence/20261016-constrained-target-resources/`.

No Haskell change or new verified Haskell defect. Repair `b9219b9e` is
merged by PR #65. The original Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pool
behavior. Root FINDINGS records its failure, reproducer, affected paths,
commit, checks, and upstream status. Record every later Haskell repair there.
