# Actual Required target-operand positive positions

Source-only review at 2026-10-21 03:01 CEST. The contracts below are proposed, not proved. Zero Lean jobs and zero public proof pairs belong to this package.

## New statement

Use the actual nonempty natural operand path index::path. Assume:

- literal requireAll(requiredFuel,requiredReadFuel,SelectedRequired.paths selected,originals,scanHeap) = done prepared preparedHeap;
- scanHeap SemanticReady, UnionNormal, CostHeap, Values originals, and GuardHeap Plain;
- every class in selected has an ORIGINAL ClassTrace false from scanHeap to the same scanHeap;
- chosenClass belongs to selected, and index::path belongs to chosenClass;
- literal TargetWorker.operand projectionFuel readFuel mergeFuel selectionFuel ((index::path).map Int.ofNat) prepared before memo = done result after saved;
- before.native.machine.heap = preparedHeap;
- physical MemoMergeEffects.Stored at that entry and new MergePositivePosition.Support memo;
- PositiveAt result residual.

Derive Support saved and an original with originals[index]?=some original and PositiveAt original (path++residual). Keep the actual operand projection and Merge receipts if useful to the caller. The initial forest slot is the SAME fixed index. Do not return an unrelated slot. The forest index is not part of the residual value path in the conclusion.

This contract needs no native leaf or finite Cap premise. It is a direct actual Required/projection/Merge composition. Exact same entry heap as the Required return is explicit. A later operand on the SAME prepared forest can use a separate actual support/effect adapter. A class-edited phaseValues forest cannot be identified with prepared by this theorem.

The empty forest path is a different branch: Forest.root reads/unions all values, while the empty primary path returns false without checking each value. It has no one fixed-slot conclusion. Exclude it by construction through index::path.

## Not already covered

RequiredPositivePosition.origin transports all residual positive paths through Origin. RequiredForestPositive.requireAll derives same-slot Origin from actual original false class traces and the literal Required return. Those results do not prepend an actual projection path.

PositiveForestProjectionOrigins.project_read and RequiredProjectionOrigins.project_read recover Route/fields/ordered children for a selected output row with a NONPLAIN ROOT GUARD. They cannot be applied to a positive descendant under a plain parent row. PositiveAt.child imposes no positivity condition on its parent guard. A root-row adapter alone would miss that case.

RequiredTargetOperandOrigins.operand likewise consumes a positive root own payload and Raw memo history. It retains exact fields/All2 Origin children, but neither its premise nor its conclusion is the new all-position theorem. The new Merge Support endpoint covers descendants but must still be connected to the projected original path. No existing public theorem gives that complete connection.

## Minimal substantive projection proof

A useful intermediate endpoint is:

    Origin original prepared
    original NodeTrace at path is false at its genuine initial gate heap
    initial SemanticReady/UnionNormal/Available original
    current SemanticReady/CostHeap/Available prepared/GuardHeap Plain
    actual Project (path.map Int.ofNat) prepared before result after
    PositiveAt result residual
    ----------------------------------------------------------
    PositiveAt original (path++residual)

This endpoint must not assume a false gate on prepared. At path=[], use PositivePosition.origin. For a nonempty path, follow actual Project/ProjectRows and their read/union effects. Original false gates exclude nonplain recursive exposure, and Required Origin supplies exact fields plus ordered child origins. Missing child positions produce no positive result. Ordinary unions and node reconstruction retain the SAME residual child index while selecting an actual source row. Canonical row indices can differ.

One small implementation route reuses the old PRIVATE Safe/gate/Origin induction additively, but strengthens its private Accepted predicate. A row is relevant when its own guard is nonplain OR one of its ordered children has a PositiveAt occurrence. The plain accepted case must exclude both alternatives using the full cap-zero Edge result, including annotated children. Every Safe.root already certifies ALL endpoint rows, so its SourceRow/All2 child origins remain sufficient. The old Accepted predicate only tested nonplain guard and is the access/strength gap.

At the end, select the relevant literal row of the ordinary nonempty projection, map a descendant through All2 Origin using PositivePosition.origin, and prepend the natural path through Route. This needs no actual additional projection along residual: such a projection is not supplied and can fail on another row. No new future completion or whole-forest identity premise is permitted.

The old Safe/Accepted helpers are private. A new module must copy the necessary small basis, not import generated private names. Expected proof size is roughly 250–420 lines for a direct joint induction; copying the existing private basis verbatim can take about 450–550 lines. This is an access-boundary cost, not a second heap evaluator. At most two public heads are useful: the reusable joint project endpoint and the actual operand consumer. Avoid public wrapper types.

## Actual consumer and safety producer

Use RequiredPrimaryExposure.selected_domain on ORIGINAL false traces. Invert requireAll_execution_iff and apply RequiredRowOrigins.children to derive All2 Origin originals prepared. RequiredHeapEffects.requireAll derives prepared semantic/cost/availability and actual Keeps. RequiredGuard.requireAll/children derives GuardHeap Plain at preparedHeap. Do not infer ExposureSafe from Good or from semantic readiness alone.

Select the same original and prepared slot through All2_selected. RequiredPrimaryExposure.false_class_paths gives the ORIGINAL operand PathTrace from the chosen class trace. false_selected gives its exact original node trace. No extra caller exposure premise is needed beyond the stated actual original gate family and physical support facts.

Invert the literal operand using AllocatedTargetWorkerSound.bind_done and projection_sound. This gives the same Project/Forest, intermediate checked state, and unchanged pre-projection Merge memo. ProjectionCosts.forest_effects derives intermediate semantic/cost/availability and preserves physical Stored. Invert the actual merge worker equation and apply MergePositivePosition.allocated (canonical Top is plain by reduction). It derives Support saved and PositiveAt projected residual from PositiveAt result residual. Apply the new joint projection endpoint to get the original path++residual occurrence.

All original/prepared/current states remain explicit. RequiredPrimaryRetentionBoundary refutes a false-gate-on-prepared shortcut. No output equals original premise, historical writer re-selection, all-guards-plain premise, native interval History, rank or general outer completion follows. Chronological class folds still need their own source-path relation through changed phaseValues.
