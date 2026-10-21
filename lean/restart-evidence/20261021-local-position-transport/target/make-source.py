from pathlib import Path
root=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
out=Path('/tmp/mcfta-target-operand-positive-position-proof/SourceCurrentTargetOperandPositivePosition.lean')
s=(root/'SourceCurrentRequiredProjectionOrigins.lean').read_text()
s=s[:s.index('/-- A later read of an actual prepared projection')]
s=s.replace('MicroCFTA.SourceCurrentRequiredProjectionOrigins','MicroCFTA.SourceCurrentTargetOperandPositivePosition')
s=s[s.index('namespace '):]
imports='''import MicroCFTA.SourceCurrentRequiredProjectionOrigins
import MicroCFTA.SourceCurrentRequiredForestPositive
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceCurrentRequiredGuard
import MicroCFTA.SourceCurrentMergePositivePosition
import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound

'''
s=imports+s
s=s.replace('open SourceCurrentRequiredRowOrigins (Origin RowMap ChildMap)','open SourceCurrentRequiredRowOrigins (Origin RowMap ChildMap)\nopen SourceCurrentRequiredPositivePosition (PositiveAt)')
pure='''private def RowPosition (row : Row) : List Nat → Prop
  | [] => SourceMemoGate.plain row.entry.key.constraint = false
  | index :: path => ∃ child, row.children[index]? = some child ∧ PositiveAt child path

private def Relevant (row : Row) : Prop := ∃ path, RowPosition row path

private theorem row_origin_position {original row : Row} {path : List Nat}
    (fields : RowOrigin original row) (children : All₂ Origin original.children row.children)
    (positive : RowPosition row path) : RowPosition original path := by
  cases path with
  | nil => simpa only [RowPosition, fields.1] using positive
  | cons index path =>
    obtain ⟨child, found, positive⟩ := positive
    obtain ⟨sourceChild, sourceFound, related⟩ :=
      SourceEqualityProjectionLanguage.all₂_selected children index child found
    exact ⟨sourceChild, sourceFound, SourceCurrentRequiredPositivePosition.origin related positive⟩

private theorem route_position (path : List Nat) {value : Node} {row : Row} {residual : List Nat}
    (route : Route (path.map Int.ofNat) value row) (positive : RowPosition row residual) :
    PositiveAt value (path ++ residual) := by
  induction path generalizing value with
  | nil =>
    cases route with
    | root entry rows depth free position row found =>
      cases residual with
      | nil => exact .root position row found positive
      | cons index rest =>
        obtain ⟨child, chosen, positive⟩ := positive
        exact .child position index row child found chosen positive
  | cons index path ih =>
    cases route with
    | child entry rows depth free position sourceRow found signed child chosen rest =>
      have natural : sourceRow.children[index]? = some child := by
        simpa only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using chosen
      exact .child position index sourceRow child found natural (ih rest positive)

'''
s=s.replace('section Actual\n',pure+'section Actual\n')
s=s.replace('¬ Plain row.entry.key.constraint → accept row','Relevant row → accept row')
s=s.replace('    exact False.elim (positive ((bounded.2 row member).1))','''    obtain ⟨path, positive⟩ := positive
    cases path with
    | nil =>
      have plain := (bounded.2 row member).1
      rw [show SourceMemoGate.plain row.entry.key.constraint = false from positive] at plain
      cases plain
    | cons index path =>
      obtain ⟨child, chosen, positive⟩ := positive
      exact False.elim (SourceCurrentRequiredPositivePosition.not_plain positive
        ((bounded.2 row member).2 child (List.mem_of_getElem? chosen)))''')
ordinary=(root/'SourceCurrentPositiveForestProjectionOrigins.lean').read_text()
ordinary=ordinary[ordinary.index('private theorem union_ordinary'):ordinary.index('/-- A positive actual row read')]
s+='\n'+ordinary
s+='''/-- A positive prepared projection retains the original natural child path. -/
theorem project (path : List Nat) (original prepared : Node)
    (gateBefore gateAfter before after : Heap) (result : Node)
    (origin : Origin original prepared)
    (gate : NodeTrace source reaches path original gateBefore false gateAfter)
    (initialSemantic : SemanticReady gateBefore)
    (initialNormal : SourceCurrentRequiredUnionNormal.UnionNormal gateBefore)
    (initialAvailable : Available gateBefore original)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before prepared)
    (guards : Guards before) (actual : Project (path.map Int.ofNat) prepared before result after)
    {residual : List Nat} (positive : PositiveAt result residual) :
    PositiveAt original (path ++ residual) := by
  cases path with
  | nil =>
    cases actual
    exact SourceCurrentRequiredPositivePosition.origin origin positive
  | cons index path =>
    have safe := safe_gate (index :: path) original gateBefore gateBefore gateAfter initialSemantic initialNormal
      initialAvailable initialSemantic initialAvailable gate
    have preparedSafe := safe_origin safe origin
    have accepted := project_origins.1 _ _ _ _ _ actual _ semantic costs available guards preparedSafe
    have effects := SourceEqualityProjectionCosts.project_effects actual semantic costs available
    have finalGuards := SourceCurrentConstrainedCapProjectionGuard.node Plain actual semantic costs available guards
    have ordinary := project_ordinary actual semantic costs available (by simp)
    cases positive with
    | root rowIndex row selected nonplain =>
      obtain ⟨sourceRow, route, fields, children⟩ :=
        accepted after _ after (.done 0 rfl) effects.2.1 effects.2.2.2 finalGuards row
          (List.mem_of_getElem? selected) ⟨[], nonplain⟩
      exact route_position (index :: path) route (row_origin_position fields children nonplain)
    | child rowIndex childIndex row child selected chosen rest =>
      obtain ⟨sourceRow, route, fields, children⟩ :=
        accepted after _ after (.done 0 rfl) effects.2.1 effects.2.2.2 finalGuards row
          (List.mem_of_getElem? selected) ⟨childIndex :: _, child, chosen, rest⟩
      exact route_position (index :: path) route
        (row_origin_position fields children ⟨child, chosen, rest⟩)
    | member => cases ordinary

end Actual

open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentMergePositivePosition (Support)

/-- An actual Required and target operand return retains its fixed original slot and full positive path. -/
theorem operand [symbolEq : DecidableEq Symbol] [edgeEq : DecidableEq (EdgeKey Symbol Guard)]
    {width requiredFuel requiredReadFuel projectionFuel readFuel mergeFuel selectionFuel : Nat}
    {selected : EqualityNormalize.Constraints} {originals prepared : List Node}
    {scanHeap preparedHeap : Heap} {index : Nat} {path residual : List Nat}
    {chosenClass : EqualityNormalize.Class}
    {before after : SourceEqualityNativeDemand.State width}
    {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard} {result : Node}
    (required : SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel
      (SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap)
    (semantic : SemanticReady scanHeap) (normal : SourceCurrentRequiredUnionNormal.UnionNormal scanHeap)
    (costs : CostHeap scanHeap) (available : Values scanHeap originals) (guards : Guards scanHeap)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap)
    (chosen : chosenClass ∈ selected) (included : index :: path ∈ chosenClass)
    (sameHeap : before.native.machine.heap = preparedHeap)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (support : Support memo)
    (actual : SourceCurrentAllocatedTargetWorker.operand projectionFuel readFuel mergeFuel selectionFuel
      ((index :: path).map Int.ofNat) prepared before memo = .done result after saved)
    (positive : PositiveAt result residual) :
    Support saved ∧ ∃ original, originals[index]? = some original ∧ PositiveAt original (path ++ residual) := by
  have sameEdge : edgeEq = SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint :=
    Subsingleton.elim _ _
  cases sameEdge
  letI : DecidableEq (EdgeKey Symbol Guard) :=
    SourceCurrentRequiredPrimaryExposure.instDecidableEqEdgeKeyLabelFormulaConstraint
  have sameSymbol : symbolEq = @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
      instDecidableEqString FormulaExecutable.formulaDecidableEq := Subsingleton.elim _ _
  cases sameSymbol
  letI : DecidableEq Symbol := @instDecidableEqProd SourceGuards.Name FullSyntax.Formula
    instDecidableEqString FormulaExecutable.formulaDecidableEq
  have requiredEffects := SourceCurrentRequiredHeapEffects.requireAll (fun _ => True)
    requiredFuel requiredReadFuel (SourceEqualitySelectedRequired.paths selected) originals prepared scanHeap preparedHeap
    required semantic costs (fun _ _ _ => trivial) available
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff
    (SourceEqualitySelectedRequired.paths selected) originals scanHeap prepared preparedHeap).mpr
      ⟨requiredFuel, requiredReadFuel, required⟩
  cases compiled : SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected) with
  | node entries =>
    simp only [compiled] at graph
    have domain := SourceCurrentRequiredPrimaryExposure.selected_domain originals selected scanHeap
      semantic normal available primary entries compiled
    have safe : SourceCurrentRequiredRowOrigins.ChildrenSafe entries 0 originals := by
      intro offset needed selectedNeeded value atOffset
      exact domain offset needed (by simpa only [Nat.zero_add] using selectedNeeded) value atOffset
    have related : All₂ Origin originals prepared :=
      SourceCurrentRequiredRowOrigins.children graph semantic costs available guards safe
    have preparedGuards := SourceCurrentRequiredGuard.children Plain graph semantic costs available guards
    obtain ⟨projected,middle,current,projectionDone,mergeDone⟩ :=
      (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    obtain ⟨heap,forest,shape,sameMemo⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound
      projectionFuel readFuel ((index :: path).map Int.ofNat) prepared before memo projected middle current projectionDone
    subst current
    have beforeSemantic : SemanticReady before.native.machine.heap := sameHeap ▸ requiredEffects.2.1
    have beforeCosts : CostHeap before.native.machine.heap := sameHeap ▸ requiredEffects.2.2.1
    have beforeValues : Values before.native.machine.heap prepared := sameHeap ▸ requiredEffects.2.2.2.2
    have facts := SourceEqualityProjectionCosts.forest_effects forest beforeSemantic beforeCosts beforeValues
    have middleHeap : middle.native.machine.heap = heap := by rw [shape]; rfl
    have currentSemantic : SemanticReady middle.native.machine.heap := by simpa only [middleHeap] using facts.2.1
    have currentCosts : CostHeap middle.native.machine.heap := by simpa only [middleHeap] using facts.2.2.1
    have currentStored : SourceCurrentMemoMergeEffects.Stored middle.native.machine.heap memo := by
      simpa only [middleHeap] using stored.grows facts.1
    have currentAvailable : Available middle.native.machine.heap projected := by simpa only [middleHeap] using facts.2.2.2
    cases called : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear
        mergeFuel selectionFuel projected (physical middle) memo with
    | failed =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
    | done output final current =>
      simp only [SourceCurrentAllocatedTargetWorker.merge,called] at mergeDone
      cases mergeDone
      have merged := SourceCurrentMergePositivePosition.allocated SourceCurrentAllocatedMerge.literalClear called
        currentSemantic currentCosts currentStored support currentAvailable
      have projectedPositive := merged.2.2.2.2 residual positive
      refine ⟨merged.2.2.1, ?_⟩
      cases forest with
      | missing absent => cases projectedPositive
      | selected found actualProject =>
        have natural : prepared[index]? = some _ := by
          simpa only [select,Int.ofNat_eq_natCast,
            ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index)),Int.toNat_natCast] using found
        obtain ⟨original, originalFound, origin⟩ :=
          SourceEqualityProjectionLanguage.all₂_selected related index _ natural
        have gatePath := SourceCurrentRequiredPrimaryExposure.false_class_paths originals chosenClass scanHeap scanHeap
          (primary chosenClass chosen) semantic available scanHeap (grows_refl _) (index :: path) included
        have gate := SourceCurrentRequiredPrimaryExposure.false_selected gatePath originalFound
        refine ⟨original, originalFound, ?_⟩
        exact project path original _ scanHeap scanHeap before.native.machine.heap heap projected origin gate
          semantic normal (available _ (List.mem_of_getElem? originalFound)) beforeSemantic beforeCosts
          (beforeValues _ (select_member found)) (sameHeap ▸ preparedGuards) actualProject projectedPositive

end MicroCFTA.SourceCurrentTargetOperandPositivePosition
'''
out.write_text(s)
print(out, len(s.splitlines()))
