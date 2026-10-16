import MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning
open MicroCFTA Cache Language BinderLanguage InternedBinderProtocol
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativeNodeRowsMeaning
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.row_forest
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.node_language
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.node_rank
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.joined_inputs
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.common_pair
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.rows_law
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.Walk.actual
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.Walk.effects
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.rows_trace
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.rows_body
#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.ordinary_body
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.row_forest
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.node_language
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.node_rank
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.joined_inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.common_pair
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.rows_law
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.Walk.actual
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.Walk.effects
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.rows_trace
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.rows_body
#check @MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning.ordinary_body

namespace NodeRowsChecks
noncomputable section
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local instance : DecidableEq Symbol := Classical.typeDecidableEq _
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

-- 1. Physical row copying retains each child's position.
example (holds : Guard → Term Symbol → Bool) (relation : IntersectSchedule.Input → Term Symbol → Prop)
    (edge : EdgeValue Symbol Guard) (terms : List (Term Symbol))
    (accepted : All₂ relation (row holds edge).children terms) :
    All₂ (fun child term => relation (inputOf child) term) edge.children terms :=
  (row_forest holds relation edge terms).mp accepted

-- 2. A common ranked row term derives actual hash-join membership.
example (holds : Guard → Term Symbol → Bool) (ranks : Nat → Nat → Lang Symbol)
    (left right : EdgeValue Symbol Guard) (term : Term Symbol)
    (accepted : RowAt holds ranks 2 left term ∧ RowAt holds ranks 3 right term) :
    (left, right) ∈ SourceRecursiveIntersectionKernel.pairs [left] [right] :=
  common_pair holds ranks [left] [right] left right (by simp) (by simp) 2 3 term accepted

-- 3. Different labels cannot enter the actual row join.
example (left right : EdgeValue Symbol Guard) (different : left.entry.key.symbol ≠ right.entry.key.symbol) :
    (left, right) ∉ SourceRecursiveIntersectionKernel.pairs [left] [right] := by
  intro member
  exact different ((SourceRecursiveIntersectionKernel.pairs_member [left] [right] (left, right)).mp member).2.2

-- 4. The source right bucket is traversed in its literal reversed order.
example (left first second : EdgeValue Symbol Guard)
    (firstSymbol : left.entry.key.symbol = first.entry.key.symbol)
    (secondSymbol : left.entry.key.symbol = second.entry.key.symbol) :
    SourceRecursiveIntersectionKernel.pairs [left] [first, second] = [(left, second), (left, first)] := by
  have same : first.entry.key.symbol = second.entry.key.symbol := firstSymbol.symm.trans secondSymbol
  simp [SourceRecursiveIntersectionKernel.pairs, SymbolicHashJoin.hashJoin_exact, firstSymbol, same]

-- 5. Duplicate matching rows retain all four actual request occurrences.
example (edge : EdgeValue Symbol Guard) :
    (SourceRecursiveIntersectionKernel.pairs [edge, edge] [edge, edge]).length = 4 := by
  simp [SourceRecursiveIntersectionKernel.pairs, SymbolicHashJoin.hashJoin_length]

-- 6. An empty actual row walk derives its own final effects.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : SourceEqualityNativeDemand.State 8)
    (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap) :
    SourceEqualityRequiredCache.Keeps state.native.machine.heap state.native.machine.heap ∧
      InternedNestedProvenance.Edges state.native.machine.heap [] ∧
      All₂ (fun (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) edge => EdgeLaw view model ranked holds
        ⟨domain, pair.1, pair.2⟩ edge) [] [] :=
  (Walk.nil state : Walk view model ranked holds domain [] state [] state 0).effects ready

-- 7. A singleton row walk uses exactly one actual local edge trace.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) (before middle : SourceEqualityNativeDemand.State 8)
    (edge : EdgeValue Symbol Guard) (fuel : Nat)
    (trace : Steps fuel (.code (requestEdge domain pair.1 pair.2)) before (.code (.pure edge)) middle)
    (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
    (resident : EdgeResident middle.native.machine.heap edge)
    (law : EdgeLaw view model ranked holds ⟨domain, pair.1, pair.2⟩ edge) :
    Walk view model ranked holds domain [pair] before [edge] middle (fuel + 0) :=
  .cons pair [] before middle middle edge [] fuel 0 trace keeps resident law (.nil middle)

-- 8. No matched rows means only the literal final node constructor is executed.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : SourceEqualityNativeDemand.State 8) :
    let built := run (makeNode []) state.native.machine.heap
    Steps 1 (.code (compileRows domain [] [])) state (.code (.pure built.1))
      {state with native := advance state.native {state.native.machine with heap := built.2}} :=
  rows_trace domain [] [] state state [] 0
    (by simpa [SourceRecursiveIntersectionKernel.pairs, SymbolicHashJoin.hashJoin] using
      (Walk.nil state : Walk view model ranked holds domain [] state [] state 0))

-- 9. Empty rows complete with the exact unchanged operation and native states.
example (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (state : SourceEqualityNativeDemand.State 8) :
    execute 2 (.code (compileRows domain [] [])) state = .done .empty state := by
  simp [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, SourceEqualityNativeDemand.lift,
    SourceRecursiveIntersectionNative.step, compileRows, SourceRecursiveIntersectionKernel.pairs,
    SymbolicHashJoin.hashJoin, SourceRecursiveIntersectionCode.walk, Code.bind,
    makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, InternedConstructorTemplates.run,
    SourceRecursiveIntersectionThunks.advance]

-- 10. An empty row body derives its parent law without any recursive edge assumption.
example (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (first second : Interned InternedBinderProtocol.NodeKey) (depth : Nat) (free : List Reference)
    (leftAvailable : Available source (.node first [] depth free))
    (rightAvailable : Available source (.node second [] depth free))
    (state : SourceEqualityNativeDemand.State 8) (ready : SourceEqualityRequiredCache.Ready state.native.machine.heap) :
    NodeLaw (view source holds) model ranked holds ⟨domain, .node first [] depth free, .node second [] depth free⟩ .empty := by
  have parent := (rows_body source facts holds model ranked domain first [] depth free second [] depth free leftAvailable rightAvailable
    state state [] 0 ready (by simpa [SourceRecursiveIntersectionKernel.pairs, SymbolicHashJoin.hashJoin] using
      (Walk.nil state : Walk (view source holds) model ranked holds domain [] state [] state 0))).2.1
  simpa [makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, InternedConstructorTemplates.run] using parent
end
end NodeRowsChecks
