import MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
import MicroCFTA.InternedGuardedConstructors

/-!
# Contextual meaning of actual checked ordinary node rows

The original physical input view remains fixed while actual row requests
and the final node constructor grow the execution heap. Only the exact
ordered row requests supply local edge laws. Actual hash joining derives
the matching pairs and retains every common accepted original row.
This component does not supply recursive edge laws or a global finish plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning
open Cache Language BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open InternedBinderProtocol
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => EdgeValue Symbol Guard × EdgeValue Symbol Guard

private theorem member_left {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (related : All₂ R inputs outputs) (input : A) (present : input ∈ inputs) :
    ∃ output ∈ outputs, R input output := by
  induction related with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | tail
      · exact ⟨_, List.mem_cons_self, first⟩
      · obtain ⟨value, inside, law⟩ := ih tail
        exact ⟨value, List.mem_cons_of_mem _ inside, law⟩

private theorem member_right {R : A → B → Prop} {inputs : List A} {outputs : List B}
    (related : All₂ R inputs outputs) (output : B) (present : output ∈ outputs) :
    ∃ input ∈ inputs, R input output := by
  induction related with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | tail
      · exact ⟨_, List.mem_cons_self, first⟩
      · obtain ⟨value, inside, law⟩ := ih tail
        exact ⟨value, List.mem_cons_of_mem _ inside, law⟩

/-- Physical row copying retains the exact ordered independent child languages. -/
theorem row_forest (holds : Guard → Term Symbol → Bool)
    (relation : IntersectSchedule.Input → Term Symbol → Prop) (edge : EdgeValue Symbol Guard) (terms : List (Term Symbol)) :
    All₂ relation (row holds edge).children terms ↔ All₂ (fun child term => relation (inputOf child) term) edge.children terms :=
  SymbolicGraphView.all₂_map_iff relation inputOf edge.children terms

/-- Fixed original node language is exactly the language of its physical stored rows. -/
theorem node_language (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available source (.node entry edges depth free)) (valid : model.valid (.node entry.identity)) (term : Term Symbol) :
    IntersectSchedule.inputLanguage model.languages (inputOf (.node entry edges depth free)) term ↔
      ∃ edge ∈ edges, RowLanguage holds model.languages edge term := by
  change model.languages entry.identity term ↔ _
  rw [model.row_exact entry.identity valid term, rows_readback source facts holds entry edges depth free available]
  constructor
  · rintro ⟨_, present, terms, shape, forest, guard⟩
    obtain ⟨edge, inside, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, inside, terms, shape, (row_forest holds _ edge terms).mp forest, guard⟩
  · rintro ⟨edge, present, terms, shape, forest, guard⟩
    exact ⟨row holds edge, List.mem_map.mpr ⟨edge, present, rfl⟩, terms, shape,
      (row_forest holds _ edge terms).mpr forest, guard⟩

/-- Each original ranked node derivation selects one actual physical stored row. -/
theorem node_rank (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available source (.node entry edges depth free)) (valid : model.valid (.node entry.identity))
    (rank : Nat) (term : Term Symbol)
    (accepted : IntersectSchedule.inputAt ranked.languages (inputOf (.node entry edges depth free)) rank term) :
    ∃ edge ∈ edges, RowAt holds ranked.languages rank edge term := by
  obtain ⟨_, present, terms, shape, forest, guard⟩ := ranked.row entry.identity valid rank term accepted
  rw [rows_readback source facts holds entry edges depth free available] at present
  obtain ⟨edge, inside, rfl⟩ := List.mem_map.mp present
  exact ⟨edge, inside, terms, shape, (row_forest holds _ edge terms).mp forest, guard⟩

/-- An actual ordinary node pair supplies the original scope of every joined edge request. -/
theorem joined_inputs [DecidableEq Symbol]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (first : Interned InternedBinderProtocol.NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned InternedBinderProtocol.NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (leftAvailable : Available source (.node first left leftDepth leftFree))
    (rightAvailable : Available source (.node second right rightDepth rightFree))
    (inputs : NodeInputs (view source holds) model
      ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩)
    (pair : Pair) (member : pair ∈ pairs left right) :
    EdgeInputs (view source holds) model ⟨domain, pair.1, pair.2⟩ := by
  have inside := (SourceRecursiveIntersectionKernel.pairs_member left right pair).mp member
  constructor
  · intro child present
    have original : Original child := by
      cases inputs.1 with
      | node _ _ _ _ originals => exact originals pair.1 inside.1 child present
    refine ⟨original, model.row_valid first.identity inputs.2.2.1 (row holds pair.1) ?_ (inputOf child) ?_⟩
    · rw [rows_readback source facts holds first left leftDepth leftFree leftAvailable]
      exact List.mem_map.mpr ⟨pair.1, inside.1, rfl⟩
    · exact List.mem_map.mpr ⟨child, present, rfl⟩
  · intro child present
    have original : Original child := by
      cases inputs.2.1 with
      | node _ _ _ _ originals => exact originals pair.2 inside.2.1 child present
    refine ⟨original, model.row_valid second.identity inputs.2.2.2 (row holds pair.2) ?_ (inputOf child) ?_⟩
    · rw [rows_readback source facts holds second right rightDepth rightFree rightAvailable]
      exact List.mem_map.mpr ⟨pair.2, inside.2.1, rfl⟩
    · exact List.mem_map.mpr ⟨child, present, rfl⟩

/-- Common original row terms have matching symbols and occur in the actual hash join. -/
theorem common_pair [DecidableEq Symbol] (holds : Guard → Term Symbol → Bool) (ranks : Nat → Nat → Lang Symbol)
    (left right : List (EdgeValue Symbol Guard)) (first second : EdgeValue Symbol Guard)
    (firstMember : first ∈ left) (secondMember : second ∈ right) (a b : Nat) (term : Term Symbol)
    (accepted : RowAt holds ranks a first term ∧ RowAt holds ranks b second term) :
    (first, second) ∈ pairs left right := by
  obtain ⟨⟨_, firstShape, _, _⟩, ⟨_, secondShape, _, _⟩⟩ := accepted
  exact (SourceRecursiveIntersectionKernel.pairs_member left right (first, second)).mpr
    ⟨firstMember, secondMember, (Term.node.inj (firstShape.symm.trans secondShape)).1⟩

/-- Exact ordered edge laws and actual node normalization derive the ordinary parent law. -/
theorem rows_law [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (first : Interned InternedBinderProtocol.NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned InternedBinderProtocol.NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (leftAvailable : Available source (.node first left leftDepth leftFree))
    (rightAvailable : Available source (.node second right rightDepth rightFree))
    (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (values : List (EdgeValue Symbol Guard)) (resident : Edges state values)
    (laws : All₂ (fun pair value => EdgeLaw (view source holds) model ranked holds ⟨domain, pair.1, pair.2⟩ value)
      (pairs left right) values) :
    NodeLaw (view source holds) model ranked holds
      ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩ (run (makeNode values) state).1 := by
  constructor
  · intro inputs output sound term accepted
    obtain ⟨value, present, accepted⟩ := (InternedGuardedLanguage.makeNode_exact state facts holds output values resident term).mp accepted
    obtain ⟨pair, inside, law⟩ := member_right laws value present
    have childInputs := joined_inputs source sourceFacts holds model domain first left leftDepth leftFree
      second right rightDepth rightFree leftAvailable rightAvailable inputs pair inside
    have common := law.sound childInputs output sound term ((InternedGuardedLanguage.edgeMeaning_all holds output value term).mpr accepted)
    have joined := (SourceRecursiveIntersectionKernel.pairs_member left right pair).mp inside
    exact ⟨(node_language source sourceFacts holds model first left leftDepth leftFree leftAvailable inputs.2.2.1 term).mpr
      ⟨pair.1, joined.1, common.1⟩,
      (node_language source sourceFacts holds model second right rightDepth rightFree rightAvailable inputs.2.2.2 term).mpr
      ⟨pair.2, joined.2.1, common.2⟩⟩
  · intro inputs bound output complete a b bounded term firstAccepted secondAccepted
    obtain ⟨leftRow, inLeft, leftAccepted⟩ := node_rank source sourceFacts holds model ranked first left leftDepth leftFree
      leftAvailable inputs.2.2.1 a term firstAccepted
    obtain ⟨rightRow, inRight, rightAccepted⟩ := node_rank source sourceFacts holds model ranked second right rightDepth rightFree
      rightAvailable inputs.2.2.2 b term secondAccepted
    have joined := common_pair holds ranked.languages left right leftRow rightRow inLeft inRight a b term ⟨leftAccepted, rightAccepted⟩
    obtain ⟨value, present, law⟩ := member_left laws (leftRow, rightRow) joined
    have childInputs := joined_inputs source sourceFacts holds model domain first left leftDepth leftFree
      second right rightDepth rightFree leftAvailable rightAvailable inputs (leftRow, rightRow) joined
    apply (InternedGuardedLanguage.makeNode_exact state facts holds output values resident term).mpr
    exact ⟨value, present, (InternedGuardedLanguage.edgeMeaning_all holds output value term).mp
      (law.complete childInputs bound output complete a b bounded term leftAccepted rightAccepted)⟩

/-- A row walk retains only actual edge calls and their reached local receipts. -/
inductive Walk [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) :
    List Pair → SourceEqualityNativeDemand.State width → List (EdgeValue Symbol Guard) → SourceEqualityNativeDemand.State width → Nat → Prop where
  | nil (state) : Walk view model ranked holds domain [] state [] state 0
  | cons (pair : Pair) (rest) (before middle after : SourceEqualityNativeDemand.State width) (value values firstFuel restFuel)
      (called : Steps firstFuel (.code (requestEdge domain pair.1 pair.2)) before (.code (.pure value)) middle)
      (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap middle.native.machine.heap)
      (resident : EdgeResident middle.native.machine.heap value)
      (law : EdgeLaw view model ranked holds ⟨domain, pair.1, pair.2⟩ value)
      (tail : Walk view model ranked holds domain rest middle values after restFuel) :
      Walk view model ranked holds domain (pair :: rest) before (value :: values) after (firstFuel + restFuel)

/-- Erasing the local receipts preserves the literal checked row execution. -/
theorem Walk.actual [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {view : IntersectSchedule.View Symbol} {model : IntersectSchedule.InputMeaning view}
    {ranked : IntersectSchedule.RankedInput view model.valid} {holds : Guard → Term Symbol → Bool}
    {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey} {inputs : List Pair} {before after : SourceEqualityNativeDemand.State width}
    {values : List (EdgeValue Symbol Guard)} {fuel : Nat} (walk : Walk view model ranked holds domain inputs before values after fuel) :
    SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestEdge domain pair.1 pair.2) inputs before values after fuel := by
  induction walk with
  | nil state => exact .nil state
  | cons pair rest before middle after value values firstFuel restFuel called keeps resident law tail ih =>
      exact .cons pair rest before middle after value values firstFuel restFuel called ih

/-- Earlier returned edge records remain resident through the actual later row calls. -/
theorem Walk.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {view : IntersectSchedule.View Symbol} {model : IntersectSchedule.InputMeaning view}
    {ranked : IntersectSchedule.RankedInput view model.valid} {holds : Guard → Term Symbol → Bool}
    {domain : Interned IntersectionFlatMemoKeyDomain.DomainKey} {inputs : List Pair} {before after : SourceEqualityNativeDemand.State width}
    {values : List (EdgeValue Symbol Guard)} {fuel : Nat} (walk : Walk view model ranked holds domain inputs before values after fuel)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap) :
    SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧ Edges after.native.machine.heap values ∧
      All₂ (fun pair value => EdgeLaw view model ranked holds ⟨domain, pair.1, pair.2⟩ value) inputs values := by
  induction walk with
  | nil state => exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready, (by intro edge member; cases member), .nil⟩
  | cons pair rest before middle after value values firstFuel restFuel called keeps resident law tail ih =>
      have later := ih keeps.ready
      refine ⟨keeps.trans later.1, ?_, .cons law later.2.2⟩
      intro edge member
      cases member with
      | head => exact edge_grows _ _ later.1.growth value resident
      | tail _ member => exact later.2.1 edge member

/-- The actual ordered row walk precedes exactly one final source node constructor. -/
theorem rows_trace [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {view : IntersectSchedule.View Symbol} {model : IntersectSchedule.InputMeaning view}
    {ranked : IntersectSchedule.RankedInput view model.valid} {holds : Guard → Term Symbol → Bool}
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (left right : List (EdgeValue Symbol Guard))
    (before after : SourceEqualityNativeDemand.State width) (values : List (EdgeValue Symbol Guard)) (fuel : Nat)
    (walk : Walk view model ranked holds domain (pairs left right) before values after fuel) :
    let built := run (makeNode values) after.native.machine.heap
    Steps (fuel + 1) (.code (compileRows domain left right)) before (.code (.pure built.1))
      {after with native := advance after.native {after.native.machine with heap := built.2}} := by
  have first := walk.actual.trace.bind _ _ _ _ _ (fun values => .work (makeNode values) .pure)
  exact first.trans _ _ _ _ _ _ _ _ (.cons _ _ _ _ _ _ 0 rfl (.refl _ _))

/-- Completed actual row calls derive ordinary node execution, language, and physical availability. -/
theorem rows_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (first : Interned InternedBinderProtocol.NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned InternedBinderProtocol.NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (leftAvailable : Available source (.node first left leftDepth leftFree))
    (rightAvailable : Available source (.node second right rightDepth rightFree))
    (before middle : SourceEqualityNativeDemand.State width) (values : List (EdgeValue Symbol Guard)) (fuel : Nat)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (walk : Walk (view source holds) model ranked holds domain (pairs left right) before values middle fuel) :
    let built := run (makeNode values) middle.native.machine.heap
    let after : SourceEqualityNativeDemand.State width := {middle with native := advance middle.native {middle.native.machine with heap := built.2}}
    execute (fuel + 2) (.code (compileRows domain left right)) before = .done built.1 after ∧
      NodeLaw (view source holds) model ranked holds
        ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩ built.1 ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap built.1 := by
  have effects := walk.effects ready
  have constructor := SourceEqualityNativeDemandHeapPrimitives.node values middle.native.machine.heap effects.1.ready effects.2.1
  exact ⟨trace_done (fuel + 1) _ before _ _ (rows_trace domain left right before middle values fuel walk),
    rows_law source sourceFacts holds model ranked domain first left leftDepth leftFree second right rightDepth rightFree
      leftAvailable rightAvailable middle.native.machine.heap effects.1.ready.semantic.1.normal.facts values effects.2.1 effects.2.2,
    effects.1.trans constructor.1, constructor.2⟩

/-- The selected ordinary source branch executes the same literal rows and constructor. -/
theorem ordinary_body [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (sourceFacts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (first : Interned InternedBinderProtocol.NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned InternedBinderProtocol.NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (leftAvailable : Available source (.node first left leftDepth leftFree))
    (rightAvailable : Available source (.node second right rightDepth rightFree))
    (selected : SourceRecursiveIntersectionControl.decision domain.key
      (.node first left leftDepth leftFree) (.node second right rightDepth rightFree) = .ordinary)
    (before middle : SourceEqualityNativeDemand.State width) (values : List (EdgeValue Symbol Guard)) (fuel : Nat)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (walk : Walk (view source holds) model ranked holds domain (pairs left right) before values middle fuel) :
    let request : NodeRequest Symbol Guard := ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩
    let built := run (makeNode values) middle.native.machine.heap
    let after : SourceEqualityNativeDemand.State width := {middle with native := advance middle.native {middle.native.machine with heap := built.2}}
    execute (fuel + 2) (.code (compileNode request)) before = .done built.1 after ∧
      NodeLaw (view source holds) model ranked holds request built.1 ∧
      SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap built.1 := by
  simpa only [compileNode, selected] using
    rows_body source sourceFacts holds model ranked domain first left leftDepth leftFree second right rightDepth rightFree
      leftAvailable rightAvailable before middle values fuel ready walk

end MicroCFTA.SourceCurrentAllocatedNativeNodeRowsMeaning
