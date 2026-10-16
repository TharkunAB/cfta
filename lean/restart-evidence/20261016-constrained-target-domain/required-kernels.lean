import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequired
namespace FiniteOrdinaryRequiredKernels
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryRequired
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A missing child rejects the complete row before any child call or allocation. -/
theorem rejected_zero_arity (entry : Interned (EdgeKey Symbol Guard)) (state : State Symbol Guard)
    (semantic : SemanticReady state) (resident : EdgeResident state (.mk entry [])) :
    let edge : EdgeValue Symbol Guard := .mk entry []
    ∃ _actual : RequireRows [(0, .node [])] [edge] state [] state,
      Keeps state state ∧ SemanticReady state ∧ Edges state ([] : List (EdgeValue Symbol Guard)) ∧
        DRows ([] : List (EdgeValue Symbol Guard)) ∧
        ∃ selected, selected.Sublist [edge] ∧ All₂ EdgeNarrow selected [] := by
  let edge : EdgeValue Symbol Guard := .mk entry []
  have actual : RequireRows [(0, .node [])] [edge] state [] state :=
    .rejected (by change fits (.node [(0, .node [])]) 0 = false; decide) .nil
  exact ⟨actual, rows actual semantic (by intro edge member; cases List.mem_singleton.mp member; exact resident)
    (.cons .nil .nil)⟩

/-- A negative requirement retains the zero-arity row and uses both actual constructors. -/
theorem retained_negative_key (entry : Interned (EdgeKey Symbol Guard))
    (own : Interned InternedBinderProtocol.NodeKey) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (state : State Symbol Guard)
    (semantic : SemanticReady state) (available : Available state (.node own [.mk entry []] depth free)) :
    let edge : EdgeValue Symbol Guard := .mk entry []
    let rebuilt := run (makeEdge entry.key.symbol entry.key.constraint []) state
    let final := run (makeNode [rebuilt.1]) rebuilt.2
    ∃ _actual : RequireNode (.node [(-1, .node [])]) (.node own [edge] depth free) state final.1 final.2,
      Keeps state final.2 ∧ SemanticReady final.2 ∧ Available final.2 final.1 ∧
        NodeNarrow (.node own [edge] depth free) final.1 := by
  let edge : EdgeValue Symbol Guard := .mk entry []
  let rebuilt := run (makeEdge entry.key.symbol entry.key.constraint []) state
  let final := run (makeNode [rebuilt.1]) rebuilt.2
  have actualRows : RequireRows [(-1, .node [])] [edge] state [rebuilt.1] rebuilt.2 :=
    .kept (by change fits (.node [(-1, .node [])]) 0 = true; decide) .nil rfl .nil
  have actual : RequireNode (.node [(-1, .node [])]) (.node own [edge] depth free) state final.1 final.2 :=
    .ordinary (by simp) actualRows rfl
  exact ⟨actual, node actual semantic available (.ordinary (.cons .nil .nil))⟩

/-- Rejecting the only ordinary row returns Empty and strictly reduces its height. -/
theorem rejected_parent_empty (entry : Interned (EdgeKey Symbol Guard))
    (own : Interned InternedBinderProtocol.NodeKey) (depth : Nat)
    (free : List InternedBinderProtocol.Reference) (state : State Symbol Guard)
    (semantic : SemanticReady state) (available : Available state (.node own [.mk entry []] depth free)) :
    ∃ _actual : RequireNode (.node [(0, .node [])]) (.node own [.mk entry []] depth free) state .empty state,
      Keeps state state ∧ SemanticReady state ∧ Available state (.empty : Value Symbol Guard) ∧
        NodeNarrow (.node own [.mk entry []] depth free) .empty ∧
        MergedOrdinaryHeight.height (.empty : Value Symbol Guard) <
          MergedOrdinaryHeight.height (.node own [.mk entry []] depth free) := by
  have actualRows : RequireRows [(0, .node [])] [.mk entry []] state [] state :=
    .rejected (by change fits (.node [(0, .node [])]) 0 = false; decide) .nil
  have actual : RequireNode (.node [(0, .node [])]) (.node own [.mk entry []] depth free) state .empty state :=
    .ordinary (by simp) actualRows (by simp [makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run])
  have verified := node actual semantic available (.ordinary (.cons .nil .nil))
  exact ⟨actual, verified.1, verified.2.1, verified.2.2.1, verified.2.2.2, by
    simp [MergedOrdinaryHeight.height, MergedOrdinaryHeight.edgesHeight,
      MergedOrdinaryHeight.edgeHeight, MergedOrdinaryHeight.childrenHeight]⟩

/-- The selected root and unselected tail retain two distinct original positions. -/
theorem selected_then_unselected (first second : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (available : Values state [first, second])
    (domains : DChildren [first, second]) :
    ∃ _actual : RequireChildren [(0, .node [])] 0 [first, second] state [first, second] state,
      Keeps state state ∧ SemanticReady state ∧ Values state [first, second] ∧ DChildren [first, second] ∧
        All₂ NodeNarrow [first, second] [first, second] := by
  have actual : RequireChildren [(0, .node [])] 0 [first, second] state [first, second] state :=
    .selected 0 (by rfl) .identity (.unselected 1 (by simp [SourceEqualityNeededMap.lookup]) .nil)
  exact ⟨actual, children actual semantic available domains⟩

/-- Two literal requireAll returns compose their derived domains and positional height bounds. -/
theorem serial_requireAll (fuel readFuel nextFuel nextRead : Nat) (paths more : List (List Int))
    (values results outputs : List (Value Symbol Guard)) (before middle after : State Symbol Guard)
    (first : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results middle)
    (second : SourceEqualityRequiredExecution.requireAll nextFuel nextRead more results middle = .done outputs after)
    (semantic : SemanticReady before) (available : Values before values) (domains : DChildren values) :
    Keeps before after ∧ SemanticReady after ∧ Values after outputs ∧ DChildren outputs ∧
      All₂ NodeNarrow values outputs ∧ outputs.length = values.length := by
  obtain ⟨firstKeeps, middleSemantic, middleAvailable, middleDomains, firstRelation⟩ :=
    requireAll_done fuel readFuel paths values results before middle first semantic available domains
  obtain ⟨lastKeeps, finalSemantic, finalAvailable, finalDomains, secondRelation⟩ :=
    requireAll_done nextFuel nextRead more results outputs middle after second middleSemantic middleAvailable middleDomains
  have compose : ∀ {xs ys zs : List (Value Symbol Guard)},
      All₂ NodeNarrow xs ys → All₂ NodeNarrow ys zs → All₂ NodeNarrow xs zs := by
    intro xs ys zs one two
    induction one generalizing zs with
    | nil => cases two; exact .nil
    | cons head tail ih =>
        cases two with
        | cons next rest => exact .cons ⟨next.1, Nat.le_trans next.2 head.2⟩ (ih rest)
  have related := compose firstRelation secondRelation
  exact ⟨firstKeeps.trans lastKeeps, finalSemantic, finalAvailable, finalDomains, related, related.length_eq.symm⟩
end FiniteOrdinaryRequiredKernels

#print axioms FiniteOrdinaryRequiredKernels.rejected_zero_arity
#check @FiniteOrdinaryRequiredKernels.rejected_zero_arity
#print axioms FiniteOrdinaryRequiredKernels.retained_negative_key
#check @FiniteOrdinaryRequiredKernels.retained_negative_key
#print axioms FiniteOrdinaryRequiredKernels.rejected_parent_empty
#check @FiniteOrdinaryRequiredKernels.rejected_parent_empty
#print axioms FiniteOrdinaryRequiredKernels.selected_then_unselected
#check @FiniteOrdinaryRequiredKernels.selected_then_unselected
#print axioms FiniteOrdinaryRequiredKernels.serial_requireAll
#check @FiniteOrdinaryRequiredKernels.serial_requireAll
