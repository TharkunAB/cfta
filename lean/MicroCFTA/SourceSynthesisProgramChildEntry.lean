import MicroCFTA.SourceCurrentInheritedConstraintRegions
import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric

/-!
# Program child requests in actual outer prefixes

The current parent row supplies the strict role and child layout. The exact
remaining child list fixes the walk offset. The actual prefix derives the
inherited region before the next child starts. No child return is required.
These laws do not establish cache role history, Type progress, or a global bound.
-/
namespace MicroCFTA.SourceSynthesisProgramChildEntry
open EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
open SourceSynthesisGuardRegions
open SourceEqualityConstraintRegions (Within)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentOuterPrefixInvariants (Good Inputs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Prefix" => SourceCurrentAllocatedInheritedPrefix.run
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {width : Nat} {literal : String → Symbol}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {g s r e p h m c n budget parentFuel fuel index : Nat}
variable {inherited combined : EqValue} {edge : Edge} {before current : Caller width}
variable {child : Node} {rest : List Node}

private theorem region_entry (region : Path → Prop)
    (rightClosed : ∀ path, region path → ∀ suffix, region (path ++ suffix))
    (annotationInto : ∀ path, annotationRegion path → region path)
    (good : Good before) (inputs : Inputs (.descendants parentFuel inherited edge before))
    (within : Within annotationRegion inherited.payload)
    (own : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []), region path)
    (prefixDone : (Prefix edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined))
    (actual : Reached g s r e p h m c n budget (.descendants parentFuel inherited edge before)
      (.walk (fuel + 1) combined index (child :: rest) current)) :
    Within (fun suffix => region (index :: suffix)) (descend current combined index).1.payload := by
  have inheritedWithin : Within region inherited.payload := by
    cases inherited with
    | contradiction => trivial
    | live identity records =>
        intro record member path included
        exact annotationInto path (within record member path included)
  obtain ⟨computed, done, _valid, _ready, _grows, inside, _children⟩ :=
    SourceCurrentInheritedConstraintRegions.run_preserves region rightClosed
      edge.entry.key.constraint inherited before.checked.operations good.checked.operations
      (good.checked.fields edge.entry.key edge inputs.2) inputs.1 inheritedWithin own
  have same : computed = combined := Option.some.inj (Except.ok.inj (done.symm.trans prefixDone))
  subst computed
  have reached := SourceCurrentOuterPrefixInvariants.reached actual good inputs
  exact SourceCurrentInheritedConstraintRegions.descend_preserves region current combined index
    reached.1.checked.operations reached.2.1 inside

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem application_endpoints (role : ProgramEdge literal edge) :
    ∀ path ∈ members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
      applicationRegion path := by
  have regions := ProgramEdge.guard_regions literal edge role
  intro path member
  rcases regions with annotation | application | filter
  · exact Or.inl (annotation path member)
  · exact application path member
  · rcases filter path member with annotation | ⟨suffix, equal⟩
    · exact Or.inl annotation
    · exact Or.inr (Or.inl ⟨0 :: suffix, equal⟩)

/-- The actual application walk enters either program child with its annotation region. -/
theorem application_entry
    (role : ProgramEdge literal edge) (arity : edge.children.length = 4)
    (programSlot : index = 2 ∨ index = 3)
    (good : Good before) (inputs : Inputs (.descendants parentFuel inherited edge before))
    (within : Within annotationRegion inherited.payload)
    (prefixDone : (Prefix edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined))
    (actual : Reached g s r e p h m c n budget (.descendants parentFuel inherited edge before)
      (.walk (fuel + 1) combined index (child :: rest) current))
    (position : edge.children.drop index = child :: rest) :
    ProgramValue literal child ∧ Within annotationRegion (descend current combined index).1.payload ∧
      Reached g s r e p h m c n budget (.descendants parentFuel inherited edge before)
        (.node fuel ⟨(descend current combined index).1, child⟩ (descend current combined index).2) := by
  have childRole : ProgramValue literal child := by
    cases role with
    | annotated original annotation guard children =>
        simp only [children, List.length_cons, List.length_nil] at arity
        omega
    | application original types marker function argument symbol guard children functionRole argumentRole =>
        rcases programSlot with rfl | rfl
        · have same : function = child := by
            simp only [children, List.drop_succ_cons, List.drop_zero] at position
            exact (List.cons.inj position).1
          exact same ▸ functionRole
        · have same : argument = child := by
            simp only [children, List.drop_succ_cons, List.drop_zero] at position
            exact (List.cons.inj position).1
          exact same ▸ argumentRole
    | filter original goal candidates symbol guard children candidateRole =>
        simp only [children, List.length_cons, List.length_nil] at arity
        omega
  have descended := region_entry applicationRegion application_rightClosed
    (fun _ included => Or.inl included) good inputs within (application_endpoints role) prefixDone actual
  have annotation : Within annotationRegion (descend current combined index).1.payload := by
    rcases programSlot with rfl | rfl
    · simpa only [application_descend_function] using descended
    · simpa only [application_descend_argument] using descended
  exact ⟨childRole, annotation, .snoc actual Step.walk_head⟩

/-- The actual filter walk enters its program child before any child result is known. -/
theorem filter_entry
    (role : ProgramEdge literal edge) (arity : edge.children.length = 2)
    (good : Good before) (inputs : Inputs (.descendants parentFuel inherited edge before))
    (within : Within annotationRegion inherited.payload)
    (prefixDone : (Prefix edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some combined))
    (actual : Reached g s r e p h m c n budget (.descendants parentFuel inherited edge before)
      (.walk (fuel + 1) combined 1 (child :: rest) current))
    (position : edge.children.drop 1 = child :: rest) :
    ProgramValue literal child ∧ Within annotationRegion (descend current combined 1).1.payload ∧
      Reached g s r e p h m c n budget (.descendants parentFuel inherited edge before)
        (.node fuel ⟨(descend current combined 1).1, child⟩ (descend current combined 1).2) := by
  have classified : ProgramValue literal child ∧
      ∀ path ∈ members ((SourceCompactGuards.sourceEqualities edge.entry.key.constraint).getD []),
        filterRegion path := by
    cases role with
    | annotated original annotation guard children =>
        simp only [children, List.length_cons, List.length_nil] at arity
        omega
    | application original types marker function argument symbol guard children functionRole argumentRole =>
        simp only [children, List.length_cons, List.length_nil] at arity
        omega
    | filter original goal candidates symbol guard children candidateRole =>
        have same : candidates = child := by
          simp only [children, List.drop_succ_cons, List.drop_zero] at position
          exact (List.cons.inj position).1
        refine ⟨same ▸ candidateRole, ?_⟩
        rw [guard]
        exact (filter_guard_endpoints .empty .empty "filter" _ [.empty, .empty] rfl).2
  have descended := region_entry filterRegion filter_rightClosed
    (fun _ included => Or.inl included) good inputs within classified.2 prefixDone actual
  have annotation : Within annotationRegion (descend current combined 1).1.payload := by
    simpa only [filter_descend_program] using descended
  exact ⟨classified.1, annotation, .snoc actual Step.walk_head⟩

end MicroCFTA.SourceSynthesisProgramChildEntry
