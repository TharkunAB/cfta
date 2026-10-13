import MicroCFTA.EqualityMergedTargetFixedPoint
import MicroCFTA.MergedComparisonSoundness

/-!
# Saturated target merging is not monotone under structural coverage

Five correlated binary rows merge into one rectangular row. An already
compressed two-row representation covers the original five rows and stays
unchanged. The two saturated results disagree on a mixed child pair.
Thus source saturation is not a monotone closure under language inclusion
or under the source's successful row-coverage order.
-/
namespace MicroCFTA.EqualityMergedTargetMonotonicity
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedSourceComparison MergedPhysicalComparison Language
open EqualityMergedTargetHeight

/-- Finite ordinary roots have no source epsilon successors. -/
theorem tree_no_epsilon [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (value : Value Symbol Guard) (tree : Tree value) : successors state value = [] := by
  cases tree <;> rfl

/-- Every constructor child of a finite ordinary tree is a finite ordinary tree. -/
theorem constructor_tree (meaning : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (tree : Tree value)
    (edge : Language.Edge (Value Symbol Guard) Symbol) (member : edge ∈ constructorRows meaning value)
    (child : Value Symbol Guard) (included : child ∈ edge.children) : Tree child := by
  cases tree with
  | empty => simp only [constructorRows, List.not_mem_nil] at member
  | node entry edges depth free below =>
      obtain ⟨original, present, same⟩ := List.mem_map.mp member
      subst edge
      exact below original present child included

/-- Ordinary constructor semantics is exact in every actual source cache on the finite ordinary fragment. -/
theorem ordinary_language [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (tree : Tree value) (term : Term Symbol) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term ↔
      Language.Accepts (constructorRows meaning) value term := by
  constructor
  · intro accepted
    induction accepted using EpsilonUnion.Accepts.rec
      (motive_2 := fun values terms _ => (∀ value ∈ values, Tree value) →
        Language.All₂ (Language.Accepts (constructorRows meaning)) values terms) with
    | @reference source target term member accepted ih =>
        have absent := tree_no_epsilon state source tree
        simp only [MergedPhysicalLanguage.graph, absent, List.not_mem_nil] at member
    | @node root edge children member accepted allowed ih =>
        exact .node edge children member (ih (constructor_tree meaning root tree edge member)) allowed
    | nil => exact .nil
    | @cons value term values terms head tail ihHead ihTail =>
        rename_i trees
        exact .cons (ihHead (trees value List.mem_cons_self))
          (ihTail (fun child member => trees child (List.mem_cons_of_mem _ member)))
  · intro accepted
    clear tree
    induction accepted using Language.Accepts.rec
      (motive_2 := fun values terms _ => Language.All₂ (EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning)) values terms) with
    | node edge children member accepted allowed ih => exact .node edge children member ih allowed
    | nil => exact .nil
    | cons _ _ head tail => exact .cons head tail

/-- Build an ordinary nullary constructor from its source symbol. -/
def leaf (symbol : Nat) : Syntax Nat Unit := .node [.mk symbol () []]

/-- Explicit correlation has five source alternatives. -/
def expandedSyntax : Syntax Nat Unit :=
  .node ([(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)].map fun pair =>
    .mk 3 () [leaf pair.1, leaf pair.2])

/-- Two rectangular alternatives describe the same original accepted pairs. -/
def compactSyntax : Syntax Nat Unit :=
  let ab := Syntax.node [.mk 0 () [], .mk 1 () []]
  .node [.mk 3 () [ab, ab], .mk 3 () [leaf 2, leaf 2]]

/-- A shared actual source constructor cache retains both input endpoints. -/
def fixture : Syntax Nat Unit := .node [.mk 4 () [expandedSyntax, compactSyntax]]

def source : Value Nat Unit × State Nat Unit :=
  match InternedNestedConstruction.build fixture [] empty with
  | .done value after => (value, after)
  | _ => (.empty, empty)

def expanded : Value Nat Unit := ((nodeEdges source.1).flatMap EdgeValue.children)[0]?.getD .empty

def compact : Value Nat Unit := ((nodeEdges source.1).flatMap EdgeValue.children)[1]?.getD .empty

/-- Both counterexample inputs are actual available closed ordinary values. -/
theorem source_valid : Facts source.2 ∧ Prepared source.2 ∧ Available source.2 expanded ∧ Available source.2 compact := by
  have done : InternedNestedConstruction.build fixture [] empty = .done source.1 source.2 := by cbv
  have verified := InternedNestedProvenance.build_verified fixture [] empty empty_facts (by simp [Values])
  have facts : Facts source.2 := by simpa only [done, Outcome.state] using verified.facts
  have available := verified.result _ _ done
  refine ⟨facts, ?_, available.children expanded (by cbv; exact List.mem_cons_self),
    available.children compact (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩
  intro key entry body depth ordinary stored
  have member := inventory_complete source.2 facts.coherent key _ stored
  have noMu : (InternedRecordCoherence.nodeInventory source.2).all (fun value => match value with
    | .mu .. => false | _ => true) = true := by cbv
  have impossible := List.all_eq_true.mp noMu _ member
  cases impossible

/-- Execute one current-policy target merge in the actual supplied cache. -/
def merged (value : Value Nat Unit) (state : State Nat Unit) : Value Nat Unit × State Nat Unit :=
  match MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () 0 value state with
  | .done result after => (result, after)
  | .failed _ after => (.empty, after)

def expandedResult := merged expanded source.2

def compactResult := merged compact source.2

/-- The explicit five-row input completes its actual target merge. -/
theorem expanded_done : MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () 0 expanded source.2 =
    .done expandedResult.1 expandedResult.2 := by
  cbv
  iterate 8 (all_goals (try simp only [MergedColdMerge.retainedColumn]; cbv))

/-- The two-row covering input also completes from the same original runtime cache. -/
theorem compact_done : MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () 0 compact source.2 =
    .done compactResult.1 compactResult.2 := by cbv

/-- Both results are already exact fixed points, so additional saturation cannot repair the discrepancy. -/
theorem saturated : merged expandedResult.1 expandedResult.2 = expandedResult ∧
    merged compactResult.1 compactResult.2 = (compactResult.1, compactResult.2) := by
  cbv
  iterate 8 (all_goals (try simp only [MergedColdMerge.retainedColumn]; cbv))

/-- Both subsequent merge calls succeed with the same actual complete value and cache. -/
theorem fixed_execution :
    MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () 0 expandedResult.1 expandedResult.2 =
      .done expandedResult.1 expandedResult.2 ∧
    MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () 0 compactResult.1 compactResult.2 =
      .done compactResult.1 compactResult.2 := by
  cbv
  iterate 8 (all_goals (try simp only [MergedColdMerge.retainedColumn]; cbv))

/-- A completed zero-comparison-fuel call has the same source result at every larger bound. -/
theorem zero_stable (value result : Value Nat Unit) (before after : State Nat Unit)
    (done : MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () 0 value before = .done result after)
    (comparison : Nat) :
    MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () comparison value before = .done result after := by
  have stable := MergedColdMergeStability.worker_refines MergedSourceGrouping.groups (fun _ => true) ()
    (MergedOrdinaryHeight.height value) (MergedOrdinaryHeight.height value) (Nat.le_refl _) 0 comparison
    value before result after done
  simpa only [MergedColdMerge.execute, Nat.zero_add] using stable

/-- Every comparison bound gives the same completed source merges and exact fixed-point replays. -/
theorem all_fuels (comparison : Nat) :
    MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () comparison expanded source.2 =
      .done expandedResult.1 expandedResult.2 ∧
    MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () comparison compact source.2 =
      .done compactResult.1 compactResult.2 ∧
    MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () comparison expandedResult.1 expandedResult.2 =
      .done expandedResult.1 expandedResult.2 ∧
    MergedColdMerge.execute MergedSourceGrouping.groups (fun _ => true) () comparison compactResult.1 compactResult.2 =
      .done compactResult.1 compactResult.2 :=
  ⟨zero_stable _ _ _ _ expanded_done comparison, zero_stable _ _ _ _ compact_done comparison,
    zero_stable _ _ _ _ fixed_execution.1 comparison, zero_stable _ _ _ _ fixed_execution.2 comparison⟩

/-- The actual source structural comparator accepts the original covering relation. -/
theorem source_cover : check (fun _ => true) 3 [] compact expanded source.2 = .done true source.2 := by cbv

/-- The same source structural comparator rejects coverage after both inputs reach exact merge fixed points. -/
theorem output_cover_fails : check (fun _ => true) 3 [] compactResult.1 expandedResult.1 expandedResult.2 =
    .done false expandedResult.2 := by
  cbv
  iterate 8 (all_goals (try simp only [MergedColdMerge.retainedColumn]; cbv))

/-- The original structural coverage implies inclusion in actual source epsilon semantics. -/
theorem input_inclusion (term : Term Nat)
    (accepted : EpsilonUnion.Accepts (MergedPhysicalLanguage.graph source.2 (fun _ _ => true)) expanded term) :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph source.2 (fun _ _ => true)) compact term :=
  MergedComparisonSoundness.check_sound source.2 source_valid.1 source_valid.2.1
    (fun _ => true) (fun _ _ => true) (by simp) 3 compact expanded source_valid.2.2.2 source_valid.2.2.1
    (by cbv) (by cbv) source.2 source_cover term accepted

/-- One child from the first correlation block and one from the second gives the separating finite term. -/
def witness : Term Nat := .node 3 [.node 0 [], .node 2 []]

/-- The merged explicit input admits the new mixed pair in its actual constructor language. -/
theorem mixed_accepted : Language.Accepts (constructorRows (fun (_ : Unit) (_ : Term Nat) => true)) expandedResult.1 witness := by
  apply Language.enumerate_sound _ 2
  cbv
  iterate 8 (all_goals (try simp only [MergedColdMerge.retainedColumn]; cbv))
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- The already compact covering input still rejects that mixed pair. -/
theorem mixed_rejected : ¬ Language.Accepts (constructorRows (fun (_ : Unit) (_ : Term Nat) => true)) compactResult.1 witness := by
  intro accepted
  have member := (Language.mem_enumerate_iff (constructorRows (fun (_ : Unit) (_ : Term Nat) => true)) 2 compactResult.1 witness).mpr
    ⟨accepted, by cbv⟩
  have absent : witness ∉ Language.enumerate (constructorRows (fun (_ : Unit) (_ : Term Nat) => true)) 2 compactResult.1 := by
    cbv
    iterate 8 (all_goals (try simp only [MergedColdMerge.retainedColumn]; cbv))
    intro present
    rcases List.mem_cons.mp present with equal | present
    · cases equal
    rcases List.mem_cons.mp present with equal | present
    · cases equal
    rcases List.mem_cons.mp present with equal | present
    · cases equal
    rcases List.mem_cons.mp present with equal | present
    · cases equal
    rcases List.mem_cons.mp present with equal | present
    · cases equal
    exact List.not_mem_nil present
  exact absent member

/-- A finite executable depth certificate recognizes only empty and ordinary constructor values. -/
def treeAt : Nat → Value Symbol Guard → Bool
  | 0, _ => false
  | _ + 1, .empty => true
  | fuel + 1, .node _ edges _ _ => edges.all fun edge => edge.children.all (treeAt fuel)
  | _ + 1, _ => false

/-- The executable depth certificate derives the independent finite ordinary-tree predicate. -/
theorem treeAt_sound (fuel : Nat) (value : Value Symbol Guard) (checked : treeAt fuel value = true) : Tree value := by
  induction fuel generalizing value with
  | zero => cases checked
  | succ fuel ih =>
      cases value with
      | empty => exact .empty
      | reference | union | mu => cases checked
      | node entry edges depth free =>
          exact .node entry edges depth free (fun edge member child included =>
            ih child (List.all_eq_true.mp (List.all_eq_true.mp checked edge member) child included))

/-- Both actual saturated outputs remain finite ordinary trees. -/
theorem results_ordinary : Tree expandedResult.1 ∧ Tree compactResult.1 := by
  constructor
  · apply treeAt_sound 3
    cbv
    iterate 8 (all_goals (try simp only [MergedColdMerge.retainedColumn]; cbv))
  · apply treeAt_sound 3
    cbv

/-- The separating term is accepted and rejected in the actual returned-cache epsilon semantics. -/
theorem output_separation :
    EpsilonUnion.Accepts (MergedPhysicalLanguage.graph expandedResult.2 (fun _ _ => true)) expandedResult.1 witness ∧
      ¬ EpsilonUnion.Accepts (MergedPhysicalLanguage.graph compactResult.2 (fun _ _ => true)) compactResult.1 witness := by
  exact ⟨(ordinary_language expandedResult.2 _ expandedResult.1 results_ordinary.1 witness).mpr mixed_accepted,
    fun accepted => mixed_rejected ((ordinary_language compactResult.2 _ compactResult.1 results_ordinary.2 witness).mp accepted)⟩

/-- Actual source coverage of the inputs does not imply inclusion between the fully saturated results. -/
theorem saturation_not_monotone :
    (∀ term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph source.2 (fun _ _ => true)) expanded term →
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph source.2 (fun _ _ => true)) compact term) ∧
    ¬ (∀ term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph expandedResult.2 (fun _ _ => true)) expandedResult.1 term →
      EpsilonUnion.Accepts (MergedPhysicalLanguage.graph compactResult.2 (fun _ _ => true)) compactResult.1 term) :=
  ⟨input_inclusion, fun included => output_separation.2 (included witness output_separation.1)⟩

end MicroCFTA.EqualityMergedTargetMonotonicity
