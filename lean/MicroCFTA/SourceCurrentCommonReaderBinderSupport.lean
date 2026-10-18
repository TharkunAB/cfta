import MicroCFTA.SourceCurrentObservationReaderSupport
import MicroCFTA.SourceCurrentStoredNodeExpansion
import MicroCFTA.SourceCurrentStoredCallsReplay

/-!
# Actual node unfoldings extend reader support

Initial Ready data constructs an actual stored Mu unfolding. Its returned
ordinary value and the Mu are settled at the exact final reader. Actual
row calls reduce their child support to strict original children. A child
can use the existing support or return the same recursive Mu. This closes
the new epsilon and row-child obligations. Nested Mu children are allowed.
The theorem does not prepare all open Mu records or compare two binders.
-/
namespace MicroCFTA.SourceCurrentCommonReaderBinderSupport
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (Environment Replacements)
open InternedEdgeResidency (nodeEdges)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceCurrentObservationReaderSupport (WarmSupport)
open SourceCurrentStoredNodeExpansion (RowCalls)
open MergedFreshOrdinaryGraph (successors Origin)

private theorem pair_right {First Second : Type} {relation : First → Second → Prop}
    {first : List First} {second : List Second} (paired : All₂ relation first second)
    (value : Second) (member : value ∈ second) :
    ∃ original ∈ first, relation original value := by
  induction paired with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_,List.mem_cons_self,head⟩
      · obtain ⟨original,included,matched⟩ := ih later
        exact ⟨original,List.mem_cons_of_mem _ included,matched⟩

private theorem child_smaller (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (level : Nat) (free : List Reference) (row : EdgeValue Symbol Guard) (member : row ∈ rows)
    (child : Value Symbol Guard) (included : child ∈ row.children) :
    sizeOf child < sizeOf (Value.node entry rows level free) := by
  have rowSmall := List.sizeOf_lt_of_mem member
  have childSmall := List.sizeOf_lt_of_mem included
  cases row with
  | mk edge children =>
      simp only [Value.node.sizeOf_spec,EdgeValue.mk.sizeOf_spec,EdgeValue.children] at *
      omega

private theorem ordinary_next [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (value : Value Symbol Guard)
    (ordinary : Ordinary value) : successors reader value = [] := by
  cases value <;> try cases ordinary <;> rfl

private theorem ordinary_settled [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) (value : Value Symbol Guard)
    (ordinary : Ordinary value) : InternedFreshMuUnfoldBudget.Settled reader value := by
  cases value <;> try cases ordinary <;> exact ⟨_,rfl⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Strict stored-child support constructs an actual node-Mu unfolding and extends support at its final reader. -/
theorem node (before : State Symbol Guard) (ready : Ready before)
    (support : Value Symbol Guard → Prop) (warm : WarmSupport before support)
    (entry nodeEntry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard))
    (level : Nat) (free : List Reference) (depth ordinary : Value Symbol Guard)
    (available : Available before (.mu entry (.node nodeEntry rows level free) depth ordinary))
    (strictChildren : ∀ row ∈ rows, ∀ child ∈ row.children,
      sizeOf child < sizeOf (Value.node nodeEntry rows level free) →
      ∀ common, Keeps before common → ∀ output,
        execute child (fun name => if name = .interned entry.identity then
          some (.mu entry (.node nodeEntry rows level free) depth ordinary) else none) common =
          .done output common → support output ∨ output = .mu entry (.node nodeEntry rows level free) depth ordinary) :
    ∃ result after,
      unfold (.mu entry (.node nodeEntry rows level free) depth ordinary) before = .done result after ∧
      Keeps before after ∧ Available after result ∧
      unfold (.mu entry (.node nodeEntry rows level free) depth ordinary) after = .done result after ∧
      Ordinary result ∧
      WarmSupport after (fun value => support value ∨
        value = .mu entry (.node nodeEntry rows level free) depth ordinary ∨ value = result) := by
  let recursive : Value Symbol Guard := .mu entry (.node nodeEntry rows level free) depth ordinary
  let environment : Environment Symbol Guard := fun name =>
    if name = .interned entry.identity then some recursive else none
  have bodyAvailable : Available before (.node nodeEntry rows level free) :=
    available.children _ List.mem_cons_self
  have replacements : Replacements before environment := by
    intro name value found
    dsimp only [environment] at found
    split at found
    · cases found; exact available
    · cases found
  obtain ⟨result,after,actual,kept,output,_⟩ := SourceCurrentStoredReconstruction.execute
    (.node nodeEntry rows level free) environment before ready bodyAvailable replacements
  have unfolded : unfold recursive before = .done result after := actual
  have repeated : unfold recursive after = .done result after :=
    InternedFreshOrdinaryStoredSubstitution.unfold_replay recursive before after result after
      ready.semantic.1.normal.facts.coherent.valid unfolded (grows_refl _)
  have bodyWarm : execute (.node nodeEntry rows level free) environment after = .done result after := repeated
  have expansion := SourceCurrentStoredNodeExpansion.node_warm nodeEntry rows level free environment after
    kept.ready.semantic.1.normal (kept.available _ bodyAvailable)
    (fun name value found => kept.available value (replacements name value found)) result bodyWarm
  obtain ⟨rebuilt,paired,plain,exposed⟩ := expansion
  have childSupport : ∀ row ∈ nodeEdges result, ∀ child ∈ row.children,
      support child ∨ child = recursive := by
    intro row member child included
    have origin : Origin after [result] row := ⟨_,.seed List.mem_cons_self,member⟩
    have survived := (exposed after row).mp origin
    obtain ⟨original,originalMember,calls⟩ := pair_right paired row (List.mem_filter.mp survived).1
    have children := SourceCurrentStoredCallsReplay.replay calls.1 after
      kept.ready.semantic.1.normal.facts.coherent.valid (grows_refl _)
    obtain ⟨source,sourceMember,called⟩ := pair_right children child included
    exact strictChildren original originalMember source sourceMember
      (child_smaller nodeEntry rows level free original originalMember source sourceMember) after kept child called
  have nexts : successors after recursive = [result] := by
    change (match unfold recursive after with | .done value _ => [value] | .pending .. => []) = [result]
    rw [repeated]
  have oldWarm := warm.grows before after ready.semantic.1.normal.facts.coherent.valid kept.growth support
  refine ⟨result,after,unfolded,kept,output,repeated,plain,?_,?_,?_⟩
  · intro value included next member
    rcases included with old | rfl | rfl
    · exact Or.inl (oldWarm.1 _ old next member)
    · have same : next = result := by
        change next ∈ successors after recursive at member
        rw [nexts] at member
        exact List.mem_singleton.mp member
      exact Or.inr (Or.inr same)
    · rw [ordinary_next after _ plain] at member
      cases member
  · intro value included row member child present
    rcases included with old | rfl | rfl
    · exact Or.inl (oldWarm.2.1 _ old row member child present)
    · cases member
    · rcases childSupport row member child present with old | same
      · exact Or.inl old
      · exact Or.inr (Or.inl same)
  · intro value included
    rcases included with old | rfl | rfl
    · exact oldWarm.2.2 _ old
    · exact ⟨result,repeated⟩
    · exact ordinary_settled after _ plain

end MicroCFTA.SourceCurrentCommonReaderBinderSupport
