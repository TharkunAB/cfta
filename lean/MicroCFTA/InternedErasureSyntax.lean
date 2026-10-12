import MicroCFTA.InternedErasureResidual

/-!
# Source declarations for a dependency erased below arbitrary constructors

The relation tracks one lexical slot. Its occurrences can sit in declared
empty-child edges below ordinary nodes, unions, or nested binders. Other
subexpressions can be arbitrary source syntax when they omit that slot.
-/
namespace MicroCFTA.InternedErasureSyntax
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedNestedSpecialization InternedNestedCoherence
open InternedNestedErasureReplay InternedErasureResidual InternedErasedEdgeReplay

/-- Enclosing environments can differ at the selected source slot only. -/
def AgreeExcept (index : Nat) (first second : List (Value Symbol Guard)) : Prop :=
  ∀ selected, selected ≠ index → first[selected]?.getD .empty = second[selected]?.getD .empty

/-- Adding the same local input shifts the only changed outer slot by one. -/
theorem AgreeExcept.local {first second : List (Value Symbol Guard)}
    (agree : AgreeExcept index first second) (value : Value Symbol Guard) :
    AgreeExcept (index + 1) (value :: first) (value :: second) := by
  intro selected different
  cases selected with
  | zero => rfl
  | succ selected => exact agree selected (by omega)

/-- Source syntax declares erasure of one selected lexical dependency. -/
inductive Erased : Nat → Syntax Symbol Guard → Prop where
  | unused (index : Nat) (expression : Syntax Symbol Guard)
      (absent : index ∉ inputs expression) : Erased index expression
  | dead (index : Nat) (live : List (EdgeSyntax Symbol Guard)) (symbol : Symbol) (constraint : Guard)
      (absent : index ∉ edgeInputs live) :
      Erased index (.node (live ++ [.mk symbol constraint [.var index, .empty]]))
  | node (index : Nat) (edges : List (EdgeSyntax Symbol Guard))
      (children : ∀ symbol constraint children, .mk symbol constraint children ∈ edges →
        ∀ child ∈ children, Erased index child) : Erased index (.node edges)
  | union (index : Nat) (members : List (Syntax Symbol Guard))
      (children : ∀ child ∈ members, Erased index child) : Erased index (.union members)
  | binder (index : Nat) (smart : Bool) (body : Syntax Symbol Guard)
      (inside : Erased (index + 1) body) : Erased index (.binder smart body)

/-- A declared discarded edge retains its allocation while the earlier live record replays exactly. -/
theorem dead_residual [DecidableEq (EdgeKey Symbol Guard)] (index : Nat) (live : List (EdgeSyntax Symbol Guard))
    (absent : index ∉ edgeInputs live) (symbol : Symbol) (constraint : Guard)
    (first second : List (Value Symbol Guard)) (agree : AgreeExcept index first second)
    (before final : State Symbol Guard) (value : Value Symbol Guard) (coherent : Coherent before)
    (completed : build (.node (live ++ [.mk symbol constraint [.var index, .empty]])) first before = .done value final) :
    Residual value final (build (.node (live ++ [.mk symbol constraint [.var index, .empty]])) second) := by
  have effects : ∀ environment state,
      build (.node (live ++ [.mk symbol constraint [.var index, .empty]])) environment state =
        (buildEdges live environment state).bind fun edges middle =>
          (work (makeEdge symbol constraint [environment[index]?.getD .empty, .empty]) middle).bind fun dead afterDead =>
            work (makeNode (edges ++ [dead])) afterDead := by
    intro environment state
    simp only [build, buildEdges_append, buildEdges, buildMany, Outcome.bind]
    cases buildEdges live environment state <;> rfl
  rw [effects] at completed
  obtain ⟨edges, middle, edgesDone, remaining⟩ := bind_done _ _ _ _ completed
  have middleCoherent : Coherent middle := by
    simpa only [edgesDone, Outcome.state] using buildEdges_coherent live first before coherent
  let oldDead := run (makeEdge symbol constraint [first[index]?.getD .empty, .empty]) middle
  have deadCorrect := InternedConstructorTemplates.run_correct
    (makeEdge symbol constraint [first[index]?.getD .empty, .empty]) middle middleCoherent.valid
  have oldErased : makeNode (edges ++ [oldDead.1]) = makeNode edges := by
    apply makeNode_erases
    rw [makeEdge_references _ _ _ middle middleCoherent]
    simp [Value.referenceOf]
  have parentDone : work (makeNode edges) oldDead.2 = .done value final := by
    simp only [work, Outcome.bind] at remaining
    rw [oldErased] at remaining
    exact remaining
  have parentCorrect := work_correct (makeNode edges) oldDead.2 deadCorrect.1
  rw [parentDone] at parentCorrect
  let newOuter := second[index]?.getD .empty
  refine ⟨(makeEdge symbol constraint [newOuter, .empty]).bind fun _ => .pure value,
    safe_bind _ _ (makeEdge_safe _ _ _) (fun _ => trivial),
    ordinary_bind _ _ (by simp [makeEdge, Ordinary]) (fun _ => trivial), ?_⟩
  intro after afterCoherent growth
  have edgesReplay := buildEdges_replays live first before after edges middle coherent.valid edgesDone
    (grows_trans deadCorrect.2 (grows_trans parentCorrect.2 growth))
  have same := buildEdges_congr live first second after (fun selected member => agree selected (fun equal => absent (equal ▸ member)))
  rw [same] at edgesReplay
  let newDead := run (makeEdge symbol constraint [newOuter, .empty]) after
  have newCorrect := InternedConstructorTemplates.run_correct (makeEdge symbol constraint [newOuter, .empty]) after afterCoherent.valid
  have newErased : makeNode (edges ++ [newDead.1]) = makeNode edges := by
    apply makeNode_erases
    rw [makeEdge_references _ _ _ after afterCoherent]
    simp [Value.referenceOf]
  have parentReplay := work_replays (makeNode edges) oldDead.2 newDead.2 value final deadCorrect.1 parentDone
    (grows_trans growth newCorrect.2)
  constructor
  · rw [effects, edgesReplay]
    simp only [work, Outcome.bind, run_bind]
    rw [newErased]
    simpa only [work, run] using parentReplay
  · simp only [run_bind, run]

end MicroCFTA.InternedErasureSyntax
