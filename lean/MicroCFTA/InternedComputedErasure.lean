import MicroCFTA.InternedComputedEmpty
import MicroCFTA.InternedErasureCorrespondence

/-!
# Changed-input replay after a child computes EmptyNode

The blocking child can execute nested constructors and ordinary cache
operations. Its source erasure certificate derives all later effects.
The parent then discards the changed edge and reuses its earlier record.
-/
namespace MicroCFTA.InternedComputedErasure
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedNestedSpecialization InternedNestedCoherence
open InternedNestedErasureReplay InternedErasureResidual InternedErasureSyntax InternedErasureCorrespondence
open InternedErasedEdgeReplay InternedComputedEmpty

/-- Execute the computed blocking child before interning the dependent edge and its surviving parent. -/
theorem effects [DecidableEq (EdgeKey Symbol Guard)] (index : Nat) (live : List (EdgeSyntax Symbol Guard))
    (symbol : Symbol) (constraint : Guard) (blocker : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) :
    build (.node (live ++ [.mk symbol constraint [.var index, blocker]])) environment state =
      (buildEdges live environment state).bind fun edges middle =>
        (build blocker environment middle).bind fun blocked afterBlock =>
          (work (makeEdge symbol constraint [environment[index]?.getD .empty, blocked]) afterBlock).bind fun dead afterDead =>
            work (makeNode (edges ++ [dead])) afterDead := by
  simp only [build, buildEdges_append, buildEdges, buildMany, Outcome.bind]
  cases buildEdges live environment state with
  | pending => rfl
  | done edges after =>
      simp only
      cases build blocker environment after <;> rfl

/-- A source-computed empty child preserves the exact earlier parent and all changed ordinary effects. -/
theorem dead_residual [DecidableEq (EdgeKey Symbol Guard)] (index : Nat) (live : List (EdgeSyntax Symbol Guard))
    (absent : index ∉ edgeInputs live) (symbol : Symbol) (constraint : Guard) (blocker : Syntax Symbol Guard)
    (zero : EmptyResult blocker) (erased : Erased index blocker)
    (first second : List (Value Symbol Guard)) (agree : AgreeExcept index first second)
    (before final : State Symbol Guard) (value : Value Symbol Guard) (coherent : Coherent before)
    (completed : build (.node (live ++ [.mk symbol constraint [.var index, blocker]])) first before = .done value final) :
    Residual value final (build (.node (live ++ [.mk symbol constraint [.var index, blocker]])) second) := by
  rw [effects] at completed
  obtain ⟨edges, middle, edgesDone, remaining⟩ := bind_done _ _ _ _ completed
  have middleCoherent : Coherent middle := by
    simpa only [edgesDone, Outcome.state] using buildEdges_coherent live first before coherent
  obtain ⟨blocked, afterBlock, blockDone, tailDone⟩ := bind_done _ _ _ _ remaining
  have emptyBlock := build_empty zero first middle blocked afterBlock middleCoherent blockDone
  subst blocked
  have blockCoherent : Coherent afterBlock := by
    simpa only [blockDone, Outcome.state] using build_coherent blocker first middle middleCoherent
  have blockGrowth : Grows middle afterBlock := by
    simpa only [blockDone, Outcome.state] using (build_correct blocker first middle middleCoherent.valid).2
  obtain ⟨code, safe, ordinary, residual⟩ := build_erased erased first second agree middle .empty afterBlock middleCoherent blockDone
  let oldDead := run (makeEdge symbol constraint [first[index]?.getD .empty, .empty]) afterBlock
  have deadCorrect := InternedConstructorTemplates.run_correct
    (makeEdge symbol constraint [first[index]?.getD .empty, .empty]) afterBlock blockCoherent.valid
  have oldErased : makeNode (edges ++ [oldDead.1]) = makeNode edges := by
    apply makeNode_erases
    rw [makeEdge_references _ _ _ afterBlock blockCoherent]
    simp [Value.referenceOf]
  have parentDone : work (makeNode edges) oldDead.2 = .done value final := by
    simp only [work, Outcome.bind] at tailDone
    rw [oldErased] at tailDone
    exact tailDone
  have parentCorrect := work_correct (makeNode edges) oldDead.2 deadCorrect.1
  rw [parentDone] at parentCorrect
  let newOuter := second[index]?.getD .empty
  refine ⟨code.bind (fun _ => (makeEdge symbol constraint [newOuter, .empty]).bind fun _ => .pure value),
    safe_bind _ _ safe (fun _ => safe_bind _ _ (makeEdge_safe _ _ _) (fun _ => trivial)),
    ordinary_bind _ _ ordinary (fun _ => ordinary_bind _ _ (by simp [makeEdge, Ordinary]) (fun _ => trivial)), ?_⟩
  intro after afterCoherent growth
  have blockLater : Grows afterBlock after := grows_trans deadCorrect.2 (grows_trans parentCorrect.2 growth)
  have edgesReplay := buildEdges_replays live first before after edges middle coherent.valid edgesDone
    (grows_trans blockGrowth blockLater)
  have same := buildEdges_congr live first second after (fun selected member => agree selected (fun equal => absent (equal ▸ member)))
  rw [same] at edgesReplay
  have repeated := residual after afterCoherent blockLater
  let newBlock := run code after
  have newBlockCoherent : Coherent newBlock.2 := run_coherent code after safe afterCoherent
  have newBlockCorrect := InternedConstructorTemplates.run_correct code after afterCoherent.valid
  let newDead := run (makeEdge symbol constraint [newOuter, .empty]) newBlock.2
  have newCorrect := InternedConstructorTemplates.run_correct (makeEdge symbol constraint [newOuter, .empty]) newBlock.2 newBlockCoherent.valid
  have newErased : makeNode (edges ++ [newDead.1]) = makeNode edges := by
    apply makeNode_erases
    rw [makeEdge_references _ _ _ newBlock.2 newBlockCoherent]
    simp [Value.referenceOf]
  have parentReplay := work_replays (makeNode edges) oldDead.2 newDead.2 value final deadCorrect.1 parentDone
    (grows_trans growth (grows_trans newBlockCorrect.2 newCorrect.2))
  constructor
  · rw [effects, edgesReplay]
    simp only [Outcome.bind, repeated.1, work, run_bind]
    rw [repeated.2]
    change Outcome.done (run (makeNode (edges ++ [newDead.1])) newDead.2).1
      (run (makeNode (edges ++ [newDead.1])) newDead.2).2 = _
    rw [newErased]
    simpa only [work, run] using parentReplay
  · simp only [run_bind, run]

end MicroCFTA.InternedComputedErasure
