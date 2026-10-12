import MicroCFTA.InternedErasureCorrespondence

/-!
# Simultaneous erasure of all enclosing source inputs

The protected prefix contains the local variables introduced below a
source call. Every other input can change together. Declared discarded
edges and source constructor composition derive exact earlier-result
replay while retaining the changed discarded-edge effects.
-/
namespace MicroCFTA.InternedOuterErasure
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedDependencies InternedNestedSpecialization InternedNestedCoherence
open InternedNestedErasureReplay InternedErasureResidual InternedErasureChildren InternedErasedEdgeReplay

/-- The environments agree at every protected local slot. -/
def AgreeLocal (count : Nat) (first second : List (Value Symbol Guard)) : Prop :=
  ∀ index, index < count → first[index]?.getD .empty = second[index]?.getD .empty

/-- The same new binder variable extends the protected local prefix. -/
theorem AgreeLocal.local {first second : List (Value Symbol Guard)}
    (agree : AgreeLocal count first second) (value : Value Symbol Guard) : AgreeLocal (count + 1) (value :: first) (value :: second) := by
  intro index bound
  cases index with
  | zero => rfl
  | succ index => exact agree index (by omega)

/-- Every dependency outside the protected local prefix erases by declared source constructors. -/
inductive OuterErased : Nat → Syntax Symbol Guard → Prop where
  | unused (count : Nat) (expression : Syntax Symbol Guard)
      (inside : ∀ index ∈ inputs expression, index < count) : OuterErased count expression
  | dead (count index : Nat) (live : List (EdgeSyntax Symbol Guard)) (symbol : Symbol) (constraint : Guard)
      (inside : ∀ index ∈ edgeInputs live, index < count) :
      OuterErased count (.node (live ++ [.mk symbol constraint [.var index, .empty]]))
  | node (count : Nat) (edges : List (EdgeSyntax Symbol Guard))
      (children : ∀ symbol constraint children, .mk symbol constraint children ∈ edges →
        ∀ child ∈ children, OuterErased count child) : OuterErased count (.node edges)
  | union (count : Nat) (members : List (Syntax Symbol Guard))
      (children : ∀ child ∈ members, OuterErased count child) : OuterErased count (.union members)
  | binder (count : Nat) (smart : Bool) (body : Syntax Symbol Guard)
      (inside : OuterErased (count + 1) body) : OuterErased count (.binder smart body)

/-- A declared discarded edge retains its allocation while the earlier live record replays exactly. -/
theorem dead_outer_residual [DecidableEq (EdgeKey Symbol Guard)] (index : Nat) (live : List (EdgeSyntax Symbol Guard))
    (symbol : Symbol) (constraint : Guard)
    (first second : List (Value Symbol Guard)) (agree : Agree (edgeInputs live) first second)
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
  have same := buildEdges_congr live first second after agree
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

/-- Declared dependency erasure derives exact earlier-result correspondence and ordinary later effects through full source syntax. -/
theorem build_outer_erased [DecidableEq (EdgeKey Symbol Guard)] {index : Nat} {expression : Syntax Symbol Guard}
    (erased : OuterErased index expression) (first second : List (Value Symbol Guard))
    (agree : AgreeLocal index first second) (before : State Symbol Guard) (value : Value Symbol Guard)
    (final : State Symbol Guard) (coherent : Coherent before)
    (completed : build expression first before = .done value final) : Residual value final (build expression second) := by
  induction erased generalizing first second before value final with
  | unused index expression absent =>
      exact pure_residual value final _ (fun after _ growth => independent_replay expression first second before after
        value final coherent.valid completed growth (fun selected member => agree selected (absent selected member)))
  | dead count index live symbol constraint inside =>
      exact dead_outer_residual index live symbol constraint first second (fun selected member => agree selected (inside selected member))
        before final value coherent completed
  | node index edges declared ih =>
      simp only [build] at completed
      obtain ⟨values, middle, edgesDone, parentDone⟩ := bind_done _ _ _ _ completed
      have edgesResidual := edges_residual edges first second
        (fun symbol constraint children member child included start value finish current returned =>
          ih symbol constraint children member child included first second agree start value finish current returned)
        before middle values coherent edgesDone
      have middleCoherent : Coherent middle := by
        simpa only [edgesDone, Outcome.state] using buildEdges_coherent edges first before coherent
      have parentResidual := work_residual (makeNode values) middle final value middleCoherent.valid parentDone
      have parentGrowth : Grows middle final := by
        simpa only [parentDone, Outcome.state] using (work_correct (makeNode values) middle middleCoherent.valid).2
      simpa only [Residual, build] using bind_residual (buildEdges edges second)
        (fun values current => work (makeNode values) current) values middle value final edgesResidual parentResidual parentGrowth
  | union index members declared ih =>
      simp only [build] at completed
      obtain ⟨values, middle, childrenDone, parentDone⟩ := bind_done _ _ _ _ completed
      have childResidual := many_residual members first second
        (fun child member start value finish current returned => ih child member first second agree start value finish current returned)
        before middle values coherent childrenDone
      have middleCoherent : Coherent middle := by
        simpa only [childrenDone, Outcome.state] using buildMany_coherent members first before coherent
      have parentResidual := work_residual (makeUnion values) middle final value middleCoherent.valid parentDone
      have parentGrowth : Grows middle final := by
        simpa only [parentDone, Outcome.state] using (work_correct (makeUnion values) middle middleCoherent.valid).2
      simpa only [Residual, build] using bind_residual (buildMany members second)
        (fun values current => work (makeUnion values) current) values middle value final childResidual parentResidual parentGrowth
  | binder index smart body inside ih =>
      let callback := fun environment name current => (build body (.reference name :: environment) current).bind
        fun value after => work (withoutSelfReference name value) after
      have growing : ∀ environment name, Growing (callback environment name) := by
        intro environment name current valid
        exact bind_correct _ _ current (build_correct body _ current valid)
          (fun value after afterValid => work_correct (withoutSelfReference name value) after afterValid)
      have callbackCoherent : ∀ environment name current, Coherent current → Coherent (callback environment name current).state := by
        intro environment name current currentCoherent
        exact bind_coherent _ _ (build_coherent body _ current currentCoherent)
          (fun value after _ afterCoherent => run_coherent (withoutSelfReference name value) after (withoutSelfReference_safe _ _) afterCoherent)
      have callbackResidual : ∀ name start result finish, Coherent start →
          callback first name start = .done result finish → Residual result finish (callback second name) := by
        intro name start result finish startCoherent returned
        obtain ⟨raw, middle, bodyDone, filterDone⟩ := bind_done _ _ _ _ returned
        have bodyResidual := ih (.reference name :: first) (.reference name :: second) (agree.local _) start raw middle startCoherent bodyDone
        have middleCoherent : Coherent middle := by
          simpa only [bodyDone, Outcome.state] using build_coherent body (.reference name :: first) start startCoherent
        have filterResidual := work_residual (withoutSelfReference name raw) middle finish result middleCoherent.valid filterDone
        have filterGrowth : Grows middle finish := by
          simpa only [filterDone, Outcome.state] using (work_correct (withoutSelfReference name raw) middle middleCoherent.valid).2
        exact bind_residual (build body (.reference name :: second)) (fun value after => work (withoutSelfReference name value) after)
          raw middle result finish bodyResidual filterResidual filterGrowth
      rw [build] at completed
      change (callback first .depth before).bind (fun depth afterDepth =>
        (callback first (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback first) afterOrdinary) = .done value final at completed
      obtain ⟨depth, afterDepth, depthDone, remaining⟩ := bind_done _ _ _ _ completed
      have depthCoherent : Coherent afterDepth := by
        simpa only [depthDone, Outcome.state] using callbackCoherent first .depth before coherent
      obtain ⟨ordinary, afterOrdinary, ordinaryDone, requestDone⟩ := bind_done _ _ _ _ remaining
      have ordinaryCoherent : Coherent afterOrdinary := by
        simpa only [ordinaryDone, Outcome.state] using callbackCoherent first (.uninterned depth.depth) afterDepth depthCoherent
      have requestGrowth : Grows afterOrdinary final := by
        simpa only [requestDone, Outcome.state] using
          (request_correct smart depth ordinary (callback first) (growing first) afterOrdinary ordinaryCoherent.valid).2
      have ordinaryGrowth : Grows afterDepth afterOrdinary := by
        simpa only [ordinaryDone, Outcome.state] using (growing first (.uninterned depth.depth) afterDepth depthCoherent.valid).2
      have requestResidual : Residual value final (request smart depth ordinary (callback second)) :=
        pure_residual value final _ (fun after _ growth => request_after_done smart depth ordinary
          (callback first) (callback second) afterOrdinary after value final ordinaryCoherent.valid (growing first) requestDone growth)
      have later := bind_residual (callback second (.uninterned depth.depth))
        (fun ordinary after => request smart depth ordinary (callback second) after)
        ordinary afterOrdinary value final
        (callbackResidual (.uninterned depth.depth) afterDepth ordinary afterOrdinary depthCoherent ordinaryDone)
        requestResidual requestGrowth
      have all := bind_residual (callback second .depth)
        (fun depth afterDepth => (callback second (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback second) afterOrdinary)
        depth afterDepth value final (callbackResidual .depth before depth afterDepth coherent depthDone)
        later (grows_trans ordinaryGrowth requestGrowth)
      simpa only [Residual, build, callback] using all

end MicroCFTA.InternedOuterErasure
