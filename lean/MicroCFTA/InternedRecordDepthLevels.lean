import MicroCFTA.InternedFreshOrdinaryLevelReplay

/-!
# Ordinary-level agreement with captured records

The projection retains ordinary names and every record's decoded shape.
Equal projected inputs determine the same cached depth and ordinary free
names. Completed Depth callbacks therefore select the same ordinary level.
-/
namespace MicroCFTA.InternedRecordDepthLevels
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedRecordDepthShape InternedRecordDepthCallback
open InternedFreshOrdinaryLevelReplay
open InternedDepthSemantics
open InternedBinderProtocol (Reference)

/-- Project each decoded capture while retaining root and deep positions. -/
def project (environment : List (Value Symbol Guard)) : List (Shape Reference) :=
  (environment.map shape).map (Shape.map ordinaryNames)

/-- Corresponding reference prefixes preserve equal projected captured records. -/
theorem project_cons (first second : List (Value Symbol Guard)) (firstName secondName : Reference)
    (names : ordinaryNames firstName = ordinaryNames secondName) (same : project first = project second) :
    project (.reference firstName :: first) = project (.reference secondName :: second) := by
  simp only [project, List.map_cons, shape, Shape.map] at same ⊢
  rw [names, same]

/-- Equal projected captured records determine equal projected symbolic bodies. -/
theorem symbolic_projected (body : Syntax Symbol Guard) (first second : List (Value Symbol Guard))
    (same : project first = project second) :
    (symbolic body first).map (Sum.map id ordinaryNames) = (symbolic body second).map (Sum.map id ordinaryNames) := by
  have left := evaluate_map (Sum.map id ordinaryNames) body
    (⟨[Sum.inl ()], [], false, 0⟩ :: (first.map shape).map (Shape.map Sum.inr))
  have right := evaluate_map (Sum.map id ordinaryNames) body
    (⟨[Sum.inl ()], [], false, 0⟩ :: (second.map shape).map (Shape.map Sum.inr))
  rw [local_map] at left right
  change evaluate body (⟨[Sum.inl ()], [], false, 0⟩ :: (project first).map (Shape.map Sum.inr)) = _ at left
  rw [same] at left
  exact left.symm.trans right

/-- Equal projected captured records determine the same predicted callback depth. -/
theorem projected_depth (body : Syntax Symbol Guard) (first second : List (Value Symbol Guard))
    (same : project first = project second) : (symbolic body first).depth = (symbolic body second).depth := by
  have depths := congrArg (fun value : Shape (Sum Unit Reference) => value.depth) (symbolic_projected body first second same)
  exact depths

/-- Equal projected bodies retain exactly the same ordinary fixed free names. -/
theorem projected_captures (body : Syntax Symbol Guard) (first second : List (Value Symbol Guard))
    (same : project first = project second) (level : Nat) :
    .uninterned level ∈ InternedProfileCallbackForm.captures (symbolic body first).free ↔
      .uninterned level ∈ InternedProfileCallbackForm.captures (symbolic body second).free := by
  have equal := congrArg (fun value => InternedProfileCallbackForm.captures value.free)
    (symbolic_projected body first second same)
  simp only [Shape.map, Shape.free, ← List.map_append, InternedProfileReferenceInputs.captures_map] at equal
  have members := congrArg (fun names => .uninterned level ∈ names) equal
  simpa only [ordinary_member, Shape.free] using Iff.of_eq members

/-- Actual Depth callbacks with equal projected captured records select the same ordinary level. -/
theorem callback_level [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (firstEnvironment secondEnvironment : List (Value Symbol Guard))
    (same : project firstEnvironment = project secondEnvironment)
    (firstState secondState : State Symbol Guard)
    (firstContext : Context firstState firstEnvironment) (secondContext : Context secondState secondEnvironment)
    (firstHeap : InternedFreshOrdinaryDepthHeap.Heap firstState) (secondHeap : InternedFreshOrdinaryDepthHeap.Heap secondState)
    (first second : Value Symbol Guard) (afterFirst afterSecond : State Symbol Guard)
    (firstDone : callback body firstEnvironment .depth firstState = .done first afterFirst)
    (secondDone : callback body secondEnvironment .depth secondState = .done second afterSecond) :
    ordinaryLevel first = ordinaryLevel second := by
  have left := (InternedRecordDepthExecution.callback_depth body firstEnvironment .depth firstState firstContext
    (InternedNestedProvenance.depth_available firstState) firstHeap).result _ _ firstDone
  have right := (InternedRecordDepthExecution.callback_depth body secondEnvironment .depth secondState secondContext
    (InternedNestedProvenance.depth_available secondState) secondHeap).result _ _ secondDone
  have depths := left.1.trans ((projected_depth body firstEnvironment secondEnvironment same).trans right.1.symm)
  have free : freeBound first.free = freeBound second.free := by
    apply freeBound_congr
    intro level
    have firstFree := InternedRecordDepthCallback.callback_free body firstEnvironment .depth firstState firstContext
      (InternedNestedProvenance.depth_available firstState) first afterFirst firstDone (.uninterned level) (by intro impossible; cases impossible)
    have secondFree := InternedRecordDepthCallback.callback_free body secondEnvironment .depth secondState secondContext
      (InternedNestedProvenance.depth_available secondState) second afterSecond secondDone (.uninterned level) (by intro impossible; cases impossible)
    exact firstFree.trans ((projected_captures body firstEnvironment secondEnvironment same level).trans secondFree.symm)
  simp only [ordinaryLevel, depths, free]

end MicroCFTA.InternedRecordDepthLevels
