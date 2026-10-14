import MicroCFTA.InternedFreshOrdinarySourceDepth
import MicroCFTA.InternedFreeNameTransport

/-!
# Ordinary-level agreement from actual projected lexical inputs

Retain each ordinary reference and replace all other reference kinds with
Depth. Equal projected capture lists determine both the actual Depth
callback's cached depth and its ordinary free names. The repaired policy
therefore chooses the same ordinary level in both completed executions.
-/
namespace MicroCFTA.InternedFreshOrdinaryLevelReplay
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedDepthSemantics
open InternedDepthFreeProjectionSource (literal)
open InternedBinderProtocol (Reference)

/-- Keep ordinary levels and identify every other literal-reference kind with Depth. -/
def ordinaryNames : Reference → Reference
  | .uninterned level => .uninterned level
  | _ => .depth

/-- The projection has exactly one preimage for every ordinary name. -/
theorem ordinary_preimage (name : Reference) (level : Nat) :
    ordinaryNames name = .uninterned level ↔ name = .uninterned level := by
  cases name <;> simp [ordinaryNames]

/-- Projecting a free-name list preserves and reflects every ordinary occurrence. -/
theorem ordinary_member (names : List Reference) (level : Nat) :
    .uninterned level ∈ names.map ordinaryNames ↔ .uninterned level ∈ names := by
  simp only [List.mem_map, ordinary_preimage]
  constructor
  · rintro ⟨name, member, rfl⟩
    exact member
  · intro member
    exact ⟨_, member, rfl⟩

/-- Ordinary free-name bounds depend only on ordinary membership, without list order or duplicate counts. -/
theorem freeBound_congr (first second : List Reference)
    (same : ∀ level, .uninterned level ∈ first ↔ .uninterned level ∈ second) : freeBound first = freeBound second := by
  apply Nat.le_antisymm
  · exact freeBound_le first _ (fun level member => freeBound_lt second level ((same level).mp member))
  · exact freeBound_le second _ (fun level member => freeBound_lt first level ((same level).mpr member))

/-- Mapping literal captures maps the richer symbolic body while retaining its distinct local. -/
theorem symbolic_map (function : Reference → Reference) (body : Syntax Symbol Guard) (names : List Reference) :
    InternedDepthFreeProjectionCallback.symbolic body (names.map function) =
      (InternedDepthFreeProjectionCallback.symbolic body names).map (Sum.map id function) := by
  have mapped := evaluate_map (Sum.map id function) body
    (literal (.inl ()) :: (names.map literal).map (Shape.map Sum.inr))
  simpa [InternedDepthFreeProjectionCallback.symbolic, literal, Shape.map, List.map_map, Function.comp_def, Sum.map] using mapped

/-- Equal projected capture lists give identical predicted callback depth. -/
theorem projected_depth (body : Syntax Symbol Guard) (first second : List Reference)
    (same : first.map ordinaryNames = second.map ordinaryNames) :
    (InternedDepthFreeProjectionCallback.symbolic body first).depth = (InternedDepthFreeProjectionCallback.symbolic body second).depth := by
  have left := congrArg Shape.depth (symbolic_map ordinaryNames body first)
  have right := congrArg Shape.depth (symbolic_map ordinaryNames body second)
  rw [same] at left
  exact left.symm.trans right

/-- The independent captured free-name set retains the same ordinary names under equal projected inputs. -/
theorem projected_captures (body : Syntax Symbol Guard) (first second : List Reference)
    (same : first.map ordinaryNames = second.map ordinaryNames) (level : Nat) :
    .uninterned level ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (first.map (fun name => some [name])) (first.map (fun name => [name]))) ↔
    .uninterned level ∈ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (second.map (fun name => some [name])) (second.map (fun name => [name]))) := by
  have left := InternedFreeNameTransport.literal_captures_map ordinaryNames body first
  have right := InternedFreeNameTransport.literal_captures_map ordinaryNames body second
  rw [same] at left
  have equal := left.symm.trans right
  have members := congrArg (fun names => .uninterned level ∈ names) equal
  simpa only [ordinary_member] using Iff.of_eq members

/-- Two actual completed Depth callbacks choose the same repaired ordinary level from equal projected literal captures. -/
theorem callback_level [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (firstNames secondNames : List Reference) (same : firstNames.map ordinaryNames = secondNames.map ordinaryNames)
    (firstState secondState : State Symbol Guard)
    (firstContext : Context firstState (firstNames.map Value.reference)) (secondContext : Context secondState (secondNames.map Value.reference))
    (firstHeap : InternedFreshOrdinaryDepthHeap.Heap firstState) (secondHeap : InternedFreshOrdinaryDepthHeap.Heap secondState)
    (first second : Value Symbol Guard) (afterFirst afterSecond : State Symbol Guard)
    (firstDone : callback body (firstNames.map Value.reference) .depth firstState = .done first afterFirst)
    (secondDone : callback body (secondNames.map Value.reference) .depth secondState = .done second afterSecond) :
    ordinaryLevel first = ordinaryLevel second := by
  have left := (InternedFreshOrdinarySourceDepth.callback_depth body firstNames .depth firstState firstContext
    (InternedNestedProvenance.depth_available firstState) firstHeap).result _ _ firstDone
  have right := (InternedFreshOrdinarySourceDepth.callback_depth body secondNames .depth secondState secondContext
    (InternedNestedProvenance.depth_available secondState) secondHeap).result _ _ secondDone
  have depths := left.1.trans ((projected_depth body firstNames secondNames same).trans right.1.symm)
  have free : freeBound first.free = freeBound second.free := by
    apply freeBound_congr
    intro level
    have firstFree := InternedFreshOrdinarySourceFreeNames.callback_other body _ .depth firstState firstContext.normal
      (firstContext.local .depth (InternedNestedProvenance.depth_available firstState)).inputs firstContext.freeNames firstContext.profiles
      first afterFirst firstDone (.uninterned level) (by intro impossible; cases impossible)
    have secondFree := InternedFreshOrdinarySourceFreeNames.callback_other body _ .depth secondState secondContext.normal
      (secondContext.local .depth (InternedNestedProvenance.depth_available secondState)).inputs secondContext.freeNames secondContext.profiles
      second afterSecond secondDone (.uninterned level) (by intro impossible; cases impossible)
    simp only [List.map_map, Function.comp_def, InternedRootProfile.profile, Value.free] at firstFree secondFree
    exact firstFree.trans ((projected_captures body firstNames secondNames same level).trans secondFree.symm)
  simp only [ordinaryLevel, depths, free]

end MicroCFTA.InternedFreshOrdinaryLevelReplay
