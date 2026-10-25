import MicroCFTA.SourcePruningEnumerationTerminal
import MicroCFTA.SourceUnionFindRoot
import MicroCFTA.MergedOrdinaryHeight
import MicroCFTA.EnumerationExpandableIndex

namespace MicroCFTA.SourcePruningEnumerationNativeIndex
open EnumerationState EnumerationSchedule SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance nativeIndexMonadList : Monad List := {
  pure := fun value => [value]
  bind := fun values continuation => values.flatMap continuation
}

/-- Classify the actual decoded node without replacing a missing handle. -/
def candidate
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (value : EnumerationState.UVarValue Symbol) : Option Bool :=
  match value with
  | .unenumerated node scs =>
      match node with
      | none => some false
      | some handle =>
          (lookupNode heap handle).map fun decodedValue =>
            !(MergedOrdinaryHeight.recursiveBoundary decodedValue && scs.isEmpty)
  | .enumerated _ | .eliminated => some false

/-- Count each occurrence at its current read-only representative. -/
def count
    (fuel : Nat) (forest : UnionFind.Forest) (change : Int)
    (scs : List EnumerationState.Suspended) (waiting : EnumerationWaitingIndex.Waiting) :
    Option EnumerationWaitingIndex.Waiting :=
  match scs with
  | [] => some waiting
  | sc :: rest =>
      (SourceUnionFindRoot.root fuel forest sc.var).bind fun representative =>
        count fuel forest change rest (EnumerationWaitingIndex.bump change representative waiting)

/-- Update the raw slot and remove lost counts before adding gained counts. -/
def write
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : EnumerationState.UVarValue Symbol)
    (gained lost : List EnumerationState.Suspended)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard) :
    Option (EnumerationExpandableIndex.Cached Symbol EnumGuard) :=
  (candidate heap value).bind fun flag =>
    (count fuel before.core.representatives (-1) lost before.waiting).bind fun removed =>
      (count fuel before.core.representatives 1 gained removed).bind fun saved =>
        some ⟨{before.core with values := before.core.values.set target value},
          fun other => if other = target then flag else before.expandable other, saved⟩

/-- Finite parent paths give one bound for every change and waiting map. -/
theorem count_complete
    (forest : UnionFind.Forest) (roots : Nat → Nat)
    (paths : Roots forest roots) (scs : List EnumerationState.Suspended) :
    ∃ (fuel : Nat), ∀ (extra : Nat) (change : Int) (waiting : EnumerationWaitingIndex.Waiting),
      count (fuel + extra) forest change scs waiting =
        some (EnumerationCanonicalWaiting.count roots change scs waiting) := by
  induction scs with
  | nil => exact ⟨0, fun _ _ _ => rfl⟩
  | cons sc rest ih =>
    obtain ⟨tailFuel, tailRun⟩ := ih
    obtain ⟨size, path⟩ := paths sc.var
    obtain ⟨headFuel, headRun⟩ :=
      SourceUnionFindRoot.root_terminates forest sc.var (roots sc.var) size path
    refine ⟨headFuel + tailFuel, ?_⟩
    intro extra change waiting
    have rootRun : SourceUnionFindRoot.root (headFuel + tailFuel + extra) forest sc.var =
      some (roots sc.var) := by
      simpa only [Nat.add_assoc] using
        SourceUnionFindRoot.root_moreFuel headFuel (tailFuel + extra) forest sc.var (roots sc.var) headRun
    rw [count, rootRun, Option.bind_some]
    simpa only [EnumerationCanonicalWaiting.count, List.map_cons,
      EnumerationWaitingIndex.count, List.foldl_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using tailRun (headFuel + extra) change (EnumerationWaitingIndex.bump change (roots sc.var) waiting)

/-- Derive native indexes at the same observed value-write and ancestry prefix. -/
theorem gained_complete
    (heap nextHeap : InternedConstructorTemplates.State Symbol NativeGuard)
    (kept : SourceEqualityRequiredCache.Keeps heap nextHeap)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (after : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (oldNode : Option Nat) (oldScs incomingScs : List EnumerationState.Suspended)
    (handle : Nat) (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (stored : before.core.values[target]? = some (.unenumerated oldNode oldScs))
    (decoded : lookupNode nextHeap handle = some value)
    (aligned : before.core.counter = before.core.values.length)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat),
      candidate heap ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (actualPrefix : ExceptT.run ((do
      setValue target (.unenumerated (some handle) (incomingScs ++ oldScs))
      inheritAncestry target) before.core) = [.ok ((), after)]) :
    ∃ (fuel : Nat) (written : EnumerationExpandableIndex.Cached Symbol EnumGuard),
      (∀ (extra : Nat), write nextHeap (fuel + extra) target
        (.unenumerated (some handle) (incomingScs ++ oldScs)) incomingScs [] before = some written) ∧
      written.core = {before.core with
        values := before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))} ∧
      written.expandable = (fun (slot : Nat) => if slot = target then
        !(MergedOrdinaryHeight.recursiveBoundary value && (incomingScs ++ oldScs).isEmpty)
        else before.expandable slot) ∧
      written.waiting = EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting ∧
      (EnumerationExpandableIndex.frame after written).core = after ∧
      after.counter = after.values.length ∧ Roots after.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.values written.waiting ∧
      (∀ (slot : Nat),
        candidate nextHeap ((after.values[slot]?).getD .eliminated) = some (written.expandable slot)) := by
  obtain ⟨fuel, countRun⟩ := count_complete before.core.representatives roots paths incomingScs
  have inside : target < before.core.values.length := by
    exact (List.getElem?_eq_some_iff.mp stored).elim (fun bound _elementEquality => bound)
  have afterSame : after = {before.core with
    values := before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.core.expansionAncestry ++ before.core.recursionAncestry target).eraseDups
      else before.core.recursionAncestry other} := by
    change [(Except.ok ((), {before.core with
      values := before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.core.expansionAncestry ++ before.core.recursionAncestry target).eraseDups
        else before.core.recursionAncestry other}) :
          Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard))] =
      [Except.ok ((), after)] at actualPrefix
    exact (Prod.mk.inj (Except.ok.inj (List.cons.inj actualPrefix).1)).2.symm
  have grownFlags : ∀ (slot : Nat),
    candidate nextHeap ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot) := by
    intro slot
    specialize flags slot
    generalize slotValueSame : ((before.core.values[slot]?).getD .eliminated) = slotValue at flags ⊢
    clear slotValueSame
    cases slotValue with
    | enumerated _ => exact flags
    | eliminated => exact flags
    | unenumerated node scs =>
      cases node with
      | none => exact flags
      | some oldHandle =>
        cases oldLookup : lookupNode heap oldHandle with
        | none =>
          simp only [candidate, oldLookup, Option.map_none] at flags
          cases flags
        | some oldValue =>
          simpa only [candidate, oldLookup,
            lookupNode_keeps heap nextHeap kept oldHandle oldValue oldLookup, Option.map_some] using flags
  have writtenFlags : ∀ (slot : Nat),
    candidate nextHeap (((before.core.values.set target
      (.unenumerated (some handle) (incomingScs ++ oldScs)))[slot]?).getD .eliminated) =
      some (if slot = target then
        !(MergedOrdinaryHeight.recursiveBoundary value && (incomingScs ++ oldScs).isEmpty)
        else before.expandable slot) := by
    intro slot
    by_cases same : slot = target
    · subst slot
      simp only [List.getElem?_set_self inside, Option.getD_some, candidate, decoded,
        Option.map_some, ↓reduceIte]
    · simpa only [List.getElem?_set_ne (Ne.symm same), ite_eq_right same] using grownFlags slot
  refine ⟨fuel, ⟨{before.core with
    values := before.core.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))},
    fun slot => if slot = target then
      !(MergedOrdinaryHeight.recursiveBoundary value && (incomingScs ++ oldScs).isEmpty)
      else before.expandable slot,
    EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting⟩,
    ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro extra
    simp only [write, candidate, decoded, Option.map_some,
      show count (fuel + extra) before.core.representatives (-1) [] before.waiting =
        some before.waiting from rfl,
      Option.bind_some, countRun extra 1 before.waiting]
  · simpa only [afterSame, List.length_set] using aligned
  · simpa only [afterSame] using paths
  · simpa only [afterSame] using
      SourcePruningEnumerationTerminal.gained_correct before.core.values target oldNode
        (some handle) incomingScs oldScs roots before.waiting stored counts
  · simpa only [afterSame] using writtenFlags

end MicroCFTA.SourcePruningEnumerationNativeIndex
