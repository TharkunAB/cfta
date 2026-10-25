import MicroCFTA.EnumerationOrder
import MicroCFTA.EnumerationCompressionFrame

namespace MicroCFTA.EnumerationOrder
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
variable {Symbol Guard : Type}

/-- Representative compression preserves the stored dependency levels. -/
theorem frame_stratified (before after : State Symbol Guard) (frame : Frame before after)
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified before level frontier) :
    Stratified after level frontier := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right same
    apply stratified.classes left right
    simpa only [UnionFind.SameClass, frame.reaches] using same
  · intro uv fragment stored
    exact stratified.expanded uv fragment (by simpa only [frame.values] using stored)
  · intro uv node scs stored
    exact stratified.pending uv node scs (by simpa only [frame.values] using stored)

/-- Replacing a stored pending slot preserves the same dependency levels and frontier. -/
theorem setValue_pending_stratified (slot : Nat) (oldNode newNode : Option Nat)
    (oldScs newScs : List Suspended) (before after : State Symbol Guard)
    (stored : before.values[slot]? = some (.unenumerated oldNode oldScs))
    (level : Nat → Nat) (frontier : Nat) (stratified : Stratified before level frontier)
    (written : Success (setValue slot (.unenumerated newNode newScs)) before () after) :
    Stratified after level frontier := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  have inside := (List.getElem?_eq_some_iff.mp stored).1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [shape] using stratified.classes
  · intro uv fragment expanded
    have different : uv ≠ slot := by
      intro same
      subst uv
      simp only [shape, List.getElem?_set_self inside] at expanded
      cases expanded
    apply stratified.expanded uv fragment
    simpa only [shape, List.getElem?_set_ne (Ne.symm different)] using expanded
  · intro uv node scs pending
    by_cases same : uv = slot
    · subst uv
      exact stratified.pending slot oldNode oldScs stored
    · apply stratified.pending uv node scs
      simpa only [shape, List.getElem?_set_ne (Ne.symm same)] using pending

end MicroCFTA.EnumerationOrder
