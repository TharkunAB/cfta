import MicroCFTA.EnumerationReferences
import MicroCFTA.EnumerationCompressionFrame

namespace MicroCFTA.EnumerationPendingReplacement
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame EnumerationReferences
variable {Symbol Guard : Type}

/-- Representative compression retains the absence of incoming suspended references. -/
theorem frame_incoming (held : Nat) (before after : State Symbol Guard)
    (frame : Frame before after) (incoming : IncomingAvoid held before) : IncomingAvoid held after := by
  intro value member sc listed same
  apply incoming value (by simpa only [frame.values] using member) sc listed
  simpa only [UnionFind.SameClass, frame.reaches] using same

/-- Representative compression retains the avoidance of every enumerated class. -/
theorem frame_pending (before after : State Symbol Guard)
    (frame : Frame before after) (pending : PendingReferences before) : PendingReferences after := by
  intro held fragment stored
  apply frame_incoming held before after frame
  exact pending held fragment (by simpa only [frame.values] using stored)

/-- Replacing only a pending node handle retains each incoming-reference condition. -/
theorem setValue_incoming (held slot : Nat) (oldNode newNode : Option Nat) (scs : List Suspended)
    (before after : State Symbol Guard)
    (stored : before.values[slot]? = some (.unenumerated oldNode scs))
    (incoming : IncomingAvoid held before)
    (written : Success (setValue slot (.unenumerated newNode scs)) before () after) : IncomingAvoid held after := by
  have payload : InputsAllowed (fun uv => ¬UnionFind.SameClass before.representatives held uv) scs :=
    incoming _ (List.mem_of_getElem? stored)
  have allowed := setValue_allowed (fun uv => ¬UnionFind.SameClass before.representatives held uv)
    slot (.unenumerated newNode scs) before after incoming payload written
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  simpa only [IncomingAvoid, shape] using allowed

/-- Replacing only a pending node handle retains global pending-reference history. -/
theorem setValue_pending (slot : Nat) (oldNode newNode : Option Nat) (scs : List Suspended)
    (before after : State Symbol Guard)
    (stored : before.values[slot]? = some (.unenumerated oldNode scs))
    (pending : PendingReferences before)
    (written : Success (setValue slot (.unenumerated newNode scs)) before () after) : PendingReferences after := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  intro held fragment expanded
  have different : held ≠ slot := by
    intro same
    subst held
    have inside : slot < before.values.length := (List.getElem?_eq_some_iff.mp stored).1
    simp only [shape, List.getElem?_set_self inside] at expanded
    cases expanded
  have original : before.values[held]? = some (.enumerated fragment) := by
    simpa only [shape, List.getElem?_set_ne (Ne.symm different)] using expanded
  exact setValue_incoming held slot oldNode newNode scs before after stored
    (pending held fragment original) written

/-- Clearing a pending bucket retains each incoming-reference condition. -/
theorem setValue_clear_incoming (held slot : Nat) (node : Option Nat)
    (before after : State Symbol Guard) (incoming : IncomingAvoid held before)
    (written : Success (setValue slot (.unenumerated node [])) before () after) : IncomingAvoid held after := by
  have allowed := setValue_allowed (fun uv => ¬UnionFind.SameClass before.representatives held uv)
    slot (.unenumerated node []) before after incoming (by simp [references, InputsAllowed]) written
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  simpa only [IncomingAvoid, shape] using allowed

/-- Clearing a stored pending bucket creates no enumerated slot or suspended reference. -/
theorem setValue_clear_pending (slot : Nat) (node : Option Nat) (scs : List Suspended)
    (before after : State Symbol Guard)
    (stored : before.values[slot]? = some (.unenumerated node scs))
    (pending : PendingReferences before)
    (written : Success (setValue slot (.unenumerated node [])) before () after) : PendingReferences after := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  intro held fragment expanded
  have different : held ≠ slot := by
    intro same
    subst held
    have inside : slot < before.values.length := (List.getElem?_eq_some_iff.mp stored).1
    simp only [shape, List.getElem?_set_self inside] at expanded
    cases expanded
  have original : before.values[held]? = some (.enumerated fragment) := by
    simpa only [shape, List.getElem?_set_ne (Ne.symm different)] using expanded
  exact setValue_clear_incoming held slot node before after (pending held fragment original) written

end MicroCFTA.EnumerationPendingReplacement
