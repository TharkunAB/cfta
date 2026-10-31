import MicroCFTA.EnumerationCanonicalWaiting

/-! Reference append uses the actual canonical optional-count representation. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingWaitingAppend
open EnumerationState EnumerationSchedule
variable {Symbol : Type}

private theorem occurrences_append (uv : Nat) (left right : List Suspended) :
    EnumerationWaitingIndex.occurrences uv (left ++ right) =
      EnumerationWaitingIndex.occurrences uv left + EnumerationWaitingIndex.occurrences uv right := by
  induction left with
  | nil =>
      simp only [List.nil_append, EnumerationWaitingIndex.occurrences]
      omega
  | cons first rest ih =>
      simp only [List.cons_append, EnumerationWaitingIndex.occurrences, ih]
      omega

private theorem append_cancel (roots : Nat → Nat) (incoming old : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (canonical : EnumerationWaitingIndex.Canonical waiting) :
    EnumerationCanonicalWaiting.count roots 1 (incoming ++ old)
        (EnumerationCanonicalWaiting.count roots (-1) old waiting) =
      EnumerationCanonicalWaiting.count roots 1 incoming waiting := by
  let normalize : Suspended → Suspended := fun sc => {sc with var := roots sc.var}
  change EnumerationWaitingIndex.count 1 ((incoming ++ old).map normalize)
      (EnumerationWaitingIndex.count (-1) (old.map normalize) waiting) =
    EnumerationWaitingIndex.count 1 (incoming.map normalize) waiting
  have removedCanonical := EnumerationWaitingIndex.count_canonical (-1) (old.map normalize) waiting canonical
  have leftCanonical := EnumerationWaitingIndex.count_canonical 1 ((incoming ++ old).map normalize)
    (EnumerationWaitingIndex.count (-1) (old.map normalize) waiting) removedCanonical
  have rightCanonical := EnumerationWaitingIndex.count_canonical 1 (incoming.map normalize) waiting canonical
  funext uv
  rw [leftCanonical uv, rightCanonical uv]
  apply congrArg EnumerationWaitingIndex.encode
  simp only [EnumerationWaitingIndex.count_read, List.map_append, occurrences_append]
  omega

/-- Original waiting correctness and stored references derive correctness after exact append. -/
theorem append_correct (roots : Nat → Nat) (values : List (UVarValue Symbol)) (target : Nat)
    (oldNode newNode : Option Nat) (incoming old : List Suspended) (waiting : EnumerationWaitingIndex.Waiting)
    (stored : values[target]? = some (.unenumerated oldNode old))
    (correct : EnumerationCanonicalWaiting.Correct roots values waiting) :
    EnumerationCanonicalWaiting.Correct roots
      (values.set target (.unenumerated newNode (incoming ++ old)))
      (EnumerationCanonicalWaiting.count roots 1 incoming waiting) := by
  have canonical : EnumerationWaitingIndex.Canonical waiting :=
    (EnumerationWaitingIndex.Correct.facts correct).1
  have replaced := EnumerationCanonicalWaiting.replace_correct roots values target
    (.unenumerated oldNode old) (.unenumerated newNode (incoming ++ old)) stored waiting correct
  simpa only [EnumerationCanonicalWaiting.replace, references,
    append_cancel roots incoming old waiting canonical] using replaced

end MicroCFTA.SourceCurrentIncomingWaitingAppend
