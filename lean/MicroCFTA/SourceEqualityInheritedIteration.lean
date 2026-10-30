import MicroCFTA.SourceEqualityNormalizationFuel
import MicroCFTA.SourceEqualityInheritedPayload

/-!
# Finite observations of inherited payload feedback

These sequences use the actual combination and indexed descent operations.
They do not assume that a complete native worker admits the sequence.
-/
namespace MicroCFTA.SourceEqualityInheritedIteration
open EqualityNormalize SourceEqualityClassOrder
open SourceEqualityNormalizationFuel

private theorem normalize_nil : SourceCompactGuards.normalize [] = some [] :=
  normalize_finished [] 1 (.normalized []) (by decide +kernel) (by intro impossible; cases impossible)

private theorem combine_some (first second : Constraints) :
    SourceCompactGuards.combineEqualities (some first) (some second) =
      SourceCompactGuards.normalize (first ++ second) := by
  cases first <;> cases second <;>
    simp [SourceCompactGuards.combineEqualities, normalize_nil]

/-- A finite reference observation retains timeout and physical readback errors. -/
def combineReference (fuel : Nat) (inherited own : SourceEqualityPrecheck.Constraint) :
    Option (Except String SourceEqualityPrecheck.Constraint) :=
  match inherited, own with
  | none, _ | _, none => some (.ok none)
  | some first, some second =>
      match mkEqConstraints fuel (first.map Record.paths ++ second.map Record.paths) with
      | .timeout => none
      | .contradiction => some (.ok none)
      | .normalized output => some (SourceEqualityPhysicalPayload.read (some output))

/-- Every completed finite reference observation is the actual physical combination. -/
theorem combineReference_exact (fuel : Nat) (inherited own : SourceEqualityPrecheck.Constraint)
    (result : Except String SourceEqualityPrecheck.Constraint)
    (done : combineReference fuel inherited own = some result) :
    SourceEqualityInheritedPayload.combine inherited own = result := by
  cases inherited with
  | none => simpa [combineReference, SourceEqualityInheritedPayload.combine,
      SourceEqualityInheritedPayload.classes, SourceCompactGuards.combineEqualities,
      SourceEqualityPhysicalPayload.read] using done
  | some first =>
      cases own with
      | none => simpa [combineReference, SourceEqualityInheritedPayload.combine,
          SourceEqualityInheritedPayload.classes, SourceCompactGuards.combineEqualities,
          SourceEqualityPhysicalPayload.read] using done
      | some second =>
          cases observed : mkEqConstraints fuel (first.map Record.paths ++ second.map Record.paths) with
          | timeout => simp [combineReference, observed] at done
          | contradiction =>
              have norm := normalize_finished _ fuel .contradiction observed (by intro impossible; cases impossible)
              change SourceEqualityPhysicalPayload.read
                (SourceCompactGuards.combineEqualities (some _) (some _)) = result
              rw [combine_some, norm]
              simpa [combineReference, observed, SymbolicEqualityBridge.resultClasses,
                SourceEqualityPhysicalPayload.read] using done
          | normalized output =>
              have norm := normalize_finished _ fuel (.normalized output) observed (by intro impossible; cases impossible)
              change SourceEqualityPhysicalPayload.read
                (SourceCompactGuards.combineEqualities (some _) (some _)) = result
              rw [combine_some, norm]
              simpa [combineReference, observed, SymbolicEqualityBridge.resultClasses] using done

/-- Repeat the actual combination and physical child descent with the same own payload. -/
noncomputable def iterate (index : Nat) (own : SourceEqualityPrecheck.Constraint) :
    Nat → SourceEqualityPrecheck.Constraint → Except String SourceEqualityPrecheck.Constraint
  | 0, inherited => .ok inherited
  | count + 1, inherited => do
      let combined ← SourceEqualityInheritedPayload.combine inherited own
      iterate index own count (SourceEqualityDescend.descend combined index)

/-- Observe the same finite sequence with a bounded reference normalizer at each step. -/
def reference (fuel index : Nat) (own : SourceEqualityPrecheck.Constraint) :
    Nat → SourceEqualityPrecheck.Constraint → Option (Except String SourceEqualityPrecheck.Constraint)
  | 0, inherited => some (.ok inherited)
  | count + 1, inherited =>
      match combineReference fuel inherited own with
      | none => none
      | some (.error message) => some (.error message)
      | some (.ok combined) => reference fuel index own count (SourceEqualityDescend.descend combined index)

/-- A completed reference sequence determines the entire actual physical sequence. -/
theorem reference_exact (fuel index : Nat) (own : SourceEqualityPrecheck.Constraint)
    (count : Nat) (inherited : SourceEqualityPrecheck.Constraint)
    (result : Except String SourceEqualityPrecheck.Constraint)
    (done : reference fuel index own count inherited = some result) :
    iterate index own count inherited = result := by
  induction count generalizing inherited result with
  | zero => simpa [reference, iterate] using done
  | succ count ih =>
      cases observed : combineReference fuel inherited own with
      | none => simp [reference, observed] at done
      | some step =>
          have actual := combineReference_exact fuel inherited own step observed
          cases step with
          | error message => simpa [reference, observed, iterate, actual, Bind.bind, Except.bind] using done
          | ok combined =>
              have tail : reference fuel index own count (SourceEqualityDescend.descend combined index) = some result := by
                simpa [reference, observed] using done
              simpa [iterate, actual, Bind.bind, Except.bind] using ih _ result tail

end MicroCFTA.SourceEqualityInheritedIteration
