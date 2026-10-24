import MicroCFTA.Language

/-!
# Constructor-name checks after node-view shape validation

The source first checks every constructor shape. It then reports the first
positional name that lacks the required prefix. This model retains the
actual name order and rendered name error. Earlier shape results remain
explicit. Generic metadata extraction and node-view semantics are separate.
-/
namespace MicroCFTA.SourceDeriveNodeViewNames

/-- Each position retains its original datatype name and node-view name. -/
abbrev Names := String × String

/-- The source uses a case-sensitive character prefix, with no delimiter check. -/
def hasPrefix (names : Names) : Bool := names.1.toList.isPrefixOf names.2.toList

/-- Independent positional validity means that the view name extends the datatype name. -/
def Extends (names : Names) : Prop :=
  ∃ suffix : List Char, names.1.toList ++ suffix = names.2.toList

/-- The actual character test agrees with independent prefix extension. -/
theorem hasPrefix_exact (names : Names) : hasPrefix names = true ↔ Extends names :=
  List.isPrefixOf_iff_prefix

/-- The first source name failure retains both original positional names. -/
def firstMismatch (positions : List Names) : Option Names :=
  positions.find? fun names => !(hasPrefix names)

/-- The source error list preserves every failing occurrence in order. -/
theorem firstMismatch_eq_head (positions : List Names) :
    firstMismatch positions = (positions.filter fun names => !(hasPrefix names)).head? := List.head?_filter.symm

/-- Every supplied position passes exactly when every view name has its original prefix. -/
theorem firstMismatch_none (positions : List Names) :
    firstMismatch positions = none ↔ ∀ names ∈ positions, Extends names := by
  simp only [firstMismatch, List.find?_eq_none, Bool.not_eq_true, Bool.not_eq_false', hasPrefix_exact]

/-- A reported mismatch has an exact source position and no earlier mismatch. -/
theorem firstMismatch_some (positions : List Names) (failed : Names) :
    firstMismatch positions = some failed ↔
      hasPrefix failed = false ∧ ∃ earlier later,
        positions = earlier ++ failed :: later ∧ ∀ names ∈ earlier, hasPrefix names = true := by
  simpa only [firstMismatch, Bool.not_eq_true', Bool.not_not] using
    (List.find?_eq_some_iff_append (xs := positions) (p := fun names => !(hasPrefix names)) (b := failed))

/-- NodeMismatch keeps the datatype name and the exact source diagnostic. -/
def mismatch (names : Names) : String × String :=
  (names.1, "the node view has " ++ names.2 ++
    " in its place, a name that does not start with " ++ names.1)

/-- The completed name phase reports the first error from the source list. -/
def checkNames (positions : List Names) : Except (String × String) Unit :=
  match firstMismatch positions with
  | none => .ok ()
  | some names => .error (mismatch names)

/-- Successful name validation is exactly independent validity at every original position. -/
theorem checkNames_exact (positions : List Names) :
    checkNames positions = .ok () ↔ ∀ names ∈ positions, Extends names := by
  rw [← firstMismatch_none]
  unfold checkNames
  cases firstMismatch positions <;> simp

/-- A concrete failure preserves its literal source diagnostic and earlier passing positions. -/
theorem checkNames_first (positions : List Names) (failed : Names)
    (done : firstMismatch positions = some failed) :
    checkNames positions = .error (mismatch failed) ∧
      ∃ earlier later, positions = earlier ++ failed :: later ∧
        (∀ names ∈ earlier, Extends names) ∧ ¬ Extends failed := by
  obtain ⟨bad, earlier, later, order, good⟩ := (firstMismatch_some positions failed).mp done
  refine ⟨by simp only [checkNames, done], earlier, later, order, ?_, ?_⟩
  · exact fun names member => (hasPrefix_exact names).mp (good names member)
  · intro valid
    have yes := (hasPrefix_exact failed).mpr valid
    rw [bad] at yes
    cases yes

/-- The name phase runs only after the earlier complete shape phase succeeds. -/
def afterShape (earlier : Except (String × String) Unit) (positions : List Names) :
    Except (String × String) Unit := earlier.bind fun _ => checkNames positions

/-- Even a later constructor's shape error precedes any name error. -/
theorem afterShape_error (error : String × String) (positions : List Names) :
    afterShape (.error error) positions = .error error := rfl

/-- After successful shape checks, the name phase supplies the remaining exact condition. -/
theorem afterShape_exact (earlier : Except (String × String) Unit) (positions : List Names) :
    afterShape earlier positions = .ok () ↔
      earlier = .ok () ∧ ∀ names ∈ positions, Extends names := by
  cases earlier with
  | error error => simp [afterShape, Except.bind]
  | ok value => cases value; simpa only [afterShape, Except.bind, true_and] using checkNames_exact positions

end MicroCFTA.SourceDeriveNodeViewNames
