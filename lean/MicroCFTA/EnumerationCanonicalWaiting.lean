import MicroCFTA.EnumerationWaitingIndex

/-!
# Waiting counts indexed by current variable classes

The renamed values are a count view. They are not an executed state.
Bucket transfers describe completed count updates. They do not assert an
invariant between the native union or assimilation writes.
-/

namespace MicroCFTA.EnumerationCanonicalWaiting
open EnumerationState EnumerationSchedule

variable {Symbol Guard : Type}

/-- Rename only the suspended references used by the count view. -/
def canonicalValue (roots : Nat → Nat) : UVarValue Symbol → UVarValue Symbol
  | .unenumerated node scs =>
      .unenumerated node (scs.map fun sc => {sc with var := roots sc.var})
  | .enumerated fragment => .enumerated fragment
  | .eliminated => .eliminated

/-- Apply the actual sparse counter fold at each current class key. -/
def count (roots : Nat → Nat) (change : Int) (scs : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) : EnumerationWaitingIndex.Waiting :=
  EnumerationWaitingIndex.count change
    (scs.map fun sc => {sc with var := roots sc.var}) waiting

/-- Remove the old slot references before adding its replacement references. -/
def replace (roots : Nat → Nat) (old new : UVarValue Symbol)
    (waiting : EnumerationWaitingIndex.Waiting) : EnumerationWaitingIndex.Waiting :=
  count roots 1 (references new) (count roots (-1) (references old) waiting)

/-- Every stored count is the exact number of references to its current class. -/
def Correct (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) : Prop :=
  EnumerationWaitingIndex.Correct (values.map (canonicalValue roots)) waiting

/-- Redirect one old bucket to the selected target bucket. -/
def redirect (target source : Nat) (roots : Nat → Nat) : Nat → Nat :=
  fun uv => if roots uv = source then target else roots uv

/-- Delete the old key and add its full count at the distinct target key. -/
def move (target source : Nat) (waiting : EnumerationWaitingIndex.Waiting) :
    EnumerationWaitingIndex.Waiting :=
  if target = source then waiting else
    match waiting source with
    | none => waiting
    | some waits => fun uv =>
        if uv = source then none
        else if uv = target then some (waits + (waiting target).getD 0)
        else waiting uv

/-- Transfer each supplied old bucket once in the supplied order. -/
def moveMany (target : Nat) (sources : List Nat) (waiting : EnumerationWaitingIndex.Waiting) :
    EnumerationWaitingIndex.Waiting :=
  sources.foldl (fun previous source => move target source previous) waiting

/-- Reference renaming preserves every trie and occurrence. -/
@[simp] theorem references_canonicalValue (roots : Nat → Nat) (value : UVarValue Symbol) :
    references (canonicalValue roots value) =
      (references value).map (fun sc => {sc with var := roots sc.var}) := by
  cases value <;> rfl

/-- Renaming suspended variable IDs does not change candidate membership. -/
@[simp] theorem candidate_canonicalValue (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (value : UVarValue Symbol) : candidate graph (canonicalValue roots value) = candidate graph value := by
  cases value with
  | unenumerated node scs =>
      cases node with
      | none => rfl
      | some node => cases view : graph.node node <;> simp [canonicalValue, candidate, view]
  | enumerated fragment => rfl
  | eliminated => rfl

private theorem replace_eq (roots : Nat → Nat) (old new : UVarValue Symbol)
    (waiting : EnumerationWaitingIndex.Waiting) :
    replace roots old new waiting = EnumerationWaitingIndex.replace
      (canonicalValue roots old) (canonicalValue roots new) waiting := by
  simp only [replace, count, EnumerationWaitingIndex.replace, references_canonicalValue]

/-- A fixed class map gives exact replacement counts at a stored raw slot. -/
theorem replace_correct (roots : Nat → Nat) (values : List (UVarValue Symbol)) (index : Nat)
    (old new : UVarValue Symbol) (stored : values[index]? = some old)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots (values.set index new) (replace roots old new waiting) := by
  unfold Correct at *
  rw [replace_eq, List.map_set]
  exact EnumerationWaitingIndex.replace_correct (values.map (canonicalValue roots)) index
    (canonicalValue roots old) (canonicalValue roots new) (by simp [stored]) waiting correct

/-- A fresh slot with no suspended references keeps every class count. -/
theorem allocate_correct (roots : Nat → Nat) (values : List (UVarValue Symbol)) (node : Option Nat)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots (values ++ [.unenumerated node []]) waiting := by
  unfold Correct at *
  simpa [canonicalValue] using
    EnumerationWaitingIndex.allocate_correct (values.map (canonicalValue roots)) node waiting correct

/-- The initial root has no waiting reference under any class map. -/
theorem initial_correct (roots : Nat → Nat) (root : Nat) :
    Correct (Symbol := Symbol) roots [.unenumerated (some root) []] (fun _ => none) := by
  simpa [Correct, canonicalValue] using EnumerationWaitingIndex.initial_correct (Symbol := Symbol) root

/-- The stored keys are exactly the current classes named by suspended references. -/
theorem support_exact (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) (key : Nat) :
    waiting key ≠ none ↔ ∃ value ∈ values, ∃ sc ∈ references value, roots sc.var = key := by
  have original := EnumerationWaitingIndex.support_exact
    (values.map (canonicalValue roots)) waiting correct key
  constructor
  · intro stored
    obtain ⟨mapped, member, sc, present, named⟩ := original.mp stored
    obtain ⟨value, valueMember, same⟩ := List.mem_map.mp member
    subst mapped
    rw [references_canonicalValue] at present
    obtain ⟨old, oldMember, same⟩ := List.mem_map.mp present
    subst sc
    exact ⟨value, valueMember, old, oldMember, named⟩
  · rintro ⟨value, valueMember, sc, present, named⟩
    apply original.mpr
    refine ⟨canonicalValue roots value, List.mem_map.mpr ⟨value, valueMember, rfl⟩,
      {sc with var := roots sc.var}, ?_, named⟩
    rw [references_canonicalValue]
    exact List.mem_map.mpr ⟨sc, present, rfl⟩

private abbrev total (roots : Nat → Nat) (values : List (UVarValue Symbol)) (key : Nat) : Int :=
  EnumerationWaitingIndex.total key (values.map (canonicalValue roots))

private theorem occurrences_redirect (target source : Nat) (roots : Nat → Nat)
    (scs : List Suspended) (key : Nat) (different : source ≠ target) :
    EnumerationWaitingIndex.occurrences key
      (scs.map (fun sc => {sc with var := redirect target source roots sc.var})) =
      if key = source then 0
      else if key = target then
        EnumerationWaitingIndex.occurrences source (scs.map (fun sc => {sc with var := roots sc.var})) +
        EnumerationWaitingIndex.occurrences target (scs.map (fun sc => {sc with var := roots sc.var}))
      else EnumerationWaitingIndex.occurrences key (scs.map (fun sc => {sc with var := roots sc.var})) := by
  induction scs with
  | nil => simp [EnumerationWaitingIndex.occurrences]
  | cons first rest ih =>
      by_cases atSource : key = source
      · subst key
        by_cases named : roots first.var = source <;>
          simp_all [redirect, EnumerationWaitingIndex.occurrences]
        all_goals omega
      · by_cases atTarget : key = target
        · subst key
          by_cases named : roots first.var = source
          · (simp_all [redirect, EnumerationWaitingIndex.occurrences]; omega)
          · by_cases namedTarget : roots first.var = target <;>
              simp_all [redirect, EnumerationWaitingIndex.occurrences]
            all_goals omega
        · by_cases named : roots first.var = source <;>
            simp_all [redirect, EnumerationWaitingIndex.occurrences]
          all_goals omega

private theorem total_redirect (target source : Nat) (roots : Nat → Nat)
    (values : List (UVarValue Symbol)) (key : Nat) (different : source ≠ target) :
    total (redirect target source roots) values key =
      if key = source then 0
      else if key = target then total roots values source + total roots values target
      else total roots values key := by
  induction values with
  | nil => simp [total, EnumerationWaitingIndex.total]
  | cons value rest ih =>
      have first := occurrences_redirect target source roots (references value) key different
      simp only [total, List.map_cons, EnumerationWaitingIndex.total, references_canonicalValue] at *
      by_cases atSource : key = source <;> by_cases atTarget : key = target <;> simp_all
      all_goals omega

/-- The literal sparse move matches a class-map redirection without root-fixed premises. -/
theorem move_correct (target source : Nat) (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct (redirect target source roots) values (move target source waiting) := by
  by_cases same : target = source
  · subst target
    have unchanged : redirect source source roots = roots := by
      funext uv
      by_cases named : roots uv = source <;> simp [redirect, named]
    simpa [move, unchanged] using correct
  · have old : ∀ key, waiting key = EnumerationWaitingIndex.encode (total roots values key) := correct
    change ∀ key, move target source waiting key =
      EnumerationWaitingIndex.encode (total (redirect target source roots) values key)
    intro key
    have transferred := total_redirect target source roots values key (Ne.symm same)
    cases sourceValue : waiting source with
    | none =>
        have sourceZero : total roots values source = 0 := by
          have encoded := old source
          rw [sourceValue] at encoded
          by_cases zero : total roots values source = 0
          · exact zero
          · simp [EnumerationWaitingIndex.encode, zero] at encoded
        simp only [move, ite_eq_right same, sourceValue]
        rw [old key, transferred]
        by_cases atSource : key = source <;> by_cases atTarget : key = target <;>
          simp_all [EnumerationWaitingIndex.encode]
    | some amount =>
        have positive : 0 < amount := EnumerationWaitingIndex.stored_positive
          (values.map (canonicalValue roots)) waiting correct source amount sourceValue
        have sourceNonzero : total roots values source ≠ 0 := by
          intro zero
          have encoded := old source
          rw [sourceValue, zero] at encoded
          simp [EnumerationWaitingIndex.encode] at encoded
        have sourceCount : total roots values source = amount := by
          have encoded := sourceValue
          rw [old source] at encoded
          simpa [EnumerationWaitingIndex.encode, sourceNonzero] using encoded
        have targetCount : (waiting target).getD 0 = total roots values target := by
          rw [old target]
          exact EnumerationWaitingIndex.encode_read _
        have targetNonnegative : 0 ≤ total roots values target :=
          EnumerationWaitingIndex.total_nonnegative target (values.map (canonicalValue roots))
        simp only [move, ite_eq_right same, sourceValue]
        rw [transferred]
        by_cases atSource : key = source
        · subst key
          simp [EnumerationWaitingIndex.encode]
        · by_cases atTarget : key = target
          · subst key
            simp only [ite_eq_right atSource]
            rw [targetCount]
            have sumNonzero : amount + total roots values target ≠ 0 := by omega
            simp [EnumerationWaitingIndex.encode, sourceCount, sumNonzero]
          · simp only [ite_eq_right atSource, ite_eq_right atTarget]
            exact old key

/-- A transfer fold maintains the count view under the matching ghost redirect fold. -/
theorem moveMany_correct (target : Nat) (sources : List Nat) (roots : Nat → Nat)
    (values : List (UVarValue Symbol)) (waiting : EnumerationWaitingIndex.Waiting)
    (correct : Correct roots values waiting) :
    Correct (sources.foldl (fun previous source => redirect target source previous) roots) values
      (moveMany target sources waiting) := by
  induction sources generalizing roots waiting with
  | nil => exact correct
  | cons source rest ih =>
      simpa only [moveMany, List.foldl_cons] using
        ih (redirect target source roots) (move target source waiting)
          (move_correct target source roots values waiting correct)

/-- Completed assimilation keeps the counts when it moves all source references to the target. -/
theorem assimilation_correct (roots : Nat → Nat) (values : List (UVarValue Symbol))
    (target source : Nat) (oldSource oldTarget merged : UVarValue Symbol)
    (different : target ≠ source) (sourceRead : values[source]? = some oldSource)
    (targetRead : values[target]? = some oldTarget)
    (mergedRefs : references merged = references oldSource ++ references oldTarget)
    (waiting : EnumerationWaitingIndex.Waiting) (correct : Correct roots values waiting) :
    Correct roots ((values.set target merged).set source .eliminated) waiting := by
  unfold Correct at *
  rw [List.map_set, List.map_set]
  intro key
  have targetStored : (values.map (canonicalValue roots))[target]? =
      some (canonicalValue roots oldTarget) := by simp [targetRead]
  have sourceStored : ((values.map (canonicalValue roots)).set target
      (canonicalValue roots merged))[source]? = some (canonicalValue roots oldSource) := by
    rw [List.getElem?_set_ne different]
    simp [sourceRead]
  have mergedCount : EnumerationWaitingIndex.occurrences key (references (canonicalValue roots merged)) =
      EnumerationWaitingIndex.occurrences key (references (canonicalValue roots oldSource)) +
      EnumerationWaitingIndex.occurrences key (references (canonicalValue roots oldTarget)) := by
    simp only [references_canonicalValue, mergedRefs, List.map_append,
      EnumerationWaitingIndex.occurrences_append]
  apply Eq.trans (correct key)
  apply congrArg EnumerationWaitingIndex.encode
  rw [show canonicalValue roots (.eliminated : UVarValue Symbol) = .eliminated from rfl]
  rw [EnumerationWaitingIndex.total_set key source
      ((values.map (canonicalValue roots)).set target (canonicalValue roots merged))
      (canonicalValue roots oldSource) .eliminated sourceStored,
    EnumerationWaitingIndex.total_set key target (values.map (canonicalValue roots))
      (canonicalValue roots oldTarget) (canonicalValue roots merged) targetStored]
  simp only [references, EnumerationWaitingIndex.occurrences] at mergedCount ⊢
  omega

end MicroCFTA.EnumerationCanonicalWaiting
