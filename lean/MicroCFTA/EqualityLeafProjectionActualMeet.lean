import MicroCFTA.EqualityLeafProjectionEditAvailability
import MicroCFTA.EqualityRawLeafAvailability

/-!
# Actual leaf intersections discharge worker payload preservation

Each target declaration list is built through the source cache constructors.
The physical global identity branch returns its available target record.
The Cartesian branch uses the actual row constructor, including rejected
raw sentinel effects. No leaf payload-preservation contract is assumed.
-/
namespace MicroCFTA.EqualityLeafProjectionActualMeet
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionEditAvailability
open EqualityLeafProjectionWorkers (sequence_safe)
open EqualityLeafProjectionLeafCache (ConstraintKey Leaf)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Canonical source leaf product and its whole-node shortcut preserve available payloads. -/
theorem admitted_intersect_available (left right : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (available : Available state left) :
    Facts (run (EqualityLeafProjectionProduct.intersect left right) state).2 ∧
      Available (run (EqualityLeafProjectionProduct.intersect left right) state).2
        (run (EqualityLeafProjectionProduct.intersect left right) state).1 := by
  unfold EqualityLeafProjectionProduct.intersect
  split
  · exact ⟨facts, available⟩
  · exact nullary_available _ state facts

/-- Build an admitted target and execute the actual physical leaf intersection. -/
noncomputable def admittedMeet (target : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey) :
    Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  (EqualityLeafProjectionLeafCache.build target).bind fun left => EqualityLeafProjectionProduct.intersect left value

/-- The concrete admitted implementation removes the edit worker's local availability premise. -/
theorem admitted_meet_available : MeetAvailable (admittedMeet (initial := initial) (symbols := symbols)) := by
  intro target value state facts _
  have targetFacts := admitted_leaves target state facts
  simp only [admittedMeet, run_bind]
  exact admitted_intersect_available _ value _ targetFacts.1 targetFacts.2

/-- Raw source product and its whole-node shortcut preserve complete available payloads. -/
theorem raw_intersect_available (left right : Value (Fin symbols) ConstraintKey)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) (available : Available state left) :
    Facts (run (EqualityRawLeafProduct.intersect left right) state).2 ∧
      Available (run (EqualityRawLeafProduct.intersect left right) state).2
        (run (EqualityRawLeafProduct.intersect left right) state).1 := by
  unfold EqualityRawLeafProduct.intersect
  split
  · exact ⟨facts, available⟩
  · exact EqualityRawLeafAvailability.build_available _ state facts

/-- Raw targets retain their original guard syntax and execute rejected sentinel requests. -/
noncomputable def rawMeet (target : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (value : Value (Fin symbols) ConstraintKey) : Work (Fin symbols) ConstraintKey (Value (Fin symbols) ConstraintKey) :=
  (EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations target)).bind fun left =>
    EqualityRawLeafProduct.intersect left value

/-- The concrete raw implementation also discharges the edit worker's local availability premise. -/
theorem raw_meet_available : MeetAvailable (rawMeet (initial := initial) (symbols := symbols)) := by
  intro target value state facts _
  have targetFacts := EqualityRawLeafAvailability.raw_leaves target state facts
  simp only [rawMeet, run_bind]
  exact raw_intersect_available _ value _ targetFacts.1 targetFacts.2

/-- Canonical target construction satisfies literal source constructor field checks. -/
theorem admitted_meet_safe (target : Leaf initial symbols) (value : Value (Fin symbols) ConstraintKey) : Safe (admittedMeet target value) := by
  unfold admittedMeet
  apply safe_bind
  · exact safe_bind _ _ (sequence_safe _ (EqualityLeafProjectionLeafCache.requests_safe target)) makeNode_safe
  · intro left
    unfold EqualityLeafProjectionProduct.intersect
    split
    · trivial
    · exact safe_bind _ _ (sequence_safe _ (EqualityLeafProjectionNullary.requests_safe _)) makeNode_safe

/-- Raw target and product requests retain their complete source keys, including rejected sentinels. -/
theorem raw_meet_safe (target : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial))
    (value : Value (Fin symbols) ConstraintKey) : Safe (rawMeet target value) := by
  have built : ∀ rows : List (Fin symbols × SourceGuards.Guard FullSyntax.Formula), Safe (EqualityRawLeafConstruction.build rows) := by
    intro rows
    apply safe_bind _ _ (sequence_safe _ ?_) makeNode_safe
    intro request member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact EqualityRawLeafConstruction.request_safe row
  unfold rawMeet
  apply safe_bind _ _ (built _) (fun left => ?_)
  unfold EqualityRawLeafProduct.intersect
  split
  · trivial
  · exact built _

/-- A compiled raw occurrence executes actual leaf intersections and returns a
complete available result without an ordinary-input or primitive contract. -/
theorem raw_edit_compiled
    (tree : EqualityLeafProjectionSyntax.Tree
      (EqualityLeafProjectionCompile.Tag (Fin symbols) ConstraintKey)
      (List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial)))
    (edits : List (EqualityLeafProjectionSyntax.Path × List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial)))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    let leaf := fun rows => EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations rows)
    let compiled := run (EqualityLeafProjectionCompile.compile leaf tree) state
    let result := run (EqualityLeafProjectionWorkers.edit rawMeet edits compiled.1) compiled.2
    ∃ value, result.1 = some value ∧ Facts result.2 ∧ Available result.2 value := by
  let leaf := fun rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial) =>
    EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations rows)
  let compiled := run (EqualityLeafProjectionCompile.compile leaf tree) state
  have compiledFacts := compile_available leaf EqualityRawLeafAvailability.raw_leaves tree state facts
  have ordinary := EqualityLeafProjectionCompileOrdinary.compile_ordinary leaf
    EqualityRawLeafAvailability.raw_leaves EqualityRawLeafAvailability.raw_ordinary tree state facts
  have checked := edit_available rawMeet raw_meet_available edits compiled.1 compiled.2 compiledFacts.1 compiledFacts.2
  obtain ⟨value, returned⟩ := EqualityLeafProjectionWorkers.edit_returns rawMeet edits compiled.1 ordinary compiled.2
  exact ⟨value, returned, checked.1, checked.2 value returned⟩

/-- Raw occurrence requirements also return complete available records with all local premises derived. -/
theorem raw_require_compiled
    (tree : EqualityLeafProjectionSyntax.Tree
      (EqualityLeafProjectionCompile.Tag (Fin symbols) ConstraintKey)
      (List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial)))
    (paths : List EqualityLeafProjectionSyntax.Path)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    let leaf := fun rows => EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations rows)
    let compiled := run (EqualityLeafProjectionCompile.compile leaf tree) state
    let result := run (EqualityLeafProjectionWorkers.require paths compiled.1) compiled.2
    ∃ value, result.1 = some value ∧ Facts result.2 ∧ Available result.2 value := by
  let leaf := fun rows : List (Fin symbols × SourceNoncanonicalLeafProgress.Raw initial) =>
    EqualityRawLeafConstruction.build (EqualityRawLeafConstruction.declarations rows)
  let compiled := run (EqualityLeafProjectionCompile.compile leaf tree) state
  have compiledFacts := compile_available leaf EqualityRawLeafAvailability.raw_leaves tree state facts
  have ordinary := EqualityLeafProjectionCompileOrdinary.compile_ordinary leaf
    EqualityRawLeafAvailability.raw_leaves EqualityRawLeafAvailability.raw_ordinary tree state facts
  have checked := EqualityLeafProjectionRequireAvailability.require_available paths compiled.1 compiled.2 compiledFacts.1 compiledFacts.2
  obtain ⟨value, returned⟩ := EqualityLeafProjectionWorkers.require_returns paths compiled.1 ordinary compiled.2
  exact ⟨value, returned, checked.1, checked.2 value returned⟩

end MicroCFTA.EqualityLeafProjectionActualMeet
