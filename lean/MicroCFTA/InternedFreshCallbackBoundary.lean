import MicroCFTA.InternedFreeAbsenceReplay
import MicroCFTA.InternedBoundaryTransport

/-!
# Fresh callback boundary transport before root-local deletion

If the raw fresh body omits its supplied local, unrestricted source replay
identifies the two raw bodies. The target filter can remove additional
captured sentinel aliases, but it cannot add a forbidden boundary.
The separate case where the first filter deletes a root local remains open.
-/
namespace MicroCFTA.InternedFreshCallbackBoundary
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback
open InternedStoredMuOrigins InternedNestedSpecialization
open InternedFreeAbsenceContext InternedFreeAbsenceReplay
open InternedObservedAbsence InternedBoundaryAtoms InternedBoundaryProvenance InternedBoundaryFilter
open InternedBinderProtocol (Reference NodeRef)

/-- A fresh local replacement leaves all captured literal names unchanged. -/
theorem change_captures (identity : Nat) (replacement : Reference) (names : List Reference)
    (fresh : .interned identity ∉ names) : names.map (change identity replacement) = names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      have different : name ≠ .interned identity := fun same => fresh (by simp [same])
      have tailFresh : .interned identity ∉ rest := fun member => fresh (List.mem_cons_of_mem _ member)
      simp only [List.map_cons, change, different, ↓reduceIte, ih tailFresh]

/-- Root filtering cannot hide a forbidden boundary when its selected name was not free in the raw value. -/
theorem clear_before_absent_filter [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (name : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (normal : Normal state) (available : Available state value) (absent : name ∉ value.free)
    (clear : Clear forbidden (run (withoutSelfReference name value) state).1) : Clear forbidden value := by
  intro atom member
  by_cases same : atom = .ref name
  · exact False.elim (absent (ref_free name value state normal.facts.coherent available (same ▸ member)))
  · exact clear atom ((filter_atom_iff name atom value state normal.facts.coherent normal.facts.cached
      normal.facts.linked normal.live available same).mpr member)

/-- Actual fresh and sentinel callbacks transport boundary absence when the raw fresh body has no local occurrence. -/
theorem callback_clear_of_raw_absent [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (expression : Syntax Symbol Guard) (identity : Nat) (target : Reference) (names : List Reference)
    (fresh : .interned identity ∉ names)
    (left right common middleLeft afterLeft afterRight : State Symbol Guard)
    (lc : Context left names) (rc : Context right names) (coherent : Coherent common)
    (la : Available left (.reference (.interned identity))) (ra : Available right (.reference target))
    (raw first second : Value Symbol Guard)
    (rawDone : build expression (.reference (.interned identity) :: names.map Value.reference) left = .done raw middleLeft)
    (firstDone : callback expression (names.map Value.reference) (.interned identity) left = .done first afterLeft)
    (secondDone : callback expression (names.map Value.reference) target right = .done second afterRight)
    (lg : Grows afterLeft common) (rg : Grows afterRight common)
    (rawAbsent : .interned identity ∉ raw.free) (clear : Clear forbidden first) : Clear forbidden second := by
  obtain ⟨targetRaw, middleRight, targetRawDone, targetFilterDone⟩ := bind_done _ _ _ _ secondDone
  have filterDone : work (withoutSelfReference (.interned identity) raw) middleLeft = .done first afterLeft := by
    simpa only [callback, rawDone, Outcome.bind] using firstDone
  have localLeft := lc.local (.interned identity) la
  have localRight := rc.local target ra
  have middleContext : Context middleLeft (.interned identity :: names) := by
    simpa only [List.map_cons, rawDone, Outcome.state] using localLeft.build expression
  have targetContext : Context middleRight (target :: names) := by
    simpa only [List.map_cons, targetRawDone, Outcome.state] using localRight.build expression
  have leftAvailable := (build_verified expression _ left lc.normal.facts localLeft.inputs).result raw middleLeft rawDone
  have rightAvailable := (build_verified expression _ right rc.normal.facts localRight.inputs).result targetRaw middleRight targetRawDone
  have leftFilterGrowth : Grows middleLeft afterLeft := by
    simpa only [filterDone, Outcome.state] using
      (work_correct (withoutSelfReference (.interned identity) raw) middleLeft middleContext.normal.facts.coherent.valid).2
  have rightFilterGrowth : Grows middleRight afterRight := by
    simpa only [targetFilterDone, Outcome.state] using
      (work_correct (withoutSelfReference target targetRaw) middleRight targetContext.normal.facts.coherent.valid).2
  have mapped : (.interned identity :: names).map (change identity target) = target :: names := by
    simp only [List.map_cons, change, ↓reduceIte, change_captures identity target names fresh]
  have same := (build_related expression identity target (.interned identity :: names)
    left right common middleLeft middleRight localLeft (by simpa only [mapped] using localRight) coherent raw targetRaw
    (by simpa only [List.map_cons] using rawDone)
    (by simpa only [mapped, List.map_cons] using targetRawDone)
    (grows_trans leftFilterGrowth lg) (grows_trans rightFilterGrowth rg)).2 rawAbsent
  have firstResult := filterDone
  have secondResult := targetFilterDone
  simp only [work, Outcome.done.injEq] at firstResult secondResult
  have rawClear := clear_before_absent_filter forbidden (.interned identity) raw middleLeft middleContext.normal leftAvailable rawAbsent
    (by simpa only [firstResult.1] using clear)
  have targetClear : Clear forbidden targetRaw := same ▸ rawClear
  have filtered := InternedBoundaryTransport.filter_clear forbidden target targetRaw middleRight targetContext.normal.facts
    targetContext.normal.live rightAvailable targetClear
  simpa only [secondResult.1] using filtered

end MicroCFTA.InternedFreshCallbackBoundary
