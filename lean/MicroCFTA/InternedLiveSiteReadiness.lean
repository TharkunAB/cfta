import MicroCFTA.InternedLiveInputSupport
import MicroCFTA.InternedProbeChoiceSites

/-!
# Actual probe-choice sites exclude fresh-only pending encounters

A completed enclosing execution supplies an actual completed representative
for each selected probe route. A later encounter cannot wait on its key when
corresponding names agree or the later name is fresh, and its depth probe
already existed before those fresh names. Ordinary probe levels remain
those from the selected source executions.
-/
namespace MicroCFTA.InternedLiveSiteReadiness
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedProvenance InternedNestedMissReadback InternedStoredMuOrigins
open InternedFreeAbsenceContext InternedLiveInputSupport InternedProbeChoiceSites
open InternedOccurrenceObservations (Paired)
open InternedBinderProtocol (Reference)

/-- Every changed lexical position contains a newly reserved name on the later side. -/
def FreshChanges (cutoff : Nat) (first second : List Reference) : Prop :=
  Paired (fun before after => before = after ∨ ∃ identity, cutoff ≤ identity ∧ after = .interned identity) first second

/-- Paired lexical inputs supply abstract atoms without assuming an injective reference map. -/
theorem paired_atoms (cutoff : Nat) (first second : List Reference) (paired : FreshChanges cutoff first second) :
    ∃ atoms : List (Reference × Reference), atoms.map Prod.fst = first ∧ atoms.map Prod.snd = second ∧
      ∀ atom ∈ atoms, atom.1 ≠ atom.2 → ∃ identity, cutoff ≤ identity ∧ atom.2 = .interned identity := by
  induction paired with
  | nil => exact ⟨[], rfl, rfl, by intro atom member; cases member⟩
  | @cons a b first second related tail ih =>
      obtain ⟨atoms, left, right, changed⟩ := ih
      refine ⟨(a, b) :: atoms, by simp [left], by simp [right], ?_⟩
      intro atom member different
      rcases List.mem_cons.mp member with rfl | member
      · exact related.resolve_left different
      · exact changed atom member different

/-- Actual literal input lists give readiness when their differences are all fresh. -/
theorem names_not_pending [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (firstNames secondNames : List Reference) (cut : State Symbol Guard) (valid : Valid cut)
    (paired : FreshChanges cut.nodes.next firstNames secondNames)
    (left right afterLeft afterRightDepth afterRight : State Symbol Guard)
    (lc : Context left firstNames) (rc : Context right secondNames)
    (first depth ordinary : Value Symbol Guard)
    (firstDone : build (.binder smart body) (firstNames.map Value.reference) left = .done first afterLeft)
    (depthDone : callback body (secondNames.map Value.reference) .depth right = .done depth afterRightDepth)
    (ordinaryDone : callback body (secondNames.map Value.reference) (.uninterned depth.depth) afterRightDepth = .done ordinary afterRight)
    (growth : Grows afterLeft afterRight) (old : Available cut depth) :
    ¬ IsPending (muKey depth ordinary) afterRight := by
  obtain ⟨atoms, firstMap, secondMap, changed⟩ := paired_atoms cut.nodes.next firstNames secondNames paired
  exact not_pending_of_fresh_changes smart body atoms Prod.fst Prod.snd cut valid changed
    left right afterLeft afterRightDepth afterRight
    (by simpa only [firstMap] using lc) (by simpa only [secondMap] using rc) first depth ordinary
    (by simpa only [firstMap] using firstDone) (by simpa only [secondMap] using depthDone)
    (by simpa only [secondMap] using ordinaryDone) growth old

/-- An actual earlier probe-choice route supplies the representative needed to exclude a later fresh-only encounter. -/
theorem site_not_pending [DecidableEq (EdgeKey Symbol Guard)]
    {expression : Syntax Symbol Guard} {smart : Bool} {body : Syntax Symbol Guard} {choices : List Bool}
    (site : Site expression (.binder smart body) choices) (names : List Reference)
    (before final : State Symbol Guard) (value : Value Symbol Guard) (context : Context before names)
    (completed : build expression (names.map Value.reference) before = .done value final) :
    ∃ crossings : List (Crossing Symbol Guard), crossings.map Crossing.ordinary = choices ∧
      (∀ crossing ∈ crossings, Grows before crossing.before ∧ Grows crossing.afterDepth final) ∧
      ∀ currentNames cut, Valid cut → FreshChanges cut.nodes.next (crossings.map Crossing.name ++ names) currentNames →
      ∀ current afterDepth afterOrdinary, Context current currentNames → ∀ depth ordinary,
        callback body (currentNames.map Value.reference) .depth current = .done depth afterDepth →
        callback body (currentNames.map Value.reference) (.uninterned depth.depth) afterDepth = .done ordinary afterOrdinary →
        Grows final afterOrdinary → Available cut depth → ¬ IsPending (muKey depth ordinary) afterOrdinary := by
  obtain ⟨crossings, start, first, finish, flags, firstDone, startContext, _, suffix, traces⟩ :=
    completed_site site names before final value context completed
  refine ⟨crossings, flags, traces, ?_⟩
  intro currentNames cut valid paired current afterDepth afterOrdinary currentContext depth ordinary depthDone ordinaryDone growth old
  exact names_not_pending smart body _ currentNames cut valid paired start current finish afterDepth afterOrdinary
    startContext currentContext first depth ordinary firstDone depthDone ordinaryDone (grows_trans suffix growth) old

end MicroCFTA.InternedLiveSiteReadiness
