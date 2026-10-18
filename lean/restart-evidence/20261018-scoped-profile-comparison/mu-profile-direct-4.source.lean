import MicroCFTA.SourceCurrentStoredProfilePlan
import MicroCFTA.SourceCurrentStoredMuProfileContract

/-!
# Pure open Mu profiles from the stored body and ordinary probe

The full stored encoding binds one fresh symbolic local. A finite marker
that is absent from the original assigned leaf profiles gives the same
profile after root erasure. No actual execution or future result is needed.
The body/probe contract then replaces the body by its ordinary probe.
-/
namespace MicroCFTA.SourceCurrentStoredMuProfileReduction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (leaves encode)
open InternedProfileSemantics (Abstract evaluate mapNames lower)
open InternedRootProfile (Profile profile Equivalent)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (Correct shadow)
open SourceCurrentStoredMuTrackedProfile (erase)

private theorem erase_equivalent (marker : Reference) {first second : Profile}
    (same : Equivalent first second) : Equivalent (erase marker first) (erase marker second) := by
  cases first with
  | none =>
      have other := same.1.mp rfl
      subst second
      exact InternedProfileEquivalence.refl _
  | some first =>
      cases second with
      | none => simp [Equivalent] at same
      | some second =>
          constructor
          · simp [erase]
          · intro name
            have members : name ∈ first ↔ name ∈ second := same.2 name
            simp [erase,members]

private theorem erase_mapped (value : Abstract (Sum Unit Reference)) (marker : Reference)
    (fresh : ∀ name, Sum.inr name ∈ value.getD [] → name ≠ marker) :
    erase marker (mapNames (Sum.elim (fun _ : Unit => marker) id) value) = lower value := by
  cases value with
  | none => rfl
  | some names =>
      simp only [erase,mapNames,Option.map_some,lower]
      apply congrArg some
      induction names with
      | nil => rfl
      | cons first rest ih =>
          have tail : ∀ name, Sum.inr name ∈ rest → name ≠ marker :=
            fun name member => fresh name (List.mem_cons_of_mem _ member)
          cases first with
          | inl token => cases token; simp [ih tail]
          | inr name =>
              have different := fresh name List.mem_cons_self
              simp [different,ih tail]

private def assigned (assignment : Reference → Profile) (leaf : Value Symbol Guard) : Profile :=
  match leaf with | .reference name => assignment name | _ => profile leaf

private def symbolic (body : Value Symbol Guard) (own : Reference) (assignment : Reference → Profile) :
    Abstract (Sum Unit Reference) :=
  evaluate (encode (leaves body) [] body) ((leaves body).map (fun leaf => match leaf with
    | .reference name => if own = name then some [Sum.inl ()]
        else mapNames Sum.inr (assigned assignment leaf)
    | _ => mapNames Sum.inr (assigned assignment leaf)))

private theorem symbolic_fresh (body : Value Symbol Guard) (own marker : Reference)
    (assignment : Reference → Profile)
    (fresh : ∀ leaf ∈ leaves body, marker ∉ (assigned assignment leaf).getD []) :
    ∀ name, Sum.inr name ∈ (symbolic body own assignment).getD [] → name ≠ marker := by
  intro name member same
  subst name
  obtain ⟨value,present,member⟩ := InternedProfileOrigins.evaluate_origin
    (encode (leaves body) [] body) _ (Sum.inr marker) member
  obtain ⟨leaf,included,rfl⟩ := List.mem_map.mp present
  cases leaf with
  | reference name =>
      change Sum.inr marker ∈ (if own = name then some [Sum.inl ()]
        else mapNames Sum.inr (assignment name)).getD [] at member
      by_cases same : own = name
      · simp only [same,ite_true,Option.getD_some,List.mem_singleton,reduceCtorEq] at member
      · simp only [same,ite_false] at member
        obtain ⟨actual,selected,equal⟩ := (InternedProfileOrigins.mapNames_member Sum.inr _ _).mp member
        cases equal
        exact fresh (.reference name) included selected
  | empty | node | union | mu =>
      obtain ⟨actual,selected,equal⟩ := (InternedProfileOrigins.mapNames_member Sum.inr _ _).mp member
      cases equal
      exact fresh _ included selected

private theorem symbolic_mapped (body : Value Symbol Guard) (own marker : Reference)
    (assignment : Reference → Profile) :
    mapNames (Sum.elim (fun _ : Unit => marker) id) (symbolic body own assignment) =
      denote body (shadow own (some [marker]) assignment) := by
  rw [symbolic,←InternedProfileSemantics.evaluate_map,List.map_map]
  unfold denote
  congr 1
  apply List.map_congr_left
  intro leaf _
  cases leaf with
  | reference name =>
      by_cases same : own = name
      · subst name
        simp [assigned,shadow,mapNames]
      · simp [assigned,shadow,Ne.symm same,same,mapNames,List.map_map,Function.comp_def]
  | empty | node | union | mu =>
      simp [assigned,mapNames,List.map_map,Function.comp_def]

private theorem symbolic_plan (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false) :
    denote (.mu entry body depth ordinary) assignment = lower (symbolic body (.interned entry.identity) assignment) := by
  have collected : leaves (.mu entry body depth ordinary) = leaves body := by
    rw [leaves.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false]
  have encoded : encode (leaves body) [] (.mu entry body depth ordinary) =
      .binder true (encode (leaves body) [.interned entry.identity] body) := by
    rw [encode.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false]
  have bodyAvailable := available.children body (by simp [InternedProbeProvenance.children])
  rw [denote,collected,encoded,evaluate]
  simp only [List.map_map,Function.comp_def]
  apply congrArg lower
  have rebound := SourceCurrentStoredProfilePlan.rebind (leaves body) body (.interned entry.identity) (some [Sum.inl ()])
    (fun leaf => mapNames Sum.inr (assigned assignment leaf)) state coherent
    (InternedStoredSubstitution.leaves_available body state bodyAvailable) (fun _ member => member)
  refine Eq.trans ?_ rebound
  congr 2
  apply List.map_congr_left
  intro leaf _
  cases leaf <;> rfl

/-- Every finite list of assigned profiles admits a literal marker absent from all of them. -/
theorem fresh_marker (profiles : List Profile) :
    ∃ marker : Reference, ∀ value ∈ profiles, marker ∉ value.getD [] := by
  let names := profiles.flatMap (fun value => value.getD [])
  refine ⟨.uninterned (InternedFreshOrdinaryConstruction.freeBound names),?_⟩
  intro value member inside
  have present : .uninterned (InternedFreshOrdinaryConstruction.freeBound names) ∈ names :=
    List.mem_flatMap.mpr ⟨value,member,inside⟩
  have smaller := InternedFreshOrdinaryConstruction.freeBound_lt names _ present
  exact Nat.lt_irrefl _ smaller

/-- An open stored Mu removes a marker from the full denotation of its strict body. -/
theorem open_denote (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false) (marker : Reference)
    (fresh : ∀ leaf ∈ leaves body, marker ∉ (match leaf with
      | .reference name => assignment name | _ => profile leaf).getD []) :
    denote (.mu entry body depth ordinary) assignment =
      erase marker (denote body (shadow (.interned entry.identity) (some [marker]) assignment)) := by
  rw [symbolic_plan entry body depth ordinary assignment state coherent available opened,
    ← symbolic_mapped body (.interned entry.identity) marker assignment]
  exact (erase_mapped _ marker (symbolic_fresh body (.interned entry.identity) marker assignment fresh)).symm

/-- A correct open stored Mu reduces to its ordinary probe under the same finite marker. -/
theorem open_correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (correct : Correct entry body depth ordinary)
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false) (marker : Reference)
    (fresh : ∀ leaf ∈ leaves body, marker ∉ (match leaf with
      | .reference name => assignment name | _ => profile leaf).getD []) :
    Equivalent (denote (.mu entry body depth ordinary) assignment)
      (erase marker (denote ordinary
        (shadow (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) (some [marker]) assignment))) := by
  rw [open_denote entry body depth ordinary assignment state coherent available opened marker fresh]
  exact erase_equivalent marker (correct assignment (some [marker]))

end MicroCFTA.SourceCurrentStoredMuProfileReduction
