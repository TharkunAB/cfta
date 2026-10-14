import MicroCFTA.SourceRecursiveIntersectionRowReplay
import MicroCFTA.SourceRecursiveIntersectionReplay
import MicroCFTA.InternedGuardedConstructors

/-!
# Actual union calls retain their ordered physical representatives

Completed union calls retain one result for each original member occurrence.
Every child call replays in the same later cache. Actual union normalization
has precisely the union of those independent guarded languages. No common
input language or functional product representative is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain

/-- A completed union branch retains its actual ordered walk and canonical constructor work. -/
theorem union_readback [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (before : Machine Symbol Guard) (valid : Valid before)
    (known : Domain before domain) (available : Available before.heap other)
    (membersAvailable : ∀ member ∈ members, Available before.heap member)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members before).bind
      (fun values current => work (makeUnion values) current) = .done value final) :
    ∃ values middle, Valid middle ∧ (∀ result ∈ values, Available middle.heap result) ∧
      walk (fun member => if left then call domain member other else call domain other member) members before = .done values middle ∧
      work (makeUnion values) middle = .done value final ∧ Extension middle final := by
  let input := fun (state : Machine Symbol Guard) (member : Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap other ∧ Available state.heap member
  have stable : Stable input := fun before after growth member known =>
    ⟨known.1.grows domain growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have checked := walk_checked
    (fun member => if left then call domain member other else call domain other member) members input _ stable available_stable
    (by
      intro member _ current currentValid known
      cases left
      · exact calls domain other member current currentValid known.1 known.2.1 known.2.2
      · exact calls domain member other current currentValid known.1 known.2.2 known.2.1)
    before valid (fun member present => ⟨known, available, membersAvailable member present⟩)
  cases walked : walk (fun member => if left then call domain member other else call domain other member) members before with
  | failed failure state => simp only [walked, Result.bind] at done; cases done
  | done values middle =>
      have middleValid : Valid middle := by simpa only [walked, Result.state] using checked.valid
      have resident := checked.result values middle walked
      have built : work (makeUnion values) middle = .done value final := by simpa only [walked, Result.bind] using done
      have growth : Extension middle final := by
        simpa only [built, Result.state] using work_extension (makeUnion values) middle middleValid
      exact ⟨values, middle, middleValid, resident, rfl, built, growth⟩

/-- Each union member retains its own completed physical child in one later cache, including duplicates. -/
theorem union_values_replay [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (before after : Machine Symbol Guard) (valid : Valid before)
    (known : Domain before domain) (available : Available before.heap other)
    (membersAvailable : ∀ member ∈ members, Available before.heap member)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members before).bind
      (fun values current => work (makeUnion values) current) = .done value final) (growth : Extension final after) :
    ∃ values, (∀ result ∈ values, Available after.heap result) ∧
      All₂ (fun member result => (if left then call domain member other else call domain other member) after = .done result after)
        members values ∧ work (makeUnion values) after = .done value after := by
  obtain ⟨values, middle, middleValid, resident, walked, built, earlier⟩ :=
    union_readback call calls domain members other left before valid known available membersAvailable value final done
  let input := fun (state : Machine Symbol Guard) (member : Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap other ∧ Available state.heap member
  have stable : Stable input := fun before after growth member known =>
    ⟨known.1.grows domain growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have paired := walk_pointwise_replay
    (fun member => if left then call domain member other else call domain other member) members input _ stable available_stable
    (by
      intro member _ current currentValid known
      cases left
      · exact calls domain other member current currentValid known.1 known.2.1 known.2.2
      · exact calls domain member other current currentValid known.1 known.2.2 known.2.1)
    (by
      intro member _ before after result final valid known
      cases left
      · exact replay domain other member before after result final valid known.1 known.2.1 known.2.2
      · exact replay domain member other before after result final valid known.1 known.2.2 known.2.1)
    before after values middle valid (fun member present => ⟨known, available, membersAvailable member present⟩)
    walked (earlier.trans growth)
  exact ⟨values, fun result present => (earlier.trans growth).available _ (resident result present), paired,
    work_replay (makeUnion values) middle after value final middleValid built growth⟩

/-- The actual union result has precisely the independent guarded language of its ordered returned children. -/
theorem union_language [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (before after : Machine Symbol Guard) (valid : Valid before)
    (afterValid : Valid after) (known : Domain before domain) (available : Available before.heap other)
    (membersAvailable : ∀ member ∈ members, Available before.heap member)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members before).bind
      (fun values current => work (makeUnion values) current) = .done value final) (growth : Extension final after) :
    ∃ values,
      All₂ (fun member result => (if left then call domain member other else call domain other member) after = .done result after)
        members values ∧ ∀ holds ambient term,
        InternedGuardedLanguage.meaning holds ambient value term ↔
          ∃ result ∈ values, InternedGuardedLanguage.meaning holds ambient result term := by
  obtain ⟨values, resident, paired, built⟩ :=
    union_values_replay call calls replay domain members other left before after valid known available membersAvailable value final done growth
  refine ⟨values, paired, ?_⟩
  intro holds ambient term
  rw [(work_done (makeUnion values) after value after built).1]
  exact InternedGuardedLanguage.makeUnion_exact after.heap afterValid.1 holds ambient values resident term

/-- Actual union language is the union of successful member-call languages in the same later cache. -/
theorem union_language_calls [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (before after : Machine Symbol Guard) (valid : Valid before)
    (afterValid : Valid after) (known : Domain before domain) (available : Available before.heap other)
    (membersAvailable : ∀ member ∈ members, Available before.heap member)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members before).bind
      (fun values current => work (makeUnion values) current) = .done value final) (growth : Extension final after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds ambient value term ↔ ∃ member ∈ members, ∃ result,
      (if left then call domain member other else call domain other member) after = .done result after ∧
        InternedGuardedLanguage.meaning holds ambient result term := by
  obtain ⟨values, paired, language⟩ :=
    union_language call calls replay domain members other left before after valid afterValid known available membersAvailable value final done growth
  rw [language holds ambient term]
  constructor
  · rintro ⟨result, present, accepted⟩
    obtain ⟨member, included, returned⟩ := (pointwise_result_member
      (fun member => (if left then call domain member other else call domain other member) after) members values after paired result).mp present
    exact ⟨member, included, result, returned, accepted⟩
  · rintro ⟨member, included, result, returned, accepted⟩
    exact ⟨result, (pointwise_result_member
      (fun member => (if left then call domain member other else call domain other member) after) members values after paired result).mpr
      ⟨member, included, returned⟩, accepted⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
