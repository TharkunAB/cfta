import MicroCFTA.InternedFreshOrdinaryDependencies
import MicroCFTA.MergedPhysicalWarmup
import MicroCFTA.Language

/-!
# Exact physical binding keys for repaired stored substitution

For one original body, the ordered optional replacement identities determine
the complete repaired computation. Coherent available records recover full
values from those identities. Closed replacements in one current cache have
a derived finite key inventory. Future caches can contain new replacements;
this result does not prove finite closure across cache growth.
-/
namespace MicroCFTA.InternedFreshOrdinaryBindingKeys
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements)

/-- Record optional replacement identities at each original free name. -/
def key (body : Value Symbol Guard) (environment : Environment Symbol Guard) :=
  body.free.map fun name => (environment name).map Value.referenceOf

/-- Equal physical binding keys recover equal full available replacements in one coherent cache. -/
theorem key_agree (body : Value Symbol Guard) (first second : Environment Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (firstAvailable : Replacements state first) (secondAvailable : Replacements state second)
    (same : key body first = key body second) : ∀ name ∈ body.free, first name = second name := by
  intro name member
  have identity := List.map_eq_map_iff.mp same name member
  cases left : first name with
  | none =>
      cases right : second name with
      | none => rfl
      | some value => simp only [left, right, Option.map_none, Option.map_some] at identity; cases identity
  | some value =>
      cases right : second name with
      | none => simp only [left, right, Option.map_none, Option.map_some] at identity; cases identity
      | some other =>
          have values : value = other := InternedFreshProbeKeys.resident_reference_injective state coherent value other
            (firstAvailable name value left).resident (secondAvailable name other right).resident
            (Option.some.inj (by simpa only [left, right, Option.map_some] using identity))
          exact congrArg some values

/-- Physical key equality derives exact repaired outcomes and cache effects without an opaque memo contract. -/
theorem execute_key [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (first second : Environment Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state body)
    (firstAvailable : Replacements state first) (secondAvailable : Replacements state second)
    (same : key body first = key body second) :
    InternedFreshOrdinaryStoredSubstitution.execute body first state =
      InternedFreshOrdinaryStoredSubstitution.execute body second state :=
  InternedFreshOrdinaryStoredSubstitution.execute_congr body first second state coherent available
    (key_agree body first second state coherent firstAvailable secondAvailable same)

/-- Equal physical binding keys replay a completed repaired result after cache growth without further allocation. -/
theorem execute_key_replay [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (first second : Environment Symbol Guard) (before after : State Symbol Guard)
    (coherent : Coherent before) (available : Available before body)
    (firstAvailable : Replacements before first) (secondAvailable : Replacements before second)
    (same : key body first = key body second) (result : Value Symbol Guard) (final : State Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.execute body first before = .done result final)
    (growth : Grows final after) :
    InternedFreshOrdinaryStoredSubstitution.execute body second after = .done result after :=
  InternedFreshOrdinaryStoredSubstitution.execute_binding_replay body first second before after coherent available
    (key_agree body first second before coherent firstAvailable secondAvailable same) result final done growth

/-- Enumerate absence, empty, and every actual completed physical record identity in the current cache. -/
def choices (state : State Symbol Guard) : List (Option InternedBinderProtocol.NodeRef) :=
  none :: some .empty :: (nodeInventory state).map (some ∘ Value.referenceOf)

/-- Each optional binding has at most one choice per issued node, plus absence and empty. -/
theorem choices_bound (state : State Symbol Guard) : (choices state).length ≤ state.nodes.next + 2 := by
  have bound := node_inventory_bound state
  simp only [choices, List.length_cons, List.length_map]
  omega

/-- Closed available replacements belong to the finite current-cache identity inventory. -/
theorem choice_member (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) :
    some value.referenceOf ∈ choices state := by
  cases value with
  | empty => simp [choices, Value.referenceOf]
  | reference name => simp [Value.free] at closed
  | node entry edges depth free | union entry members depth free | mu entry body depth ordinary =>
      unfold choices
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨_, MergedPhysicalWarmup.inventory_complete state coherent entry.key _
        (available.resident entry rfl), rfl⟩

/-- List every ordered binding key formed from one current cache and one original body's free names. -/
def keys (state : State Symbol Guard) (body : Value Symbol Guard) :=
  Language.products (fun _ : InternedBinderProtocol.Reference => choices state) body.free

/-- Every environment of closed available replacements has a key in the derived finite current-cache list. -/
theorem key_member (state : State Symbol Guard) (coherent : Coherent state) (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (available : Replacements state environment)
    (closed : ∀ name value, environment name = some value → value.free = []) : key body environment ∈ keys state body := by
  apply (Language.mem_products _ _ _).mpr
  have pointwise : ∀ name ∈ body.free, (environment name).map Value.referenceOf ∈ choices state := by
    intro name _
    cases found : environment name with
    | none => simp [choices]
    | some value => exact choice_member state coherent value (available name value found) (closed name value found)
  unfold key
  generalize body.free = names at pointwise ⊢
  induction names with
  | nil => exact .nil
  | cons name rest ih =>
      exact .cons (pointwise name List.mem_cons_self)
        (ih (fun other member => pointwise other (List.mem_cons_of_mem _ member)))

end MicroCFTA.InternedFreshOrdinaryBindingKeys
