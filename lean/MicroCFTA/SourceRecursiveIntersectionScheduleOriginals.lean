import MicroCFTA.SourceRecursiveIntersectionScheduleGrowth
import MicroCFTA.SourceRecursiveIntersectionScheduleConstructors

/-!
# Original input records along semantic schedule calls

Closed source copies have the same language in pair environments. Actual
Mu extension retains original source bindings. Physical reference lookup
recovers the same original available binder as the semantic domain.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (Reference)
open IntersectSchedule (DomainInputs)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)

/-- The actual closed-self shortcut has exactly the copied original schedule language. -/
theorem closed_copy_corresponds (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (original : Original value) (state : State Symbol Guard) (facts : Facts state)
    (available : Available state value) (closed : value.free = []) : Corresponds holds value (shape holds value) := by
  intro ambient
  let originalEnvironment : InternedGuardedLanguage.Env Symbol := fun name => match name with
    | .interned name => ambient name
    | _ => fun _ => False
  have same := InternedGuardedLanguage.meaning_free holds value state facts.coherent available
    (SourceRecursiveIntersectionScheduleEnvironment.environment ambient) originalEnvironment (by
      intro name member
      rw [closed] at member
      cases member)
  exact same.trans (SourceRecursiveIntersectionGuardedInput.original_meaning holds value original originalEnvironment)

/-- Mu body requests retain original syntax; other operands remain literal original inputs. -/
theorem body_original (value : Value Symbol Guard) (original : Original value) :
    Original (SourceRecursiveIntersectionKernel.body value) := by
  cases original <;> simp only [SourceRecursiveIntersectionKernel.body] <;> first
    | assumption
    | constructor <;> assumption

/-- Semantic domain-input closure states exactly that each enclosing binder has an original record. -/
theorem domain_inputs_iff (state : State Symbol Guard) (domain : IntersectionFlatMemoKeyDomain.DomainKey) :
    DomainInputs (OriginalInput state) (SourceRecursiveIntersectionSchedule.domain domain) ↔
      ∀ name ∈ SourceRecursiveIntersectionDomain.names domain, OriginalInput state (.mu name) := by
  constructor
  · intro known name member
    exact known (name, .mu name) (List.mem_map.mpr ⟨name, member, rfl⟩)
  · intro known entry member
    obtain ⟨name, present, rfl⟩ := List.mem_map.mp member
    exact known name present

/-- Each new source Mu binding has its actual original available operand. -/
theorem binder_original (state : State Symbol Guard) (value : Value Symbol Guard) (original : Original value)
    (available : Available state value) (name : Nat)
    (member : name ∈ (SourceRecursiveIntersectionEnvironment.binder value).map Prod.fst) :
    OriginalInput state (.mu name) := by
  cases original <;> simp only [SourceRecursiveIntersectionEnvironment.binder, List.map_nil, List.not_mem_nil] at member
  case mu entry body depth ordinary bodyOriginal =>
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
    subst name
    exact ⟨.mu entry body depth ordinary, .mu entry body depth ordinary bodyOriginal, available, rfl⟩

/-- Actual canonical Mu entry retains original records for every semantic free binding. -/
theorem extended_domain_inputs (state : State Symbol Guard) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (known : DomainInputs (OriginalInput state) (SourceRecursiveIntersectionSchedule.domain domain))
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state left) (rightAvailable : Available state right) (pair : Nat × Nat) :
    DomainInputs (OriginalInput state) (SourceRecursiveIntersectionSchedule.domain
      (SourceRecursiveIntersectionDomain.extend domain ((SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst) pair)) := by
  apply (domain_inputs_iff state _).mpr
  intro name member
  rcases (SourceRecursiveIntersectionDomain.extend_names domain _ pair name).mp member with new | old
  · simp only [SourceRecursiveIntersectionEnvironment.bindings, List.map_append, List.mem_append] at new
    rcases new with first | second
    · exact binder_original state left leftOriginal leftAvailable name first
    · exact binder_original state right rightOriginal rightAvailable name second
  · exact (domain_inputs_iff state domain).mp known name old

/-- Physical reference resolution recovers the exact original available Mu in the semantic domain. -/
theorem reference_original (state : State Symbol Guard) (facts : Facts state) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (known : DomainInputs (OriginalInput state) (SourceRecursiveIntersectionSchedule.domain domain))
    (name : Nat) (member : name ∈ SourceRecursiveIntersectionDomain.names domain)
    (value : Value Symbol Guard) (found : SourcePreparedSharedRows.read state name = some value) :
    Original value ∧ Available state value ∧ inputOf value = .mu name := by
  obtain ⟨originalValue, original, available, complete⟩ := (domain_inputs_iff state domain).mp known name member
  cases original <;>
    simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case mu entry body depth ordinary bodyOriginal =>
    cases complete
    have selected := SourcePreparedSharedRows.read_identity state facts (.mu entry body depth ordinary) available entry.identity rfl
    have same := Option.some.inj (selected.symm.trans found)
    subst value
    exact ⟨.mu entry body depth ordinary bodyOriginal, available, rfl⟩

end MicroCFTA.SourceRecursiveIntersectionInputView
