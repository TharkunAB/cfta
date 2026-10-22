import MicroCFTA.SourceRecursiveIntersectionKernel

/-!
# Cache invariants for recursive source requests

Each result retains source facts and both cache histories. Sequential calls
use the preceding result's actual state. Existing operand and domain records
remain available after later child and constructor effects.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionDomain

/-- Both source cache families satisfy their complete validity conditions. -/
def Valid (state : Machine Symbol Guard) : Prop := InternedNestedFacts.Facts state.heap ∧ Cache.Valid state.domains

/-- Later caller states retain physical records, issued identities, and canonical domain entries. -/
structure Extension (before after : Machine Symbol Guard) : Prop where
  heap : Grows before.heap after.heap
  history : Extends before.heap.nodes.issued after.heap.nodes.issued
  domains : Extends before.domains.table after.domains.table

/-- A call with no cache effect retains every earlier record. -/
theorem Extension.refl (state : Machine Symbol Guard) : Extension state state :=
  ⟨grows_refl _, extends_refl _, extends_refl _⟩

/-- Ordered caller effects compose both physical and domain histories. -/
theorem Extension.trans (first : Extension before middle) (second : Extension middle after) : Extension before after :=
  ⟨grows_trans first.heap second.heap, extends_trans first.history second.history, extends_trans first.domains second.domains⟩

/-- All earlier complete physical records survive recursive caller effects. -/
theorem Extension.available {before after : Machine Symbol Guard} (extension : Extension before after) (value : Value Symbol Guard)
    (available : Available before.heap value) : Available after.heap value :=
  available.grows before.heap after.heap extension.heap extension.history

/-- A source domain retains its actual cache identity and original complete Mu bindings. -/
structure Domain (state : Machine Symbol Guard) (domain : Interned DomainKey) : Prop where
  represented : IntersectionEmptyDomain.Represents state.domains domain.key domain
  canonical : Canonical domain.key
  typed : Typed domain.key
  bindings : AvailableBindings state.heap domain.key

/-- An earlier source domain remains valid after later caller effects. -/
theorem Domain.grows (domain : Interned DomainKey) (known : Domain before domain) (extension : Extension before after) :
    Domain after domain := by
  refine ⟨⟨known.represented.1, ?_⟩, known.canonical, known.typed,
    known.bindings.grows before.heap after.heap domain.key extension.heap extension.history⟩
  by_cases empty : domain.key = IntersectionEmptyDomain.emptyKey
  · simpa only [empty, ite_true] using known.represented.2
  · obtain ⟨entry, present, same⟩ := by simpa only [empty, ite_false] using known.represented.2
    simpa only [empty, ite_false] using
      (show ∃ entry, after.domains.table domain.key = some entry ∧ domain.identity = entry.identity + 1 from
        ⟨entry, extension.domains _ _ present, same⟩)

/-- The reserved empty source domain requires no cache allocation or physical binding. -/
theorem empty_domain (state : Machine Symbol Guard) : Domain state IntersectionEmptyDomain.emptyDomain := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [IntersectionEmptyDomain.Represents, IntersectionEmptyDomain.emptyDomain]
  · exact ⟨List.Pairwise.nil, List.Pairwise.nil⟩
  · intro binding member
    cases member
  · intro name member
    cases member

/-- Success and failure preserve validity and histories; success additionally retains its result property. -/
structure Checked (before : Machine Symbol Guard) (result : Result Symbol Guard A)
    (property : Machine Symbol Guard → A → Prop) : Prop where
  valid : Valid result.state
  extension : Extension before result.state
  result : ∀ value after, result = .done value after → property after value

/-- Returning an existing result has no physical or domain allocation. -/
theorem checked_pure (state : Machine Symbol Guard) (valid : Valid state) (value : A)
    (property : Machine Symbol Guard → A → Prop) (holds : property state value) :
    Checked state (.done value state) property := by
  refine ⟨valid, .refl state, ?_⟩
  intro actual after same
  cases same
  exact holds

/-- An explicit source failure keeps the exact current valid cache. -/
theorem checked_failed (state : Machine Symbol Guard) (valid : Valid state) (failure : Failure)
    (property : Machine Symbol Guard → A → Prop) : Checked state (.failed failure state) property :=
  ⟨valid, .refl state, by intro value after impossible; cases impossible⟩

/-- A completed earlier source allocation precedes the checked child result. -/
theorem Checked.prepend {before middle : Machine Symbol Guard} {outcome : Result Symbol Guard A}
    (earlier : Extension before middle) (checked : Checked middle outcome property) :
    Checked before outcome property := ⟨checked.valid, earlier.trans checked.extension, checked.result⟩

/-- Sequential callers compose invariants without discarding a failed call's actual cache. -/
theorem checked_bind (state : Machine Symbol Guard) (result : Result Symbol Guard A)
    (next : A → Machine Symbol Guard → Result Symbol Guard B)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (checked : Checked state result input)
    (nextChecked : ∀ value after, result = .done value after → Valid after → input after value → Checked after (next value after) output) :
    Checked state (result.bind next) output := by
  cases result with
  | failed failure after => exact ⟨checked.valid, checked.extension, by intro value final impossible; cases impossible⟩
  | done value after =>
      have later := nextChecked value after rfl checked.valid (checked.result value after rfl)
      exact ⟨later.valid, checked.extension.trans later.extension, later.result⟩

/-- Complete constructor verification transfers to the caller's actual caches. -/
theorem construction_checked (state : Machine Symbol Guard) (valid : Valid state)
    (outcome : InternedNestedConstruction.Outcome Symbol Guard A)
    (property : InternedConstructorTemplates.State Symbol Guard → A → Prop)
    (checked : InternedNestedFacts.Verified state.heap outcome property) :
    Checked state (construction outcome state) (fun after value => property after.heap value) := by
  cases outcome with
  | pending key after =>
      exact ⟨⟨checked.facts, valid.2⟩, ⟨checked.growth, checked.history, extends_refl _⟩,
        by intro value final impossible; cases impossible⟩
  | done value after =>
      refine ⟨⟨checked.facts, valid.2⟩, ⟨checked.growth, checked.history, extends_refl _⟩, ?_⟩
      intro actual final same
      cases same
      exact checked.result value after rfl

/-- Ordinary constructor work has the same actual cache effects inside the recursive caller. -/
theorem work_checked [DecidableEq (EdgeKey Symbol Guard)] (state : Machine Symbol Guard) (valid : Valid state)
    (request : Work Symbol Guard A) (property : InternedConstructorTemplates.State Symbol Guard → A → Prop)
    (checked : InternedNestedFacts.Verified state.heap (InternedNestedConstruction.work request state.heap) property) :
    Checked state (work request state) (fun after value => property after.heap value) := by
  have lifted := construction_checked state valid _ property checked
  simpa only [InternedNestedConstruction.work, construction, work] using lifted

/-- A property survives all earlier physical and domain effects. -/
def Stable (property : Machine Symbol Guard → A → Prop) : Prop :=
  ∀ before after, Extension before after → ∀ value, property before value → property after value

/-- Available values survive ordered recursive caller effects. -/
theorem available_stable : Stable (fun (state : Machine Symbol Guard) value => Available state.heap value) := by
  intro before after extension value available
  exact extension.available value available

/-- Resident edge records survive ordered recursive caller effects. -/
theorem edge_stable : Stable (fun (state : Machine Symbol Guard) edge => InternedEdgeResidency.EdgeResident state.heap edge) := by
  intro before after extension edge resident
  exact InternedEdgeResidency.edge_grows before.heap after.heap extension.heap edge resident

/-- Ordered walks retain all complete returned records at their exact final cache. -/
theorem walk_checked (call : A → Machine Symbol Guard → Result Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, Valid state → input state request → Checked state (call request state) output)
    (state : Machine Symbol Guard) (valid : Valid state) (inputs : ∀ request ∈ requests, input state request) :
    Checked state (walk call requests state) (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => exact checked_pure state valid [] _ (by simp)
  | cons head tail ih =>
      have first := calls head List.mem_cons_self state valid (inputs head List.mem_cons_self)
      simp only [walk]
      apply checked_bind state _ _ output _ first
      intro value after returned afterValid present
      have growth : Extension state after := by simpa only [returned, Result.state] using first.extension
      have rest := ih (fun request member => calls request (List.mem_cons_of_mem _ member)) after afterValid
        (fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member)))
      apply checked_bind after _ _ _ _ rest
      intro values final completed finalValid remaining
      have later : Extension after final := by simpa only [completed, Result.state] using rest.extension
      apply checked_pure final finalValid (value :: values)
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · exact outputStable after final later actual present
      · exact remaining actual member

end MicroCFTA.SourceRecursiveIntersectionKernel
