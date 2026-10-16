import MicroCFTA.SourceCurrentAllocatedNativeContextRebase
import MicroCFTA.SourceRecursiveIntersectionDomainEquivalence

/-!
# Admission of actual entered recursive pair contexts

Admitted nonempty operands cover their literal source identities. The
canonical pair retains both covered names. Actual domain entry inserts
that pair and preserves every old seen pair. These proofs use the actual
domain-constructor readback. They do not infer admission from a conditional
result law or establish an execution-wide cache invariant.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePairAdmission
open Cache Language IntersectSchedule InternedConstructorTemplates
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedNativeContextRebase
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
variable {Symbol Guard : Type} {view : View Symbol}

/-- An admitted nonempty input covers its own identity. -/
theorem name_covered (inputs : FiniteInput view) (input : Input)
    (valid : inputs.valid input) (nonempty : input ≠ .empty) :
    NameCovered inputs (identity input) := ⟨input, valid, nonempty, rfl⟩

/-- A successful literal physical identity read retains its nonempty complete input. -/
theorem identity_input (value : Value Symbol Guard) (name : Nat)
    (actual : SourceRecursiveIntersectionControl.identity value = some name) :
    inputOf value ≠ .empty ∧ identity (inputOf value) = name := by
  cases value with
  | empty => cases actual
  | node entry edges depth free | mu entry edges depth ordinary | union entry edges depth free =>
      cases actual
      constructor
      · intro same; cases same
      · rfl
  | reference reference =>
      cases reference <;> simp only [SourceRecursiveIntersectionControl.identity, reduceCtorEq] at actual
      cases actual
      constructor
      · intro same; cases same
      · rfl

/-- Current operand admission covers the identity returned by its actual source read. -/
theorem physical_name_covered (inputs : FiniteInput view) (value : Value Symbol Guard)
    (valid : inputs.valid (inputOf value)) (name : Nat)
    (actual : SourceRecursiveIntersectionControl.identity value = some name) : NameCovered inputs name := by
  have exactInput := identity_input value name actual
  exact ⟨inputOf value, valid, exactInput.1, exactInput.2⟩

/-- Canonical min/max ordering retains both admitted operand names. -/
theorem pair_covered (inputs : FiniteInput view) (first second : Nat)
    (left : NameCovered inputs first) (right : NameCovered inputs second) :
    NameCovered inputs (SourceRecursiveIntersectionControl.pair first second).1 ∧
      NameCovered inputs (SourceRecursiveIntersectionControl.pair first second).2 := by
  by_cases ordered : first ≤ second
  · simpa only [SourceRecursiveIntersectionControl.pair, Nat.min_eq_left ordered, Nat.max_eq_right ordered] using
      And.intro left right
  · have reversed : second ≤ first := by omega
    simpa only [SourceRecursiveIntersectionControl.pair, Nat.min_eq_right reversed, Nat.max_eq_left reversed] using
      And.intro right left

/-- The actual constant empty domain has no seen-pair admission obligation. -/
theorem empty_seen (inputs : FiniteInput view) : SeenCovered inputs IntersectionEmptyDomain.emptyDomain.key := by
  intro pair member
  cases member

/-- Restriction retains the admission of every remaining seen pair. -/
theorem restrict_seen (inputs : FiniteInput view) (before after : IntersectionFlatMemoKeyDomain.DomainKey)
    (old : SeenCovered inputs before) (included : ∀ pair ∈ after.seen, pair ∈ before.seen) :
    SeenCovered inputs after := fun pair member => old pair (included pair member)

/-- Exact source extension covers the inserted pair and every retained old pair. -/
theorem extend_seen (inputs : FiniteInput view) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (bound : List Nat) (first second : Nat) (old : SeenCovered inputs domain)
    (left : NameCovered inputs first) (right : NameCovered inputs second) :
    SeenCovered inputs (SourceRecursiveIntersectionDomain.extend domain bound
      (SourceRecursiveIntersectionControl.pair first second)) := by
  intro pair member
  rcases (SourceRecursiveIntersectionDomain.extend_seen domain bound _ pair).mp member with rfl | earlier
  · exact pair_covered inputs first second left right
  · exact old pair earlier

/-- Literal source Mu bindings add only admitted operand identities. -/
theorem bindings_covered (inputs : FiniteInput view) (left right : Value Symbol Guard)
    (leftValid : inputs.valid (inputOf left)) (rightValid : inputs.valid (inputOf right)) :
    ∀ name ∈ (SourceRecursiveIntersectionEnvironment.bindings left right).map Prod.fst, NameCovered inputs name := by
  intro name member
  simp only [SourceRecursiveIntersectionEnvironment.bindings, List.map_append, List.mem_append] at member
  rcases member with first | second
  · cases left <;> simp only [SourceRecursiveIntersectionEnvironment.binder, List.map_nil, List.not_mem_nil,
      List.map_cons, List.mem_singleton] at first
    subst name
    exact physical_name_covered inputs _ leftValid _ rfl
  · cases right <;> simp only [SourceRecursiveIntersectionEnvironment.binder, List.map_nil, List.not_mem_nil,
      List.map_cons, List.mem_singleton] at second
    subst name
    exact physical_name_covered inputs _ rightValid _ rfl

/-- The actual entered cache key retains old seen pairs and the admitted current pair. -/
theorem entered_seen (inputs : FiniteInput view)
    (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid cache)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (left right : Value Symbol Guard)
    (old : SeenCovered inputs domain) (leftValid : inputs.valid (inputOf left))
    (rightValid : inputs.valid (inputOf right)) (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity right = some second) :
    SeenCovered inputs (SourceRecursiveIntersectionEnvironment.enter cache domain left right first second).1.key := by
  rw [SourceRecursiveIntersectionSchedule.entered_key cache cacheValid domain left right first second]
  exact extend_seen inputs domain _ first second old
    (physical_name_covered inputs left leftValid first leftIdentity)
    (physical_name_covered inputs right rightValid second rightIdentity)

/-- The actual entered free map retains old covered names and literal new Mu names. -/
theorem entered_names (inputs : FiniteInput view)
    (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid cache)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (left right : Value Symbol Guard)
    (old : ∀ name ∈ SourceRecursiveIntersectionDomain.names domain, NameCovered inputs name)
    (leftValid : inputs.valid (inputOf left)) (rightValid : inputs.valid (inputOf right))
    (first second : Nat) :
    ∀ name ∈ SourceRecursiveIntersectionDomain.names
      (SourceRecursiveIntersectionEnvironment.enter cache domain left right first second).1.key, NameCovered inputs name := by
  rw [SourceRecursiveIntersectionSchedule.entered_key cache cacheValid domain left right first second]
  intro name member
  rcases (SourceRecursiveIntersectionDomain.extend_names domain _ _ name).mp member with added | earlier
  · exact bindings_covered inputs left right leftValid rightValid name added
  · exact old name earlier

local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- An admitted parent request derives seen coverage at its actual entered child domain. -/
theorem request_entered_seen {sourceView : View SourceSymbol} (inputs : FiniteInput sourceView)
    (request : NodeRequest SourceSymbol SourceGuard)
    (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid cache)
    (old : SeenCovered inputs request.domain.key)
    (admitted : SourceCurrentAllocatedNativeContextCache.NodeInputs sourceView
      (finiteInputMeaning sourceView inputs) request)
    (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second) :
    SeenCovered inputs (SourceRecursiveIntersectionEnvironment.enter cache request.domain.key
      request.left request.right first second).1.key :=
  entered_seen inputs cache cacheValid request.domain.key request.left request.right old
    admitted.2.2.1 admitted.2.2.2 first second leftIdentity rightIdentity

/-- An admitted parent request covers the names of its actual entered free map. -/
theorem request_entered_names {sourceView : View SourceSymbol} (inputs : FiniteInput sourceView)
    (request : NodeRequest SourceSymbol SourceGuard)
    (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid cache)
    (old : ∀ name ∈ SourceRecursiveIntersectionDomain.names request.domain.key, NameCovered inputs name)
    (admitted : SourceCurrentAllocatedNativeContextCache.NodeInputs sourceView
      (finiteInputMeaning sourceView inputs) request) (first second : Nat) :
    ∀ name ∈ SourceRecursiveIntersectionDomain.names (SourceRecursiveIntersectionEnvironment.enter cache request.domain.key
      request.left request.right first second).1.key, NameCovered inputs name :=
  entered_names inputs cache cacheValid request.domain.key request.left request.right old
    admitted.2.2.1 admitted.2.2.2 first second

end MicroCFTA.SourceCurrentAllocatedNativePairAdmission
