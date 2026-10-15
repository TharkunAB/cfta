import MicroCFTA.SourceEqualityNativeDemandProvenance
import MicroCFTA.SourceRecursiveIntersectionScheduleEnvironment

/-!
# Explicit language contexts for checked open requests

Original bound names use actual physical readback. Result pair names use
only pairs in the incoming seen set. These contexts give local source
branch laws and exact closed specialization. They do not prove recursive
domain extension for every optional-binder candidate.
-/
namespace MicroCFTA.SourceEqualityNativeDemandOpenMeaning
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol (Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Interpret one actual issued source identity through its stored record. -/
def namedLanguage (holds : Guard → Term Symbol → Bool) (source : InternedConstructorTemplates.State Symbol Guard)
    (input : InternedGuardedLanguage.Env Symbol) (name : Nat) : BinderLanguage.Lang Symbol :=
  match SourcePreparedSharedRows.read source name with
  | some value => InternedGuardedLanguage.meaning holds input value
  | none => fun _ => False

/-- Only names in the actual source free map must denote their stored binders. -/
def BoundContext (holds : Guard → Term Symbol → Bool) (source : InternedConstructorTemplates.State Symbol Guard)
    (input : InternedGuardedLanguage.Env Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey) : Prop :=
  ∀ name ∈ SourceRecursiveIntersectionDomain.names domain,
    input (.interned name) = namedLanguage holds source input name

/-- Only actual seen pairs constrain the result's pair environment. -/
def SeenContext (holds : Guard → Term Symbol → Bool) (source : InternedConstructorTemplates.State Symbol Guard)
    (input output : InternedGuardedLanguage.Env Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey) : Prop :=
  ∀ key ∈ domain.seen, output (.intersection key.1 key.2) =
    fun term => namedLanguage holds source input key.1 term ∧ namedLanguage holds source input key.2 term

/-- Assign pair names directly from physical operand languages. -/
def pairEnvironment (holds : Guard → Term Symbol → Bool) (source : InternedConstructorTemplates.State Symbol Guard)
    (input : InternedGuardedLanguage.Env Symbol) : InternedGuardedLanguage.Env Symbol
  | .intersection first second => fun term =>
      namedLanguage holds source input first term ∧ namedLanguage holds source input second term
  | name => input name

/-- A pair context exists for every fixed source environment and incoming seen set. -/
theorem pairEnvironment_seen (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (input : InternedGuardedLanguage.Env Symbol)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) :
    SeenContext holds source input (pairEnvironment holds source input) domain := by intro key _; rfl

/-- Closed bound readbacks derive both context environments without a supplied result law. -/
theorem contexts_of_closed_readbacks (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (ambient : InternedGuardedLanguage.Env Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (closed : ∀ name ∈ SourceRecursiveIntersectionDomain.names domain, ∀ value,
      SourcePreparedSharedRows.read source name = some value → value.free = []) :
    ∃ input output, BoundContext holds source input domain ∧ SeenContext holds source input output domain := by
  let input : InternedGuardedLanguage.Env Symbol := fun name => match name with
    | .interned identity => namedLanguage holds source ambient identity
    | _ => ambient name
  refine ⟨input, pairEnvironment holds source input, ?_, pairEnvironment_seen holds source input domain⟩
  intro name member
  change namedLanguage holds source ambient name = namedLanguage holds source input name
  cases found : SourcePreparedSharedRows.read source name with
  | none => simp only [namedLanguage, found]
  | some value =>
      simp only [namedLanguage, found]
      exact InternedGuardedLanguage.closed_meaning holds value source facts.coherent
        (SourcePreparedSharedRows.read_available source facts name value found) (closed name member value found) ambient input

/-- An original free recursion reference must belong to the current source free map. -/
def BoundNames (domain : IntersectionFlatMemoKeyDomain.DomainKey) (value : Value Symbol Guard) : Prop :=
  ∀ name, Reference.interned name ∈ value.free → name ∈ SourceRecursiveIntersectionDomain.names domain

/-- An open result denotes operand intersection in the explicit finite source context. -/
def Meaning (holds : Guard → Term Symbol → Bool) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∀ input output, BoundContext holds source input request.domain.key →
    SeenContext holds source input output request.domain.key → ∀ term,
      InternedGuardedLanguage.meaning holds output value term ↔
        InternedGuardedLanguage.meaning holds input request.left term ∧
        InternedGuardedLanguage.meaning holds input request.right term

/-- Equal actual seen-pair assignments retain the entire scoped result language. -/
theorem environment_transport (holds : Guard → Term Symbol → Bool)
    (source current : InternedConstructorTemplates.State Symbol Guard) (facts : Facts current)
    (input first second : InternedGuardedLanguage.Env Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (value : Value Symbol Guard) (available : Available current value)
    (scope : SourceRecursiveIntersectionResultScope.Scope domain.seen value)
    (firstContext : SeenContext holds source input first domain)
    (secondContext : SeenContext holds source input second domain) :
    InternedGuardedLanguage.meaning holds first value = InternedGuardedLanguage.meaning holds second value := by
  apply InternedGuardedLanguage.meaning_free holds value current facts.coherent available
  intro name member
  obtain ⟨key, present, rfl⟩ := scope name member
  exact (firstContext key present).trans (secondContext key present).symm

/-- The empty domain discharges both contexts and gives the existing closed law. -/
theorem Meaning.closed (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (request : NodeRequest Symbol Guard)
    (value : Value Symbol Guard) (law : Meaning holds source request value) :
    SourceEqualityNativeDemandProvenance.NodeMeaning holds request value := by
  intro empty _ _ ambient term
  apply law ambient ambient
  · intro name member
    simp only [empty, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey,
      SourceRecursiveIntersectionDomain.names, List.map_nil, List.not_mem_nil] at member
  · intro key member
    simp only [empty, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey,
      List.not_mem_nil] at member

/-- Actual nonreference readback and scoped bound references have one identity language. -/
theorem identity_language (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (input : InternedGuardedLanguage.Env Symbol) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (bound : BoundContext holds source input domain) (value : Value Symbol Guard)
    (available : Available source value) (names : BoundNames domain value) (name : Nat)
    (identified : identity value = some name) :
    InternedGuardedLanguage.meaning holds input value = namedLanguage holds source input name := by
  cases value with
  | empty => cases identified
  | reference reference =>
      cases reference <;> simp only [identity, reduceCtorEq] at identified
      cases identified
      simpa only [InternedGuardedLanguage.meaning] using
        bound name (names name (by simp only [Value.free, List.mem_singleton]))
  | node entry edges depth free | union entry edges depth free | mu entry edges depth free =>
      cases identified
      have read := SourcePreparedSharedRows.read_identity source facts _ available entry.identity rfl
      simp only [namedLanguage, read]

/-- A selected repeated branch retains the actual two identities and canonical pair. -/
theorem repeated_identities (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Guard) (key : Nat × Nat)
    (selected : decision domain left right = .repeated key) :
    ∃ first second, identity left = some first ∧ identity right = some second ∧ key = pair first second := by
  unfold decision at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · split at selected
        · cases selected
        · split at selected
          · rename_i first second leftId rightId
            split at selected
            · cases selected
              exact ⟨first, second, leftId, rightId, rfl⟩
            · cases left <;> cases right <;> simp only [payload] at selected <;> cases selected
          · cases selected

/-- The actual repeated branch derives its open law from scoped physical context entries. -/
theorem repeated (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (leftAvailable : Available source request.left)
    (rightAvailable : Available source request.right) (leftNames : BoundNames request.domain.key request.left)
    (rightNames : BoundNames request.domain.key request.right) (key : Nat × Nat)
    (selected : decision request.domain.key request.left request.right = .repeated key) :
    Meaning holds source request (repeatedValue key) := by
  intro input output bound seen term
  obtain ⟨first, second, leftId, rightId, keyEq⟩ := repeated_identities _ _ _ key selected
  have left := identity_language holds source facts input request.domain.key bound _ leftAvailable leftNames first leftId
  have right := identity_language holds source facts input request.domain.key bound _ rightAvailable rightNames second rightId
  have context := congrFun (seen key (SourceRecursiveIntersectionResultScope.repeated_seen _ _ _ key selected)) term
  simp only [InternedGuardedLanguage.meaning, repeatedValue]
  rw [left, right]
  rw [context, keyEq]
  rcases Nat.le_total first second with ordered | ordered
  · simp only [pair, Nat.min_eq_left ordered, Nat.max_eq_right ordered]
  · simp only [pair, Nat.min_eq_right ordered, Nat.max_eq_left ordered]
    exact and_comm

/-- Literal empty operands give the full open law without a context assumption. -/
theorem empty (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (request : NodeRequest Symbol Guard)
    (literal : request.left = .empty ∨ request.right = .empty) : Meaning holds source request .empty := by
  intro input output _ _ term
  rcases literal with left | right
  · simp only [left, InternedGuardedLanguage.meaning, false_and]
  · simp only [right, InternedGuardedLanguage.meaning, and_false]

/-- Actual coherent closed self reuse gives the full open law. -/
theorem self (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (leftAvailable : Available source request.left)
    (rightAvailable : Available source request.right) (same : closedSelf request.left request.right = true) :
    Meaning holds source request request.left := by
  have equal := self_record source facts _ _ leftAvailable rightAvailable same
  have closed : request.left.free = [] := by
    simp only [closedSelf, Bool.and_eq_true] at same
    exact List.isEmpty_iff.mp same.2
  intro input output _ _ term
  rw [← equal]
  rw [InternedGuardedLanguage.closed_meaning holds request.left source facts.coherent leftAvailable closed output input]
  exact ⟨fun accepted => ⟨accepted, accepted⟩, fun accepted => accepted.1⟩

/-- The source swap retains both contexts and reverses only the operand conjunction. -/
theorem swap (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (request : NodeRequest Symbol Guard)
    (value : Value Symbol Guard)
    (law : Meaning holds source ⟨request.domain, request.right, request.left⟩ value) : Meaning holds source request value := by
  intro input output bound seen term
  exact (law input output bound seen term).trans and_comm

/-- A closed reset child law transports to every incoming source and result environment. -/
theorem reset (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (leftClosed : request.left.free = []) (rightClosed : request.right.free = [])
    (child : SourceEqualityNativeDemandProvenance.NodeMeaning holds
      ⟨IntersectionEmptyDomain.emptyDomain, request.left, request.right⟩ value) : Meaning holds source request value := by
  intro input output _ _ term
  have observed := child rfl leftClosed rightClosed output term
  rw [InternedGuardedLanguage.closed_meaning holds request.left source facts.coherent leftAvailable leftClosed output input,
    InternedGuardedLanguage.closed_meaning holds request.right source facts.coherent rightAvailable rightClosed output input] at observed
  exact observed

/-- At closed inputs in the exact empty domain, the open law and existing law agree. -/
theorem closed_iff (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (left right value : Value Symbol Guard) (leftAvailable : Available source left)
    (rightAvailable : Available source right) (leftClosed : left.free = []) (rightClosed : right.free = []) :
    Meaning holds source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value ↔
      SourceEqualityNativeDemandProvenance.NodeMeaning holds ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value :=
  ⟨Meaning.closed holds source _ value, reset holds source facts
    ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value leftAvailable rightAvailable leftClosed rightClosed⟩

/-- Actual optional-binder completion gives its least language for every candidate environment. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (source : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap source)
    (heap : InternedGuardedProbeHeap.Heap source) (available : Available source body)
    (value : Value Symbol Guard) (after : InternedConstructorTemplates.State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body source = .done value after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning holds ambient value = BinderLanguage.least (fun candidate =>
      InternedGuardedLanguage.meaning holds
        (InternedGuardedLanguage.bind ambient (.intersection key.1 key.2) candidate) body) :=
  (SourceRecursiveIntersectionGuardedEffects.optionalBinder_checked key body source semantic heap available).result
    value after done holds ambient

/-- Actual binder completion removes its own pair before environment transport. -/
theorem optionalBinder_transport [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat)
    (body : Value Symbol Guard) (source current : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap current) (available : Available current body)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (scope : SourceRecursiveIntersectionResultScope.Scope (key :: domain.seen) body)
    (value : Value Symbol Guard) (after : InternedConstructorTemplates.State Symbol Guard)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu key body current = .done value after)
    (holds : Guard → Term Symbol → Bool) (input first second : InternedGuardedLanguage.Env Symbol)
    (firstContext : SeenContext holds source input first domain)
    (secondContext : SeenContext holds source input second domain) :
    SourceRecursiveIntersectionResultScope.Scope domain.seen value ∧
      InternedGuardedLanguage.meaning holds first value = InternedGuardedLanguage.meaning holds second value := by
  have facts := semantic.1.normal.facts
  have context := SourceRecursiveIntersectionSemanticHeap.context current semantic (InternedStoredSubstitution.leaves body)
    (InternedStoredSubstitution.leaves_available body current available)
  have resultScope := SourceRecursiveIntersectionResultScope.optionalBinder domain.seen key body current context available scope value after done
  have actual := SourceRecursiveIntersectionMaybeMu.verified key body current facts available
  have afterFacts : Facts after := by simpa only [done, InternedNestedConstruction.Outcome.state] using actual.facts
  exact ⟨resultScope, environment_transport holds source after afterFacts input first second domain value
    (actual.result value after done) resultScope firstContext secondContext⟩

/-- Every actual repeated branch makes the prior closed-only law vacuous for every result. -/
theorem repeated_nodeMeaning_any (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (key : Nat × Nat) (selected : decision request.domain.key request.left request.right = .repeated key)
    (value : Value Symbol Guard) : SourceEqualityNativeDemandProvenance.NodeMeaning holds request value := by
  intro empty
  have member := SourceRecursiveIntersectionResultScope.repeated_seen _ _ _ key selected
  simp only [empty, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey, List.not_mem_nil] at member

/-- The checked interpreter returns the actual repeated leaf without an edge or constructor call. -/
theorem repeated_body_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (key : Nat × Nat)
    (selected : decision request.domain.key request.left request.right = .repeated key)
    (state : SourceEqualityNativeDemand.State width) :
    SourceEqualityNativeDemand.execute 1 (.code (compileNode request)) state = .done (repeatedValue key) state := by
  simp only [compileNode, selected, SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
    SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift]

/-- A seen-pair override satisfies this context only at the prescribed operand language. -/
theorem seen_override_forces (holds : Guard → Term Symbol → Bool)
    (source : InternedConstructorTemplates.State Symbol Guard) (input output : InternedGuardedLanguage.Env Symbol)
    (domain : IntersectionFlatMemoKeyDomain.DomainKey) (key : Nat × Nat) (member : key ∈ domain.seen)
    (candidate : BinderLanguage.Lang Symbol)
    (context : SeenContext holds source input
      (InternedGuardedLanguage.bind output (.intersection key.1 key.2) candidate) domain) :
    candidate = fun term => namedLanguage holds source input key.1 term ∧ namedLanguage holds source input key.2 term := by
  simpa only [InternedGuardedLanguage.bind, ↓reduceIte] using context key member

/-- Actual repeated reference calls satisfy the old law while an unrestricted ambient law fails. -/
theorem repeated_reference_boundary [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Term Symbol → Bool) (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (seen : (0, 1) ∈ domain.key.seen) (state : SourceEqualityNativeDemand.State width) (symbol : Symbol) :
    let request : NodeRequest Symbol Guard := ⟨domain, .reference (.interned 0), .reference (.interned 1)⟩
    let value : Value Symbol Guard := repeatedValue (0, 1)
    SourceEqualityNativeDemand.execute 1 (.code (compileNode request)) state = .done value state ∧
      SourceEqualityNativeDemandProvenance.NodeMeaning holds request value ∧
      ¬ (∀ ambient term, InternedGuardedLanguage.meaning holds ambient value term ↔
        InternedGuardedLanguage.meaning holds ambient request.left term ∧
        InternedGuardedLanguage.meaning holds ambient request.right term) := by
  dsimp only
  have selected : decision domain.key (.reference (.interned 0) : Value Symbol Guard)
      (.reference (.interned 1)) = .repeated (0, 1) :=
    repeated_first domain.key _ _ rfl rfl rfl rfl 0 1 rfl rfl seen
  refine ⟨repeated_body_done _ (0, 1) selected state, repeated_nodeMeaning_any holds _ (0, 1) selected _, ?_⟩
  intro unrestricted
  let ambient : InternedGuardedLanguage.Env Symbol := fun name => match name with
    | .interned _ => fun _ => True
    | _ => fun _ => False
  have common : InternedGuardedLanguage.meaning holds ambient (.reference (.interned 0)) (.node symbol []) ∧
      InternedGuardedLanguage.meaning holds ambient (.reference (.interned 1)) (.node symbol []) := by
    simp only [InternedGuardedLanguage.meaning, ambient, and_self]
  have impossible := (unrestricted ambient (.node symbol [])).mpr common
  simp only [repeatedValue, InternedGuardedLanguage.meaning, ambient] at impossible

end MicroCFTA.SourceEqualityNativeDemandOpenMeaning
