import MicroCFTA.SourceRecursiveIntersectionControl

/-!
# Physical recursive control and the semantic schedule

The accepted memo-input codec retains the complete source ordering tags.
Canonical physical domain bindings give the same lookup results as the
semantic schedule. Mu extension retains the original available records.
-/
namespace MicroCFTA.SourceRecursiveIntersectionSchedule
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain

/-- Constructor tags read from the actual source equality reference. -/
def referenceTag : NodeRef → Nat
  | .empty => 0
  | .node _ => 1
  | .mu _ => 2
  | .union _ => 3
  | .ref _ => 4

/-- Source comparison reads only the constructor tag and complete identity. -/
def referenceCompare (left right : NodeRef) : Ordering :=
  (compare (referenceTag left) (referenceTag right)).then
    (match left, right with
    | .node first, .node second | .mu first, .mu second | .union first, .union second => compare first second
    | .ref first, .ref second => compare first second
    | _, _ => .eq)

/-- Cached physical payload fields do not change source operand order. -/
theorem compare_reference (left right : Value Symbol Guard) :
    compareValue left right = referenceCompare left.referenceOf right.referenceOf := by
  cases left <;> cases right <;> rfl

/-- Complete recursive references compare their original enclosing identities. -/
theorem reference_interned (first second : Nat) :
    compare (Reference.interned first) (Reference.interned second) = compare first second := by
  change (compare first second).then .eq = compare first second
  exact Ordering.then_eq

/-- The complete source-input codec preserves comparison, including recursive occurrences. -/
theorem referenceCompare_source (left right : IntersectSchedule.Input) :
    (referenceCompare (IntersectionFlatMemoKey.source left) (IntersectionFlatMemoKey.source right)).isGT =
      IntersectSchedule.greater left right := by
  cases left <;> cases right <;>
    simp only [referenceCompare, referenceTag, IntersectionFlatMemoKey.source,
      IntersectSchedule.greater, IntersectSchedule.tag, IntersectSchedule.identity] <;> try rfl
  all_goals simp only [reference_interned, Nat.lt_irrefl, false_or, true_and]
  all_goals change (compare (_ : Nat) (_ : Nat)).isGT = decide ((_ : Nat) < _)
  all_goals exact Bool.eq_iff_iff.mpr (by simp [Nat.compare_eq_gt])

/-- Every complete physical operand comparison equals the proved semantic schedule comparison. -/
theorem greater_encoded (left right : Value Symbol Guard) (first second : IntersectSchedule.Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second) :
    greater left right = IntersectSchedule.greater first second := by
  rw [greater, compare_reference,
    IntersectionFlatMemoKey.input_reconstruct _ _ leftInput,
    IntersectionFlatMemoKey.input_reconstruct _ _ rightInput]
  exact referenceCompare_source first second

/-- A sorted complete physical request cannot require a second operand swap. -/
theorem swap_once (left right : Value Symbol Guard) (first second : IntersectSchedule.Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second)
    (swap : greater left right = true) : greater right left = false := by
  rw [greater_encoded right left second first rightInput leftInput]
  exact IntersectSchedule.greater_asymmetric first second
    ((greater_encoded left right first second leftInput rightInput).symm.trans swap)

/-- Translate each actual free-map key to the original enclosing semantic Mu identity. -/
def domain (source : DomainKey) : IntersectSchedule.Domain :=
  ⟨(names source).map (fun name => (name, IntersectSchedule.Input.mu name)), source.seen⟩

/-- The semantic free-map lookup names the same original binder as the typed source map. -/
theorem lookup_domain (source : DomainKey) (name : Nat) :
    IntersectSchedule.lookup (domain source) name =
      if name ∈ names source then some (.mu name) else none := by
  cases source with
  | mk bindings seen =>
      induction bindings with
      | nil => rfl
      | cons binding rest ih =>
          by_cases same : binding.1 = name
          · simp [domain, names, IntersectSchedule.lookup, same]
          · simp only [domain, names, List.map_cons, IntersectSchedule.lookup, List.find?_cons,
              beq_eq_false_iff_ne.mpr same]
            have equation := ih
            simp only [domain, names, IntersectSchedule.lookup] at equation
            rw [equation]
            simp only [List.mem_cons, Ne.symm same, false_or]
            rfl

/-- The physical canonical domain returns the same tagged binder as the semantic schedule. -/
theorem lookup_key (source : DomainKey) (typed : Typed source) (name : Nat) :
    keyLookup source name = (IntersectSchedule.lookup (domain source) name).map IntersectionFlatMemoKey.source := by
  rw [keyLookup_typed source typed name, lookup_domain]
  split <;> rfl

/-- Semantic lookup and physical cache readback agree on the complete original Mu record. -/
theorem lookup_record (state : State Symbol Guard) (facts : Facts state) (source : DomainKey)
    (bindings : AvailableBindings state source) (name : Nat)
    (found : IntersectSchedule.lookup (domain source) name = some (.mu name)) :
    ∃ entry body depth ordinary, entry.identity = name ∧ Available state (.mu entry body depth ordinary) ∧
      lookup state source name = some (.mu entry body depth ordinary) := by
  have member : name ∈ names source := by
    rw [lookup_domain] at found
    split at found
    · assumption
    · contradiction
  exact lookup_complete state facts source bindings name member

/-- Canonical physical extension and the source schedule's overwrite list have identical lookups. -/
theorem extend_lookup (source : DomainKey) (bound : List Nat) (key : Nat × Nat) (name : Nat) :
    IntersectSchedule.lookup (domain (extend source bound key)) name =
      IntersectSchedule.lookup
        (IntersectSchedule.extend (domain source) (bound.map (fun name => (name, IntersectSchedule.Input.mu name))) key) name := by
  rw [lookup_domain]
  have sourceLookup : ∀ bindings : List Nat,
      ((bindings.map (fun key => (key, IntersectSchedule.Input.mu key))).find? (fun binding => binding.1 == name)).map Prod.snd =
        if name ∈ bindings then some (IntersectSchedule.Input.mu name) else none := by
    intro bindings
    induction bindings with
    | nil => rfl
    | cons first rest ih =>
        by_cases same : first = name
        · simp [same]
        · simp only [List.map_cons, List.find?_cons, beq_eq_false_iff_ne.mpr same]
          rw [ih]
          simp only [List.mem_cons, Ne.symm same, false_or]
  simp only [extend_names]
  change (if name ∈ bound ∨ name ∈ names source then some _ else none) =
    (((bound.map (fun key => (key, IntersectSchedule.Input.mu key))).reverse ++
      (names source).map (fun key => (key, IntersectSchedule.Input.mu key))).find? (fun binding => binding.1 == name)).map Prod.snd
  rw [← List.map_reverse, ← List.map_append, sourceLookup]
  simp

/-- Read the source payload branch from its complete canonical references. -/
def referencePayload : NodeRef → NodeRef → Branch
  | .mu _, .mu _ => .bothMu
  | .mu _, _ => .leftMu
  | _, .mu _ => .rightMu
  | .union _, _ => .leftUnion
  | _, .union _ => .rightUnion
  | .ref _, _ => .leftReference
  | _, .ref _ => .rightReference
  | .node _, .node _ => .ordinary
  | _, _ => .unsupported

/-- Complete source payload tags retain the exact recursive branch. -/
theorem payload_reference (left right : Value Symbol Guard) :
    payload left right = referencePayload left.referenceOf right.referenceOf := by
  cases left <;> cases right <;> rfl

/-- The accepted complete-input codec reconstructs the optional source identity. -/
def referenceIdentity : NodeRef → Option Nat
  | .node name | .mu name | .union name | .ref (.interned name) => some name
  | _ => none

/-- Physical source identities depend only on complete equality references. -/
theorem identity_reference (value : Value Symbol Guard) : identity value = referenceIdentity value.referenceOf := by
  cases value <;> try rfl
  rename_i name
  cases name <;> rfl

/-- Accepted physical operands retain the semantic identity, with zero used only for Empty. -/
theorem identity_encoded (value : Value Symbol Guard) (input : IntersectSchedule.Input)
    (encoded : IntersectionFlatMemoKey.input value.referenceOf = some input) :
    (identity value).getD 0 = IntersectSchedule.identity input := by
  rw [identity_reference, IntersectionFlatMemoKey.input_reconstruct _ _ encoded]
  cases input <;> rfl

/-- Actual nonempty source identities give exactly the semantic schedule's independently sorted pair. -/
theorem pair_encoded (left right : Value Symbol Guard) (first second : IntersectSchedule.Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second)
    (leftId rightId : Nat) (leftIdentity : identity left = some leftId) (rightIdentity : identity right = some rightId) :
    pair leftId rightId = IntersectSchedule.pair first second := by
  have firstId := identity_encoded left first leftInput
  have secondId := identity_encoded right second rightInput
  simp only [leftIdentity, rightIdentity, Option.getD_some] at firstId secondId
  simp only [pair, IntersectSchedule.pair, ← firstId, ← secondId]

/-- The complete codec round trip retains every accepted input tag and identity. -/
theorem input_source (value : IntersectSchedule.Input) :
    IntersectionFlatMemoKey.input (IntersectionFlatMemoKey.source value) = some value := by
  cases value <;> rfl

/-- Complete equality references identify exactly one semantic input. -/
theorem source_injective : Function.Injective IntersectionFlatMemoKey.source := by
  intro first second same
  have roundtrip := congrArg IntersectionFlatMemoKey.input same
  simpa only [input_source, Option.some.injEq] using roundtrip

/-- Complete source equality has the same result in the semantic schedule. -/
theorem source_beq (first second : IntersectSchedule.Input) :
    (IntersectionFlatMemoKey.source first == IntersectionFlatMemoKey.source second) = (first == second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact source_injective.eq_iff

/-- Complete empty tests have the same result in the semantic schedule. -/
theorem source_empty (value : IntersectSchedule.Input) :
    (IntersectionFlatMemoKey.source value == NodeRef.empty) = (value == IntersectSchedule.Input.empty) := by
  exact source_beq value .empty

/-- Read the semantic schedule's complete branch with the actual cached closedness tests. -/
def inputDecision (domain : IntersectSchedule.Domain) (leftClosed rightClosed : Bool)
    (left right : IntersectSchedule.Input) : Branch :=
  if left == .empty || right == .empty then .empty
  else if leftClosed && rightClosed && !domain.free.isEmpty then .reset
  else if left == right && leftClosed then .self
  else if IntersectSchedule.greater left right then .swap
  else if IntersectSchedule.pair left right ∈ domain.seen then .repeated (IntersectSchedule.pair left right)
  else referencePayload (IntersectionFlatMemoKey.source left) (IntersectionFlatMemoKey.source right)

/-- Physical branch selection agrees with the complete semantic schedule for every accepted input pair. -/
theorem decision_encoded (source : DomainKey) (left right : Value Symbol Guard)
    (first second : IntersectSchedule.Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second) :
    decision source left right = inputDecision (domain source) left.free.isEmpty right.free.isEmpty first second := by
  have order := greater_encoded left right first second leftInput rightInput
  have firstRef := IntersectionFlatMemoKey.input_reconstruct _ _ leftInput
  have secondRef := IntersectionFlatMemoKey.input_reconstruct _ _ rightInput
  simp only [decision, hasEmpty, reset, closedSelf, order, identity_reference, payload_reference,
    firstRef, secondRef, source_empty, source_beq, inputDecision, domain, names, List.isEmpty_map]
  cases first <;> cases second <;>
    simp [referenceIdentity, IntersectionFlatMemoKey.source, pair, IntersectSchedule.pair, IntersectSchedule.identity] <;> rfl

end MicroCFTA.SourceRecursiveIntersectionSchedule
