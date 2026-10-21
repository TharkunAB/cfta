import MicroCFTA.SourceRecursiveIntersectionNativeApi
import MicroCFTA.InternedNormalizationFree
import MicroCFTA.IntersectConstruction
import MicroCFTA.SourceRecursiveIntersectionStep

/-!
# Physical recursive input view

The view reads original records through the actual issued-key and payload
maps. Constructor tags and canonical identities select their exact payload.
Rows retain executable guards and ordered children. Unsupported reference
placeholders map to the empty default outside the complete input codec.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedFreshProbeKeys InternedBinderProtocol IntersectSchedule
open InternedNestedFacts

/-- Complete physical input references use the existing source codec. -/
def inputOf (value : Value Symbol Guard) : Input := (IntersectionFlatMemoKey.input value.referenceOf).getD .empty

/-- Only actual interned recursion names occur in the complete input view. -/
def internedName : Reference → Option Nat
  | .interned name => some name
  | _ => none

/-- Project the actual cached free field onto complete interned recursion names. -/
def freeNames (value : Value Symbol Guard) : List Nat := value.free.filterMap internedName

/-- Read the exact requested constructor tag and canonical identity, with empty defaults elsewhere. -/
def payload (state : InternedConstructorTemplates.State Symbol Guard) (input : Input) : Value Symbol Guard :=
  match input with
  | .empty => .empty
  | .ref name => .reference (.interned name)
  | .node name | .mu name | .union name =>
      match SourcePreparedSharedRows.read state name with
      | some value => if inputOf value = input then value else .empty
      | none => .empty

mutual
/-- Copy original physical payload syntax without probe metadata. -/
def shape (holds : Guard → Language.Term Symbol → Bool) : Value Symbol Guard → Shape (Payload Symbol)
  | .empty => .empty
  | .reference (.interned name) => .ref name
  | .reference _ => .empty
  | .node _ edges _ _ => .alternatives (shapeEdges holds edges)
  | .union _ members _ _ => .alternatives (shapeValues holds members)
  | .mu entry body _ _ => .binder entry.identity (shape holds body)
termination_by value => sizeOf value

/-- Copy the actual symbol, complete guard, and ordered physical children of an edge. -/
def shapeEdge (holds : Guard → Language.Term Symbol → Bool) (edge : EdgeValue Symbol Guard) : Shape (Payload Symbol) :=
  .branch ⟨edge.entry.key.symbol, fun term => holds edge.entry.key.constraint term = true⟩ (shapeValues holds edge.children)
termination_by sizeOf edge
decreasing_by cases edge; simp_wf; simp only [EdgeValue.children]; omega

/-- Copy physical member lists in their original order. -/
def shapeValues (holds : Guard → Language.Term Symbol → Bool) : List (Value Symbol Guard) → List (Shape (Payload Symbol))
  | [] => []
  | first :: rest => shape holds first :: shapeValues holds rest
termination_by values => sizeOf values

/-- Copy original physical row lists in their original order. -/
def shapeEdges (holds : Guard → Language.Term Symbol → Bool) : List (EdgeValue Symbol Guard) → List (Shape (Payload Symbol))
  | [] => []
  | first :: rest => shapeEdge holds first :: shapeEdges holds rest
termination_by edges => sizeOf edges
end

/-- An input row retains actual ordered child references and the executable physical guard. -/
def row (holds : Guard → Language.Term Symbol → Bool) (edge : EdgeValue Symbol Guard) : Row Symbol :=
  ⟨edge.entry.key.symbol, edge.children.map inputOf, holds edge.entry.key.constraint⟩

/-- Construct the semantic input view from actual physical payload reads. -/
def view (state : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool) : View Symbol where
  rows name := match payload state (.node name) with
    | .node _ edges _ _ => edges.map (row holds)
    | _ => []
  body name := match payload state (.mu name) with
    | .mu _ body _ _ => inputOf body
    | _ => .empty
  members name := match payload state (.union name) with
    | .union _ members _ _ => members.map inputOf
    | _ => []
  free input := freeNames (payload state input)
  copy input := shape holds (payload state input)

/-- The complete source codec gives the exact input selected by physical readback. -/
theorem inputOf_codec (value : Value Symbol Guard) (input : Input)
    (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) : inputOf value = input := by
  simp only [inputOf, complete, Option.getD_some]

/-- Interned free-name projection retains exactly the actual cached interned references. -/
theorem freeNames_member (value : Value Symbol Guard) (name : Nat) : name ∈ freeNames value ↔ Reference.interned name ∈ value.free := by
  simp only [freeNames, List.mem_filterMap]
  constructor
  · rintro ⟨reference, member, found⟩
    cases reference <;> simp only [internedName, reduceCtorEq, Option.some.injEq] at found
    subst name
    exact member
  · intro member
    exact ⟨.interned name, member, rfl⟩

/-- Complete available values read back their original payload through the actual maps. -/
theorem payload_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value) (input : Input)
    (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) : payload state input = value := by
  cases value with
  | empty => cases complete; rfl
  | reference name =>
      cases name <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, reduceCtorEq] at complete
      cases complete
      rfl
  | node entry edges depth free | union entry edges depth free | mu entry edges depth free =>
      cases complete
      have found := SourcePreparedSharedRows.read_identity state facts _ available entry.identity rfl
      simp only [payload, found]
      rw [ite_eq_left (inputOf_codec _ _ rfl)]

/-- Cached interned free fields read back exactly, including placeholder defaults. -/
theorem free_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (available : Available state value) :
    (view state holds).free (inputOf value) = freeNames value := by
  cases value with
  | empty => rfl
  | reference name => cases name <;> rfl
  | node entry edges depth free | union entry edges depth free | mu entry edges depth free =>
      exact congrArg freeNames (payload_readback state facts _ available _ rfl)

/-- Exact physical readback retains the copied payload syntax and its original guard. -/
theorem copy_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard) (available : Available state value)
    (input : Input) (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) :
    (view state holds).copy input = shape holds value :=
  congrArg (shape holds) (payload_readback state facts value available input complete)

/-- A selected nonprimitive payload is either the empty default or the exact tagged map read. -/
theorem payload_selected (state : InternedConstructorTemplates.State Symbol Guard) (name : Nat) (input : Input)
    (tagged : input = .node name ∨ input = .mu name ∨ input = .union name) :
    payload state input = .empty ∨ ∃ value, SourcePreparedSharedRows.read state name = some value ∧
      inputOf value = input ∧ payload state input = value := by
  cases found : SourcePreparedSharedRows.read state name with
  | none =>
      left
      rcases tagged with rfl | rfl | rfl <;> simp [payload, found]
  | some value =>
      by_cases same : inputOf value = input
      · right
        refine ⟨value, rfl, same, ?_⟩
        rcases tagged with rfl | rfl | rfl <;> simp [payload, found, same]
      · left
        rcases tagged with rfl | rfl | rfl <;> simp [payload, found, same]

/-- An original node's free metadata is exact for its ordered physical row children. -/
theorem node_free_member (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (available : Available state (.node entry edges depth free)) (name : Nat) :
    name ∈ freeNames (.node entry edges depth free) ↔
      ∃ edge ∈ edges, ∃ child ∈ edge.children, name ∈ freeNames child := by
  rw [freeNames_member]
  simp only [Value.free, InternedNormalizationFree.node_free state facts.coherent entry edges depth free available.resident,
    childFree_member]
  simp only [List.mem_flatMap, freeNames_member]
  constructor
  · rintro ⟨child, ⟨edge, present, inside⟩, named⟩
    exact ⟨edge, present, child, inside, named⟩
  · rintro ⟨edge, present, child, inside, named⟩
    exact ⟨child, ⟨edge, present, inside⟩, named⟩

/-- Cached free-name equations follow from actual coherent physical payloads. -/
theorem free_correct (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) : FreeCorrect (view state holds) := by
  constructor
  · rfl
  · intro name; rfl
  · intro bound name
    rcases payload_selected state bound (.mu bound) (.inr (.inl rfl)) with absent | ⟨value, found, same, selected⟩
    · simp [view, absent, freeNames, Value.free, payload.eq_1]
    · cases value <;> simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input,
        Option.getD_some, reduceCtorEq, Input.mu.injEq] at same <;> try contradiction
      case reference reference => cases reference <;> contradiction
      case mu entry body depth ordinary =>
        subst bound
        have available := SourcePreparedSharedRows.read_available state facts _ _ found
        have bodyAvailable := available.children body (by simp [children])
        change name ∈ freeNames (payload state (.mu entry.identity)) ↔ _
        rw [selected]
        have bodyExact : (view state holds).body entry.identity = inputOf body := by simp only [view, selected]
        rw [bodyExact]
        change name ∈ freeNames (.mu entry body depth ordinary) ↔
          name ∈ (view state holds).free (inputOf body) ∧ name ≠ entry.identity
        rw [free_readback state facts holds body bodyAvailable, freeNames_member, freeNames_member]
        simp [Value.free]
  · intro identity name
    rcases payload_selected state identity (.node identity) (.inl rfl) with absent | ⟨value, found, same, selected⟩
    · simp [view, absent, freeNames, Value.free]
    · cases value <;> simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input,
        Option.getD_some, reduceCtorEq, Input.node.injEq] at same <;> try contradiction
      case reference reference => cases reference <;> contradiction
      case node entry edges depth free =>
        subst identity
        have available := SourcePreparedSharedRows.read_available state facts _ _ found
        change name ∈ freeNames (payload state (.node entry.identity)) ↔ _
        rw [selected]
        rw [node_free_member state facts entry edges depth free available name]
        have rowsExact : (view state holds).rows entry.identity = edges.map (row holds) := by simp only [view, selected]
        rw [rowsExact]
        constructor
        · rintro ⟨edge, present, child, inside, named⟩
          refine ⟨row holds edge, List.mem_map.mpr ⟨edge, present, rfl⟩,
            inputOf child, List.mem_map.mpr ⟨child, inside, rfl⟩, ?_⟩
          rw [free_readback state facts holds child (available.children child (List.mem_flatMap.mpr ⟨edge, present, inside⟩))]
          exact named
        · rintro ⟨_, present, _, inside, named⟩
          obtain ⟨edge, inEdges, rfl⟩ := List.mem_map.mp present
          obtain ⟨child, inChildren, rfl⟩ := List.mem_map.mp inside
          refine ⟨edge, inEdges, child, inChildren, ?_⟩
          rw [free_readback state facts holds child (available.children child (List.mem_flatMap.mpr ⟨edge, inEdges, inChildren⟩))] at named
          exact named
  · intro identity name
    rcases payload_selected state identity (.union identity) (.inr (.inr rfl)) with absent | ⟨value, found, same, selected⟩
    · simp [view, absent, freeNames, Value.free]
    · cases value <;> simp only [inputOf, Value.referenceOf, IntersectionFlatMemoKey.input,
        Option.getD_some, reduceCtorEq, Input.union.injEq] at same <;> try contradiction
      case reference reference => cases reference <;> contradiction
      case union entry members depth free =>
        subst identity
        have available := SourcePreparedSharedRows.read_available state facts _ _ found
        change name ∈ freeNames (payload state (.union entry.identity)) ↔ _
        rw [selected, freeNames_member]
        simp only [Value.free, InternedNormalizationFree.union_free state facts.coherent entry members depth free available.resident,
          childFree_member]
        have membersExact : (view state holds).members entry.identity = members.map inputOf := by simp only [view, selected]
        rw [membersExact]
        constructor
        · rintro ⟨member, present, named⟩
          refine ⟨inputOf member, List.mem_map.mpr ⟨member, present, rfl⟩, ?_⟩
          rw [free_readback state facts holds member (available.children member present), freeNames_member]
          exact named
        · rintro ⟨_, present, named⟩
          obtain ⟨member, inMembers, rfl⟩ := List.mem_map.mp present
          refine ⟨member, inMembers, ?_⟩
          rw [free_readback state facts holds member (available.children member inMembers), freeNames_member] at named
          exact named

/-- Original payload syntax contains only complete interned references. Probe metadata is excluded. -/
inductive Original : Value Symbol Guard → Prop where
  | empty : Original .empty
  | reference (name : Nat) : Original (.reference (.interned name))
  | node (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
      (children : ∀ edge ∈ edges, ∀ child ∈ edge.children, Original child) : Original (.node entry edges depth free)
  | union (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
      (children : ∀ member ∈ members, Original member) : Original (.union entry members depth free)
  | mu (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
      (original : Original body) : Original (.mu entry body depth ordinary)

/-- Original available syntax has a complete root codec. -/
theorem Original.codec (value : Value Symbol Guard) (original : Original value) :
    IntersectionFlatMemoKey.input value.referenceOf = some (inputOf value) := by
  cases original <;> rfl

/-- Coherent cached free fields contain only interned names for original payload syntax. -/
theorem Original.free_interned (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (original : Original value) (available : Available state value) :
    ∀ reference ∈ value.free, ∃ name, reference = .interned name := by
  induction original with
  | empty => simp [Value.free]
  | reference name => intro reference member; simp only [Value.free, List.mem_singleton] at member; exact ⟨name, member⟩
  | node entry edges depth free children ih =>
      intro reference member
      rw [Value.free, InternedNormalizationFree.node_free state facts.coherent entry edges depth free available.resident,
        childFree_member] at member
      obtain ⟨child, inside, named⟩ := member
      obtain ⟨edge, present, inChild⟩ := List.mem_flatMap.mp inside
      exact ih edge present child inChild (available.children child inside) reference named
  | union entry members depth free children ih =>
      intro reference member
      rw [Value.free, InternedNormalizationFree.union_free state facts.coherent entry members depth free available.resident,
        childFree_member] at member
      obtain ⟨child, present, named⟩ := member
      exact ih child present (available.children child present) reference named
  | mu entry body depth ordinary original ih =>
      intro reference member
      exact ih (available.children body (by simp [children])) reference (List.mem_filter.mp member).1

/-- Original syntax makes projected closedness equal to the actual cached source test. -/
theorem closed_readback (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (value : Value Symbol Guard)
    (original : Original value) (available : Available state value) :
    closed (view state holds) (inputOf value) = value.free.isEmpty := by
  rw [closed, free_readback state facts holds value available]
  apply Bool.eq_iff_iff.mpr
  simp only [List.isEmpty_iff]
  constructor
  · intro empty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro reference member
    obtain ⟨name, rfl⟩ := original.free_interned state facts value available reference member
    have named := (freeNames_member value name).mpr member
    simp [empty] at named
  · intro empty
    simp [freeNames, empty]

/-- Actual complete physical branches select the semantic step with derived cached closedness. -/
theorem physical_step [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (fuel : Nat) (domain : IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state left) (rightAvailable : Available state right) :
    SourceRecursiveIntersectionStep.action (view state holds) fuel (SourceRecursiveIntersectionSchedule.domain domain)
        (inputOf left) (inputOf right) (SourceRecursiveIntersectionControl.decision domain left right) =
      some (IntersectSchedule.run (view state holds) (fuel + 1) (SourceRecursiveIntersectionSchedule.domain domain)
        (inputOf left) (inputOf right)) :=
  SourceRecursiveIntersectionStep.physical_step (view state holds) fuel domain left right (inputOf left) (inputOf right)
    (leftOriginal.codec left) (rightOriginal.codec right)
    (closed_readback state facts holds left leftOriginal leftAvailable)
    (closed_readback state facts holds right rightOriginal rightAvailable)

end MicroCFTA.SourceRecursiveIntersectionInputView
