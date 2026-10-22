import MicroCFTA.SourceRecursiveIntersectionInputRanks

/-!
# Finite original physical input inventory

The actual issued counter contains all complete available inputs. Original
payload reachability retains complete available records. Closed-root
reference unfolding therefore remains inside this finite physical inventory.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule

/-- An input represents original available syntax through the complete physical codec. -/
def OriginalInput (state : InternedConstructorTemplates.State Symbol Guard) (input : Input) : Prop :=
  ∃ value, Original value ∧ Available state value ∧ IntersectionFlatMemoKey.input value.referenceOf = some input

/-- The finite issued counter bounds a tagged carrier for all original available payloads. -/
def inventory (state : InternedConstructorTemplates.State Symbol Guard) : List Input :=
  .empty :: (List.range state.nodes.next).flatMap fun name => [.node name, .mu name, .union name, .ref name]

/-- Every complete available input belongs to the actual finite issued carrier. -/
theorem inventory_available (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (value : Value Symbol Guard) (available : Available state value) (input : Input)
    (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) : input ∈ inventory state := by
  cases value with
  | empty => cases complete; simp [inventory]
  | reference reference =>
      cases reference with
      | interned name =>
          cases complete
          have bound := IntersectionFlatMemoKeyPhysical.reference_bounded state facts name available
          simp only [inventory, List.mem_cons, List.mem_flatMap]
          exact .inr ⟨name, List.mem_range.mpr bound, by simp⟩
      | uninterned | depth | intersection | state => cases complete
  | node entry edges depth free | union entry edges depth free | mu entry edges depth free =>
      cases complete
      have bound := IntersectionFlatMemoKeyPhysical.entry_bounded state facts _ available entry rfl
      simp only [inventory, List.mem_cons, List.mem_flatMap]
      exact .inr ⟨entry.identity, List.mem_range.mpr bound, by simp⟩

/-- Every original physical input is in the finite actual issued carrier. -/
theorem OriginalInput.inventory (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (input : Input) (original : OriginalInput state input) : input ∈ inventory state := by
  obtain ⟨value, _, available, complete⟩ := original
  exact inventory_available state facts value available input complete

/-- An original Mu input retains its actual complete available body. -/
theorem OriginalInput.body (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (name : Nat) (original : OriginalInput state (.mu name)) :
    OriginalInput state ((view state holds).body name) := by
  obtain ⟨value, original, available, complete⟩ := original
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case mu entry body depth ordinary original =>
    cases complete
    have selected := payload_readback state facts _ available (.mu entry.identity) rfl
    have bodyExact : (view state holds).body entry.identity = inputOf body := by simp only [view, selected]
    rw [bodyExact]
    exact ⟨body, original, available.children body (by simp [children]), original.codec body⟩

/-- An original node retains complete available original children in every physical row. -/
theorem OriginalInput.child (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (name : Nat) (original : OriginalInput state (.node name))
    (selectedRow : Row Symbol) (present : selectedRow ∈ (view state holds).rows name)
    (input : Input) (member : input ∈ selectedRow.children) : OriginalInput state input := by
  obtain ⟨value, original, available, complete⟩ := original
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case node entry edges depth free originals =>
    cases complete
    have selected := payload_readback state facts _ available (.node entry.identity) rfl
    have rowsExact : (view state holds).rows entry.identity = edges.map (row holds) := by simp only [view, selected]
    rw [rowsExact] at present
    obtain ⟨edge, inEdges, rfl⟩ := List.mem_map.mp present
    obtain ⟨child, inChildren, rfl⟩ := List.mem_map.mp member
    have original := originals edge inEdges child inChildren
    exact ⟨child, original, available.children child (List.mem_flatMap.mpr ⟨edge, inEdges, inChildren⟩), original.codec child⟩

/-- An original union retains its complete available original members. -/
theorem OriginalInput.member (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (name : Nat) (original : OriginalInput state (.union name))
    (input : Input) (member : input ∈ (view state holds).members name) : OriginalInput state input := by
  obtain ⟨value, original, available, complete⟩ := original
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case union entry members depth free originals =>
    cases complete
    have selected := payload_readback state facts _ available (.union entry.identity) rfl
    have membersExact : (view state holds).members entry.identity = members.map inputOf := by simp only [view, selected]
    rw [membersExact] at member
    obtain ⟨child, inMembers, rfl⟩ := List.mem_map.mp member
    have original := originals child inMembers
    exact ⟨child, original, available.children child inMembers, original.codec child⟩

/-- Original payload containment retains complete available syntax. -/
theorem payload_reach_original (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (root input : Input) (original : OriginalInput state root)
    (reachable : PayloadReach (view state holds) root input) : OriginalInput state input := by
  induction reachable with
  | root => exact original
  | body _ ih => exact ih.body state facts holds _
  | child _ present member ih => exact ih.child state facts holds _ _ present _ member
  | member _ present ih => exact ih.member state facts holds _ _ present

/-- Closed-root reference unfolding retains complete available original syntax. -/
theorem closed_reach_original (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (root input : Input) (original : OriginalInput state root)
    (isClosed : closed (view state holds) root = true) (reachable : InputReach (view state holds) root input) :
    OriginalInput state input :=
  payload_reach_original state facts holds root input original
    (closed_reach_payload (view state holds) (free_correct state facts holds) root input isClosed reachable)

/-- Every input reached from a closed original root is in the actual finite physical carrier. -/
theorem closed_reach_inventory (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (root input : Input) (original : OriginalInput state root)
    (isClosed : closed (view state holds) root = true) (reachable : InputReach (view state holds) root input) :
    input ∈ inventory state :=
  (closed_reach_original state facts holds root input original isClosed reachable).inventory state facts input

end MicroCFTA.SourceRecursiveIntersectionInputView
