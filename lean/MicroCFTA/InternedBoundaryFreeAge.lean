import MicroCFTA.InternedObservedAbsence
import MicroCFTA.InternedBoundaryProvenance
import MicroCFTA.InternedNestedOldRecords
import MicroCFTA.InternedNestedMissReadback

/-!
# Free-name age from observed recursive boundaries

A free name occurs at a literal boundary or inside a boundary Mu record.
An old Mu payload already existed before the actual nested source call.
Its issued free references therefore also predate that call. Ordinary
node identities need no age condition in this argument.
-/
namespace MicroCFTA.InternedBoundaryFreeAge
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBoundaryAtoms InternedObservedAbsence InternedNormalizationFree InternedFreshProbeKeys
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedPendingOrigins InternedNestedOldRecords
open InternedLiveEdges InternedBoundaryProvenance InternedBoundaryFilter
open InternedBinderProtocol (Reference NodeRef NodeKey)

mutual
/-- Every actual free name lies at a literal boundary or in the free set of one boundary Mu record. -/
theorem free_source (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (name : Reference) (member : name ∈ value.free) :
    .ref name ∈ atoms value ∨ ∃ entry body depth ordinary,
      .mu entry.identity ∈ atoms value ∧ Available state (.mu entry body depth ordinary) ∧
        name ∈ (Value.mu entry body depth ordinary).free := by
  cases value with
  | empty => simp [Value.free] at member
  | reference own =>
      left
      simpa only [Value.free, atoms, List.mem_singleton, NodeRef.ref.injEq] using member
  | node entry edges depth free =>
      have source : ∃ child ∈ edges.flatMap EdgeValue.children, name ∈ child.free := by
        apply (childFree_member _ name).mp
        simpa only [Value.free, node_free state coherent entry edges depth free available.resident] using member
      simpa only [atoms] using edges_free_source edges state coherent
        (fun child included => available.children child included) name source
  | union entry members depth free =>
      have source : ∃ child ∈ members, name ∈ child.free := by
        apply (childFree_member _ name).mp
        simpa only [Value.free, union_free state coherent entry members depth free available.resident] using member
      simpa only [atoms] using many_free_source members state coherent
        (fun child included => available.children child included) name source
  | mu entry body depth ordinary =>
      exact Or.inr ⟨entry, body, depth, ordinary, by simp [atoms], available, member⟩
termination_by sizeOf value

/-- The boundary source of a free child name survives concatenation of ordered member profiles. -/
theorem many_free_source (values : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ values, Available state value) (name : Reference)
    (member : ∃ value ∈ values, name ∈ value.free) :
    .ref name ∈ manyAtoms values ∨ ∃ entry body depth ordinary,
      .mu entry.identity ∈ manyAtoms values ∧ Available state (.mu entry body depth ordinary) ∧
        name ∈ (Value.mu entry body depth ordinary).free := by
  cases values with
  | nil => simp at member
  | cons first rest =>
      simp only [manyAtoms]
      obtain ⟨value, included, free⟩ := member
      rcases List.mem_cons.mp included with same | included
      · subst value
        rcases free_source first state coherent (available first List.mem_cons_self) name free with direct | nested
        · exact Or.inl (List.mem_append_left _ direct)
        · obtain ⟨entry, body, depth, ordinary, boundary, resident, present⟩ := nested
          exact Or.inr ⟨entry, body, depth, ordinary, List.mem_append_left _ boundary, resident, present⟩
      · rcases many_free_source rest state coherent (fun child present => available child (List.mem_cons_of_mem _ present))
          name ⟨value, included, free⟩ with direct | nested
        · exact Or.inl (List.mem_append_right _ direct)
        · obtain ⟨entry, body, depth, ordinary, boundary, resident, present⟩ := nested
          exact Or.inr ⟨entry, body, depth, ordinary, List.mem_append_right _ boundary, resident, present⟩
termination_by sizeOf values
decreasing_by all_goals simp_wf; all_goals simp_all; all_goals omega

/-- Ordinary edge profiles expose a boundary source for each actual free child name. -/
theorem edges_free_source (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state)
    (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available state value) (name : Reference)
    (member : ∃ value ∈ edges.flatMap EdgeValue.children, name ∈ value.free) :
    .ref name ∈ edgeAtoms edges ∨ ∃ entry body depth ordinary,
      .mu entry.identity ∈ edgeAtoms edges ∧ Available state (.mu entry body depth ordinary) ∧
        name ∈ (Value.mu entry body depth ordinary).free := by
  cases edges with
  | nil => simp at member
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [edgeAtoms]
          obtain ⟨value, included, free⟩ := member
          rcases List.mem_append.mp included with head | tail
          · rcases many_free_source children state coherent
              (fun child present => available child (List.mem_append_left _ present)) name ⟨value, head, free⟩ with direct | nested
            · exact Or.inl (List.mem_append_left _ direct)
            · obtain ⟨entry, body, depth, ordinary, boundary, resident, present⟩ := nested
              exact Or.inr ⟨entry, body, depth, ordinary, List.mem_append_left _ boundary, resident, present⟩
          · rcases edges_free_source rest state coherent
              (fun child present => available child (List.mem_append_right _ present)) name ⟨value, tail, free⟩ with direct | nested
            · exact Or.inl (List.mem_append_right _ direct)
            · obtain ⟨entry, body, depth, ordinary, boundary, resident, present⟩ := nested
              exact Or.inr ⟨entry, body, depth, ordinary, List.mem_append_right _ boundary, resident, present⟩
termination_by sizeOf edges
end

/-- Fresh literal references and fresh Mu identities expose a dependency on the new reservation range. -/
def Fresh (cutoff : Nat) : NodeRef → Prop
  | .ref (.interned identity) | .mu identity => cutoff ≤ identity
  | _ => False

/-- An observed source result with only old boundaries has only old issued free names, even inside captured Mu records. -/
theorem build_free_below [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (dense : Cache.Dense before.nodes)
    (origins : Origins pending before) (covered : Covered pending before)
    (value : Value Symbol Guard) (available : Available (build expression environment before).state value)
    (clear : Clear (Fresh before.nodes.next) value) (identity : Nat) (member : .interned identity ∈ value.free) :
    identity < before.nodes.next := by
  have checked := build_verified expression environment before facts inputs
  rcases free_source value _ checked.facts.coherent available (.interned identity) member with direct | nested
  · have excluded := clear (.ref (.interned identity)) direct
    simp only [Fresh] at excluded
    omega
  · obtain ⟨entry, body, depth, ordinary, boundary, resident, free⟩ := nested
    have old : entry.identity < before.nodes.next := by
      have excluded := clear (.mu entry.identity) boundary
      simp only [Fresh] at excluded
      omega
    have stored := build_old_record expression environment before facts inputs dense origins covered
      (.mu entry body depth ordinary) entry resident.resident rfl old
    exact issued_free_below before.nodes facts.coherent.valid.2 _ (facts.cached.nodes entry.key _ stored).issued identity free

/-- The same source observation excludes every new local free name after the actual call. -/
theorem build_fresh_absent [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (dense : Cache.Dense before.nodes)
    (origins : Origins pending before) (covered : Covered pending before)
    (value : Value Symbol Guard) (available : Available (build expression environment before).state value)
    (clear : Clear (Fresh before.nodes.next) value) (identity : Nat) (fresh : before.nodes.next ≤ identity) :
    .interned identity ∉ value.free := by
  intro member
  have := build_free_below expression environment before facts inputs dense origins covered value available clear identity member
  omega

/-- Actual root filtering preserves the old free-name bound, including its new ordinary cache records. -/
theorem build_filtered_free_below [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before environment) (dense : Cache.Dense before.nodes)
    (origins : Origins pending before) (covered : Covered pending before) (live : Live before)
    (raw : Value Symbol Guard) (after : State Symbol Guard)
    (completed : build expression environment before = .done raw after) (name : Reference)
    (clear : Clear (Fresh before.nodes.next) (run (withoutSelfReference name raw) after).1)
    (identity : Nat) (member : .interned identity ∈ (run (withoutSelfReference name raw) after).1.free) :
    identity < before.nodes.next := by
  have checked := build_verified expression environment before facts inputs
  have afterFacts : Facts after := by simpa only [completed, Outcome.state] using checked.facts
  have afterLive : Live after := by simpa only [completed, Outcome.state] using build_live expression environment before live
  have rawAvailable := checked.result raw after completed
  have filtered := filter_verified name raw after afterFacts rawAvailable
  have outputAvailable := filtered.result _ _ rfl
  rcases free_source _ _ filtered.facts.coherent outputAvailable (.interned identity) member with direct | nested
  · have excluded := clear (.ref (.interned identity)) direct
    simp only [Fresh] at excluded
    omega
  · obtain ⟨entry, body, depth, ordinary, boundary, resident, free⟩ := nested
    have old : entry.identity < before.nodes.next := by
      have excluded := clear (.mu entry.identity) boundary
      simp only [Fresh] at excluded
      omega
    have rawBoundary := (filter_mu_iff name entry.identity raw after afterFacts.coherent afterFacts.cached
      afterFacts.linked afterLive rawAvailable).mp boundary
    obtain ⟨earlier, earlierBody, earlierDepth, earlierOrdinary, sameIdentity, earlierAvailable⟩ :=
      mu_available raw after rawAvailable entry.identity rawBoundary
    have actualSame : Value.mu entry body depth ordinary = .mu earlier earlierBody earlierDepth earlierOrdinary :=
      resident_reference_injective _ filtered.facts.coherent _ _ resident.resident
        (available_after_run (withoutSelfReference name raw) after afterFacts.coherent.valid earlierAvailable).resident
        (by simp only [Value.referenceOf, sameIdentity])
    have originalResident : Resident (build expression environment before).state (.mu earlier earlierBody earlierDepth earlierOrdinary) := by
      simpa only [completed, Outcome.state] using earlierAvailable.resident
    have stored := build_old_record expression environment before facts inputs dense origins covered
      (.mu earlier earlierBody earlierDepth earlierOrdinary) earlier originalResident rfl (by simpa only [sameIdentity] using old)
    have oldAvailable := facts.cached.nodes earlier.key _ stored
    exact issued_free_below before.nodes facts.coherent.valid.2 _ oldAvailable.issued identity (actualSame ▸ free)

/-- Every complete source callback with old visible boundaries has only old issued free names. -/
theorem callback_free_below [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (before : State Symbol Guard) (facts : Facts before)
    (inputs : Values before (.reference name :: environment)) (dense : Cache.Dense before.nodes)
    (origins : Origins pending before) (covered : Covered pending before) (live : Live before)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : InternedNestedMissReadback.callback body environment name before = .done value final)
    (clear : Clear (Fresh before.nodes.next) value) (identity : Nat) (member : .interned identity ∈ value.free) :
    identity < before.nodes.next := by
  obtain ⟨raw, after, doneBody, doneFilter⟩ := InternedNestedSpecialization.bind_done _ _ _ _ completed
  have exactValue : (run (withoutSelfReference name raw) after).1 = value := by
    simpa only [work, Outcome.done.injEq] using (congrArg (fun outcome => match outcome with
      | .done found _ => found
      | .pending _ _ => .empty) doneFilter)
  apply build_filtered_free_below body (.reference name :: environment) before facts inputs dense origins covered live raw after doneBody name
  · simpa only [exactValue] using clear
  · simpa only [exactValue] using member

end MicroCFTA.InternedBoundaryFreeAge
