import MicroCFTA.InternedRecordCoherence

/-!
# Fresh outer references separate actual Mu probe keys

Canonical readback makes cached free-reference metadata observable from a
resident node identity. A fresh issued reference cannot occur in a probe
whose references were all issued before that reservation.
-/
namespace MicroCFTA.InternedFreshProbeKeys
open Cache InternedBinderProtocol InternedConstructorTemplates InternedRecordCoherence

/-- Nonprimitive values are the complete canonical records stored under their own entry keys. -/
def Resident (state : InternedConstructorTemplates.State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∀ entry, entryOf value = some entry → state.nodeRecords entry.key = some value

/-- Actual coherent table readback supplies residency without a separate identity assumption. -/
theorem stored_resident (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (key : NodeKey) (value : Value Symbol Guard) (stored : state.nodeRecords key = some value) : Resident state value := by
  obtain ⟨actual, present, fields⟩ := coherent.nodes key value stored
  intro entry field
  have same : actual = entry := Option.some.inj ((fields_entry _ _ _ fields).symm.trans field)
  subst actual
  have keyEq := (coherent.valid.2.2 key entry present).1
  simpa [keyEq] using stored

/-- Resident records remain resident after actual record-table growth. -/
theorem resident_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (growth : Grows before after) (value : Value Symbol Guard) (resident : Resident before value) : Resident after value :=
  fun entry field => growth.nodeRecords _ _ (resident entry field)

/-- A resident record carries the exact canonical entry in its identity table. -/
theorem resident_entry (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (resident : Resident state value) (entry : Interned NodeKey)
    (field : entryOf value = some entry) : state.nodes.table entry.key = some entry := by
  obtain ⟨actual, present, fields⟩ := coherent.nodes entry.key value (resident entry field)
  have same : actual = entry := Option.some.inj ((fields_entry _ _ _ fields).symm.trans field)
  simpa [same] using present

/-- Resident records with the same canonical node identity are equal as complete immutable records. -/
theorem resident_identity_unique (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (left right : Value Symbol Guard) (leftResident : Resident state left) (rightResident : Resident state right)
    (first second : Interned NodeKey) (leftField : entryOf left = some first) (rightField : entryOf right = some second)
    (same : first.identity = second.identity) : left = right := by
  have firstStored := resident_entry state coherent left leftResident first leftField
  have secondStored := resident_entry state coherent right rightResident second rightField
  have keys := (Cache.identity_eq_iff_key_eq state.nodes coherent.valid.2 firstStored secondStored).mp same
  have leftStored := leftResident first leftField
  have rightStored := rightResident second rightField
  rw [← keys] at rightStored
  exact Option.some.inj (leftStored.symm.trans rightStored)

/-- Source node-reference equality determines the complete record for all resident constructor kinds. -/
theorem resident_reference_injective (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (left right : Value Symbol Guard) (leftResident : Resident state left) (rightResident : Resident state right)
    (same : left.referenceOf = right.referenceOf) : left = right := by
  cases left <;> cases right <;>
    simp_all only [Value.referenceOf, reduceCtorEq, NodeRef.ref.injEq]
  all_goals
    apply resident_identity_unique state coherent _ _ leftResident rightResident _ _ rfl rfl
    simpa only [Value.referenceOf, NodeRef.node.injEq, NodeRef.union.injEq, NodeRef.mu.injEq] using same

/-- Every cached free interned reference came from an actual earlier identity reservation. -/
def IssuedReferences (state : Cache.State NodeKey) (value : Value Symbol Guard) : Prop :=
  ∀ identity, .interned identity ∈ value.free → ∃ key, state.issued identity = some key

/-- Source interning preserves every actual earlier reference reservation. -/
theorem intern_issued_extends (state : Cache.State NodeKey) (key : NodeKey) (valid : Cache.Valid state) :
    Extends state.issued (Cache.intern state key).2.issued := by
  cases found : state.table key with
  | some entry => simpa only [Cache.intern, found] using extends_refl state.issued
  | none => simpa only [Cache.intern, found, install] using Cache.reserve_extends state key valid

/-- Earlier reference provenance survives each concrete source interning operation. -/
theorem issued_after_intern (state : Cache.State NodeKey) (key : NodeKey) (valid : Cache.Valid state)
    (value : Value Symbol Guard) (issued : IssuedReferences state value) :
    IssuedReferences (Cache.intern state key).2 value := by
  intro identity member
  obtain ⟨oldKey, present⟩ := issued identity member
  exact ⟨oldKey, intern_issued_extends state key valid identity oldKey present⟩

/-- A valid reservation supply places every issued free name below its next fresh identity. -/
theorem issued_free_below (state : Cache.State NodeKey) (valid : Cache.Valid state)
    (value : Value Symbol Guard) (issued : IssuedReferences state value) (identity : Nat)
    (member : .interned identity ∈ value.free) : identity < state.next := by
  obtain ⟨key, present⟩ := issued identity member
  exact valid.1 identity key present

/-- The next identity is absent from every probe with actual earlier-reference provenance. -/
theorem next_absent (state : Cache.State NodeKey) (valid : Cache.Valid state)
    (value : Value Symbol Guard) (issued : IssuedReferences state value) : .interned state.next ∉ value.free := by
  intro member
  exact Nat.lt_irrefl _ (issued_free_below state valid value issued state.next member)

/-- On a genuine cache miss, source interning assigns exactly the previous next identity. -/
theorem intern_miss_identity (state : Cache.State NodeKey) (key : NodeKey) (missing : state.table key = none) :
    (Cache.intern state key).1.identity = state.next := by
  simp [Cache.intern, missing, install, reserve, keepFirst, put]

/-- A completed state cannot have an identity entry without its corresponding Mu payload. -/
theorem missing_record_is_fresh (state : InternedConstructorTemplates.State Symbol Guard) (complete : Covered [] state)
    (key : NodeKey) (missing : state.nodeRecords key = none) : state.nodes.table key = none := by
  cases found : state.nodes.table key with
  | none => rfl
  | some entry =>
      have present := complete.nodes key entry found
      simp only [List.not_mem_nil, false_or] at present
      obtain ⟨value, stored⟩ := present
      simp [missing] at stored

/-- Actual reservation makes its own recursive reference carry valid issued-name provenance. -/
theorem reserved_reference_issued (state : Cache.State NodeKey) (key : NodeKey) (valid : Cache.Valid state) :
    IssuedReferences (Symbol := Symbol) (Guard := Guard) (Cache.intern state key).2
      (.reference (.interned (Cache.intern state key).1.identity)) := by
  intro identity member
  have same : identity = (Cache.intern state key).1.identity := by simpa [Value.free] using member
  subst identity
  have correct := Cache.intern_correct state key valid
  exact ⟨key, (correct.1.2 key _ correct.2.1).2⟩

/-- Primitive depth and ordinary probes introduce no interned reference names. -/
theorem sentinel_references_issued (state : Cache.State NodeKey) (depth : Nat) :
    IssuedReferences (Symbol := Symbol) (Guard := Guard) state (.reference .depth) ∧
      IssuedReferences (Symbol := Symbol) (Guard := Guard) state (.reference (.uninterned depth)) := by
  constructor <;> intro identity impossible <;> simp [Value.free] at impossible

/-- Exact ordinary and union metadata retain only references issued by their actual children. -/
theorem child_free_issued (state : Cache.State NodeKey) (children : List (Value Symbol Guard))
    (issued : ∀ child ∈ children, IssuedReferences state child) (identity : Nat)
    (member : .interned identity ∈ childFree children) : ∃ key, state.issued identity = some key := by
  obtain ⟨child, present, free⟩ := (childFree_member children (.interned identity)).mp member
  exact issued child present identity free

/-- The source ordinary identification callback preserves actual child-reference provenance. -/
theorem identifyNode_issued (state : Cache.State NodeKey) (edges : List (EdgeValue Symbol Guard)) (entry : Interned NodeKey)
    (issued : ∀ child ∈ edges.flatMap EdgeValue.children, IssuedReferences state child) :
    IssuedReferences state (identifyNode edges entry) :=
  fun identity member => child_free_issued state _ issued identity member

/-- The source union identification callback preserves actual member-reference provenance. -/
theorem identifyUnion_issued (state : Cache.State NodeKey) (members : List (Value Symbol Guard)) (entry : Interned NodeKey)
    (issued : ∀ child ∈ members, IssuedReferences state child) :
    IssuedReferences state (.union entry members (maximumDepth members) (childFree members)) :=
  fun identity member => child_free_issued state _ issued identity member

/-- Mu metadata removes its own reference and introduces no new free reference. -/
theorem identifyMu_issued (state : Cache.State NodeKey) (entry : Interned NodeKey)
    (body depthShape ordinaryShape : Value Symbol Guard) (issued : IssuedReferences state body) :
    IssuedReferences state (.mu entry body depthShape ordinaryShape) := by
  intro identity member
  exact issued identity (List.mem_filter.mp member).1

/-- Binding the actual local reference removes the only newly introduced free name. -/
theorem identifyMu_removes_local (before : Cache.State NodeKey) (entry : Interned NodeKey)
    (body depthShape ordinaryShape : Value Symbol Guard)
    (bodyNames : ∀ identity, .interned identity ∈ body.free →
      identity = entry.identity ∨ ∃ key, before.issued identity = some key) :
    IssuedReferences before (.mu entry body depthShape ordinaryShape) := by
  intro identity member
  have free := (List.mem_filter.mp member).1
  have different : identity ≠ entry.identity := by
    simpa using (List.mem_filter.mp member).2
  exact (bodyNames identity free).resolve_left different

/-- A newly retained free reference separates a resident node from an earlier resident probe. -/
theorem retained_reference_separates (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (earlier later : Value Symbol Guard) (earlierResident : Resident state earlier) (laterResident : Resident state later)
    (reference : Reference) (absent : reference ∉ earlier.free) (present : reference ∈ later.free) :
    earlier.referenceOf ≠ later.referenceOf := by
  intro same
  have equal := resident_reference_injective state coherent earlier later earlierResident laterResident same
  exact absent (equal ▸ present)

/-- A fresh outer reference in either inner probe excludes the exact pending outer two-probe key. -/
theorem fresh_probe_key_separates (before after : InternedConstructorTemplates.State Symbol Guard)
    (coherentBefore : Coherent before) (coherentAfter : Coherent after) (growth : Grows before after)
    (outerDepth outerOrdinary innerDepth innerOrdinary : Value Symbol Guard)
    (outerDepthResident : Resident before outerDepth) (outerOrdinaryResident : Resident before outerOrdinary)
    (innerDepthResident : Resident after innerDepth) (innerOrdinaryResident : Resident after innerOrdinary)
    (depthIssued : IssuedReferences before.nodes outerDepth) (ordinaryIssued : IssuedReferences before.nodes outerOrdinary)
    (missing : before.nodes.table (muKey outerDepth outerOrdinary) = none)
    (retained :
      .interned (Cache.intern before.nodes (muKey outerDepth outerOrdinary)).1.identity ∈ innerDepth.free ∨
      .interned (Cache.intern before.nodes (muKey outerDepth outerOrdinary)).1.identity ∈ innerOrdinary.free) :
    muKey outerDepth outerOrdinary ≠ muKey innerDepth innerOrdinary := by
  rw [intern_miss_identity before.nodes _ missing] at retained
  intro same
  have keys : outerDepth.referenceOf = innerDepth.referenceOf ∧ outerOrdinary.referenceOf = innerOrdinary.referenceOf := by
    simpa [muKey, MuKey.mk.injEq] using same
  rcases retained with depthPresent | ordinaryPresent
  · exact retained_reference_separates after coherentAfter outerDepth innerDepth
      (resident_grows before after growth outerDepth outerDepthResident) innerDepthResident _
      (next_absent before.nodes coherentBefore.valid.2 outerDepth depthIssued) depthPresent keys.1
  · exact retained_reference_separates after coherentAfter outerOrdinary innerOrdinary
      (resident_grows before after growth outerOrdinary outerOrdinaryResident) innerOrdinaryResident _
      (next_absent before.nodes coherentBefore.valid.2 outerOrdinary ordinaryIssued) ordinaryPresent keys.2

/-- Empty-cache construction derives the older cache invariants and genuine freshness needed by the separation rule. -/
theorem constructed_pending_key_separates [DecidableEq (EdgeKey Symbol Guard)]
    (before after : InternedConstructorTemplates.State Symbol Guard) (built : Constructed before)
    (coherentAfter : Coherent after) (growth : Grows before after)
    (outerDepth outerOrdinary innerDepth innerOrdinary : Value Symbol Guard)
    (outerDepthResident : Resident before outerDepth) (outerOrdinaryResident : Resident before outerOrdinary)
    (innerDepthResident : Resident after innerDepth) (innerOrdinaryResident : Resident after innerOrdinary)
    (depthIssued : IssuedReferences before.nodes outerDepth) (ordinaryIssued : IssuedReferences before.nodes outerOrdinary)
    (missing : before.nodeRecords (muKey outerDepth outerOrdinary) = none)
    (retained :
      .interned (Cache.intern before.nodes (muKey outerDepth outerOrdinary)).1.identity ∈ innerDepth.free ∨
      .interned (Cache.intern before.nodes (muKey outerDepth outerOrdinary)).1.identity ∈ innerOrdinary.free) :
    muKey outerDepth outerOrdinary ≠ muKey innerDepth innerOrdinary := by
  have correct := constructed_correct built
  exact fresh_probe_key_separates before after correct.1 coherentAfter growth outerDepth outerOrdinary innerDepth innerOrdinary
    outerDepthResident outerOrdinaryResident innerDepthResident innerOrdinaryResident depthIssued ordinaryIssued
    (missing_record_is_fresh before correct.2 _ missing) retained

/-- Change only the outer binder's actual environment entry. -/
def outerBinding (environment : Reference → Option NodeRef) (outer : Reference) (value : NodeRef) : Reference → Option NodeRef :=
  fun name => if name = outer then some value else environment name

/-- The actual restricted source memo key ignores an outer variable absent from the original binder's free set. -/
theorem absent_outer_memo_key (binder : NodeRef) (free : List Reference)
    (environment : Reference → Option NodeRef) (outer : Reference) (absent : outer ∉ free) (first second : NodeRef) :
    memoKey binder free (outerBinding environment outer first) =
      memoKey binder free (outerBinding environment outer second) := by
  apply memoKey_congr
  intro name member
  have different : name ≠ outer := by intro same; subst name; exact absent member
  simp [outerBinding, different]

/-- A completed earlier memo request is reused when only an irrelevant outer reference changes. -/
theorem absent_outer_memo_replay (before after : Table MemoKey NodeRef) (binder : NodeRef) (free : List Reference)
    (environment : Reference → Option NodeRef) (outer : Reference) (absent : outer ∉ free)
    (first second original candidate : NodeRef)
    (growth : Extends (memoReadback before (memoKey binder free (outerBinding environment outer first)) original).2 after) :
    memoReadback after (memoKey binder free (outerBinding environment outer second)) candidate =
      ((memoReadback before (memoKey binder free (outerBinding environment outer first)) original).1, after) := by
  rw [← absent_outer_memo_key binder free environment outer absent first second]
  exact memoReadback_replay before after _ original candidate growth

/-- A source edge can contain an outer reference and another independently substituted child. -/
def beforeErasure : Template Nat Unit :=
  .node [.mk 0 () [.argument, .captured (.reference (.state 1))]]

/-- Replacing the other child with EmptyNode makes the source smart constructor discard the entire edge. -/
def afterErasure : Template Nat Unit :=
  .node [.mk 0 () [.argument, .captured .empty]]

/-- Absence after normalization does not imply absence from the original prepared source record. -/
theorem normalization_can_erase_outer_dependency :
    .state 0 ∈ (run (compile beforeErasure (.reference (.state 0))) empty).1.free ∧
      (run (compile afterErasure (.reference (.interned 0))) empty).1 = .empty := by
  cbv
  simp
  exact List.Mem.head _

end MicroCFTA.InternedFreshProbeKeys
