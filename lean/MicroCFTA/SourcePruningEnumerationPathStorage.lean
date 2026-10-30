import MicroCFTA.SourcePruningEnumerationPathTransport

/-!
# Path preservation for actual stored values

Value-list updates preserve the predicate on every pending bucket.
The native writes need no model, counter, or trie-validity premise.
-/
namespace MicroCFTA.SourcePruningEnumerationPathStorage
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationPathTransport

/-- A state with the same stored values has the same path property. -/
theorem values_paths {Symbol Guard : Type} {P : EqualityTrie.Path → Prop}
    {before after : EnumerationState.State Symbol Guard}
    (paths : StatePaths P before) (values : after.values = before.values) :
    StatePaths P after := by
  intro value member
  exact paths value (by simpa only [values] using member)

/-- A raw value-list update preserves paths when the new bucket does. -/
theorem values_set_paths {Symbol Guard : Type} {P : EqualityTrie.Path → Prop}
    {before after : EnumerationState.State Symbol Guard} (target : Nat)
    (value : UVarValue Symbol) (paths : StatePaths P before)
    (payload : BucketPaths P (references value))
    (values : after.values = before.values.set target value) :
    StatePaths P after := by
  intro stored member
  rw [values] at member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact paths stored old
  · simpa only [same] using payload

/-- An actual setValue step preserves the path predicate. -/
theorem setValue_paths {Symbol Guard : Type} {P : EqualityTrie.Path → Prop}
    (target : Nat) (value : UVarValue Symbol)
    (before after : EnumerationState.State Symbol Guard)
    (paths : StatePaths P before) (payload : BucketPaths P (references value))
    (success : Success (setValue target value) before () after) :
    StatePaths P after := by
  obtain rfl := (EnumerationDriver.modify_success _ before after).mp success
  exact values_set_paths target value paths payload rfl

/-- An actual representative lookup changes no stored bucket. -/
theorem representative_paths {Symbol Guard : Type} {P : EqualityTrie.Path → Prop}
    (fuel uv root : Nat) (before after : EnumerationState.State Symbol Guard)
    (paths : StatePaths P before)
    (success : Success (representative fuel uv) before root after) :
    StatePaths P after := by
  obtain ⟨_found, _, _, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact paths

/-- An actual representative union changes no stored bucket. -/
theorem unionVariables_paths {Symbol Guard : Type} {P : EqualityTrie.Path → Prop}
    (fuel left right : Nat) (before after : EnumerationState.State Symbol Guard)
    (paths : StatePaths P before)
    (success : Success (unionVariables fuel left right) before () after) :
    StatePaths P after := by
  obtain ⟨_forest, _, rfl⟩ := (unionVariables_success fuel left right before after).mp success
  exact paths

local notation "Symbol" => SourcePruningTemplates.Symbol

/-- An actual native index write installs only its supplied value. -/
theorem native_write_paths {EnumGuard NativeGuard : Type}
    {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (paths : StatePaths P before.core) (payload : BucketPaths P (references value))
    (observed : SourcePruningEnumerationNativeIndex.write heap fuel target value gained lost before =
      some after) : StatePaths P after.core := by
  simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff,
    Option.some.injEq] at observed
  obtain ⟨flag, _classified, removed, _removed, saved, _saved, same⟩ := observed
  have values : after.core.values = before.core.values.set target value :=
    (congrArg
      (fun result : EnumerationExpandableIndex.Cached Symbol EnumGuard => result.core.values) same).symm
  exact values_set_paths target value paths payload values

/-- Reading the old slot before an actual native write adds no paths. -/
theorem writeSlot_paths {EnumGuard NativeGuard : Type}
    {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel target : Nat) (value : UVarValue Symbol)
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (paths : StatePaths P before.core) (payload : BucketPaths P (references value))
    (observed : SourcePruningEnumerationCachedChild.writeSlot heap fuel target value before =
      some after) : StatePaths P after.core := by
  unfold SourcePruningEnumerationCachedChild.writeSlot at observed
  obtain ⟨old, _stored, written⟩ := Option.bind_eq_some_iff.mp observed
  exact native_write_paths heap fuel target value (references value) (references old)
    before after paths payload written

/-- An actual ordinary child installs the supplied bucket unchanged. -/
theorem prepareOrdinary_paths {EnumGuard NativeGuard : Type}
    {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (scs : List Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (fragment : Fragments.Fragment Symbol)
    (after : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs)
    (observed : SourcePruningEnumerationCachedChild.prepareOrdinary heap fuel scs value before =
      some (fragment, after)) : StatePaths P after.core := by
  cases value with
  | empty => cases observed
  | reference name => cases observed
  | union entry members depth free => cases observed
  | mu entry body depth ordinary => cases observed
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [SourcePruningEnumerationCachedChild.prepareOrdinary, terminal] at observed
      · simp only [SourcePruningEnumerationCachedChild.prepareOrdinary, ite_eq_right terminal] at observed
        obtain ⟨handle, _encoded, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨allocation, allocated, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨written, writeRun, same⟩ := Option.map_eq_some_iff.mp observed
        have allocationPaths := cached_allocate_paths heap (some handle) before paths allocated
        have writtenPaths := writeSlot_paths heap fuel allocation.1
          (.unenumerated (some handle) scs) allocation.2 written allocationPaths inputs writeRun
        have cacheSame : written = after := congrArg Prod.snd same
        rw [← cacheSame]
        exact writtenPaths

/-- Every actual cached child row preserves the supplied path predicate. -/
theorem prepareChild_paths {EnumGuard NativeGuard : Type}
    {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel : Nat) (scs : List Suspended)
    (value : InternedConstructorTemplates.Value Symbol NativeGuard)
    (before : EnumerationExpandableIndex.Cached Symbol EnumGuard)
    (paths : StatePaths P before.core) (inputs : BucketPaths P scs)
    {rows : List (Fragments.Fragment Symbol × EnumerationExpandableIndex.Cached Symbol EnumGuard)}
    (observed : SourcePruningEnumerationCachedPrepare.prepareChild heap fuel scs value before =
      some rows) : ∀ row ∈ rows, StatePaths P row.2.core := by
  cases value with
  | empty =>
      have same : [] = rows := Option.some.inj observed
      rw [← same]
      intro row member
      cases member
  | reference name => cases observed
  | node entry edges depth free =>
      simp only [SourcePruningEnumerationCachedPrepare.prepareChild] at observed
      obtain ⟨result, prepared, same⟩ := Option.map_eq_some_iff.mp observed
      intro row member
      rw [← same] at member
      have rowSame := List.mem_singleton.mp member
      cases rowSame
      exact prepareOrdinary_paths heap fuel scs (.node entry edges depth free) before
        result.1 result.2 paths inputs prepared
  | union entry members depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [SourcePruningEnumerationCachedPrepare.prepareChild, terminal] at observed
      · simp only [SourcePruningEnumerationCachedPrepare.prepareChild, ite_eq_right terminal] at observed
        obtain ⟨handle, _encoded, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨allocation, allocated, same⟩ := Option.map_eq_some_iff.mp observed
        intro row member
        rw [← same] at member
        have rowSame := List.mem_singleton.mp member
        cases rowSame
        exact cached_allocate_paths heap (some handle) before paths allocated
  | mu entry body depth ordinary =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp [SourcePruningEnumerationCachedPrepare.prepareChild, terminal] at observed
      · simp only [SourcePruningEnumerationCachedPrepare.prepareChild, ite_eq_right terminal] at observed
        obtain ⟨handle, _encoded, observed⟩ := Option.bind_eq_some_iff.mp observed
        obtain ⟨allocation, allocated, same⟩ := Option.map_eq_some_iff.mp observed
        intro row member
        rw [← same] at member
        have rowSame := List.mem_singleton.mp member
        cases rowSame
        exact cached_allocate_paths heap (some handle) before paths allocated

end MicroCFTA.SourcePruningEnumerationPathStorage
