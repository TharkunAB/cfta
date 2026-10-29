import MicroCFTA.SourcePruningEnumerationCachedOwn
import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission

/-!
# Model-free transport of stored paths

The predicate applies to every represented path in a pending bucket.
Child descent needs only closure under deletion of a leading index.
The statements do not require a satisfying term or trie validity.
-/
namespace MicroCFTA.SourcePruningEnumerationPathTransport
open EnumerationState EnumerationSchedule

/-- Every represented path in the bucket satisfies the predicate. -/
def BucketPaths (P : EqualityTrie.Path → Prop) (scs : List Suspended) : Prop :=
  ∀ sc ∈ scs, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, P path

/-- Every stored pending bucket satisfies the path predicate. -/
def StatePaths {Symbol Guard : Type} (P : EqualityTrie.Path → Prop)
    (state : EnumerationState.State Symbol Guard) : Prop :=
  ∀ value ∈ state.values, BucketPaths P (references value)

/-- Each actual guard projection satisfies the path predicate. -/
def ProjectionPaths
    (guards : List (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (P : EqualityTrie.Path → Prop) : Prop :=
  ∀ guard ∈ guards, ∀ tries residual,
    SourcePruningEnumerationConstraint.project guard = some (tries, residual) →
    ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path

/-- A represented child path comes from its indexed parent path. -/
theorem descended_path_original (trie : EqualityTrie.Trie)
    (index : Nat) (suffix : EqualityTrie.Path)
    (member : suffix ∈ EqualityTrie.fromPathTrie (EqualityTrie.pathTrieDescend trie index)) :
    index :: suffix ∈ EqualityTrie.fromPathTrie trie := by
  cases trie with
  | empty | terminal =>
      simp [EqualityTrie.pathTrieDescend, EqualityTrie.fromPathTrie] at member
  | branch children =>
      cases found : EqualityTrie.lookup index children with
      | none =>
          simp [EqualityTrie.pathTrieDescend, found, EqualityTrie.fromPathTrie] at member
      | some child =>
          have present : suffix ∈ EqualityTrie.fromPathTrie child := by
            simpa [EqualityTrie.pathTrieDescend, found] using member
          exact (EqualityTrie.mem_fromChildren children _).mpr
            ⟨index, child, suffix, EqualityTrie.lookup_mem _ _ _ found, present, rfl⟩

/-- Appending two buckets preserves their common path predicate. -/
theorem BucketPaths.append {P : EqualityTrie.Path → Prop} {first second : List Suspended}
    (left : BucketPaths P first) (right : BucketPaths P second) :
    BucketPaths P (first ++ second) := by
  intro sc member
  rcases List.mem_append.mp member with old | added
  · exact left sc old
  · exact right sc added

/-- Every retained child bucket satisfies the tail-closed path predicate. -/
theorem BucketPaths.descend {P : EqualityTrie.Path → Prop} {scs : List Suspended}
    (paths : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix) (index : Nat) :
    BucketPaths P (descendScs index scs) := by
  intro sc member suffix represented
  change sc ∈ EqualityTrie.descendScs index scs at member
  unfold EqualityTrie.descendScs at member
  obtain ⟨mapped, _⟩ := List.mem_filter.mp member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
  exact tails index suffix (paths original originalMember (index :: suffix)
    (descended_path_original original.trie index suffix represented))

/-- A fresh empty pending bucket adds no represented path. -/
theorem StatePaths.allocated {Symbol Guard : Type} {P : EqualityTrie.Path → Prop}
    {before : EnumerationState.State Symbol Guard}
    (paths : StatePaths P before) (node : Option Nat) :
    StatePaths P (EnumerationState.allocated node before) := by
  intro value member
  change value ∈ before.values ++ [UVarValue.unenumerated node []] at member
  rcases List.mem_append.mp member with retained | fresh
  · exact paths value retained
  · have same := List.mem_singleton.mp fresh
    subst value
    simp [BucketPaths, references]

local notation "SourceSymbol" => SourcePruningTemplates.Symbol
local notation "SourceConstraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- An actual native allocation adds only an empty pending bucket. -/
theorem cached_allocate_paths {EnumGuard NativeGuard : Type}
    {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State SourceSymbol NativeGuard)
    (node : Option Nat)
    (before : EnumerationExpandableIndex.Cached SourceSymbol EnumGuard)
    {allocation : Nat × EnumerationExpandableIndex.Cached SourceSymbol EnumGuard}
    (paths : StatePaths P before.core)
    (observed : SourcePruningEnumerationCachedChild.allocate heap node before = some allocation) :
    StatePaths P allocation.2.core := by
  unfold SourcePruningEnumerationCachedChild.allocate at observed
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp observed
  have coreSame := congrArg
    (fun result : Nat × EnumerationExpandableIndex.Cached SourceSymbol EnumGuard => result.2.core) same
  change EnumerationState.allocated node before.core = allocation.2.core at coreSame
  rw [← coreSame]
  exact paths.allocated node

/-- Own allocation preserves stored paths and the input trie-path predicate. -/
theorem suspendMany_paths {EnumGuard NativeGuard : Type}
    {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State SourceSymbol NativeGuard)
    (tries : List EqualityTrie.Trie)
    (before : EnumerationExpandableIndex.Cached SourceSymbol EnumGuard)
    (suspended : List Suspended)
    (after : EnumerationExpandableIndex.Cached SourceSymbol EnumGuard)
    (triePaths : ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path)
    (paths : StatePaths P before.core)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries before =
      some (suspended, after)) :
    BucketPaths P suspended ∧ StatePaths P after.core := by
  induction tries generalizing before suspended after with
  | nil =>
      have same : ([], before) = (suspended, after) := Option.some.inj observed
      have bucketSame : [] = suspended := congrArg Prod.fst same
      have cacheSame : before = after := congrArg Prod.snd same
      refine ⟨?_, ?_⟩
      · rw [← bucketSame]
        simp [BucketPaths]
      · rw [← cacheSame]
        exact paths
  | cons trie rest ih =>
      simp only [SourcePruningEnumerationCachedOwn.suspendMany,
        Option.bind_eq_some_iff, Option.map_eq_some_iff] at observed
      obtain ⟨allocation, allocated, result, continued, same⟩ := observed
      have allocatedPaths := cached_allocate_paths heap none before paths allocated
      have restPaths : ∀ other ∈ rest,
          ∀ path ∈ EqualityTrie.fromPathTrie other, P path := by
        intro other member
        exact triePaths other (List.mem_cons_of_mem _ member)
      have tailResult := ih (before := allocation.2) (suspended := result.1)
        (after := result.2) restPaths allocatedPaths continued
      have bucketSame : ⟨trie, allocation.1⟩ :: result.1 = suspended := congrArg Prod.fst same
      have cacheSame : result.2 = after := congrArg Prod.snd same
      refine ⟨?_, ?_⟩
      · rw [← bucketSame]
        intro sc member path represented
        rcases List.mem_cons.mp member with first | later
        · subst sc
          exact triePaths trie List.mem_cons_self path represented
        · exact tailResult.1 sc later path represented
      · rw [← cacheSame]
        exact tailResult.2

/-- Every actual own row and staged child bucket preserves the path predicate. -/
theorem prepare_paths {P : EqualityTrie.Path → Prop}
    {heap : InternedConstructorTemplates.State SourceSymbol SourceConstraint}
    {scs : List Suspended}
    {edge : InternedConstructorTemplates.EdgeValue SourceSymbol SourceConstraint}
    {before : EnumerationExpandableIndex.Cached SourceSymbol SourceConstraint}
    (original : StatePaths P before.core) (inherited : BucketPaths P scs)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projectedPaths : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ trie ∈ tries, ∀ path ∈ EqualityTrie.fromPathTrie trie, P path)
    {rows : List _}
    (observed : SourcePruningEnumerationCachedOwn.prepare heap scs edge before = some rows) :
    ∀ row ∈ rows,
      StatePaths P row.2.core ∧ ∀ child ∈ row.1.2.1, BucketPaths P child.2.1 := by
  unfold SourcePruningEnumerationCachedOwn.prepare at observed
  split at observed
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        simp only [projected] at observed
        cases observed
    | some projection =>
        obtain ⟨tries, residual⟩ := projection
        simp only [projected] at observed
        obtain ⟨result, suspended, same⟩ := Option.map_eq_some_iff.mp observed
        have ownPaths := suspendMany_paths heap tries before result.1 result.2
          (projectedPaths tries residual projected) original suspended
        intro row member
        rw [← same] at member
        have rowSame := List.mem_singleton.mp member
        cases rowSame
        refine ⟨ownPaths.2, ?_⟩
        intro child member
        obtain ⟨indexed, _chosen, childSame⟩ := List.mem_map.mp member
        cases childSame
        exact (inherited.descend tails indexed.2).append (ownPaths.1.descend tails indexed.2)
  · have rowsSame : [] = rows := Option.some.inj observed
    rw [← rowsSame]
    intro row member
    cases member

end MicroCFTA.SourcePruningEnumerationPathTransport

namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState InternedConstructorTemplates SourcePruningEnumerationPathTransport
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {Typing : Type} {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Current head admission supplies paths for every actual own row and staged child. -/
theorem HeadAdmission.prepare_paths_of_forecast
    {seed : Seed}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing} {before : Cached}
    {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {storedEdges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    (admission : HeadAdmission seed formulas solver inventory caller memos metadata
      before uv handle scs parentEntry storedEdges depth free edge)
    (guards : List Constraint) (P : EqualityTrie.Path → Prop)
    (included : seed.1 ⊆ guards) (projected : ProjectionPaths guards P)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (original : StatePaths P before.core)
    {rows : List _}
    (observed : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before = some rows) :
    ∀ row ∈ rows,
      StatePaths P row.2.core ∧ ∀ child ∈ row.1.2.1, BucketPaths P child.2.1 := by
  have inherited : BucketPaths P scs :=
    original (.unenumerated (some handle) scs) (List.mem_of_getElem? admission.stored)
  have resident : InternedEdgeResidency.EdgeResident caller.checked.native.machine.heap edge :=
    InternedEdgeResidency.resident_edges caller.checked.native.machine.heap
      admission.packet.context.ready.semantic.ready.semantic.1.normal.facts.linked
      _ admission.parentAvailable.resident edge admission.selected
  have guardIncluded : edge.entry.key.constraint ∈ guards :=
    included (admission.known edge.entry.key edge resident)
  apply prepare_paths original inherited tails ?_ observed
  intro tries residual projection
  exact projected edge.entry.key.constraint guardIncluded tries residual projection

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
