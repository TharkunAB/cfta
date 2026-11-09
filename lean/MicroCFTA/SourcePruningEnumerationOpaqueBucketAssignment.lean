import MicroCFTA.SourcePruningEnumerationRetentionBoundary
import MicroCFTA.SourcePruningEnumerationShallowChildLanguage

/-!
# An assignment admitted after opaque bucket removal

The initial state has two independent unrestricted slots.
The actual opaque preparation allocates a third slot without its supplied bucket.
A nullary assignment satisfies that state and fails the supplied descendant path.
This result does not establish source reachability or a complete caller context.
-/
namespace MicroCFTA.SourcePruningEnumerationOpaqueBucketAssignment
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSemantics
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationNativeLanguage
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Two unrestricted slots start in different singleton classes. -/
def before : EnumerationState.State Symbol EnumGuard :=
  ⟨2, UnionFind.withInitialValues [0, 1],
    [.unenumerated none [], .unenumerated none []], [], fun _ => [], []⟩

/-- This bucket requires the existing variable at the first descendant. -/
abbrev bucket : List Suspended := SourcePruningEnumerationRetentionBoundary.bucket

/-- The fresh child is nullary. The two older slots retain separate assignments. -/
def assignment (captured anchor : Term Symbol) (symbol : Symbol) : Nat → Term Symbol :=
  fun uv => if uv = 0 then captured else if uv = 1 then anchor else .node symbol []

/-- Only union and recursive values use the opaque allocation branch. -/
def Opaque (value : Value Symbol NativeGuard) : Prop :=
  match value with
  | .union _ _ _ _ | .mu _ _ _ _ => True
  | _ => False

/-- The two allocated variables are independent and the supply is aligned. -/
theorem before_independent :
    (before : EnumerationState.State Symbol EnumGuard).counter = 2 ∧
      (before : EnumerationState.State Symbol EnumGuard).values.length = 2 ∧
      ¬UnionFind.SameClass (before : EnumerationState.State Symbol EnumGuard).representatives 0 1 := by
  simp [before, UnionFind.initial_classes]

/-- The supplied descendant obligation is valid, nonterminal, and names an old slot. -/
theorem bucket_valid :
    ValidSuspended bucket ∧
      bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
      ∀ sc ∈ bucket, sc.var < 2 := by
  simp [bucket, SourcePruningEnumerationRetentionBoundary.bucket, ValidSuspended,
    EqualityTrie.Valid, EqualityTrie.isTerminal]

/-- A nullary term cannot satisfy the supplied descendant obligation. -/
theorem bucket_rejects (assigned : Nat → Term Symbol) (symbol : Symbol) :
    ¬(∀ sc ∈ bucket, Suspended.Holds assigned (.node symbol []) sc) := by
  simp [bucket, SourcePruningEnumerationRetentionBoundary.bucket, Suspended.Holds,
    EqualityTrie.fromPathTrie, EqualityTrie.fromChildren, Term.atPath]

/-- The two pure slots and empty residual list admit every assignment. -/
theorem before_satisfies (language : NodeLanguage Symbol)
    (meaning : EnumGuard → Term Symbol → Prop) (assigned : Nat → Term Symbol) :
    Satisfies language meaning assigned before := by
  refine ⟨⟨UnionFind.initial_satisfies [0, 1] assigned, ?_⟩, ?_⟩
  · intro uv
    cases uv with
    | zero => simp [before, heap, slot, slotSatisfies, permits]
    | succ uv =>
        cases uv with
        | zero => simp [before, heap, slot, slotSatisfies, permits]
        | succ uv => simp [before, heap, slot, slotSatisfies]
  · simp [before, guardsHold]

/-- Actual opaque allocation admits an assignment that its supplied valid bucket excludes. -/
theorem countermodel
    (native : InternedConstructorTemplates.State Symbol NativeGuard)
    (value : Value Symbol NativeGuard)
    (coherent : InternedRecordCoherence.Coherent native)
    (available : Available native value) (closed : value.free = []) (isOpaque : Opaque value)
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol)
    (accepted : InternedGuardedLanguage.meaning holds ambient value (.node symbol []))
    (meaning : EnumGuard → Term Symbol → Prop) (captured anchor : Term Symbol) :
    ∃ (handle : Nat) (action : EnumerateM Symbol EnumGuard (Fragment Symbol))
      (after : EnumerationState.State Symbol EnumGuard),
      encodeNode value = some handle ∧ lookupNode native handle = some value ∧
      SourcePruningEnumerationShallowChild.prepareChild bucket value = some action ∧
      ExceptT.run (action before) = [.ok (.hole 2, after)] ∧
      Success action before (.hole 2) after ∧
      after = allocated (some handle) before ∧
      after.values[2]? = some (.unenumerated (some handle) []) ∧
      after.counter = 3 ∧ after.values.length = 3 ∧
      Satisfies (handles holds ambient native) meaning (assignment captured anchor symbol) before ∧
      Satisfies (handles holds ambient native) meaning (assignment captured anchor symbol) after ∧
      ¬(∀ sc ∈ bucket, Suspended.Holds (assignment captured anchor symbol)
        ((assignment captured anchor symbol) 2) sc) ∧
      ¬Satisfies (handles holds ambient native) meaning (assignment captured anchor symbol)
        {after with values := after.values.set 2 (.unenumerated (some handle) bucket)} := by
  obtain ⟨handle, encoded, decoded⟩ := available_readback native value coherent available closed
  let action : EnumerateM Symbol EnumGuard (Fragment Symbol) :=
    allocate (some handle) >>= fun uv => pure (.hole uv)
  let after : EnumerationState.State Symbol EnumGuard := allocated (some handle) before
  have nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := rfl
  have prepared : SourcePruningEnumerationShallowChild.prepareChild bucket value = some action := by
    cases value with
    | empty | reference | node => exact False.elim isOpaque
    | union | mu =>
        simp [SourcePruningEnumerationShallowChild.prepareChild, nonterminal, encoded, action]
  have observed : ExceptT.run (action before) = [.ok (.hole 2, after)] := by
    change ExceptT.run (((allocate (some handle) >>= fun uv => pure (Fragment.hole uv)) :
      EnumerateM Symbol EnumGuard (Fragment Symbol)) before) = _
    rw [bind_single _ _ _ _ _ (allocate_exact (some handle) before)]
    rfl
  have successful : Success action before (.hole 2) after := by
    simp only [Success, observed, List.mem_singleton]
  have initial := before_satisfies (handles holds ambient native) meaning
    (assignment captured anchor symbol)
  have admitted : Satisfies (handles holds ambient native) meaning
      (assignment captured anchor symbol) after := by
    apply (allocation_semantics (handles holds ambient native) meaning
      (assignment captured anchor symbol) (some handle) before rfl).mpr
    refine ⟨initial, ?_⟩
    change handles holds ambient native handle (.node symbol [])
    exact (handles_lookup holds ambient native handle value (.node symbol []) decoded).mpr accepted
  have rejected : ¬(∀ sc ∈ bucket, Suspended.Holds (assignment captured anchor symbol)
      ((assignment captured anchor symbol) 2) sc) :=
    bucket_rejects (assignment captured anchor symbol) symbol
  have retained : ¬Satisfies (handles holds ambient native) meaning
      (assignment captured anchor symbol)
      {after with values := after.values.set 2 (.unenumerated (some handle) bucket)} := by
    intro satisfied
    have obligations := (SourcePruningEnumerationShallowChild.allocation_bucket_semantics
      (handles holds ambient native) meaning (assignment captured anchor symbol)
      before handle bucket rfl).mp satisfied
    exact rejected obligations.2.2
  exact ⟨handle, action, after, encoded, decoded, prepared, observed, successful, rfl,
    allocated_slot (some handle) before rfl, rfl, rfl, initial, admitted, rejected, retained⟩

end MicroCFTA.SourcePruningEnumerationOpaqueBucketAssignment
