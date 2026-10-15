import MicroCFTA.SourceEqualityInheritedChildren
import MicroCFTA.EqualityLeafProjectionSetChildren

/-!
# Scoped language laws for indexed inherited child traversal

The induction uses one local recursive node law at each actual callback.
Every later child uses the returned warm cache and both constructor histories.
Parent constraints supply the actual descended obligation at each child index.
The outer caller must derive this local callback law; it is explicit here.
-/
namespace MicroCFTA.SourceEqualityInheritedChildrenProofs
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityClassFoldGraph
open SourceEqualityAnnotationHeap (Heap)
open SourceEqualityInheritedChildren

/-- The recursive induction hypothesis concerns one actual successful node call and its physical scope. -/
def Callback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (meaning : Value Symbol Guard → Term Symbol → Prop)
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation) : Prop :=
  ∀ inherited value before, IdleReady emptyGuard conjoin before → Available before.machine.heap value → value.free = [] →
    Heap annotation before.machine.heap → ∀ result after, call inherited value before = .done (.ok result) after →
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Available after.machine.heap result ∧ result.free = [] ∧
        Heap annotation after.machine.heap ∧ ∀ term,
          (meaning result term → meaning value term) ∧
          (SourceEqualityPrecheck.Sat term inherited → (meaning result term ↔ meaning value term))

/-- Every complete indexed traversal derives actual output scope and each pointwise forest language law. -/
theorem walk_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (meaning : Value Symbol Guard → Term Symbol → Prop)
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation)
    (callback : Callback annotation emptyGuard conjoin meaning call)
    {payload index values before results after} (trace : Walk call payload index values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      Heap annotation after.machine.heap ∧ ∀ terms,
        (All₂ meaning results terms → All₂ meaning values terms) ∧
        ((∀ offset term, terms[offset]? = some term → SourceEqualityPrecheck.Sat term (SourceEqualityDescend.descend payload (index + offset))) →
          (All₂ meaning results terms ↔ All₂ meaning values terms)) := by
  induction trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, by simp [Values], by simp [ClosedValues], heap, fun _ => ⟨id, fun _ => Iff.rfl⟩⟩
  | @cons index value before result middle values results after first rest ih =>
      have head := callback _ value before ready (available _ List.mem_cons_self) (closed _ List.mem_cons_self) heap result middle first
      have tail := ih head.1 (fun child member => head.2.1.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member)) head.2.2.2.2.1
      refine ⟨tail.1, head.2.1.trans tail.2.1, ?_, ?_, tail.2.2.2.2.1, ?_⟩
      · intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact tail.2.1.available _ head.2.2.1
        · exact tail.2.2.1 child member
      · intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact head.2.2.2.1
        · exact tail.2.2.2.1 child member
      · intro terms
        cases terms with
        | nil =>
            constructor
            · intro accepted; cases accepted
            · intro _; constructor <;> intro accepted <;> cases accepted
        | cons term terms =>
            have firstLaw := head.2.2.2.2.2 term
            have restLaw := tail.2.2.2.2.2 terms
            constructor
            · intro accepted
              cases accepted with
              | cons first rest => exact .cons (firstLaw.1 first) (restLaw.1 rest)
            · intro satisfied
              have firstSat : SourceEqualityPrecheck.Sat term (SourceEqualityDescend.descend payload index) := by simpa using satisfied 0 term (by simp)
              have restSat : ∀ offset child, terms[offset]? = some child →
                  SourceEqualityPrecheck.Sat child (SourceEqualityDescend.descend payload (index + 1 + offset)) := by
                intro offset child found
                have selected := satisfied (offset + 1) child (by simpa using found)
                simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using selected
              constructor
              · intro accepted
                cases accepted with
                | cons first rest => exact .cons ((firstLaw.2 firstSat).mp first) ((restLaw.2 restSat).mp rest)
              · intro accepted
                cases accepted with
                | cons first rest => exact .cons ((firstLaw.2 firstSat).mpr first) ((restLaw.2 restSat).mpr rest)

/-- A satisfied parent physical payload supplies every actual zero-based child obligation. -/
theorem parent_obligations (payload : SourceEqualityPrecheck.Constraint) (wellFormed : SourceEqualityDescend.WellFormed payload)
    (symbol : Symbol) (terms : List (Term Symbol)) (satisfied : SourceEqualityPrecheck.Sat (.node symbol terms) payload) :
    ∀ index term, terms[index]? = some term → SourceEqualityPrecheck.Sat term (SourceEqualityDescend.descend payload (0 + index)) := by
  intro index term found
  simpa only [Nat.zero_add] using SourceEqualityDescend.descend_sound payload wellFormed symbol terms index term found satisfied

/-- Literal complete live child traversal preserves the forest under its actual parent equalities. -/
theorem live_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (meaning : Value Symbol Guard → Term Symbol → Prop)
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation)
    (callback : Callback annotation emptyGuard conjoin meaning call)
    {payload values before results after} (trace : Walk call payload 0 values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) (wellFormed : SourceEqualityDescend.WellFormed payload)
    (symbol : Symbol) (terms : List (Term Symbol)) (satisfied : SourceEqualityPrecheck.Sat (.node symbol terms) payload) :
    All₂ meaning results terms ↔ All₂ meaning values terms :=
  (walk_verified annotation emptyGuard conjoin meaning call callback trace ready available closed heap).2.2.2.2.2 terms |>.2
    (parent_obligations payload wellFormed symbol terms satisfied)

/-- Every completed source child graph derives scopes and exact forest meaning under its parent equalities. -/
theorem graph_verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → Result width Symbol Guard (Value Symbol Guard) Observation)
    (callback : Callback annotation emptyGuard conjoin (InternedGuardedLanguage.meaning holds ambient) call)
    {payload values before results after} (trace : Graph call payload values before results after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values) (closed : ClosedValues values)
    (heap : Heap annotation before.machine.heap) (wellFormed : SourceEqualityDescend.WellFormed payload) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧ Values after.machine.heap results ∧ ClosedValues results ∧
      Heap annotation after.machine.heap ∧ ∀ symbol terms,
        (All₂ (InternedGuardedLanguage.meaning holds ambient) results terms → All₂ (InternedGuardedLanguage.meaning holds ambient) values terms) ∧
        (SourceEqualityPrecheck.Sat (.node symbol terms) payload →
          (All₂ (InternedGuardedLanguage.meaning holds ambient) results terms ↔ All₂ (InternedGuardedLanguage.meaning holds ambient) values terms)) := by
  cases trace with
  | contradiction =>
      have scope := SourceEqualityEmptyPropagation.erased_scope before.machine.heap values
      refine ⟨ready, pure_keeps _ ready.semantic.ready, scope.1, scope.2, heap, ?_⟩
      intro symbol terms
      constructor
      · intro accepted
        cases values with
        | nil => exact accepted
        | cons value values =>
            cases accepted with
            | cons first _ => simp only [InternedGuardedLanguage.meaning] at first
      · intro impossible; exact False.elim impossible
  | live actual =>
      have checked := walk_verified annotation emptyGuard conjoin (InternedGuardedLanguage.meaning holds ambient) call callback actual ready available closed heap
      refine ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.1, ?_⟩
      intro symbol terms
      exact ⟨(checked.2.2.2.2.2 terms).1, fun satisfied =>
        (checked.2.2.2.2.2 terms).2 (parent_obligations _ wellFormed symbol terms satisfied)⟩

/-- Actual source child traversal always takes setChildren's equal-arity direct interning branch. -/
theorem setChildren [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (checked : Symbol → List (Value Symbol Guard) → Guard → Work Symbol Guard (EdgeValue Symbol Guard))
    {call payload edge before results after}
    (trace : Graph (Observation := Observation) (width := width) call payload (edge : EdgeValue Symbol Guard).children before results after) :
    EqualityLeafProjectionSetChildren.setChildren checked edge results = makeEdge edge.entry.key.symbol edge.entry.key.constraint results :=
  EqualityLeafProjectionSetChildren.same_arity checked edge results trace.length

end MicroCFTA.SourceEqualityInheritedChildrenProofs
