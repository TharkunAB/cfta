import MicroCFTA.SourceCurrentAllocatedNativeContextCache
open MicroCFTA
open Language BinderLanguage InternedConstructorTemplates InternedBinderProtocol
open SourceRecursiveIntersectionThunks SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativePairContexts
#print axioms initial_contextual
#print axioms advance_contextual
#print axioms lookupNode_contextual
#print axioms lookupEdge_contextual
#print axioms demandNode_contextual
#print axioms demandEdge_contextual
#print axioms finishNode_contextual
#print axioms finishEdge_contextual
#print axioms node_ready_contextual
#print axioms edge_ready_contextual
#print axioms node_observed_ready
#print axioms edge_observed_ready
#check NodeLaw.sound
#check NodeLaw.complete
#check EdgeLaw.sound
#check EdgeLaw.complete
#check Contextual
#check node_observed_ready
#check edge_observed_ready
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

-- The open repeated-reference law follows from the current pair context.
example (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (seen : (0, 1) ∈ domain.key.seen) :
    NodeLaw view model ranked holds ⟨domain, .reference (.interned 0), .reference (.interned 1)⟩
      (.reference (.intersection 0 1)) := by
  constructor
  · intro _ output sound term accepted
    apply sound (0, 1) seen term
    simpa only [InternedGuardedLanguage.meaning] using accepted
  · intro _ bound output complete first second bounded term left right
    simpa only [InternedGuardedLanguage.meaning] using
      complete (0, 1) seen term ⟨first, second, bounded, left, right⟩

-- The sum bound includes the sum of the two actual ranks.
example (ranks : Nat → Nat → Lang Symbol) (key : Nat × Nat) (first second : Nat) (term : Term Symbol)
    (left : ranks key.1 first term) (right : ranks key.2 second term) :
    RankedPair ranks (first + second) key term := ⟨first, second, Nat.le_refl _, left, right⟩

private def suspended : FlatMemoThunk.State Nat Nat Nat :=
  (FlatMemoThunk.lookupOrInsert 7 10 FlatMemoThunk.empty).2
private def running : FlatMemoThunk.State Nat Nat Nat := (FlatMemoThunk.demand 0 suspended).2
private def completed : FlatMemoThunk.State Nat Nat Nat := FlatMemoThunk.finish 0 20 running
example : suspended.cells 0 = some ⟨10, .suspended⟩ := by cbv
example : (FlatMemoThunk.demand 0 suspended).1 = .evaluate 10 := by cbv
example : running.cells 0 = some ⟨10, .evaluating⟩ := by cbv
example : completed.cells 0 = some ⟨10, .returned 20⟩ := by cbv
example : FlatMemoThunk.lookupOrInsert 7 99 completed = (0, completed) := by cbv
example : FlatMemoThunk.demand 0 completed = (.ready 20, completed) := by cbv
example : FlatMemoThunk.finish 0 30 completed = completed := by cbv
example : completed.table 7 = some 0 ∧ completed.next = 1 := by constructor <;> cbv
example : (FlatMemoThunk.demand 0 running).1 = .busy := by cbv
example : FlatMemoThunk.finish 0 20 suspended = suspended := by cbv
