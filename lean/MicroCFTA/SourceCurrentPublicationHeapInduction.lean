import MicroCFTA.SourceCurrentNativeMuIssuedHistory

/-!
# Recursive payload invariants through causal publication histories

The payload predicate has no state parameter. Earlier payloads retain the
predicate through ordinary effects and reservation. Each publication must
prove the predicate for its own exact candidate after its callback paths.
This module supplies induction, not the missing semantic publication law.
-/
namespace MicroCFTA.SourceCurrentPublicationHeapInduction
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedBinderProtocol (NodeKey)
open InternedShallowHeap (NoNewMu)
open InternedNestedConstruction (Syntax Outcome)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentConstrainedCapSourceHistory (Context)

/-- Every stored recursive payload satisfies one state-independent predicate. -/
def Heap (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    predicate entry body depth ordinary

/-- Empty payload tables satisfy every recursive payload invariant. -/
theorem empty (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop) :
    Heap predicate (InternedConstructorTemplates.empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- An effect that adds no Mu preserves a state-independent payload invariant. -/
theorem retain (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    {before after : State Symbol Guard} (initial : Heap predicate before) (old : NoNewMu before after) :
    Heap predicate after := by
  intro key entry body depth ordinary present
  exact initial key entry body depth ordinary (old key entry body depth ordinary present)

/-- Reserving a node identity leaves every stored payload unchanged. -/
private theorem reserve (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    (state : State Symbol Guard) (key : NodeKey) (initial : Heap predicate state) :
    Heap predicate {state with nodes := (Cache.intern state.nodes key).2} := initial

/-- Completion retains an old winner or installs the proved exact candidate. -/
theorem complete (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (initial : Heap predicate state) (candidate : predicate entry body depth ordinary) :
    Heap predicate (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_,same⟩
  · exact initial key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact candidate

/-- Causal path induction exposes all earlier callback heaps to the publication obligation. -/
theorem path_heap [DecidableEq (EdgeKey Symbol Guard)]
    (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    {before after : State Symbol Guard} (path : Path before after) (initial : Heap predicate before)
    (publication : ∀ event : Publication (Symbol := Symbol) (Guard := Guard),
      Heap predicate event.before → Heap predicate event.afterDepth → Heap predicate event.cut →
      Heap predicate event.allocated → Heap predicate event.afterBody →
      predicate event.entry event.body event.depth event.ordinary) : Heap predicate after := by
  induction path with
  | refl => exact initial
  | retain _ _ old _ _ => exact retain predicate initial old
  | trans _ _ first next => exact next (first initial)
  | publication event _ _ _ depth ordinary body =>
      have afterDepth := depth initial
      have cut := ordinary afterDepth
      have allocated : Heap predicate event.allocated := reserve predicate event.cut event.key cut
      have afterBody := body allocated
      exact complete predicate event.smart event.entry event.body event.depth event.ordinary event.afterBody afterBody
        (publication event initial afterDepth cut allocated afterBody)

/-- Actual source execution retains the invariant at its complete or pending stopping state. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)]
    (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (initial : Heap predicate state)
    (publication : ∀ event : Publication (Symbol := Symbol) (Guard := Guard),
      Heap predicate event.before → Heap predicate event.afterDepth → Heap predicate event.cut →
      Heap predicate event.allocated → Heap predicate event.afterBody →
      predicate event.entry event.body event.depth event.ordinary) :
    Heap predicate (InternedFreshOrdinaryConstruction.build expression environment state).state := by
  obtain ⟨path⟩ := SourceCurrentNativeMuIssuedHistory.build_path expression environment state context
  exact path_heap predicate path initial publication

/-- Closed actual source histories discharge the initial empty heap without a return premise. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)]
    (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    (expression : Syntax Symbol Guard)
    (publication : ∀ event : Publication (Symbol := Symbol) (Guard := Guard),
      Heap predicate event.before → Heap predicate event.afterDepth → Heap predicate event.cut →
      Heap predicate event.allocated → Heap predicate event.afterBody →
      predicate event.entry event.body event.depth event.ordinary) :
    Heap predicate (InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty).state :=
  build predicate expression [] InternedConstructorTemplates.empty
    SourceCurrentConstrainedCapSourceHistory.empty_context (empty predicate) publication

end MicroCFTA.SourceCurrentPublicationHeapInduction
