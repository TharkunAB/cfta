import MicroCFTA.SourceCurrentPublicationHeapInduction

/-!
# Payload induction with actual empty-table history prefixes

Each publication receives the history through its completed body callback.
The induction composes this prefix from the actual issued-name path.
The payload obligation is evaluated before the candidate is installed.
-/
namespace MicroCFTA.SourceCurrentCausalPublicationHeapInduction
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax)
open InternedBinderProtocol (NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentPublicationHeapInduction (Heap)

/-- Actual path induction supplies the empty-table prefix at each completed body callback. -/
theorem path_heap [DecidableEq (EdgeKey Symbol Guard)]
    (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    {before after : State Symbol Guard} (path : Path before after)
    (prefix : History empty before) (initial : Heap predicate before)
    (publication : ∀ event : Publication (Symbol := Symbol) (Guard := Guard),
      History empty event.afterBody →
      Heap predicate event.before → Heap predicate event.afterDepth → Heap predicate event.cut →
      Heap predicate event.allocated → Heap predicate event.afterBody →
      predicate event.entry event.body event.depth event.ordinary) : Heap predicate after := by
  revert prefix initial
  induction path with
  | refl state =>
      intro _ initial
      exact initial
  | retain before after old growth issued =>
      intro _ initial
      exact SourceCurrentPublicationHeapInduction.retain predicate initial old
  | trans first next firstIH nextIH =>
      intro prefix initial
      exact nextIH (.trans prefix first.forget.history) (firstIH prefix initial)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      intro prefix initial
      have depthPrefix : History empty event.afterDepth := .trans prefix depthPath.forget.history
      have afterDepth := depthIH prefix initial
      have cutPrefix : History empty event.cut := .trans depthPrefix ordinaryPath.forget.history
      have cut := ordinaryIH depthPrefix afterDepth
      have allocated : Heap predicate event.allocated := cut
      have reservation : History event.cut event.allocated :=
        .retain event.cut event.allocated (fun _ _ _ _ _ present => present)
      have allocatedPrefix : History empty event.allocated := .trans cutPrefix reservation
      have bodyPrefix : History empty event.afterBody := .trans allocatedPrefix bodyPath.forget.history
      have afterBody := bodyIH allocatedPrefix allocated
      exact SourceCurrentPublicationHeapInduction.complete predicate event.smart event.entry event.body
        event.depth event.ordinary event.afterBody afterBody
        (publication event bodyPrefix initial afterDepth cut allocated afterBody)

/-- Actual source execution supplies every publication prefix at its complete or pending state. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)]
    (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (prefix : History empty state) (initial : Heap predicate state)
    (publication : ∀ event : Publication (Symbol := Symbol) (Guard := Guard),
      History empty event.afterBody →
      Heap predicate event.before → Heap predicate event.afterDepth → Heap predicate event.cut →
      Heap predicate event.allocated → Heap predicate event.afterBody →
      predicate event.entry event.body event.depth event.ordinary) :
    Heap predicate (InternedFreshOrdinaryConstruction.build expression environment state).state := by
  obtain ⟨path⟩ := SourceCurrentNativeMuIssuedHistory.build_path expression environment state context
  exact path_heap predicate path prefix initial publication

/-- Empty source tables establish the initial prefix and payload heap without a return premise. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)]
    (predicate : Interned NodeKey → Value Symbol Guard → Value Symbol Guard → Value Symbol Guard → Prop)
    (expression : Syntax Symbol Guard)
    (publication : ∀ event : Publication (Symbol := Symbol) (Guard := Guard),
      History empty event.afterBody →
      Heap predicate event.before → Heap predicate event.afterDepth → Heap predicate event.cut →
      Heap predicate event.allocated → Heap predicate event.afterBody →
      predicate event.entry event.body event.depth event.ordinary) :
    Heap predicate (InternedFreshOrdinaryConstruction.build expression [] empty).state :=
  build predicate expression [] empty SourceCurrentConstrainedCapSourceHistory.empty_context
    (.refl empty) (SourceCurrentPublicationHeapInduction.empty predicate) publication

end MicroCFTA.SourceCurrentCausalPublicationHeapInduction
