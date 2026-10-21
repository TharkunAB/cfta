import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Original source construction derives normalized annotation heaps

Every source edge literal checks its own stored payload. The actual repaired
constructor retains this invariant through all children, both probes, fresh
binder allocation, canonical hits, and pending outcomes. No final heap or
whole-record language invariant is supplied.
-/
namespace MicroCFTA.SourceEqualityAnnotationConstruction
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction
open SourceEqualityAnnotationHeap

mutual
/-- Original source syntax checks every complete edge guard, including discarded alternatives and probe bodies. -/
def Allowed (valid : Guard → Prop) : Syntax Symbol Guard → Prop
  | .empty | .var _ => True
  | .node edges => EdgesAllowed valid edges
  | .union members => ManyAllowed valid members
  | .binder _ body => Allowed valid body
termination_by expression => sizeOf expression

/-- Ordered child syntax retains each original source annotation check. -/
def ManyAllowed (valid : Guard → Prop) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Allowed valid first ∧ ManyAllowed valid rest
termination_by expressions => sizeOf expressions

/-- Each edge syntax retains its literal guard and all nested child checks. -/
def EdgesAllowed (valid : Guard → Prop) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ guard children :: rest => valid guard ∧ ManyAllowed valid children ∧ EdgesAllowed valid rest
termination_by expressions => sizeOf expressions
end

/-- Annotation heaps compose through actual source outcomes, including pending branches. -/
theorem bind_heap (valid : Guard → Prop) (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B)
    (heap : Heap valid outcome.state) (later : ∀ value state, Heap valid state → Heap valid (next value state).state) :
    Heap valid (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value state => exact later value state heap

/-- Actual constructor work supplies its final physical annotation heap from emitted guards. -/
theorem work_heap [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (job : Work Symbol Guard A)
    (safe : SafeWork valid job) (state : State Symbol Guard) (heap : Heap valid state) : Heap valid (work job state).state :=
  SourceEqualityAnnotationHeap.run valid job safe state heap

mutual
/-- Original repaired source construction preserves all physical edge annotations in every outcome. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expression : Syntax Symbol Guard)
    (allowed : Allowed valid expression) (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (heap : Heap valid state) :
    Heap valid (InternedFreshOrdinaryConstruction.build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [InternedFreshOrdinaryConstruction.build, Outcome.state] using heap
  | node edges =>
      simp only [Allowed] at allowed
      simp only [InternedFreshOrdinaryConstruction.build]
      exact bind_heap valid _ _ (buildEdges valid edges allowed environment state heap)
        (fun values next nextHeap => work_heap valid _ (SourceEqualityAnnotationHeap.makeNode valid values) next nextHeap)
  | union members =>
      simp only [Allowed] at allowed
      simp only [InternedFreshOrdinaryConstruction.build]
      exact bind_heap valid _ _ (buildMany valid members allowed environment state heap)
        (fun values next nextHeap => work_heap valid _ (SourceEqualityAnnotationHeap.makeUnion valid values) next nextHeap)
  | binder smart body =>
      simp only [Allowed] at allowed
      simp only [InternedFreshOrdinaryConstruction.build, request]
      apply bind_heap valid
      · exact bind_heap valid _ _ (build valid body allowed _ state heap)
          (fun value next nextHeap => work_heap valid _ (SourceEqualityAnnotationHeap.withoutSelfReference valid .depth value) next nextHeap)
      · intro depth afterDepth depthHeap
        apply bind_heap valid
        · exact bind_heap valid _ _ (build valid body allowed _ afterDepth depthHeap)
            (fun value next nextHeap => work_heap valid _ (SourceEqualityAnnotationHeap.withoutSelfReference valid (.uninterned (ordinaryLevel depth)) value) next nextHeap)
        · intro ordinary afterOrdinary ordinaryHeap
          split
          · split <;> exact ordinaryHeap
          · let key := muKey depth ordinary
            let entry := Cache.intern afterOrdinary.nodes key
            let allocated := {afterOrdinary with nodes := entry.2}
            have allocatedHeap : Heap valid allocated := ordinaryHeap
            apply bind_heap valid
            · exact bind_heap valid _ _ (build valid body allowed _ allocated allocatedHeap)
                (fun value next nextHeap => work_heap valid _
                  (SourceEqualityAnnotationHeap.withoutSelfReference valid (.interned entry.1.identity) value) next nextHeap)
            · intro bodyValue afterBody bodyHeap
              exact bodyHeap
termination_by sizeOf expression

/-- Ordered nested child construction retains annotations through every actual earlier child effect. -/
theorem buildMany [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expressions : List (Syntax Symbol Guard))
    (allowed : ManyAllowed valid expressions) (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (heap : Heap valid state) :
    Heap valid (InternedFreshOrdinaryConstruction.buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildMany, Outcome.state] using heap
  | cons first rest =>
      simp only [ManyAllowed] at allowed
      simp only [InternedFreshOrdinaryConstruction.buildMany]
      apply bind_heap valid _ _ (build valid first allowed.1 environment state heap)
      intro value next nextHeap
      apply bind_heap valid _ _ (buildMany valid rest allowed.2 environment next nextHeap)
      intro values final finalHeap
      exact finalHeap
termination_by sizeOf expressions

/-- Each actual edge emission derives its own annotation check from the original literal syntax. -/
theorem buildEdges [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expressions : List (EdgeSyntax Symbol Guard))
    (allowed : EdgesAllowed valid expressions) (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (heap : Heap valid state) :
    Heap valid (InternedFreshOrdinaryConstruction.buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildEdges, Outcome.state] using heap
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [EdgesAllowed] at allowed
          simp only [InternedFreshOrdinaryConstruction.buildEdges]
          apply bind_heap valid _ _ (buildMany valid children allowed.2.1 environment state heap)
          intro values next nextHeap
          apply bind_heap valid _ _ (work_heap valid _ (SourceEqualityAnnotationHeap.makeEdge valid symbol guard values allowed.1) next nextHeap)
          intro edge afterEdge edgeHeap
          apply bind_heap valid _ _ (buildEdges valid rest allowed.2.2 environment afterEdge edgeHeap)
          intro edges final finalHeap
          exact finalHeap
termination_by sizeOf expressions
end

/-- Original closed source construction derives both the physical annotation heap and every semantic record annotation. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expression : Syntax Symbol Guard)
    (allowed : Allowed valid expression) :
    ∃ value heap, ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Heap valid heap ∧ SourceEqualityAnnotationLanguage.Annotated valid value := by
  obtain ⟨value, heap, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have physical : Heap valid heap := by
    simpa only [done, Outcome.state] using build valid expression allowed [] empty (empty_heap valid)
  have checked := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by simpa only [done, Outcome.state] using checked.facts
  exact ⟨value, heap, done, physical,
    SourceEqualityAnnotationHeap.available valid heap physical facts.linked value (checked.result value heap done)⟩

end MicroCFTA.SourceEqualityAnnotationConstruction
