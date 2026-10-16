import MicroCFTA.SourceCurrentAllocatedPartialWorker
import MicroCFTA.SourceCurrentAllocatedParentWorkerStability

/-!
# Successful mutual outer execution under larger bounds

The outer recursion bound and nine lower bounds can increase independently.
Every successful phase retains its exact output and entire caller state.
The strong outer-bound induction supplies all smaller request transports.
No physical, semantic, completion, or callback premise is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialWorkerStability
open Language InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
variable {width : Nat} {A B : Type}

/-- Successful sequencing exposes the exact intermediate complete caller. -/
theorem bind_done_iff (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (result : B) (after : Caller width) :
    first.bind next = .done result after ↔
      ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro actual; exact ⟨value, state, rfl, actual⟩
      · rintro ⟨_, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, impossible, _⟩; cases impossible

private def StableAt (fuel : Nat)
    (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width) : Prop :=
  ∀ {F g s r e p h m c n G S R E P H M C N : Nat} {result : A} {after : Caller width},
    evaluation fuel g s r e p h m c n = .done result after →
    fuel ≤ F → g ≤ G → s ≤ S → r ≤ R → e ≤ E → p ≤ P → h ≤ H → m ≤ M → c ≤ C → n ≤ N →
    evaluation F G S R E P H M C N = .done result after

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private def NodeCallAt (fuel : Nat) : Prop := ∀ budget request (before : Caller width),
  StableAt fuel (fun f g s r e p h m c n => nodeCall f g s r e p h m c n budget request before)
private def NodeBodyAt (fuel : Nat) : Prop := ∀ budget request (before : Caller width),
  StableAt fuel (fun f g s r e p h m c n => nodeBody f g s r e p h m c n budget request before)
private def RowsAt (fuel : Nat) : Prop := ∀ budget inherited originals (before : Caller width),
  StableAt fuel (fun f g s r e p h m c n => rows f g s r e p h m c n budget inherited originals before)
private def DescendantsAt (fuel : Nat) : Prop := ∀ budget inherited original (before : Caller width),
  StableAt fuel (fun f g s r e p h m c n => descendants f g s r e p h m c n budget inherited original before)
private def ChildrenAt (fuel : Nat) : Prop := ∀ budget combined values (before : Caller width),
  StableAt fuel (fun f g s r e p h m c n => children f g s r e p h m c n budget combined values before)
private def WalkAt (fuel : Nat) : Prop := ∀ budget combined index values (before : Caller width),
  StableAt fuel (fun f g s r e p h m c n => walk f g s r e p h m c n budget combined index values before)

/-- A successful parent body retains the exact full caller under all ten larger bounds. -/
theorem edgeBody_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : edgeBody fuel g s r e p h m c n budget request before = .done result after)
    (_enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    edgeBody F G S R E P H M C N budget request before = .done result after := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge with
  | done value checked fourth memo =>
      have stable := SourceCurrentAllocatedParentWorkerStability.edge_done_stable observed
        enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      simp only [edgeBody, observed] at actual
      simpa only [edgeBody, stable] using actual
  | failed => simp only [edgeBody, observed] at actual; cases actual

/-- A ready edge hit or successful stored body retains its exact demand and finish return. -/
theorem edgeCall_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after)
    (enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    edgeCall F G S R E P H M C N budget request before = .done result after := by
  rcases started : beginEdge request before with ⟨handle, action, running⟩
  cases action with
  | ready value => simpa only [edgeCall, started] using actual
  | evaluate original =>
      simp only [edgeCall, started] at actual ⊢
      obtain ⟨value, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp actual
      have stable := edgeBody_done_stable first enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      simpa only [stable, Outcome.bind] using last
  | busy | absent => simp only [edgeCall, started] at actual; cases actual

private theorem nodeCall_step (fuel : Nat) (body : NodeBodyAt (width := width) fuel) : NodeCallAt (width := width) fuel := by
  intro budget request before F g s r e p h m c n G S R E P H M C N result after actual
    enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
  rcases started : beginNode request before with ⟨handle, action, running⟩
  cases action with
  | ready value => simpa only [nodeCall, started] using actual
  | evaluate original =>
      simp only [nodeCall, started] at actual ⊢
      obtain ⟨value, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp actual
      have stable := body budget original running first enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      simpa only [stable, Outcome.bind] using last
  | busy | absent => simp only [nodeCall, started] at actual; cases actual

private theorem walk_step (fuel : Nat)
    (nodes : ∀ smaller, smaller < fuel → NodeCallAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → WalkAt (width := width) smaller) : WalkAt (width := width) fuel := by
  intro budget combined index values before F g s r e p h m c n G S R E P H M C N result after actual
    enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
  cases values with
  | nil => simpa only [walk] using actual
  | cons value rest =>
      cases fuel with
      | zero => simp only [walk] at actual; cases actual
      | succ fuel =>
          cases F with
          | zero => omega
          | succ later =>
              simp only [walk] at actual ⊢
              obtain ⟨firstValue, middle, first, remaining⟩ := (bind_done_iff _ _ _ _).mp actual
              obtain ⟨restValues, final, tail, last⟩ := (bind_done_iff _ _ _ _).mp remaining
              have firstStable := nodes fuel (Nat.lt_succ_self _) budget _ _ (F := later) first (by omega)
                enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
              have tailStable := tails fuel (Nat.lt_succ_self _) budget combined (index + 1) rest middle (F := later) tail (by omega)
                enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
              simpa only [firstStable, tailStable, Outcome.bind] using last

private theorem children_step (fuel : Nat) (walks : WalkAt (width := width) fuel) : ChildrenAt (width := width) fuel := by
  intro budget combined values before F g s r e p h m c n G S R E P H M C N result after actual
    enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
  cases combined with
  | contradiction => simpa only [children] using actual
  | live entry payload =>
      simp only [children] at actual ⊢
      exact walks budget (.live entry payload) 0 values before actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

private theorem descendants_step (fuel : Nat) (child : ChildrenAt (width := width) fuel) : DescendantsAt (width := width) fuel := by
  intro budget inherited original before F g s r e p h m c n G S R E P H M C N result after actual
    enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
  cases observed : SourceCurrentAllocatedInheritedPrefix.run original.entry.key.constraint inherited before.checked.operations with
  | mk answer operations =>
      cases answer with
      | error message => simp only [descendants, observed] at actual; cases actual
      | ok answer =>
          cases answer with
          | none => simp only [descendants, observed] at actual; cases actual
          | some combined =>
              simp only [descendants, observed] at actual ⊢
              obtain ⟨values, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp actual
              have stable := child budget combined original.children _ first enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
              simpa only [stable, Outcome.bind] using last

private theorem rows_step (fuel : Nat)
    (descend : ∀ smaller, smaller < fuel → DescendantsAt (width := width) smaller)
    (tails : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) : RowsAt (width := width) fuel := by
  intro budget inherited originals before F g s r e p h m c n G S R E P H M C N result after actual
    enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
  cases originals with
  | nil => simpa only [rows] using actual
  | cons original rest =>
      cases fuel with
      | zero => simp only [rows] at actual; cases actual
      | succ fuel =>
          cases F with
          | zero => omega
          | succ later =>
              simp only [rows] at actual ⊢
              obtain ⟨narrowed, middle, first, remaining⟩ := (bind_done_iff _ _ _ _).mp actual
              obtain ⟨edge, current, second, remaining⟩ := (bind_done_iff _ _ _ _).mp remaining
              obtain ⟨restValues, final, tail, last⟩ := (bind_done_iff _ _ _ _).mp remaining
              have firstStable := edgeCall_done_stable (F := later) first (by omega) enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
              have secondStable := descend fuel (Nat.lt_succ_self _) budget inherited narrowed middle (F := later) second (by omega)
                enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
              have tailStable := tails fuel (Nat.lt_succ_self _) budget inherited rest current (F := later) tail (by omega)
                enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
              simpa only [firstStable, secondStable, tailStable, Outcome.bind] using last

private theorem nodeBody_step (fuel : Nat)
    (rows : ∀ smaller, smaller < fuel → RowsAt (width := width) smaller) : NodeBodyAt (width := width) fuel := by
  intro budget request before F g s r e p h m c n G S R E P H M C N result after actual
    enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
  cases request with
  | mk inherited value =>
      cases value with
      | empty | union | reference | mu => simpa only [nodeBody] using actual
      | node entry original depth free =>
          cases fuel with
          | zero => simp only [nodeBody] at actual; cases actual
          | succ fuel =>
              cases F with
              | zero => omega
              | succ later =>
                  simp only [nodeBody] at actual ⊢
                  obtain ⟨values, middle, first, last⟩ := (bind_done_iff _ _ _ _).mp actual
                  have stable := rows fuel (Nat.lt_succ_self _) budget inherited original before (F := later) first (by omega)
                    enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
                  simpa only [stable, Outcome.bind] using last

private theorem all_stable (fuel : Nat) :
    NodeCallAt (width := width) fuel ∧ NodeBodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walks := walk_step fuel (fun smaller less => (ih smaller less).1)
        (fun smaller less => (ih smaller less).2.2.2.2.2)
      have children := children_step fuel walks
      have descendants := descendants_step fuel children
      have rows := rows_step fuel (fun smaller less => (ih smaller less).2.2.2.1)
        (fun smaller less => (ih smaller less).2.2.1)
      have body := nodeBody_step fuel (fun smaller less => (ih smaller less).2.2.1)
      exact ⟨nodeCall_step fuel body, body, rows, descendants, children, walks⟩


/-- Larger outer and lower bounds retain the exact successful nodeCall return. -/
theorem nodeCall_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done result after)
    (enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    nodeCall F G S R E P H M C N budget request before = .done result after :=
  (all_stable fuel).1 budget request before actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

/-- Larger outer and lower bounds retain the exact successful nodeBody return. -/
theorem nodeBody_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : nodeBody fuel g s r e p h m c n budget request before = .done result after)
    (enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    nodeBody F G S R E P H M C N budget request before = .done result after :=
  (all_stable fuel).2.1 budget request before actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

/-- Larger outer and lower bounds retain the exact successful rows return. -/
theorem rows_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {inherited : EqValue} {originals : List Edge} {before after : Caller width} {result : List Edge}
    (actual : rows fuel g s r e p h m c n budget inherited originals before = .done result after)
    (enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    rows F G S R E P H M C N budget inherited originals before = .done result after :=
  (all_stable fuel).2.2.1 budget inherited originals before actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

/-- Larger outer and lower bounds retain the exact successful descendants return. -/
theorem descendants_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {inherited : EqValue} {original : Edge} {before after : Caller width} {result : Edge}
    (actual : descendants fuel g s r e p h m c n budget inherited original before = .done result after)
    (enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    descendants F G S R E P H M C N budget inherited original before = .done result after :=
  (all_stable fuel).2.2.2.1 budget inherited original before actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

/-- Larger outer and lower bounds retain the exact successful children return. -/
theorem children_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {combined : EqValue} {values : List Node} {before after : Caller width} {result : List Node}
    (actual : children fuel g s r e p h m c n budget combined values before = .done result after)
    (enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    children F G S R E P H M C N budget combined values before = .done result after :=
  (all_stable fuel).2.2.2.2.1 budget combined values before actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

/-- Larger outer and lower bounds retain the exact successful walk return. -/
theorem walk_done_stable {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {combined : EqValue} {index : Nat} {values : List Node} {before after : Caller width} {result : List Node}
    (actual : walk fuel g s r e p h m c n budget combined index values before = .done result after)
    (enoughFuel : fuel ≤ F) (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughR : r ≤ R) (enoughE : e ≤ E)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughM : m ≤ M) (enoughC : c ≤ C) (enoughN : n ≤ N) :
    walk F G S R E P H M C N budget combined index values before = .done result after :=
  (all_stable fuel).2.2.2.2.2 budget combined index values before actual enoughFuel enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem success_unique
    (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width)
    (stable : ∀ fuel, StableAt fuel evaluation)
    {fuel F g s r e p h m c n G S R E P H M C N : Nat}
    {first second : A} {after later : Caller width}
    (one : evaluation fuel g s r e p h m c n = .done first after)
    (two : evaluation F G S R E P H M C N = .done second later) : first = second ∧ after = later := by
  have left := stable fuel one (Nat.le_max_left fuel F) (Nat.le_max_left g G) (Nat.le_max_left s S)
    (Nat.le_max_left r R) (Nat.le_max_left e E) (Nat.le_max_left p P) (Nat.le_max_left h H)
    (Nat.le_max_left m M) (Nat.le_max_left c C) (Nat.le_max_left n N)
  have right := stable F two (Nat.le_max_right fuel F) (Nat.le_max_right g G) (Nat.le_max_right s S)
    (Nat.le_max_right r R) (Nat.le_max_right e E) (Nat.le_max_right p P) (Nat.le_max_right h H)
    (Nat.le_max_right m M) (Nat.le_max_right c C) (Nat.le_max_right n N)
  exact Outcome.done.inj (left.symm.trans right)

/-- Successful nodeCall bounds identify both the output and entire caller state. -/
theorem nodeCall_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : NodeRequest} {before after later : Caller width} {first second : Node}
    (one : nodeCall fuel g s r e p h m c n budget request before = .done first after)
    (two : nodeCall F G S R E P H M C N budget request before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun fuel => (all_stable fuel).1 budget request before) one two

/-- Successful nodeBody bounds identify both the output and entire caller state. -/
theorem nodeBody_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : NodeRequest} {before after later : Caller width} {first second : Node}
    (one : nodeBody fuel g s r e p h m c n budget request before = .done first after)
    (two : nodeBody F G S R E P H M C N budget request before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun fuel => (all_stable fuel).2.1 budget request before) one two

/-- Successful edgeCall bounds identify both the output and entire caller state. -/
theorem edgeCall_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : EdgeRequest} {before after later : Caller width} {first second : Edge}
    (one : edgeCall fuel g s r e p h m c n budget request before = .done first after)
    (two : edgeCall F G S R E P H M C N budget request before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun _ => edgeCall_done_stable) one two

/-- Successful edgeBody bounds identify both the output and entire caller state. -/
theorem edgeBody_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {request : EdgeRequest} {before after later : Caller width} {first second : Edge}
    (one : edgeBody fuel g s r e p h m c n budget request before = .done first after)
    (two : edgeBody F G S R E P H M C N budget request before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun _ => edgeBody_done_stable) one two

/-- Successful rows bounds identify both the output and entire caller state. -/
theorem rows_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {inherited : EqValue} {originals : List Edge} {before after later : Caller width} {first second : List Edge}
    (one : rows fuel g s r e p h m c n budget inherited originals before = .done first after)
    (two : rows F G S R E P H M C N budget inherited originals before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun fuel => (all_stable fuel).2.2.1 budget inherited originals before) one two

/-- Successful descendants bounds identify both the output and entire caller state. -/
theorem descendants_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {inherited : EqValue} {original : Edge} {before after later : Caller width} {first second : Edge}
    (one : descendants fuel g s r e p h m c n budget inherited original before = .done first after)
    (two : descendants F G S R E P H M C N budget inherited original before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun fuel => (all_stable fuel).2.2.2.1 budget inherited original before) one two

/-- Successful children bounds identify both the output and entire caller state. -/
theorem children_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {combined : EqValue} {values : List Node} {before after later : Caller width} {first second : List Node}
    (one : children fuel g s r e p h m c n budget combined values before = .done first after)
    (two : children F G S R E P H M C N budget combined values before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun fuel => (all_stable fuel).2.2.2.2.1 budget combined values before) one two

/-- Successful walk bounds identify both the output and entire caller state. -/
theorem walk_done_unique {fuel F g s r e p h m c n G S R E P H M C N budget : Nat}
    {combined : EqValue} {index : Nat} {values : List Node} {before after later : Caller width} {first second : List Node}
    (one : walk fuel g s r e p h m c n budget combined index values before = .done first after)
    (two : walk F G S R E P H M C N budget combined index values before = .done second later) :
    first = second ∧ after = later :=
  success_unique _ (fun fuel => (all_stable fuel).2.2.2.2.2 budget combined index values before) one two

end MicroCFTA.SourceCurrentAllocatedPartialWorkerStability
