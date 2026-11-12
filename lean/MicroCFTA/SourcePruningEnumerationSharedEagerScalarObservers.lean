import MicroCFTA.SourcePruningEnumerationSharedEagerChildren
import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
import MicroCFTA.SourcePruningEnumerationCostBounds

/-!
# Scalar bounds at actual eager consumer inputs

The counter and suspended mass use maxima across alternatives.
They use sums across a completed tuple path.
Consumer equality on these inputs preserves the entire actual fold.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEagerScalarObservers
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild ordinaryNonterminal consumeSelected)
open SourcePruningEnumerationSharedBranching (scan)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Fold" => NativeContinuations.Result Output Reason width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation width → Option Cached → Fold) → Fold

private def tupleGrowth (child : Node → Nat → Nat × Nat) : List Node → Nat → Nat × Nat
  | [], _ => (0, 0)
  | value :: rest, bound =>
      let first := child value bound
      let later := tupleGrowth child rest bound
      (first.1 + later.1, first.2 + later.2)

private noncomputable def rowGrowth (child : Node → Nat → Nat × Nat) (edge : Edge) (bound : Nat) : Nat × Nat :=
  match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
  | none => (0, 0)
  | some (tries, _) =>
      let children := tupleGrowth child edge.children (bound + tries.length)
      (tries.length + children.1, children.2)

private noncomputable def rowsGrowth (child : Node → Nat → Nat × Nat) : List Edge → Nat → Nat × Nat
  | [], _ => (0, 0)
  | edge :: rest, bound =>
      let first := rowGrowth child edge bound
      let later := rowsGrowth child rest bound
      (max first.1 later.1, max first.2 later.2)

/-- Derive cache growth from the literal selector and the actual eager rank guard. -/
noncomputable def nodeGrowth (edgesOf : Node → List Edge) (incoming : Node) (bound : Nat) : Nat × Nat :=
  let child := fun value retained =>
    if _lower : MergedOrdinaryHeight.height value < MergedOrdinaryHeight.height incoming then
      nodeGrowth edgesOf value retained
    else (1, retained)
  let branches := rowsGrowth child (edgesOf incoming) bound
  (max 1 branches.1, max bound branches.2)
termination_by MergedOrdinaryHeight.height incoming
decreasing_by exact _lower

/-- Derive the scalar ceiling of one actual selected-edge operation. -/
noncomputable def selectedGrowth (edgesOf : Node → List Edge) (edge : Edge) (bound : Nat) : Nat × Nat :=
  rowGrowth (nodeGrowth edgesOf) edge bound

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def CacheBound (before after : Cached) (bound : Nat × Nat) : Prop :=
  after.core.counter ≤ before.core.counter + bound.1 ∧
    suspendedBound after.core ≤ suspendedBound before.core + bound.2

private def ReceiptBound (before : Cached) (bound : Nat × Nat) : Receipt width → Prop
  | .complete _ _ _ after | .rejected _ _ after => CacheBound before after bound
  | .stopped _ _ candidate => ∀ after, candidate = some after → CacheBound before after bound
  | .unhandled => True
  | .finalizeStopped .. => False

private def At (visit : Visitor) (growth : Node → Nat → Nat × Nat) (incoming : Node) : Prop :=
  ∀ (scs : List Suspended) (bound : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (yesLeft yesRight : Fragment → Caller width → Queries → Cached → Fold)
    (noLeft noRight : Observation width → Option Cached → Fold), scs.length ≤ bound →
    (∀ fragment reached saved after, CacheBound before after (growth incoming bound) →
      yesLeft fragment reached saved after = yesRight fragment reached saved after) →
    (∀ observation candidate, (∀ after, candidate = some after → CacheBound before after (growth incoming bound)) →
      noLeft observation candidate = noRight observation candidate) →
    visit scs incoming caller before queries yesLeft noLeft = visit scs incoming caller before queries yesRight noRight

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem bound_refl (before : Cached) (bound : Nat × Nat) : CacheBound before before bound :=
  ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem bound_mono {before after : Cached} {first last : Nat × Nat}
    (actual : CacheBound before after first) (counter : first.1 ≤ last.1) (mass : first.2 ≤ last.2) :
    CacheBound before after last := by
  dsimp [CacheBound] at actual ⊢
  exact ⟨by omega, by omega⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem bound_trans {before middle after : Cached} {first last : Nat × Nat}
    (head : CacheBound before middle first) (tail : CacheBound middle after last) :
    CacheBound before after (first.1 + last.1, first.2 + last.2) := by
  dsimp [CacheBound] at head tail ⊢
  exact ⟨by omega, by omega⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem tuple_bounds (visit : Visitor) (growth : Node → Nat → Nat × Nat)
    (childBounds : ∀ incoming, At visit growth incoming) (inputs : List (Node × List Suspended)) (bound : Nat) :
    (∀ input ∈ inputs, input.2.length ≤ bound) →
    ∀ caller before queries
      (yesLeft yesRight : List Fragment → Caller width → Queries → Cached → Fold)
      (noLeft noRight : List Fragment → Observation width → Option Cached → Fold),
      (∀ fragments reached saved after, CacheBound before after (tupleGrowth growth (inputs.map Prod.fst) bound) →
        yesLeft fragments reached saved after = yesRight fragments reached saved after) →
      (∀ completed observation candidate,
        (∀ after, candidate = some after → CacheBound before after (tupleGrowth growth (inputs.map Prod.fst) bound)) →
        noLeft completed observation candidate = noRight completed observation candidate) →
      visitChildren visit yesLeft noLeft inputs caller before queries =
        visitChildren visit yesRight noRight inputs caller before queries := by
  induction inputs with
  | nil =>
      intro _lengths caller before queries yesLeft yesRight noLeft noRight yesSame _noSame
      exact yesSame [] caller queries before (bound_refl before _)
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      intro lengths caller before queries yesLeft yesRight noLeft noRight yesSame noSame
      apply childBounds incoming bucket bound caller before queries _ _ _ _ (lengths _ List.mem_cons_self)
      · intro fragment reached saved middle head
        apply ih (fun input member => lengths input (List.mem_cons_of_mem _ member)) reached middle saved
          (fun fragments => yesLeft (fragment :: fragments)) (fun fragments => yesRight (fragment :: fragments))
          (fun completed => noLeft (fragment :: completed)) (fun completed => noRight (fragment :: completed))
        · intro fragments current retained after tail
          exact yesSame (fragment :: fragments) current retained after (bound_trans head tail)
        · intro completed observation candidate tail
          exact noSame (fragment :: completed) observation candidate
            (fun after found => bound_trans head (tail after found))
      · intro observation candidate head
        exact noSame [] observation candidate (fun after found =>
          bound_mono (head after found) (Nat.le_add_right _ _) (Nat.le_add_right _ _))

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem selected_bounds (visit : Visitor) (growth : Node → Nat → Nat × Nat)
    (childBounds : ∀ incoming, At visit growth incoming)
    (scs : List Suspended) (bound : Nat) (length : scs.length ≤ bound) (edge : Edge)
    (caller : Caller width) (before : Cached) (queries : Queries) (left right : Receipt width → Fold)
    (same : ∀ receipt, ReceiptBound before (rowGrowth growth edge bound) receipt → left receipt = right receipt) :
    visitSelected visit left scs edge caller before queries = visitSelected visit right scs edge caller before queries := by
  cases prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => simpa only [visitSelected, prepared] using same .unhandled trivial
  | some results =>
      cases results with
      | nil => simpa only [visitSelected, prepared] using same (.rejected caller queries before) (bound_refl before _)
      | cons first rest =>
          cases rest with
          | cons second remaining => simpa only [visitSelected, prepared] using same .unhandled trivial
          | nil =>
              rcases first with ⟨⟨symbol, staged, savedResidual⟩, middle⟩
              by_cases allowed : arityAllows edge.children.length scs = true
              · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
                | none => simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected] at prepared
                | some fields =>
                    rcases fields with ⟨tries, residual⟩
                    obtain ⟨_allowed, _core, ownCounter, ownMass⟩ := SourcePruningEnumerationCachedOwn.prepare_scalars
                      caller.checked.native.machine.heap scs edge before middle tries residual (symbol, staged, savedResidual)
                      projected prepared
                    have shape := SourcePruningEnumerationCachedOwn.prepare_inputs caller.checked.native.machine.heap
                      scs edge before middle tries residual (symbol, staged, savedResidual) projected prepared
                    simp only [Prod.mk.injEq] at shape
                    obtain ⟨rfl, rfl, rfl⟩ := shape
                    let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
                    have readback : (inputs.map (fun input => (input.1, input.2,
                        SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
                        (fun input => (input.1, input.2.1)) = inputs := by
                      simp only [List.map_map]
                      exact List.map_id _
                    have nodes : inputs.map Prod.fst = edge.children := by
                      simp only [inputs, SourcePruningEnumerationEdgeInputs.children, List.map_map]
                      change edge.children.zipIdx.map Prod.fst = edge.children
                      exact List.zipIdx_map_fst 0 edge.children
                    have lengths : ∀ input ∈ inputs, input.2.length ≤ bound + tries.length := by
                      intro input member
                      obtain ⟨indexed, _listed, rfl⟩ := List.mem_map.mp member
                      have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
                      have own := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
                        (EnumerationCorrectness.suspendedVars before.core.counter tries)
                      rw [SourcePruningEnumerationCostBounds.suspended_length] at own
                      simp only [List.length_append]
                      omega
                    have combine (after : Cached)
                        (actual : CacheBound middle after (tupleGrowth growth (inputs.map Prod.fst) (bound + tries.length))) :
                        CacheBound before after (rowGrowth growth edge bound) := by
                      rw [nodes] at actual
                      simp only [rowGrowth, projected]
                      dsimp [CacheBound] at actual ⊢
                      exact ⟨by omega, by omega⟩
                    dsimp only [inputs] at readback
                    simp only [visitSelected, prepared, readback]
                    apply tuple_bounds visit growth childBounds inputs (bound + tries.length) lengths caller middle queries
                    · intro fragments reached saved after actual
                      apply same
                      change CacheBound before after (rowGrowth growth edge bound)
                      exact combine after actual
                    · intro completed observation candidate actual
                      exact same (.stopped completed observation candidate) (fun after found => combine after (actual after found))
              · simp [SourcePruningEnumerationCachedOwn.prepare, allowed] at prepared

private theorem shallow_bounds (checkEmpty : Bool) (r n p h k : Nat) (incoming : Node) :
    At (width := width) (Output := Output) (Reason := Reason)
      (shallowVisit checkEmpty r n p h k) (fun _ bound => (1, bound)) incoming := by
  intro scs bound caller before queries yesLeft yesRight noLeft noRight length yesSame noSame
  cases observed : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries with
  | mk observation candidate =>
      have bounds : ∀ after, candidate = some after → CacheBound before after (1, bound) := by
        intro after found
        have actual := ChildDispatch.observed_scalar_bounds checkEmpty r n p h k scs incoming caller before queries after
          (by rw [observed]; exact found)
        dsimp [CacheBound]
        exact ⟨actual.1, by omega⟩
      rcases observation with ⟨outcome, reached, saved, outer, waiting⟩
      have noThis := noSame (outcome, reached, saved, outer, waiting) candidate bounds
      cases outcome with
      | error fault => simpa only [shallowVisit, observed] using noThis
      | ok possible =>
          cases possible with
          | none => simpa only [shallowVisit, observed] using noThis
          | some rows =>
              cases rows with
              | nil => simpa only [shallowVisit, observed] using noThis
              | cons first rest =>
                  cases first with
                  | error fault => simpa only [shallowVisit, observed] using noThis
                  | ok pair =>
                      rcases pair with ⟨fragment, returned⟩
                      cases rest with
                      | cons second remaining => simpa only [shallowVisit, observed] using noThis
                      | nil =>
                          cases candidate with
                          | none => simpa only [shallowVisit, observed] using noThis
                          | some after => simpa only [shallowVisit, observed] using yesSame fragment reached saved after (bounds after rfl)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem row_le (growth : Node → Nat → Nat × Nat) (edges : List Edge) (bound : Nat)
    (edge : Edge) (member : edge ∈ edges) :
    (rowGrowth growth edge bound).1 ≤ (rowsGrowth growth edges bound).1 ∧
      (rowGrowth growth edge bound).2 ≤ (rowsGrowth growth edges bound).2 := by
  induction edges with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩
      · obtain ⟨counter, mass⟩ := ih later
        exact ⟨Nat.le_trans counter (Nat.le_max_right _ _), Nat.le_trans mass (Nat.le_max_right _ _)⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem scan_congr (left right : Edge → Caller width → Queries → Cached → Fold)
    (before : Cached) (edges : List Edge)
    (same : ∀ edge ∈ edges, ∀ caller queries, left edge caller queries before = right edge caller queries before)
    (caller : Caller width) (queries : Queries) :
    scan left before edges caller queries = scan right before edges caller queries := by
  induction edges generalizing caller queries with
  | nil => rfl
  | cons edge rest ih =>
      simp only [scan, same edge List.mem_cons_self caller queries]
      cases observed : right edge caller queries before with
      | stopped processed outputs current => rfl
      | complete processed outputs reached saved =>
          simp only [ih (fun chosen member => same chosen (List.mem_cons_of_mem _ member)) reached saved]

private theorem eager_bounds (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (incoming : Node) :
    At (width := width) (Output := Output) (Reason := Reason)
      (eagerChild checkEmpty r n p h k edgesOf) (nodeGrowth edgesOf) incoming := by
  intro scs bound caller before queries yesLeft yesRight noLeft noRight length yesSame noSame
  let child : Visitor := fun bucket value current cache memos yes no =>
    if _lower : MergedOrdinaryHeight.height value < MergedOrdinaryHeight.height incoming then
      eagerChild checkEmpty r n p h k edgesOf bucket value current cache memos yes no
    else shallowVisit checkEmpty r n p h k bucket value current cache memos yes no
  let growth := fun value retained =>
    if _lower : MergedOrdinaryHeight.height value < MergedOrdinaryHeight.height incoming then
      nodeGrowth edgesOf value retained
    else (1, retained)
  have childBounds : ∀ value, At child growth value := by
    intro value
    by_cases lower : MergedOrdinaryHeight.height value < MergedOrdinaryHeight.height incoming
    · simpa only [At, child, growth, dite_eq_left lower] using eager_bounds checkEmpty r n p h k edgesOf value
    · simpa only [At, child, growth, dite_eq_right lower] using
        shallow_bounds (width := width) (Output := Output) (Reason := Reason) checkEmpty r n p h k value
  have equation : nodeGrowth edgesOf incoming bound =
      (max 1 (rowsGrowth growth (edgesOf incoming) bound).1,
        max bound (rowsGrowth growth (edgesOf incoming) bound).2) := by
    rw [nodeGrowth]
  by_cases ordinary : ordinaryNonterminal scs incoming = true
  · rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary checkEmpty r n p h k edgesOf scs incoming caller before queries
      yesLeft noLeft ordinary,
      SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary checkEmpty r n p h k edgesOf scs incoming caller before queries
      yesRight noRight ordinary]
    apply scan_congr _ _ before (edgesOf incoming) _ caller queries
    intro edge member current saved
    apply selected_bounds child growth childBounds scs bound length edge current before saved
      (consumeSelected yesLeft current saved) (consumeSelected yesRight current saved)
    intro receipt actual
    cases receipt with
    | complete fragment reached retained after =>
        have row := row_le growth (edgesOf incoming) bound edge member
        have within : CacheBound before after (nodeGrowth edgesOf incoming bound) := by
          rw [equation]
          exact bound_mono actual (Nat.le_trans row.1 (Nat.le_max_right _ _))
            (Nat.le_trans row.2 (Nat.le_max_right _ _))
        simp only [consumeSelected, yesSame fragment reached retained after within]
    | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ => rfl
  · have fallback : ordinaryNonterminal scs incoming = false := by
      cases classified : ordinaryNonterminal scs incoming with
      | false => rfl
      | true => exact (ordinary classified).elim
    rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty r n p h k edgesOf scs incoming caller before queries
      yesLeft noLeft fallback,
      SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty r n p h k edgesOf scs incoming caller before queries
      yesRight noRight fallback]
    apply shallow_bounds (width := width) (Output := Output) (Reason := Reason) checkEmpty r n p h k incoming scs bound caller before queries yesLeft yesRight noLeft noRight length
    · intro fragment reached saved after actual
      apply yesSame fragment reached saved after
      rw [equation]
      exact bound_mono actual (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    · intro observation candidate actual
      apply noSame observation candidate
      intro after found
      rw [equation]
      exact bound_mono (actual after found) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
termination_by MergedOrdinaryHeight.height incoming
decreasing_by exact lower

/-- Equal consumers on the derived input bounds give the same complete eager fold. -/
theorem visitSelected_callback_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (edge : Edge) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    let bound := selectedGrowth edgesOf edge scs.length
    ∀ left right : Receipt width → Fold,
      (∀ receipt,
        (match receipt with
        | .complete _ _ _ after | .rejected _ _ after =>
            after.core.counter ≤ before.core.counter + bound.1 ∧
            suspendedBound after.core ≤ suspendedBound before.core + bound.2
        | .stopped _ _ candidate => ∀ after, candidate = some after →
            after.core.counter ≤ before.core.counter + bound.1 ∧
            suspendedBound after.core ≤ suspendedBound before.core + bound.2
        | .unhandled => True
        | .finalizeStopped .. => False) → left receipt = right receipt) →
      visitSelected (eagerChild checkEmpty r n p h k edgesOf)
        left scs edge caller before queries =
      visitSelected (eagerChild checkEmpty r n p h k edgesOf)
        right scs edge caller before queries := by
  dsimp only
  intro left right same
  exact selected_bounds (eagerChild checkEmpty r n p h k edgesOf) (nodeGrowth edgesOf)
    (eager_bounds (width := width) (Output := Output) (Reason := Reason) checkEmpty r n p h k edgesOf) scs scs.length (Nat.le_refl _) edge caller before queries left right same

end MicroCFTA.SourcePruningEnumerationSharedEagerScalarObservers
