import MicroCFTA.SourceCurrentOuterPrefixInvariants
import MicroCFTA.SourceCurrentNormalizedInheritedPrefix

/-!
# Actual inherited height gains before an active owner key recurs

A nonempty inherited payload strictly loses path height at child descent.
If an actual nested dispatch uses its active owner's full key again, an
intervening returned row prefix must increase this height. The prefix has
an effective nonempty own field. Initial physical invariants derive all
current readiness and fixedness facts. The theorem does not exclude the
identified gain or bound fresh recursive requests.
-/
namespace MicroCFTA.SourceCurrentOuterInheritedGain
open Cache InternedConstructorTemplates InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentOuterPrefixInvariants
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
open SourceCurrentEqualityOperationFixed (FixedPayload)
open SourceCurrentOuterInheritedDescent (pathHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "prefixRun" => SourceCurrentAllocatedInheritedPrefix.run
variable {width : Nat}

/-- Every phase retains its exact current inherited value. -/
def inherited : Phase width → EqValue
  | .node _ request _ | .body _ request _ => request.inherited
  | .rows _ input _ _ | .descendants _ input _ _ | .children _ input _ _ | .walk _ input _ _ _ => input

private theorem ready (phase : Phase width) (inputs : Inputs phase) :
    EqReady (caller phase).checked.operations.constraints (inherited phase) := by
  cases phase <;> exact inputs.1

private theorem demand_table (handle : Nat) (state : FlatMemoThunk.State Key Request Result) :
    (FlatMemoThunk.demand handle state).2.table = state.table := by
  cases found : state.cells handle with
  | none => simp only [FlatMemoThunk.demand,found]
  | some cell => cases phase : cell.status <;> simp only [FlatMemoThunk.demand,found,phase,FlatMemoThunk.setStatus]

section
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem owner_eq {before running : Caller width} {request owner : NodeRequest} {handle : Nat}
    (good : Good before) (inputs : NodeReady before request)
    (started : beginNode request before = (handle,.evaluate owner,running)) : owner = request := by
  have current := SourceCurrentOuterPrefixInvariants.activate started good inputs
  have same := (beginNode_components request before).1
  rw [started] at same
  have requested : NodeReady running request := by
    change NodeReady running request
    unfold NodeReady
    rw [show running.checked = before.checked from same]
    exact inputs
  have table : running.nodeResults.table request.key = some handle := by
    have stored : (beginNode request before).2.2.nodeResults.table request.key =
        some (beginNode request before).1 := by
      change (FlatMemoThunk.demand _ _).2.table _ = _
      rw [demand_table]
      exact FlatMemoThunk.lookup_stored _ _ _
    simpa only [started] using stored
  obtain ⟨stored,found,key⟩ := current.1.nodes.linked request.key handle table
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  have observed := congrArg (fun result => (result.2.1,result.2.2.nodeResults)) started
  change FlatMemoThunk.demand published.1 published.2 = (.evaluate owner,running.nodeResults) at observed
  have present := (FlatMemoThunk.demand_evaluate _ _ _ owner observed).2
  have handles : published.1 = handle := congrArg Prod.fst started
  rw [handles] at present
  have equal := Option.some.inj (found.symm.trans present)
  subst stored
  exact SourceCurrentOuterPrefixInvariants.same_key current.1 current.2 requested key

end

private theorem prefix_fixed {before : Caller width} {edge : Edge} {input output : EqValue}
    (good : Good before) (inputs : Inputs (.descendants fuel input edge before))
    (actual : (prefixRun edge.entry.key.constraint input before.checked.operations).1 = .ok (some output)) :
    FixedPayload output.payload := by
  obtain ⟨result,done,_,_,_,fixed⟩ := SourceCurrentEqualityOperationFixed.inherited_prefix
    edge.entry.key.constraint input before.checked.operations good.checked.operations inputs.1
    (good.checked.fields edge.entry.key edge inputs.2)
  have same := Option.some.inj (Except.ok.inj (done.symm.trans actual))
  exact same ▸ fixed

private theorem descend_le (input : EqValue) (index : Nat) (before : Caller width)
    (good : Good before) (known : EqReady before.checked.operations.constraints input) :
    pathHeight (SourceCurrentAllocatedPartialGraph.descend before input index).1 ≤ pathHeight input := by
  cases input with
  | contradiction => exact Nat.le_refl _
  | live identity records =>
    cases records with
    | nil => exact Nat.le_refl _
    | cons first rest =>
      exact Nat.le_of_lt (SourceCurrentOuterInheritedDescent.descend_lt identity (first :: rest) index _
        good.checked.operations known (by intro impossible; cases impossible))

private theorem descend_fixed (input : EqValue) (index : Nat) (before : Caller width)
    (good : Good before) (known : EqReady before.checked.operations.constraints input)
    (fixed : FixedPayload input.payload) :
    FixedPayload (SourceCurrentAllocatedPartialGraph.descend before input index).1.payload :=
  (SourceCurrentEqualityOperationFixed.descend input index before.checked.operations good.checked.operations known fixed).2.2.2

variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem fixed_step (actual : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (fixed : FixedPayload (inherited first).payload) :
    FixedPayload (inherited last).payload := by
  cases actual with
  | node_evaluate started =>
      have same := owner_eq good inputs started
      simpa only [inherited,same] using fixed
  | body_rows | rows_edge | rows_tail | children_walk | walk_tail => exact fixed
  | descendants_children actual => exact prefix_fixed good inputs actual
  | walk_head => exact descend_fixed _ _ _ good inputs.1 fixed

private theorem fixed_reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (fixed : FixedPayload (inherited first).payload) :
    FixedPayload (inherited last).payload := by
  induction actual with
  | refl => exact fixed
  | snoc earlier last ih =>
      have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
      exact fixed_step last current.1 current.2 ih

private def DispatchFixed (phase : Phase width) : Prop :=
  match phase with
  | .node _ request _ => FixedPayload request.inherited.payload
  | .children _ input _ _ | .walk _ input _ _ _ => FixedPayload input.payload
  | _ => True

private theorem dispatch_step (actual : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (fixed : DispatchFixed first) : DispatchFixed last := by
  cases actual with
  | node_evaluate | body_rows | rows_edge | rows_tail => trivial
  | descendants_children actual => exact prefix_fixed good inputs actual
  | children_walk | walk_tail => exact fixed
  | walk_head => exact descend_fixed _ _ _ good inputs.1 fixed

private theorem dispatch_reached (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (fixed : DispatchFixed first) : DispatchFixed last := by
  induction actual with
  | refl => exact fixed
  | snoc earlier last ih =>
      have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
      exact dispatch_step last current.1 current.2 ih

private def Rise (g s r e p h m c n budget : Nat) (first last : Phase width) : Prop :=
  ∃ fuel input edge before output,
    Reached g s r e p h m c n budget first (.descendants fuel input edge before) ∧
    (prefixRun edge.entry.key.constraint input before.checked.operations).1 = .ok (some output) ∧
    Reached g s r e p h m c n budget
      (.children fuel output edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge input)) last ∧
    pathHeight input < pathHeight output

private theorem rise_suffix (rise : Rise g s r e p h m c n budget first middle)
    (later : Reached g s r e p h m c n budget middle last) : Rise g s r e p h m c n budget first last := by
  obtain ⟨fuel,input,edge,before,output,past,actual,remaining,increase⟩ := rise
  exact ⟨fuel,input,edge,before,output,past,actual,remaining.trans later,increase⟩

private theorem step_rise_or_le (actual : Step g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) :
    Rise g s r e p h m c n budget first last ∨ pathHeight (inherited last) ≤ pathHeight (inherited first) := by
  cases actual with
  | node_evaluate started =>
      have same := owner_eq good inputs started
      exact Or.inr (by simp only [inherited,same,Nat.le_refl])
  | body_rows | rows_edge | rows_tail | children_walk | walk_tail => exact Or.inr (Nat.le_refl _)
  | descendants_children actual =>
      rename_i input output fuel before edge
      by_cases increase : pathHeight input < pathHeight output
      · exact Or.inl ⟨_,_,_,_,_,.refl _,actual,.refl _,increase⟩
      · exact Or.inr (Nat.le_of_not_gt increase)
  | walk_head => exact Or.inr (descend_le _ _ _ good inputs.1)

private theorem rise_or_le (actual : Reached g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) :
    Rise g s r e p h m c n budget first last ∨ pathHeight (inherited last) ≤ pathHeight (inherited first) := by
  induction actual with
  | refl => exact Or.inr (Nat.le_refl _)
  | snoc earlier last ih =>
      have current := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
      rcases step_rise_or_le last current.1 current.2 with rise | decreases
      · obtain ⟨fuel,input,edge,before,output,past,actual,remaining,increase⟩ := rise
        exact Or.inl ⟨fuel,input,edge,before,output,earlier.trans past,actual,remaining,increase⟩
      · rcases ih with rise | earlierLe
        · exact Or.inl (rise_suffix rise (.snoc (.refl _) last))
        · exact Or.inr (Nat.le_trans decreases earlierLe)

/-- The actual earlier row prefix gains height and has a nonempty effective own field. -/
def HeightGain (g s r e p h m c n budget : Nat) (first last : Phase width) : Prop :=
  ∃ fuel input edge before output,
    Reached g s r e p h m c n budget first (.descendants fuel input edge before) ∧
    (prefixRun edge.entry.key.constraint input before.checked.operations).1 = .ok (some output) ∧
    Reached g s r e p h m c n budget
      (.children fuel output edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge input)) last ∧
    Good before ∧ Inputs (.descendants fuel input edge before) ∧
    FixedPayload input.payload ∧ FixedPayload output.payload ∧
    pathHeight input < pathHeight output ∧
    SourceCompactGuards.sourceEqualities edge.entry.key.constraint ≠ some [] ∧
    ∃ own,
      (SourceCurrentConjunctionEquality.accessor edge.entry.key.constraint before.checked.operations).1 = .ok (some own) ∧
      (SourceEqualityConstraintMemoAllocation.combine input own
        (SourceCurrentConjunctionEquality.accessor edge.entry.key.constraint before.checked.operations).2).1 = .ok output

private theorem rise_gain (rise : Rise g s r e p h m c n budget first last)
    (good : Good (caller first)) (inputs : Inputs first) (fixed : FixedPayload (inherited first).payload) :
    HeightGain g s r e p h m c n budget first last := by
  obtain ⟨fuel,input,edge,before,output,past,actual,remaining,increase⟩ := rise
  have current := SourceCurrentOuterPrefixInvariants.reached past good inputs
  have inputFixed := fixed_reached past good inputs fixed
  have outputFixed := prefix_fixed current.1 current.2 actual
  have field := current.1.checked.fields edge.entry.key edge current.2.2
  have nonempty : SourceCompactGuards.sourceEqualities edge.entry.key.constraint ≠ some [] := by
    intro emptyOwn
    cases input with
    | contradiction => simp only [SourceCurrentAllocatedInheritedPrefix.run_contradiction] at actual; cases actual; omega
    | live identity records =>
      have plain := SourceCurrentNormalizedInheritedPrefix.plain edge.entry.key.constraint identity records before.checked.operations
        current.1.checked.operations current.2.1 field emptyOwn (inputFixed records rfl)
      have same := Option.some.inj (Except.ok.inj (actual.symm.trans plain.1))
      rw [same] at increase
      omega
  cases input with
  | contradiction => simp only [SourceCurrentAllocatedInheritedPrefix.run_contradiction] at actual; cases actual; omega
  | live identity records =>
    obtain ⟨own,loaded,_,_,_,_,_⟩ := SourceCurrentConjunctionEquality.accessor_correct
      edge.entry.key.constraint before.checked.operations current.1.checked.operations field
    have combined : (SourceEqualityConstraintMemoAllocation.combine (.live identity records) own
        (SourceCurrentConjunctionEquality.accessor edge.entry.key.constraint before.checked.operations).2).1 = .ok output := by
      rw [SourceCurrentAllocatedInheritedPrefix.run_combine _ _ _ _ own loaded] at actual
      cases calculated : (SourceEqualityConstraintMemoAllocation.combine (.live identity records) own
          (SourceCurrentConjunctionEquality.accessor edge.entry.key.constraint before.checked.operations).2).1 with
      | error message => simp only [calculated,Except.map] at actual; cases actual
      | ok result =>
        have same := Option.some.inj (Except.ok.inj (by simpa only [calculated,Except.map] using actual))
        exact same ▸ calculated
    exact ⟨fuel,.live identity records,edge,before,output,past,actual,remaining,current.1,current.2,
      inputFixed,outputFixed,increase,nonempty,own,loaded,combined⟩

/-- A nested full-key return to a nonempty owner requires an actual intervening own-field height gain. -/
theorem collision {fuel next : Nat} {owner request : NodeRequest} {running after : Caller width}
    (actual : Reached g s r e p h m c n budget (.body fuel owner running) (.node next request after))
    (good : Good running) (inputs : NodeReady running owner)
    (nonempty : ∃ identity records, owner.inherited = .live identity records ∧ records ≠ [])
    (same : owner.key = request.key) :
    HeightGain g s r e p h m c n budget (.body fuel owner running) (.node next request after) := by
  have current := SourceCurrentOuterPrefixInvariants.reached actual good inputs
  have growth := SourceCurrentOuterExecutionGrowth.reached actual
  have ownerReady : EqReady after.checked.operations.constraints owner.inherited :=
    inputs.1.grows growth.constraint_growth
  have inheritedSame : owner.inherited = request.inherited :=
    SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _ current.1.checked.operations.constraints
      _ _ ownerReady current.2.1 (congrArg Prod.fst same)
  have fixed : FixedPayload owner.inherited.payload := by
    have atDispatch := dispatch_reached actual good inputs (by trivial)
    simpa only [DispatchFixed,← inheritedSame] using atDispatch
  have positive : 0 < pathHeight owner.inherited := by
    obtain ⟨identity,records,shape,known⟩ := nonempty
    rw [shape]
    exact SourceCurrentOuterInheritedDescent.positive identity records known (by simpa only [shape,SourceEqualityConstraintAllocation.Value.payload] using inputs.1.2)
  cases actual with
  | snoc earlier last =>
    cases last with
    | walk_head =>
      rename_i combined index value rest before
      have atWalk := SourceCurrentOuterPrefixInvariants.reached earlier good inputs
      have strict : pathHeight request.inherited < pathHeight combined := by
        cases combined with
        | contradiction => simp only [SourceCurrentAllocatedPartialGraph.descend,SourceEqualityConstraintMemoAllocation.descend] at inheritedSame; simp_all [pathHeight]
        | live identity records =>
          cases records with
          | nil => simp only [SourceCurrentAllocatedPartialGraph.descend,SourceEqualityConstraintMemoAllocation.descend] at inheritedSame; simp_all [pathHeight,EqualityModel.depth,EqualityModel.maxOn]
          | cons first rest =>
            exact SourceCurrentOuterInheritedDescent.descend_lt identity (first :: rest) index _
              atWalk.1.checked.operations atWalk.2.1 (by intro impossible; cases impossible)
      rcases rise_or_le earlier good inputs with rise | decreases
      · exact rise_gain (rise_suffix rise (.snoc (.refl _) .walk_head)) good inputs fixed
      · change pathHeight combined ≤ pathHeight owner.inherited at decreases
        rw [← inheritedSame] at strict
        omega

end MicroCFTA.SourceCurrentOuterInheritedGain
