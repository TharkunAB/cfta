import MicroCFTA.SourceCurrentEnabledCheckPost
import MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
import MicroCFTA.SourcePruningEnumerationIncomingNode

/-! Actual incoming returns that permit continuation supply their caller Post. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingPost
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
variable {bits : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- Every actual incoming `.ok` return derives Post and its saved query memo. -/
theorem incoming_ok_post (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Core)
    (checkEmpty : Bool) (r n p h target : Nat) (incoming : Node) (scs : List Suspended) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits profile caller.checked) (room : Room bits profile) :
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs memos.query
    match actual.1 with
    | .ok _ => ∃ next final, Post formulas solver next caller actual.2.1 final ∧ final.query = actual.2.2.1
    | .error _ => True := by
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  have unchanged : ∃ next final, Post formulas solver next caller caller final ∧ final.query = memos.query :=
    ⟨inventory, memos, Post.refl initial, rfl⟩
  cases rootRead : UnionFind.findRoot r before.representatives target with
  | none => simpa [SourcePruningEnumerationIncomingNode.run, rootRead] using unchanged
  | some found =>
      cases oldRead : before.values[found.representative]? with
      | none => simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead] using unchanged
      | some oldValue => cases oldValue with
        | eliminated => simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead] using unchanged
        | enumerated fragment => simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead] using unchanged
        | unenumerated oldNode oldScs =>
          cases oldNode with
          | none =>
              cases encoded : encodeNode incoming <;>
                simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead, encoded] using unchanged
          | some oldHandle =>
              obtain ⟨old, oldLookup, oldAvailable, oldClosed⟩ := realized found.representative oldHandle oldScs oldRead
              have bounds := fits.room room
              simp only [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead, oldLookup]
              cases actual : SourceEqualityNativeDemand.execute n
                  (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old)) caller.checked with
              | done query queried =>
                obtain ⟨next, _source, _roots, receipt, queryPost⟩ := SourceCurrentAllocatedTargetQuery.raw_done_caller_initial
                  bits n formulas solver inventory caller queried incoming old query memos initial
                  available oldAvailable closed oldClosed bounds.1 bounds.2.1 bounds.2.2 actual
                cases checkEmpty with
                | false =>
                    have returned : ∃ destination final, Post formulas solver destination caller
                        (SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge) final ∧
                        final.query = memos.query := ⟨next, memos, queryPost, rfl⟩
                    cases encoded : encodeNode query <;>
                      simpa [encoded, SourceCurrentAllocatedPartialState.advance,
                        SourceCurrentAllocatedConjunctionWorker.Outcome.state,
                        SourceCurrentAllocatedConjunctionWorker.Outcome.memo] using returned
                | true =>
                    have checkedPost := SourceCurrentEnabledCheckPost.check_post formulas solver next p h query
                      (SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge)
                      memos queryPost.context receipt.available receipt.closed
                    dsimp only [SourceCurrentAllocatedPartialState.advance] at checkedPost
                    cases observed : SourcePruningEnumerationEnabledEmpty.check p h query queried caller.fourth memos.query with
                    | mk outcome savedQueries =>
                        simp only [observed] at checkedPost
                        cases outcome with
                        | done answer checkedAfter saved =>
                            have combined := queryPost.trans checkedPost
                            have returned : ∃ destination final, Post formulas solver destination caller
                                (SourceCurrentAllocatedPartialState.advance caller checkedAfter saved caller.merge) final ∧
                                final.query = savedQueries := by
                              refine ⟨next, {memos with query := savedQueries}, ?_, rfl⟩
                              simpa [SourceCurrentAllocatedPartialState.advance,
                                SourceCurrentAllocatedConjunctionWorker.Outcome.state,
                                SourceCurrentAllocatedConjunctionWorker.Outcome.memo] using combined
                            cases encoded : encodeNode (if answer then .empty else query) <;>
                              simpa [observed, encoded, SourceCurrentAllocatedPartialState.advance,
                                SourceCurrentAllocatedConjunctionWorker.Outcome.state,
                                SourceCurrentAllocatedConjunctionWorker.Outcome.memo] using returned
                        | failed fault checkedAfter saved => simp [observed]
              | yielded control current => trivial
              | failed fault current => trivial
              | constraintError message current => trivial
              | blocked reason control current => trivial

end MicroCFTA.SourceCurrentIncomingPost
