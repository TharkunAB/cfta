import MicroCFTA.SourceCurrentIncomingReadFrame
import MicroCFTA.SourceCurrentIncomingPost

/-! Literal singleton success derives its replacement and actual finish execution. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingFinishWitness
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationNativeBranchCompletion (CacheValid)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
private noncomputable def canonicalSymbol : DecidableEq Symbol := inferInstance
private noncomputable def canonicalNode : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
variable {bits : Nat}

/-- Original facts derive the actual replacement and finish certificate on literal singleton success. -/
theorem singleton_finish (symbolEquality : DecidableEq Symbol)
    (edgeEquality : DecidableEq (EdgeKey Symbol Constraint)) (nodeEquality : DecidableEq Node)
    (profile : Profile) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checkEmpty : Bool) (r n p h target : Nat) (incoming : Node) (scs oldScs : List Suspended)
    (oldNode : Option Nat) (rooted : IsRoot before.core.representatives target)
    (stored : before.core.values[target]? = some (.unenumerated oldNode oldScs)) :
    letI : DecidableEq Symbol := symbolEquality
    letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
    letI : DecidableEq Node := nodeEquality
    Context formulas solver inventory caller memos → CacheValid caller before →
    Available caller.checked.native.machine.heap incoming → incoming.free = [] →
    Fits profile caller.checked → Room bits profile →
    let actual := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before.core target incoming scs memos.query
    ∀ returned, actual.1 = .ok (some [.ok ((), returned)]) →
      ∃ replacement handle, Available actual.2.1.checked.native.machine.heap replacement ∧
        replacement.free = [] ∧ encodeNode replacement = some handle ∧
        ExceptT.run (SourcePruningEnumerationIncomingNode.finish target handle scs oldScs
          replacement actual.2.2.2) = [.ok ((), returned)] := by
  cases Subsingleton.elim symbolEquality canonicalSymbol
  cases Subsingleton.elim nodeEquality canonicalNode
  letI : DecidableEq Symbol := canonicalSymbol
  letI : DecidableEq (EdgeKey Symbol Constraint) := edgeEquality
  letI : DecidableEq Node := canonicalNode
  dsimp only
  intro initial valid available closed fits room returned observed
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := valid
  cases rootRead : UnionFind.findRoot r before.core.representatives target with
  | none => simp [SourcePruningEnumerationIncomingNode.run, rootRead] at observed
  | some found =>
      have rootSame := SourceCurrentIncomingOriginalRoot.original_target before.core.representatives
        r target rooted found rootRead
      cases oldNode with
      | none =>
          cases encoded : encodeNode incoming with
          | none =>
              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame, stored, encoded] at observed
          | some handle =>
              simp only [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame, stored, encoded] at observed ⊢
              refine ⟨incoming, handle, available, closed, encoded, ?_⟩
              exact Option.some.inj (Except.ok.inj observed)
      | some oldHandle =>
          obtain ⟨old, oldLookup, oldAvailable, oldClosed⟩ := realized target oldHandle oldScs stored
          have bounds := fits.room room
          cases nativeRead : SourceEqualityNativeDemand.execute n
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
              caller.checked with
          | done query queried =>
              obtain ⟨next, _source, _queryRoots, receipt, queryPost⟩ :=
                SourceCurrentAllocatedTargetQuery.raw_done_caller_initial bits n formulas solver inventory
                  caller queried incoming old query memos initial available oldAvailable closed oldClosed
                  bounds.1 bounds.2.1 bounds.2.2 nativeRead
              cases checkEmpty with
              | false =>
                  cases encoded : encodeNode query with
                  | none =>
                      simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                        stored, oldLookup, nativeRead, encoded] at observed
                  | some handle =>
                      simp only [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                        stored, oldLookup, nativeRead, Bool.false_eq_true, ite_false, encoded,
                        SourceCurrentAllocatedPartialState.advance] at observed ⊢
                      refine ⟨query, handle, ?_, receipt.closed, encoded, ?_⟩
                      · exact receipt.available
                      · exact Option.some.inj (Except.ok.inj observed)
              | true =>
                  have checkedPost := SourceCurrentEnabledCheckPost.check_post formulas solver next p h query
                    (SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge)
                    memos queryPost.context receipt.available receipt.closed
                  dsimp only [SourceCurrentAllocatedPartialState.advance] at checkedPost
                  have queryKept := checkedPost.effects.keeps.available query receipt.available
                  change Available (SourcePruningEnumerationEnabledEmpty.check p h query queried
                    caller.fourth memos.query).1.state.native.machine.heap query at queryKept
                  generalize checked : SourcePruningEnumerationEnabledEmpty.check p h query queried
                    caller.fourth memos.query = checkedResult at queryKept
                  rcases checkedResult with ⟨outcome, savedQueries⟩
                  cases outcome with
                  | failed fault checkedAfter saved =>
                      simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                        stored, oldLookup, nativeRead, checked] at observed
                  | done answer checkedAfter saved =>
                      have queryAvailable : Available checkedAfter.native.machine.heap query := queryKept
                      cases answer with
                      | false =>
                          cases encoded : encodeNode query with
                          | none =>
                              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                                stored, oldLookup, nativeRead, checked, encoded] at observed
                          | some handle =>
                              simp only [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                                stored, oldLookup, nativeRead, checked, ite_true, Bool.false_eq_true,
                                ite_false, encoded, SourceCurrentAllocatedPartialState.advance] at observed ⊢
                              refine ⟨query, handle, queryAvailable, receipt.closed, encoded, ?_⟩
                              exact Option.some.inj (Except.ok.inj observed)
                      | true =>
                          have rejectEmpty (handle : Nat) (core : Core) :
                              ExceptT.run (SourcePruningEnumerationIncomingNode.finish target handle
                                scs oldScs (.empty : Node) core) = [] := by rfl
                          cases encoded : encodeNode (.empty : Node) with
                          | none =>
                              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                                stored, oldLookup, nativeRead, checked, encoded] at observed
                          | some handle =>
                              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                                stored, oldLookup, nativeRead, checked, encoded, rejectEmpty] at observed
          | yielded control current =>
              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                stored, oldLookup, nativeRead] at observed
          | failed fault current =>
              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                stored, oldLookup, nativeRead] at observed
          | constraintError message current =>
              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                stored, oldLookup, nativeRead] at observed
          | blocked reason control current =>
              simp [SourcePruningEnumerationIncomingNode.run, rootRead, rootSame,
                stored, oldLookup, nativeRead] at observed

end MicroCFTA.SourceCurrentIncomingFinishWitness
