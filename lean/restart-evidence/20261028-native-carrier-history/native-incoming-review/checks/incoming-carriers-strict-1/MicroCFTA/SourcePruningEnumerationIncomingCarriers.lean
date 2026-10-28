import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
import MicroCFTA.SourcePruningEnumerationCarrierFrame

/-!
# Graph carriers at actual native incoming endpoints

The representative read retains every old carrier and stored reference.
An actual incoming write stores a SOME handle in the reached class.
The cached Empty branch has the same structural write without acceptance.
-/
namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationCompressionFrame
open EnumerationDependencies EnumerationCarriers EnumerationGraphReferences InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- The explicit incoming write retains old carriers and supplies the requested class. -/
theorem written_carriers
    (before after : Core) (uv target handle : Nat) (oldNode : Option Nat)
    (incomingScs oldScs : List Suspended)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (related : UnionFind.SameClass before.representatives uv target)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (shape : after = {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}) :
    UnionFind.Total after.representatives ∧ PreservesCarriers before after ∧
      ReferencesCarry after ∧ CarriesGraph after uv := by
  subst after
  have preserved : PreservesCarriers before
      {before with
        values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = target then
          (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
          else before.recursionAncestry other} :=
    set_graph_carriers before target (.unenumerated (some handle) (incomingScs ++ oldScs)) trivial
  have origin := setValue_origin target (.unenumerated (some handle) (incomingScs ++ oldScs))
    before {before with values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))}
    (by intro fragment same; cases same)
    ((EnumerationDriver.modify_success _ _ _).mpr rfl)
  have inside := (List.getElem?_eq_some_iff.mp stored).1
  refine ⟨total, preserved, references_transport before _ references preserved origin rfl, ?_⟩
  exact ⟨target, .unenumerated (some handle) (incomingScs ++ oldScs), related,
    by simp [inside], trivial⟩

private theorem finish_singleton_carriers
    {before returned : Core} {uv target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (related : UnionFind.SameClass before.representatives uv target)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      [.ok ((), returned)]) :
    UnionFind.Total returned.representatives ∧ PreservesCarriers before returned ∧
      ReferencesCarry returned ∧ CarriesGraph returned uv := by
  let written : Core :=
    {before with
      values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
      recursionAncestry := fun other => if other = target then
        (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
        else before.recursionAncestry other}
  have rawRun : ExceptT.run (finish target handle incomingScs oldScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  rw [rawRun] at observed
  have coreSame : written = returned := by
    split at observed
    · cases observed
    · exact (Prod.mk.inj (Except.ok.inj (List.cons.inj observed).1)).2
  exact written_carriers before returned uv target handle oldNode incomingScs oldScs
    total references related stored coreSame.symm

private theorem finish_reply_carriers
    {Fault : Type _} {before returned : Core} {uv target handle : Nat} {oldNode : Option Nat}
    {incomingScs oldScs : List Suspended} {replacement : Node}
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before)
    (related : UnionFind.SameClass before.representatives uv target)
    (stored : before.values[target]? = some (.unenumerated oldNode oldScs))
    (observed : (Except.ok (some (ExceptT.run
        (finish target handle incomingScs oldScs replacement before))) : Except Fault (Option Raw)) =
      .ok (some [.ok ((), returned)])) :
    UnionFind.Total returned.representatives ∧ PreservesCarriers before returned ∧
      ReferencesCarry returned ∧ CarriesGraph returned uv :=
  finish_singleton_carriers total references related stored (Option.some.inj (Except.ok.inj observed))

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual read retains carriers; a successful singleton also supplies its requested hole. -/
theorem run_carriers
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (total : UnionFind.Total before.representatives) (references : ReferencesCarry before) :
    (UnionFind.Total (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2.representatives ∧
      PreservesCarriers before (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2 ∧
      ReferencesCarry (run checkEmpty r n p h caller before target incoming incomingScs queries).2.2.2) ∧
      ∀ returned, (run checkEmpty r n p h caller before target incoming incomingScs queries).1 =
        .ok (some [.ok ((), returned)]) →
        UnionFind.Total returned.representatives ∧ PreservesCarriers before returned ∧
          ReferencesCarry returned ∧ CarriesGraph returned target := by
  generalize observedEq : run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reachedCaller, savedQueries, read⟩ := observed
  dsimp only
  unfold run at observedEq
  cases lookup : UnionFind.findRoot r before.representatives target with
  | none =>
      simp only [lookup, Prod.mk.injEq] at observedEq
      rcases observedEq with ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨⟨total, .refl before, references⟩, ?_⟩
      intro returned singleton
      simp at singleton
  | some found =>
      simp only [lookup] at observedEq
      have frame : Frame before {before with representatives := found.forest} := by
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        intro other root size
        exact UnionFind.findRoot_reaches_iff total lookup other root size
      have reached := (UnionFind.findRoot_correct r before.representatives target found lookup).2
        (UnionFind.findRoot_correct r before.representatives target found lookup).1
      have related : UnionFind.SameClass found.forest target found.representative :=
        UnionFind.sameClass_root reached
      repeat' first
        | (have readSame := congrArg (fun observed : _ × Caller width × Queries × Core => observed.2.2.2) observedEq
           have resultSame := congrArg Prod.fst observedEq
           dsimp only at readSame resultSame
           constructor
           · rw [← readSame]
             exact ⟨frame.total total, frame.carriers, frame.references references⟩
           · intro returned singleton
             rw [← resultSame] at singleton
             solve
             | simp at singleton
             | (obtain ⟨returnedTotal, preserved, returnedReferences, own⟩ :=
                  finish_reply_carriers (frame.total total) (frame.references references)
                    related (by assumption) singleton
                exact ⟨returnedTotal, frame.carriers.trans preserved, returnedReferences, own⟩))
        | split at observedEq
        | (dsimp only at observedEq; split at observedEq)

end MicroCFTA.SourcePruningEnumerationIncomingNode

namespace MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationCarriers EnumerationGraphReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An adapter candidate derives carriers from its actual incoming observation, including Empty. -/
theorem adapt_carriers
    {checkEmpty : Bool} {r n p h k : Nat} {caller reachedCaller : Caller width}
    {before after : Cached} {target : Nat} {incoming : Node} {incomingScs : List Suspended}
    {queries savedQueries : Queries} {read : Core} {raw : Raw}
    (total : UnionFind.Total before.core.representatives) (references : ReferencesCarry before.core)
    (observed : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h caller before.core
      target incoming incomingScs queries = (.ok (some raw), reachedCaller, savedQueries, read))
    (adapted : adapt reachedCaller.checked.native.machine.heap k target incomingScs before read raw = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core ∧ CarriesGraph after.core target := by
  have fields := SourcePruningEnumerationIncomingNode.run_carriers checkEmpty r n p h caller before.core
    target incoming incomingScs queries total references
  rw [observed] at fields
  dsimp only at fields
  obtain ⟨⟨readTotal, readPreserved, readReferences⟩, rows⟩ := fields
  cases raw with
  | nil =>
      simp only [adapt] at adapted
      split at adapted
      · rename_i oldNode oldScs stored
        simp only [Option.map_eq_some_iff] at adapted
        obtain ⟨written, _written, same⟩ := adapted
        subst after
        have related : UnionFind.SameClass read.representatives target target := by
          obtain ⟨root, size, path⟩ := readTotal target
          exact ⟨root, size, path, path⟩
        obtain ⟨writtenTotal, writtenPreserved, writtenReferences, own⟩ :=
          SourcePruningEnumerationIncomingNode.written_carriers read
            {read with
              values := read.values.set target (.unenumerated (some 0) (incomingScs ++ oldScs))
              recursionAncestry := fun other => if other = target then
                (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
                else read.recursionAncestry other}
            target target 0 oldNode incomingScs oldScs readTotal readReferences related stored rfl
        exact ⟨writtenTotal, readPreserved.trans writtenPreserved, writtenReferences, own⟩
      · cases adapted
  | cons row rest =>
      cases row with
      | error fault => simp only [adapt] at adapted; cases adapted
      | ok payload =>
          obtain ⟨⟨⟩, returned⟩ := payload
          cases rest with
          | nil =>
              have coreSame := adapt_singleton_core reachedCaller.checked.native.machine.heap k target
                incomingScs before after read returned adapted
              simpa only [coreSame] using rows returned rfl
          | cons next later => simp only [adapt] at adapted; cases adapted

/-- Every actual attached cache retains old carriers and supplies the requested target class. -/
theorem observed_cache_carriers
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (total : UnionFind.Total before.core.representatives) (references : ReferencesCarry before.core)
    (after : Cached)
    (candidate : (run checkEmpty r n p h k caller before target incoming incomingScs queries).2 = some after) :
    UnionFind.Total after.core.representatives ∧ PreservesCarriers before.core after.core ∧
      ReferencesCarry after.core ∧ CarriesGraph after.core target := by
  unfold run at candidate
  generalize original : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
    caller before.core target incoming incomingScs queries = observed at candidate
  obtain ⟨result, reached, saved, read⟩ := observed
  dsimp only at candidate
  cases result with
  | error fault => cases candidate
  | ok payload =>
      cases payload with
      | none => cases candidate
      | some raw => exact adapt_carriers total references original candidate

end MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
