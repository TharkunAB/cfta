import MicroCFTA.SourceCurrentAllocatedEqualityAbsorption
import MicroCFTA.SourceCurrentOuterRowFieldOrigins

/-!
# New effective equalities at actual inherited height gains

A fixed inherited payload absorbs every covered own class. An actual
strict height gain therefore adds a distinct path pair outside the old
inherited components. The actual owner and original row receipts remain
exact. This result does not exclude a busy collision or prove termination.
-/
namespace MicroCFTA.SourceCurrentOuterEffectiveGain
open Cache EqualityNormalize EqualitySaturation
open InternedConstructorTemplates InternedEdgeResidency
open SourceEqualityClassOrder
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Reached)
open SourceCurrentEqualityOperationFixed (FixedPayload)
open SourceCurrentOuterInheritedDescent (pathHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "prefixRun" => SourceCurrentAllocatedInheritedPrefix.run

/-- One effective own class contains a distinct pair absent from the inherited components. -/
def NewPair (original : Guard) (input : EqValue) : Prop :=
  ∃ classes paths left right,
    SourceCompactGuards.sourceEqualities original = some classes ∧ paths ∈ classes ∧
    left ∈ paths ∧ right ∈ paths ∧ left ≠ right ∧
    inSame ((SourceEqualityInheritedPayload.classes input.payload).getD []) left right = false

private theorem covered_of_pairs (inherited own : Constraints)
    (disjoint : inherited.Pairwise (fun left right => overlap left right = false))
    (active : Active own)
    (pairs : ∀ paths ∈ own, ∀ left ∈ paths, ∀ right ∈ paths, left ≠ right →
      inSame inherited left right = true) : Covers own inherited := by
  intro paths member
  obtain ⟨left,first,right,second,different⟩ := active paths member
  obtain ⟨component,present,firstMember,_⟩ :=
    (inSame_correct _ _ _).mp (pairs paths member left first right second different)
  refine ⟨component,present,?_⟩
  intro path included
  by_cases same : left = path
  · exact same ▸ firstMember
  · obtain ⟨other,known,atLeft,atPath⟩ :=
      (inSame_correct _ _ _).mp (pairs paths member left first path included same)
    have equal := components_equal inherited disjoint component other present known left firstMember atLeft
    exact equal.symm ▸ atPath

/-- A literal successful fixed-input prefix with strict height gain adds a new effective pair. -/
theorem inherited_prefix {original : Guard} {input output : EqValue} {before : Operations}
    (actual : (prefixRun original input before).1 = .ok (some output))
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (ready : EqReady before.constraints input)
    (field : SourceCurrentConjunctionEquality.FieldAvailable before original)
    (fixed : FixedPayload input.payload) (increase : pathHeight input < pathHeight output) :
    NewPair original input := by
  cases input with
  | contradiction =>
      simp only [SourceCurrentAllocatedInheritedPrefix.run_contradiction] at actual
      cases actual
      change 0 < 0 at increase
      omega
  | live identity records =>
      obtain ⟨own,loaded,_,ownReady,classes,_,_⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before valid field
      cases own with
      | contradiction =>
          rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before _ loaded] at actual
          simp only [SourceEqualityConstraintMemoAllocation.combine,Except.map] at actual
          cases actual
          change pathHeight (.live identity records) < 0 at increase
          omega
      | live ownIdentity ownRecords =>
          have compiled : SourceCompactGuards.sourceEqualities original = some (ownRecords.map Record.paths) := classes.symm
          apply Classical.byContradiction
          intro absent
          have pairs : ∀ paths ∈ ownRecords.map Record.paths, ∀ left ∈ paths, ∀ right ∈ paths,
              left ≠ right → inSame (records.map Record.paths) left right = true := by
            intro paths member left first right second different
            cases found : inSame (records.map Record.paths) left right with
            | false =>
                exact False.elim (absent ⟨ownRecords.map Record.paths,paths,left,right,
                  compiled,member,first,second,different,found⟩)
            | true => rfl
          have active : Active (ownRecords.map Record.paths) := by
            intro paths member
            obtain ⟨record,present,rfl⟩ := List.mem_map.mp member
            exact (ownReady.2 ownRecords rfl record present).2.2
          have covered := covered_of_pairs _ _
            (SourceCurrentEqualityNormalizationFixed.invariants _ (fixed records rfl)).2.2.1 active pairs
          have absorbed := SourceCurrentAllocatedEqualityAbsorption.inherited_prefix original identity records
            (ownRecords.map Record.paths) before valid ready field compiled (fixed records rfl) covered
          have same := Option.some.inj (Except.ok.inj (actual.symm.trans absorbed.1))
          rw [same] at increase
          omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- An actual owner gain retains its exact original row and a newly added effective pair. -/
theorem gain_source {g s r e p h m c n budget ownerFuel : Nat} {owner : NodeRequest}
    {running : Caller width} {last : Phase width}
    (gain : SourceCurrentOuterInheritedGain.HeightGain g s r e p h m c n budget (.body ownerFuel owner running) last)
    (good : Good running) (inputs : NodeReady running owner)
    (origins : SourceCurrentOuterRowFieldOrigins.Origins running) :
    ∃ fuel input edge before output original rest start,
      Reached g s r e p h m c n budget (.body ownerFuel owner running)
        (.rows (fuel + 1) input (original :: rest) start) ∧
      edgeCall fuel g s r e p h m c n budget ⟨input,original⟩ start = .done edge before ∧
      edge.entry.key.symbol = original.entry.key.symbol ∧
      edge.entry.key.constraint = original.entry.key.constraint ∧
      (prefixRun edge.entry.key.constraint input before.checked.operations).1 = .ok (some output) ∧
      Reached g s r e p h m c n budget
        (.children fuel output edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge input)) last ∧
      Good before ∧ Inputs (.descendants fuel input edge before) ∧
      FixedPayload input.payload ∧ FixedPayload output.payload ∧ pathHeight input < pathHeight output ∧
      (∃ classes, SourceCompactGuards.sourceEqualities original.entry.key.constraint = some classes ∧ classes ≠ []) ∧
      NewPair original.entry.key.constraint input := by
  obtain ⟨fuel,input,edge,before,output,original,rest,start,past,completed,symbol,guard,
    actual,remaining,current,known,inputFixed,outputFixed,increase,nonempty⟩ :=
      SourceCurrentOuterRowFieldOrigins.gain_source gain good inputs origins
  have fresh := inherited_prefix actual current.checked.operations known.1
    (current.checked.fields _ _ known.2) inputFixed increase
  refine ⟨fuel,input,edge,before,output,original,rest,start,past,completed,symbol,guard,
    actual,remaining,current,known,inputFixed,outputFixed,increase,nonempty,?_⟩
  simpa only [guard] using fresh

/-- An actual initial busy fault yields the same owner and exact effective original-row gain. -/
theorem initial_busy {g s r e p h m c n budget handle : Nat} (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (fuel : Nat) (request : NodeRequest) (good : SourceCurrentNativeOperationHeap.Good checked)
    (stored : SourceCurrentMemoMergeEffects.Stored checked.native.machine.heap memo)
    (probes : InternedFreshOrdinaryProbeHeap.Heap checked.native.machine.heap)
    (ready : EqReady checked.operations.constraints request.inherited)
    (available : InternedProbeProvenance.Available checked.native.machine.heap request.value)
    {after : Caller width}
    (actual : nodeCall fuel g s r e p h m c n budget request
      (SourceCurrentAllocatedPartialState.initial checked memo fourth) = .failed (.nodeMemo handle .busy) after) :
    ∃ next candidate,
      Good after ∧ NodeReady after candidate ∧ SourceCurrentOuterRowFieldOrigins.Origins after ∧
      Reached g s r e p h m c n budget
        (.node fuel request (SourceCurrentAllocatedPartialState.initial checked memo fourth)) (.node next candidate after) ∧
      beginNode candidate after = (handle,.busy,after) ∧
      after.nodeResults.cells handle = some ⟨candidate,.evaluating⟩ ∧
      ∀ identity records, candidate.inherited = .live identity records → records ≠ [] →
        ∃ ownerFuel original entered running,
          Reached g s r e p h m c n budget
            (.node fuel request (SourceCurrentAllocatedPartialState.initial checked memo fourth)) (.node ownerFuel original entered) ∧
          beginNode original entered = (handle,.evaluate candidate,running) ∧
          SourceCurrentOuterRowFieldOrigins.GainSource g s r e p h m c n budget
            (.body ownerFuel candidate running) (.node next candidate after) ∧
          ∃ gainFuel input edge before output source rest start,
            Reached g s r e p h m c n budget (.body ownerFuel candidate running)
              (.rows (gainFuel + 1) input (source :: rest) start) ∧
            edgeCall gainFuel g s r e p h m c n budget ⟨input,source⟩ start = .done edge before ∧
            edge.entry.key.symbol = source.entry.key.symbol ∧
            edge.entry.key.constraint = source.entry.key.constraint ∧
            (prefixRun edge.entry.key.constraint input before.checked.operations).1 = .ok (some output) ∧
            Reached g s r e p h m c n budget
              (.children gainFuel output edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge input))
              (.node next candidate after) ∧
            Good before ∧ Inputs (.descendants gainFuel input edge before) ∧
            FixedPayload input.payload ∧ FixedPayload output.payload ∧ pathHeight input < pathHeight output ∧
            NewPair source.entry.key.constraint input := by
  obtain ⟨next,candidate,current,known,origins,past,busy,present,gains⟩ :=
    SourceCurrentOuterRowFieldOrigins.initial_busy checked memo fourth fuel request good stored probes ready available actual
  refine ⟨next,candidate,current,known,origins,past,busy,present,?_⟩
  intro identity records shape nonempty
  obtain ⟨ownerFuel,original,entered,running,earlier,started,gain⟩ := gains identity records shape nonempty
  refine ⟨ownerFuel,original,entered,running,earlier,started,gain,?_⟩
  obtain ⟨gainFuel,input,edge,before,output,source,rest,start,earlier,completed,symbol,guard,
    prefixDone,remaining,current,known,inputFixed,outputFixed,increase,_nonempty⟩ := gain
  have fresh := inherited_prefix prefixDone current.checked.operations known.1
    (current.checked.fields _ _ known.2) inputFixed increase
  refine ⟨gainFuel,input,edge,before,output,source,rest,start,earlier,completed,symbol,guard,
    prefixDone,remaining,current,known,inputFixed,outputFixed,increase,?_⟩
  simpa only [guard] using fresh

end MicroCFTA.SourceCurrentOuterEffectiveGain
