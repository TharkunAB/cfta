import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassResources

namespace MicroCFTA.ClassResourceChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryClassResources
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "StableRun" => SourceCurrentAllocatedClassWorkerCompletion.StableRun
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An empty forest uses no bound or request and retains the whole checked state and Merge memo. -/
theorem empty_class_identity (record : SourceEqualityClassOrder.Record) (rows arity depth bound : Nat)
    (e p h m s n : Nat) (before : Checked width) (memo : Memo) :
    nodeBudget record rows arity 0 depth bound = 0 ∧ edgeBudget record rows arity 0 depth bound = 0 ∧
    SourceCurrentAllocatedClassWorker.runClass e p h m s n record [] before memo = .done [] before memo := by
  refine ⟨by simp [nodeBudget], by simp [edgeBudget], ?_⟩
  unfold SourceCurrentAllocatedClassWorker.runClass
  cases SourceCurrentAllocatedClassEditPlan.compiled record <;> rfl

/-- A second class captures the first actual output and uses its computed inventory and warm certificates. -/
theorem two_actual_classes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (first second : SourceEqualityClassOrder.Record)
    (firstCoherent : SourceEqualityClassOrder.Coherent first) (firstActive : EqualityNormalize.Nontrivial first.paths)
    (secondCoherent : SourceEqualityClassOrder.Coherent second) (secondActive : EqualityNormalize.Nontrivial second.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count firstDepth secondDepth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (firstPaths : ∀ path ∈ first.paths, path.length ≤ firstDepth)
    (secondPaths : ∀ path ∈ second.paths, path.length ≤ secondDepth) (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget first rows arity count firstDepth bound +
      nodeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget first rows arity count firstDepth bound +
      edgeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound ≤ 2 ^ (bits + 2)) :
    ∃ middleValues middle current next currentMemos results after saved last final requests,
      ∃ firstActual : Class first values before memo middleValues middle current,
      ∃ secondActual : Class second middleValues middle current results after saved,
        ClassReads formulas solver firstActual memos currentMemos ∧
        Receipt formulas solver next first values before memo middleValues middle current memos currentMemos ∧
        ClassReads formulas solver secondActual currentMemos final ∧
        Receipt formulas solver last second middleValues middle current results after saved currentMemos final ∧
        StableRun (fun e p h m s n => SourceCurrentAllocatedClassWorker.runClass e p h m s n
          first values before memo) middleValues middle current ∧
        StableRun (fun e p h m s n => SourceCurrentAllocatedClassWorker.runClass e p h m s n
          second middleValues middle current) results after saved ∧
        NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
        ChildrenShape (outputRows second (outputRows first rows count firstDepth bound) count secondDepth bound)
          (outputArity (outputArity arity)) results ∧
        results.length = values.length ∧ childrenHeight results ≤ bound ∧
        Trace before.native.machine.heap after.native.machine.heap requests ∧
        SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after ∧
        after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget first rows arity count firstDepth bound +
          nodeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound ∧
        after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget first rows arity count firstDepth bound +
          edgeBudget second (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound := by
  obtain ⟨middleValues, middle, current, next, currentMemos, firstRequests, firstActual, firstReads, firstReceipt,
    firstStable, firstNative, firstOutput, firstProfiles, middleProfile, _firstNarrow, firstLength, middleHeight,
    firstTrace, _firstNodes, _firstEdges, _middleCapacity, firstNodeSupply, firstEdgeSupply⟩ :=
    complete formulas solver inventory bits first firstCoherent firstActive values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count firstDepth bound profile lengthBound firstPaths heightBound
      (by omega) (by omega)
  obtain ⟨results, after, saved, last, final, secondRequests, secondActual, secondReads, secondReceipt,
    secondStable, lastNative, lastOutput, lastProfiles, resultProfile, _secondNarrow, secondLength, resultHeight,
    secondTrace, _secondNodes, _secondEdges, finalCapacity, secondNodeSupply, secondEdgeSupply⟩ :=
    complete formulas solver next bits second secondCoherent secondActive middleValues middle current firstReceipt.ready
      firstReceipt.admitted firstReceipt.available firstReceipt.stored firstProfiles firstNative firstOutput firstReceipt.covered
      currentMemos firstReceipt.globals.valid (outputRows first rows count firstDepth bound) (outputArity arity) count secondDepth bound
      middleProfile (by omega) secondPaths middleHeight (by omega) (by omega)
  exact ⟨middleValues, middle, current, next, currentMemos, results, after, saved, last, final,
    firstRequests ++ secondRequests, firstActual, secondActual, firstReads, firstReceipt, secondReads, secondReceipt,
    firstStable, secondStable, lastNative, lastOutput, lastProfiles, resultProfile,
    by omega, resultHeight, firstTrace.trans secondTrace, finalCapacity, by omega, by omega⟩

#print axioms empty_class_identity
#check @empty_class_identity
#print axioms two_actual_classes
#check @two_actual_classes
end MicroCFTA.ClassResourceChecks
