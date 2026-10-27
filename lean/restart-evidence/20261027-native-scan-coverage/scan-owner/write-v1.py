from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-native-scan-coverage-20261027');out=area/'scan-owner'
source=(repo/'lean/MicroCFTA/SourcePruningEnumerationNativeBranchResources.lean').read_text()
start=source.index('theorem complete_with_history_resources\n');end=source.index('/-- The resource interface',start)
old=source[start:end].rstrip();declaration,proof=old.split(' := by\n',1)
observer='''      ∀ (index : Nat) (chosen : EdgeValue Symbol Constraint),
        selectedEdges[index]? = some chosen →
        (∀ earlier ∈ selectedEdges.take index, arityAllows earlier.children.length scs = true →
          SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none) →
        ∀ (ambient : InternedGuardedLanguage.Env Symbol)
          (assignment : Nat → Language.Term Symbol),
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            assignment before.core →
          InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient chosen (assignment uv) →
          ∃ (headCaller : Caller (bits + 2)) (headInventory : Inventory) (headMemos : Memos)
            (branchCaller : Caller (bits + 2)) (branchQueries : Queries) (branchMemos : Memos)
            (branchInventory : Inventory) (afterCache : Cached)
            (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol),
            Post formulas solver headInventory caller headCaller headMemos ∧
            Post formulas solver branchInventory headCaller branchCaller branchMemos ∧
            branchMemos.query = branchQueries ∧
            processed[index]? = some (.complete fragment branchCaller branchQueries afterCache) ∧
            (∀ er en P H ek, p ≤ P → h ≤ H →
              SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
                uv scs chosen headCaller before headMemos.query =
                  some (.complete fragment branchCaller branchQueries afterCache)) ∧
            (∀ old < before.core.counter, extended old = assignment old) ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              extended before.core ∧
            Fragments.fill extended fragment = assignment uv ∧
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient branchCaller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              extended afterCache.core'''
declaration=declaration.replace('theorem complete_with_history_resources\n','theorem complete_with_history_resources_accepting\n',1)+' ∧\n'+observer
# Preserve the original proof and its full packet. Add only the new observer branches.
proof=proof.replace('      exact ⟨0, 0, 0, 0, 0, [],','      refine ⟨0, 0, 0, 0, 0, [],',1)
oldnil='''        (by intro index receipt found; cases found)⟩'''
newnil='''        (by intro index receipt found; cases found), ?_⟩
      intro index chosen found
      simp at found'''
assert proof.count(oldnil)==1;proof=proof.replace(oldnil,newnil)
proof=proof.replace('headRun, headPost, headQueries, admitted, headPending, headHistory, shape, headFits, headKnown⟩ :=','headRun, headPost, headQueries, admitted, headPending, headHistory, shape, headFits, headKnown, headAccepting⟩ :=',1)
proof=proof.replace('        head_complete_resources seed formulas','        head_complete_resources_accepting seed formulas',1)
proof=proof.replace('tailFits, tailKnown, tailResources⟩ :=','tailFits, tailKnown, tailResources, tailAccepting⟩ :=',1)
needle='''          (by simpa only [cost, SourcePruningEnumerationIncomingReservation.advance_add] using tailKnown), ?_⟩'''
assert proof.count(needle)==1;proof=proof.replace(needle,needle[:-2]+', ?_⟩',1)
# The append point precedes the original unsupported-head branch.
marker='''      · subst receipt
        refine ⟨r, n, p, h, k, [],'''
semantic='''        · intro index chosen found supported ambient assignment satisfied accepted
          cases index with
          | zero =>
              have chosenSame : edge = chosen := Option.some.inj found
              subst chosen
              obtain ⟨extended, fragment, afterCache, agree, originalSatisfied, completed, filled, afterSatisfied⟩ :=
                headAccepting ambient assignment satisfied accepted
              refine ⟨caller, inventory, memos, middleCaller, middleQueries, middleMemos, middleInventory,
                afterCache, extended, fragment, Post.refl initial, headPost, headQueries, ?_, ?_,
                agree, originalSatisfied, filled, afterSatisfied⟩
              · simpa only [List.getElem?_cons_zero] using congrArg (fun current => some current) completed
              · intro er en P H ek largeP largeH
                have first := headRun (tr + er) (tn + en) P H (tk + ek)
                  (Nat.le_trans (Nat.le_max_left _ _) largeP)
                  (Nat.le_trans (Nat.le_max_left _ _) largeH)
                rw [completed] at first
                simpa only [Nat.add_assoc] using first
          | succ index =>
              have tailFound : rest[index]? = some chosen := by
                simpa only [List.getElem?_cons_succ] using found
              have tailSupported : ∀ earlier ∈ rest.take index,
                  arityAllows earlier.children.length scs = true →
                  SourcePruningEnumerationConstraint.project earlier.entry.key.constraint ≠ none := by
                intro earlier member earlierAllowed
                exact supported earlier (by
                  simp only [List.take_succ_cons, List.mem_cons]
                  exact .inr member) earlierAllowed
              have middleSatisfied :=
                (SourcePruningEnumerationNativeLanguage.satisfies_keeps
                  (SourceEqualityPCSGuard.holds formulas solver) ambient
                  caller.checked.native.machine.heap middleCaller.checked.native.machine.heap before.core
                  (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                  assignment realized kept).mpr satisfied
              obtain ⟨chosenCaller, chosenInventory, chosenMemos, branchCaller, branchQueries,
                branchMemos, branchInventory, afterCache, extended, fragment,
                inputPost, branchPost, branchQuery, selectedReceipt, selectedRun,
                agree, oldSatisfied, filled, afterSatisfied⟩ :=
                tailAccepting index chosen tailFound tailSupported ambient assignment middleSatisfied accepted
              have originalSatisfied :=
                (SourcePruningEnumerationNativeLanguage.satisfies_keeps
                  (SourceEqualityPCSGuard.holds formulas solver) ambient
                  caller.checked.native.machine.heap middleCaller.checked.native.machine.heap before.core
                  (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                  extended realized kept).mp oldSatisfied
              refine ⟨chosenCaller, chosenInventory, chosenMemos, branchCaller, branchQueries,
                branchMemos, branchInventory, afterCache, extended, fragment,
                headPost.trans inputPost, branchPost, branchQuery, ?_, ?_, agree,
                originalSatisfied, filled, afterSatisfied⟩
              · simpa only [List.getElem?_cons_succ] using selectedReceipt
              · intro er en P H ek largeP largeH
                have last := selectedRun (r + er) (n + en) P H (k + ek)
                  (Nat.le_trans (Nat.le_max_right _ _) largeP)
                  (Nat.le_trans (Nat.le_max_right _ _) largeH)
                simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using last
'''
assert proof.count(marker)==1;proof=proof.replace(marker,semantic+marker,1)
unsupported='''          (by intro current member; cases member), .inr rfl, ?_, ?_, ?_, ?_⟩'''
assert proof.count(unsupported)==1;proof=proof.replace(unsupported,unsupported[:-2]+', ?_⟩',1)
proof+='''
        · intro index chosen found supported ambient assignment satisfied accepted
          cases index with
          | zero =>
              have chosenSame : edge = chosen := Option.some.inj found
              subst chosen
              obtain ⟨extended, fragment, afterCache, _agree, _originalSatisfied, impossible, _filled, _afterSatisfied⟩ :=
                headAccepting ambient assignment satisfied accepted
              cases impossible
          | succ index =>
              exact (supported edge (by
                simp only [List.take_succ_cons, List.mem_cons]
                exact .inl rfl) allowed projected).elim
'''
header='''import MicroCFTA.SourcePruningEnumerationNativeBranchResources
import MicroCFTA.SourcePruningEnumerationNativeHeadCoverage
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Constructive coverage at an actual ordered native alternative

The original resource induction retains the same captured enumeration cache.
A supported original prefix reaches the chosen indexed accepting edge.
Its actual input and output retain their full memo states and postconditions.
Later alternatives can still stop after that completed receipt.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeBranchCompletion
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationNativeBranches (advance)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Result" => SourcePruningEnumerationNativeBranches.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A supported prefix reaches the same chosen edge and constructs its actual satisfying receipt. -/
'''
result=header+declaration+' := by\n'+proof+'\nend MicroCFTA.SourcePruningEnumerationNativeBranchCompletion\n'
p=out/'drafts/v1/SourcePruningEnumerationNativeBranchCoverage.lean';p.write_text(result)
# Recover the entire old declaration by removing only the new observer/name.
recovered=declaration[:declaration.index(' ∧\n'+observer)].replace('theorem complete_with_history_resources_accepting\n','theorem complete_with_history_resources\n',1)
assert recovered==old.split(' := by\n',1)[0]
c=out/'contracts';c.mkdir(exist_ok=True);(c/'original-full-proposition.txt').write_text(recovered);(c/'recovered-full-proposition-v1.txt').write_text(recovered)
sha=lambda b:hashlib.sha256(b).hexdigest()
(c/'comparison-v1.json').write_text(json.dumps({'status':'EXACT','original_bytes':len(recovered.encode()),'original_sha256':sha(recovered.encode()),'draft_sha256':sha(result.encode()),'mapping':'Remove only appended semantic observer and reverse theorem-name accepting suffix; all original inputs/witnesses/flattened output retained byte exactly','compiler_status':'UNTESTED; Root owns all checks'},indent=2)+'\n')
print(p);print('lines',len(result.splitlines()),'bytes',len(result.encode()),'sha256',sha(result.encode()))
