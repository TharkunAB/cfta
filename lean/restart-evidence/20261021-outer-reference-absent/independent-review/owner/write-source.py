from pathlib import Path
import re
root = Path('/home/tritlo/Code/mcfta')
old = (root/'lean/MicroCFTA/SourceCurrentOuterParentFailure.lean').read_text()
body = old[old.index('private theorem all_failures'):old.index('/-- Every reported Parent fault')].rstrip()
body = body.replace('observation after failed', 'kind name handle after failed').replace('dispatch_step', 'cut_step')
body = re.sub(r'((?:_\s+)+)(headFailed|tailFailed|failed|childFailed|rowsFailed|bodyFailed)\)', r'\1_ _ \2)', body)
body = body.replace('          · exact ⟨fuel,inherited,original,rest,before,.refl _,edgeFailed⟩', '          · exact False.elim (edge_safe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ edgeFailed)')
body = body.replace('      | empty | union | reference => simp only [nodeBody] at failed; cases failed', '''      | empty | union => simp only [nodeBody] at failed; cases failed
      | reference actualName =>
        cases kind <;> simp only [nodeBody, diagnostic] at failed
        · cases failed
        · cases failed; exact ⟨fuel,inherited,.refl _⟩''')
body = body.replace('      | ready result | absent | busy => simp only [nodeCall,started] at failed; cases failed', '''      | ready result => simp only [nodeCall,started] at failed; cases failed
      | busy => cases kind <;> simp only [nodeCall,started,diagnostic] at failed <;> cases failed
      | absent =>
        cases kind <;> simp only [nodeCall,started,diagnostic] at failed
        · cases failed; exact ⟨fuel,request,before,.refl _,started⟩
        · cases failed''')
body = body.replace('split at failed <;> cases failed', 'split at failed <;> cases kind <;> simp only [diagnostic] at failed <;> cases failed')
head = '''import MicroCFTA.SourceCurrentOuterClosedInputs

/-!
# Reference and absent-node faults in actual outer execution

Each failure supplies its exact reached cut and unchanged failed caller.
Closed phase inputs exclude references. Valid node links exclude absence.
-/
namespace MicroCFTA.SourceCurrentOuterReferenceAbsent
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached NodeValid)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "caller" => SourceCurrentOuterActiveAncestry.caller

private theorem not_absent (request : NodeRequest) (before : Caller width) (valid : NodeValid before) :
    (beginNode request before).2.1 ≠ .absent := by
  cases published : before.nodeResults.table request.key with
  | none => simp only [beginNode,FlatMemoThunk.lookupOrInsert,published,FlatMemoThunk.demand,put]; simp
  | some handle =>
    obtain ⟨⟨original,status⟩,present,_key⟩ := valid.linked request.key handle published
    cases status <;> simp only [beginNode,FlatMemoThunk.lookupOrInsert,published,FlatMemoThunk.demand,present] <;> simp

private theorem erase_failed {actual : Outcome A width}
    (failed : actual.bind (fun _ after => .done () after) = .failed fault after) : actual = .failed fault after := by
  cases actual <;> simp_all [Outcome.bind]

private theorem bind_failed (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (failed : first.bind next = .failed fault after) :
    first = .failed fault after ∨ ∃ value middle, first = .done value middle ∧ next value middle = .failed fault after := by
  cases first with
  | failed => simp only [Outcome.bind] at failed; cases failed; exact Or.inl rfl
  | done value middle => exact Or.inr ⟨value,middle,rfl,failed⟩

private def diagnostic (kind : Bool) (name : InternedBinderProtocol.Reference) (handle : Nat) : Fault width :=
  if kind then .unexpectedReference name else .nodeMemo handle .absent

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private def Cut (g s r e p h m c n budget : Nat) (entry : Phase width)
    (kind : Bool) (name : InternedBinderProtocol.Reference) (handle : Nat) (after : Caller width) : Prop :=
  if kind then ∃ fuel inherited, Reached g s r e p h m c n budget entry (.body fuel ⟨inherited,.reference name⟩ after)
  else ∃ fuel request before, Reached g s r e p h m c n budget entry (.node fuel request before) ∧
    beginNode request before = (handle,.absent,after)

private theorem cut_step (first : Step g s r e p h m c n budget entry middle)
    (last : Cut g s r e p h m c n budget middle kind name handle after) :
    Cut g s r e p h m c n budget entry kind name handle after := by
  cases kind <;> dsimp only [Cut] at last ⊢
  · obtain ⟨fuel,request,before,later,started⟩ := last
    exact ⟨fuel,request,before,(Reached.snoc (.refl _) first).trans later,started⟩
  · obtain ⟨fuel,inherited,later⟩ := last
    exact ⟨fuel,inherited,(Reached.snoc (.refl _) first).trans later⟩

private theorem edge_safe (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) (kind : Bool) (name : InternedBinderProtocol.Reference) (handle : Nat) (after : Caller width) :
    edgeCall fuel g s r e p h m c n budget request before ≠ .failed (diagnostic kind name handle) after := by
  intro failed
  rcases started : beginEdge request before with ⟨chosen,action,running⟩
  cases action with
  | ready result | busy | absent => cases kind <;> simp only [edgeCall,started,diagnostic] at failed <;> cases failed
  | evaluate original =>
    simp only [edgeCall,started,edgeBody] at failed
    split at failed <;> simp only [Outcome.bind] at failed <;> cases kind <;> simp only [diagnostic] at failed <;> cases failed
'''
motives = []
for kind, args, worker_args in [
 ('Node', 'request (before : Caller width)', 'request before'),
 ('Body', 'request (before : Caller width)', 'request before'),
 ('Rows', 'inherited values (before : Caller width)', 'inherited values before'),
 ('Descendants', 'inherited value (before : Caller width)', 'inherited value before'),
 ('Children', 'combined values (before : Caller width)', 'combined values before'),
 ('Walk', 'combined index values (before : Caller width)', 'combined index values before'),
]:
 worker={'Node':'nodeCall','Body':'nodeBody'}.get(kind, kind.lower())
 phase={'Node':'node','Body':'body'}.get(kind,kind.lower())
 motives.append(f'''private def {kind}FailureAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget {args} kind name handle after,
  {worker} fuel g s r e p h m c n budget {worker_args} = .failed (diagnostic kind name handle) after →
  Cut g s r e p h m c n budget (.{phase} fuel {worker_args}) kind name handle after
''')
cut = '''private theorem failure_cut {g s r e p h m c n budget : Nat} {first : Phase width}
    {kind : Bool} {name : InternedBinderProtocol.Reference} {handle : Nat} {after : Caller width}
    (failed : SourceCurrentOuterActiveAncestry.run g s r e p h m c n budget first = .failed (diagnostic kind name handle) after) :
    Cut g s r e p h m c n budget first kind name handle after := by
  cases first with
  | node fuel request before => exact (all_failures fuel).1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | body fuel request before => exact (all_failures fuel).2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | rows fuel inherited values before => exact (all_failures fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | descendants fuel inherited value before => exact (all_failures fuel).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | children fuel combined values before => exact (all_failures fuel).2.2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)
  | walk fuel combined index values before => exact (all_failures fuel).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (erase_failed failed)

variable {bits : Nat}

/-- Closed initial inputs and valid node links exclude both literal diagnostics at their actual reached cuts. -/
'''
public=(Path('/tmp/mcfta-outer-reference-absent-next-plan/proposed-signature.lean.txt')).read_text().rstrip()
end=''' := by
  constructor
  · intro failed
    obtain ⟨fuel,inherited,actual⟩ := failure_cut (kind := true) failed
    have closedAt := (SourceCurrentOuterClosedInputs.reached formulas solver seed actual initial frame fits known inputs room
      normal supported causal merged positiveMemo origins stored closed).2
    change [name] = [] at closedAt
    cases closedAt
  · intro failed
    obtain ⟨fuel,request,before,actual,started⟩ := failure_cut (kind := false) failed
    have valid : NodeValid (caller first) :=
      FlatMemoThunk.Valid.keyMap _ _ _ _ initial.sound.valid.nodes (fun _ _ linked => linked.2)
    exact not_absent request before (actual.valid valid) (congrArg (fun result => result.2.1) started)

end MicroCFTA.SourceCurrentOuterReferenceAbsent
'''
source = head+'\n'+''.join(motives)+'\n'+body+'\n\n'+cut+public+end
lines=len(source.splitlines())
print(f'Draft source: {lines} lines')
if lines>=250:
 print('STOP: over prelaunch source limit; proposed source not written.')
 Path('/tmp/mcfta-outer-reference-absent-proof/source-budget.txt').write_text(str(lines)+'\n')
else:
 Path('/tmp/mcfta-outer-reference-absent-proof/SourceCurrentOuterReferenceAbsent.lean').write_text(source)
