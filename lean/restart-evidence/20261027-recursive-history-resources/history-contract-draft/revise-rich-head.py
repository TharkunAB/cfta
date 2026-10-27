from pathlib import Path
base=Path('/tmp/mcfta-recursive-history-resources-20261027/history-contract-draft');p=base/'SourcePruningEnumerationFiniteHistoryContract.lean';s=p.read_text()
marker='/-- Every operation tag retains its actual original resource inputs and reached callback input. -/'
receipt='''/-- The actual ordinary entry and completed head retain their full local source receipts. -/
def OrdinaryHistoryReceipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (metadata : Metadata Typing) (checkEmpty : Bool) (workFuel uv : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (fragment : Fragment) (reached : Caller (bits + 2)) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos) : Prop :=
  ∃ (entered : Cached) (handle : Nat) (scs : List Suspended) (decoded : Node)
    (edge : EdgeValue Symbol Constraint) (headSeed : Seed) (inherited : Nat)
    (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos) (headBound : Nat),
    Packet formulas solver inventory caller memos metadata before ∧
    ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap workFuel uv before.core) =
      [.ok ((uv, handle, scs, decoded), entered.core)] ∧
    Packet formulas solver inventory caller memos metadata entered ∧
    Post formulas solver headInventory caller headCaller headMemos ∧
    SourcePruningEnumerationCapturedEdge.run checkEmpty workFuel workFuel workFuel workFuel workFuel
      uv scs edge headCaller entered headMemos.query = some (.complete fragment reached returnedMemos.query after) ∧
    SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
      headInventory headCaller headMemos metadata entered checkEmpty uv scs edge headBound fragment reached
      returnedMemos.query after returnedInventory returnedMemos

'''
assert marker in s;s=s.replace(marker,receipt+marker,1)
a=s.index('  /-- The actual ordinary invocation reaches its own admitted false callback and recursive input. -/')
z=s.index('\n/-- Resource decoration retains the same actual operation path and output. -/',a)
ordinary='''  /-- The actual ordinary invocation retains entry, full head receipts and its admitted false callback. -/
  | ordinary {fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
        ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
        returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output}
      (admission : HistoryAdmission formulas solver inventory caller memos metadata before (fuel + 1) seed ceiling)
      (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
        stop order metadata formulas solver inventory workFuel uv caller before memos
        (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query))
      (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
          .narrowed checked prepared ordinaryCaller ordinaryMemos.query action (some narrowed)
            (some [.ok ((false, updated), rightCore)]) none)
      (prefixPost : Post formulas solver ordinaryInventory caller ordinaryCaller ordinaryMemos)
      (invocation : SourcePruningEnumerationHookInvocation.OrdinaryInvocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel uv edgesOf ordinaryCaller narrowed ordinaryMemos.query
          fragment headCaller returnedMemos.query headCache)
      (receipt : OrdinaryHistoryReceipt formulas solver updated checkEmpty workFuel uv ordinaryInventory
        ordinaryCaller ordinaryMemos narrowed fragment headCaller headCache returnedInventory returnedMemos)
      (callbackAdmission : RecursiveCallbackAdmission formulas solver returnedInventory headCaller returnedMemos updated
        headCache uv fragment fuel callbackSeed callbackCeiling)
      (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
        (.inl fragment) headCache.core) = [.ok ((false, recorded), callbackCore)])
      (tail : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        fuel returnedInventory headCaller returnedMemos recorded (EnumerationExpandableIndex.frame callbackCore headCache)
          callbackSeed callbackCeiling
          (SourcePruningEnumerationRestart.decision stop order recorded
            (EnumerationExpandableIndex.frame callbackCore headCache)) output) :
      ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
        (fuel + 1) inventory caller memos metadata before seed ceiling (some (.expand uv)) output
'''
s=s[:a]+ordinary+s[z:]
s=s.replace('| ordinary _ _ observed invocation _ _ callback _ ih => exact .ordinary observed invocation callback ih','| ordinary _ _ observed _ invocation _ _ callback _ ih => exact .ordinary observed invocation callback ih')
p.write_text(s);d=base/'revisions/v2';d.mkdir(exist_ok=True);(d/p.name).write_text(s)
print(p);print(len(s.splitlines()),len(s.encode()))
