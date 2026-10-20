from pathlib import Path
h=Path('/tmp/mcfta-native-nested-mu-capture-fixture');old=Path('/tmp/mcfta-native-compiled-terminal-generation-fixture')
for name in ['run-check.py','capped-worker.py']:
 s=(old/('terminal-mu-kernels-'+name)).read_text().replace('terminal-mu-kernels','captured-mu-kernels').replace('TERMINAL_MU_KERNELS','CAPTURED_MU_KERNELS')
 (h/('captured-mu-kernels-'+name)).write_text(s)
s=(old/'terminal-mu-kernels.lean').read_text().split('private theorem source_facts',1)[0]
s=s.replace('SourceCurrentNativeTerminalGeneration','SourceCurrentNativeCapturedMuOrigins').replace('CompiledTerminalMuGenerationFixture','NestedCapturedMuFixture').replace('128','1024')
s=s.replace('set_option maxRecDepth 100000','set_option maxRecDepth 100000\nset_option exponentiation.threshold 2048')
a=s.index('private def recursive');s=s[:a]+'''private def inner (label : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("rec",.top) top [.var 0],.mk (label,.top) top []])
private def recursive (label innerLabel : String) : Syntax Symbol Guard :=
  .binder false (.node [.mk ("outer",.top) top [.var 0,inner innerLabel],.mk (label,.top) top []])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("pair",.top) top [recursive "outerLeft" "innerLeft",recursive "outerRight" "innerRight"]]
private def built := InternedFreshOrdinaryConstruction.build expression [] (empty : Heap)
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap : Heap := built.state
private def left : Node := (children root)[0]?.getD .empty
private def right : Node := (children root)[1]?.getD .empty
private def allocatedOps := SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def before : Checked 1024 := ⟨initial 1024 machine,allocatedOps⟩
private def request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩
private def control : Control Node := .code (requestNode request.domain request.left request.right)
private def outerPair := SourceRecursiveIntersectionControl.pair
  (SourceRecursiveIntersectionControl.identity left).getD 0 (SourceRecursiveIntersectionControl.identity right).getD 0
private def locate : Nat → Nat → Control Node → Checked 1024 → Nat
  | 0, elapsed, _, _ => elapsed
  | remaining+1, elapsed, input, state =>
      let selected := match input with
        | .code (.optionalBinder pair _ _) => pair == outerPair
        | _ => false
      if selected then elapsed else
      match step input state with
        | .yielded next after => locate remaining (elapsed+1) next after
        | _ => elapsed
private def fuel := locate 128 0 control before
private def prefix := execute fuel control before
private def current : Checked 1024 := prefix.state
private def siteBody : Node := match prefix with
  | .yielded (.code (.optionalBinder _ bodyValue _)) _ => bodyValue | _ => .empty
private def siteNext : Node → Code Symbol Guard Node := match prefix with
  | .yielded (.code (.optionalBinder _ _ next)) _ => next | _ => .pure
private def captured : Node := (leaves siteBody)[1]?.getD .empty
private def entry : Interned InternedBinderProtocol.NodeKey := match captured with
  | .mu selected .. => selected | _ => ⟨0,.empty⟩
private def stored : Node := match captured with | .mu _ bodyValue _ _ => bodyValue | _ => .empty
private def depth : Node := match captured with | .mu _ _ probe _ => probe | _ => .empty
private def ordinary : Node := match captured with | .mu _ _ _ probe => probe | _ => .empty
private theorem built_done : built = .done root heap := by cbv
private theorem actual_prefix : prefix = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current := by cbv
private theorem found : (leaves siteBody)[1]? = some (.mu entry stored depth ordinary) := by cbv
private theorem new_capture : heap.nodeRecords entry.key = none ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free := by
  constructor
  · cbv
  constructor
  · cbv
  · cbv
    exact List.mem_cons_self
private theorem bounded : 0 < fuel ∧ fuel < 128 := by constructor <;> cbv
end MicroCFTA.NestedCapturedMuFixture
'''
# Fix getD application grouping in the source pair.
s=s.replace('(SourceRecursiveIntersectionControl.identity left).getD 0 (SourceRecursiveIntersectionControl.identity right).getD 0', '((SourceRecursiveIntersectionControl.identity left).getD 0) ((SourceRecursiveIntersectionControl.identity right).getD 0)')
(h/'captured-mu-calculation.lean').write_text(s)
