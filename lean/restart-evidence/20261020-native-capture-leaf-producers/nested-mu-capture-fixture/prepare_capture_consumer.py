from pathlib import Path
import re
h=Path('/tmp/mcfta-native-nested-mu-capture-fixture');root=Path('/home/tritlo/Code/mcfta')
s=(h/'captured-mu-calculation.lean').read_text().split('end MicroCFTA.NestedCapturedMuFixture')[0]
start=s.index('/-!');end=s.index('-/',start)
s=s[:start]+'''/-!
# An outer optional captures an earlier generated full Mu

Two closed source binders contain distinct closed recursive inner binders.
Actual execution stops at the outer pair's optional instruction. Its leaf
pool contains the newly generated inner Mu at occurrence index one.
The initial heap has no record for that selected inner Mu key.
The same capture producer retains the earlier actual generating site.
-/'''+s[end+2:]
old=Path('/tmp/mcfta-native-compiled-terminal-generation-fixture/terminal-mu-kernels.lean').read_text()
helpers=old.split('private theorem source_facts',1)[1].split('private theorem checked_witness :',1)[0]
helpers='private theorem source_facts'+helpers
helpers=helpers.replace('Resources 126','Resources 1022').replace('[expression,recursive,SourceEqualityAnnotationConstruction.Allowed','[expression,recursive,inner,SourceEqualityAnnotationConstruction.Allowed')
s+='\n'+helpers
capture=(root/'lean/MicroCFTA/SourceCurrentNativeCapturedMuOrigins.lean').read_text().split('    ∃ prefixFuel',1)[1].split(' := by',1)[0]
capture='    ∃ prefixFuel'+capture
capture=re.sub(r'\bbody\b','stored',capture)
capture=capture.replace('(.code (.optionalBinder pair siteBody siteNext)) current','(.code (.optionalBinder outerPair siteBody siteNext)) current')
origin=(root/'lean/MicroCFTA/SourceCurrentNativeOptionalTerminalOrigin.lean').read_text().split(' : Prop :=\n',1)[1].split('\n/-- An actual optional prefix',1)[0]
origin=origin.replace('Checked width','Checked 1024').replace('State width Symbol Guard','State 1024 Symbol Guard').replace('lookupNode width','lookupNode 1024').replace('fuel = queryFuel','prefixFuel = queryFuel').replace('pair = SourceRecursiveIntersectionControl.pair','priorPair = SourceRecursiveIntersectionControl.pair').replace('siteNext','next')
# The earlier Origin's body is parent, not the final outer optional body.
origin=origin.replace('siteBody','parent')
capture=capture.replace('SourceCurrentNativeOptionalTerminalOrigin.Origin request prefixFuel before siteBefore priorPair parent next','('+origin.strip()+')')
head='''    InternedFreshOrdinaryConstruction.build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    (match left with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    (match right with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    0 < fuel ∧ fuel < 128 ∧
    execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Available current.native.machine.heap siteBody ∧
    (leaves siteBody)[1]? = some (.mu entry stored depth ordinary) ∧
    heap.nodeRecords entry.key = none ∧
    current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧\n'''
proof=''' := by
  have rawTrace := execute_steps fuel control (.code (.optionalBinder outerPair siteBody siteNext)) before current actual_prefix
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources fuel control before
    (.code (.optionalBinder outerPair siteBody siteNext)) current (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have available : Available current.native.machine.heap siteBody := checked.inputs
  rcases SourceCurrentNativeCapturedMuOrigins.capture request fuel before current outerPair siteBody siteNext
    good history semantic checked.trace available 1 entry stored depth ordinary found with prior | generated
  · change heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) at prior
    rw [new_capture.1] at prior
    cases prior
  · exact ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
      operands_used.1,operands_used.2,good,history,bounded.1,bounded.2,
      actual_prefix,checked.trace,available,found,new_capture.1,new_capture.2.1,new_capture.2.2,generated⟩
'''
s+='private theorem checked_witness :\n'+head+capture+proof
s+='\n/-- The exact outer leaf occurrence retains its same earlier generated Mu writer and terminal origin. -/\ntheorem actual_nested_capture :\n'+head+capture+' := checked_witness\n\nend MicroCFTA.NestedCapturedMuFixture\n'
(h/'captured-mu-kernels.lean').write_text(s)
