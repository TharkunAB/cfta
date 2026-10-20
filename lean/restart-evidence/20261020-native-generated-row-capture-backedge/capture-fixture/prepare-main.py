from pathlib import Path
import re
p=Path('/tmp/mcfta-native-generated-row-capture-backedge-fixture')
base=(p/'backedge-kernels.lean').read_text().split('\nend MicroCFTA.GeneratedRowCaptureBackedgeFixture')[0]
base=base.replace('{smart body inputs start raw after event}', '{smart body inputs start event}')
extra_opens='''open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceCurrentNativeOriginalPublicationTrace (events)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceCurrentNativeOriginalObservedResume (SyntaxBound)
open SourceCurrentNativeOriginalUnionDescent (UnionDescent)
open SourceCurrentNativeCapturedMuStoredRows (Stored)
open SourceCurrentNativeCapturedMuUnfoldRows (Observed)
open InternedEdgeResidency (nodeEdges)
'''
base=base.replace('private instance : DecidableEq FullSyntax.Formula',extra_opens+'private instance : DecidableEq FullSyntax.Formula')
main=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentNativeGeneratedRowCaptureBackedge.lean').read_text()
a=main.index(' :\n    SourceRecursiveIntersectionMaybeMu.maybeMu',main.index('theorem generated_row_capture_backedge'))+3
b=main.index(' := by',a)
out=main[a:b]
ren={'original':'expression','sourceRoot':'root','pair':'outerPair','result':'generated','targetEntry':'generatedEntry','targetBody':'generatedBody','targetDepth':'generatedDepth','targetOrdinary':'generatedOrdinary','reader':'generatedHeap'}
for old,new in ren.items(): out=re.sub(r'(?<![.\w])'+old+r'\b',new,out)
# Extract the initial capture disjunct, including all indexed original node origins.
i=out.index('((before.native.machine.heap.nodeRecords entry.key')+1
level=0
for j in range(i,len(out)):
 if out[j]=='(':level+=1
 elif out[j]==')':
  level-=1
  if level==0:break
initial=out[i+1:j]
initial=re.sub(r'(?<![.\w])body\b','stored',initial)
# Add one concrete same-terminal initial-capture receipt under the same event/raw witnesses.
extra='''(∃ terminalInputs terminalBefore terminalRaw terminalAfter
          (crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)),
          SourceRow (.var 2) terminalInputs terminalBefore terminalRaw terminalAfter storedRow ∧
          build (.var 2) terminalInputs terminalBefore = .done terminalRaw terminalAfter ∧
          Context terminalBefore terminalInputs ∧
          Reached generatedExpression generatedInputs (.var 2) terminalInputs terminalBefore ∧
          SyntaxBound (.var 2) event.expression ∧
          Grows terminalAfter rawAfter ∧ Extends terminalAfter.nodes.issued rawAfter.nodes.issued ∧
          terminalInputs[2]? = some (.mu entry stored depth ordinary) ∧
          InternedFreshOrdinaryActiveOrigins.Path generatedExpression generatedInputs
            (.var 2) terminalInputs crossings ∧ crossings.length = 1 ∧
          generatedInputs[1]? = some (.mu entry stored depth ordinary) ∧
          RowAt stored storedRow ∧ Available current.native.machine.heap (.mu entry stored depth ordinary) ∧
          current.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
          entry.key ≠ generatedEntry.key ∧
'''+initial+''')'''
# Find the first stored-row forall's balanced parentheses.
r=out.index('(∀ storedRow,')
level=0
for z in range(r,len(out)):
 if out[z]=='(':level+=1
 elif out[z]==')':
  level-=1
  if level==0:break
out=out[:z+1]+' ∧\n        '+extra+out[z+1:]
facts='''build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    locate 256 0 control before = 60 ∧ fuel = 60 ∧
    execute fuel control before = .yielded (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Trace fuel control before (.code (.optionalBinder outerPair siteBody siteNext)) current ∧
    Available current.native.machine.heap siteBody ∧
    generatedInputs[1]? = some (.mu entry stored depth ordinary) ∧
    heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    Reference.interned generatedEntry.identity ∈ generatedBody.free ∧
    storedRow.entry.key.symbol = ("tag17",.top) ∧ storedRow.entry.key.constraint = top ∧ storedRow.children = [] ∧
    RowAt generatedBody storedRow ∧\n'''
# Build a concise variable-source path classifier, used only for the returned exact terminal.
helpers='''
private theorem node_variable_path {inputs captures : List Node} {slot : Nat}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path (.node sourceEdges) inputs (.var slot) captures crossings) : slot = 0 := by
  cases path with
  | node edge member nested =>
    simp only [sourceEdges,List.mem_singleton,InternedNestedConstruction.EdgeSyntax.mk.injEq] at edge
    obtain ⟨rfl,rfl,rfl⟩ := edge
    simp only [List.mem_singleton] at member
    subst_vars
    cases nested
    rfl
private theorem variable_path {inputs captures : List Node} {slot : Nat}
    {crossings : List (InternedFreshOrdinaryActiveOrigins.Crossing Symbol Guard)}
    (path : InternedFreshOrdinaryActiveOrigins.Path generatedExpression inputs (.var slot) captures crossings) :
    slot = 0 ∨ slot = 2 := by
  have generatedShape : generatedExpression = .binder true sourceBody := congrArg (Syntax.binder true) encoded_shape
  rw [generatedShape] at path
  cases path with
  | binder crossing nested =>
    cases nested with
    | union member nested =>
      simp only [List.mem_cons,List.mem_singleton] at member
      rcases member with rfl | rfl
      · exact .inl (node_variable_path nested)
      · cases nested
        exact .inr rfl
'''
proof=''' := by
  obtain ⟨trace,available,semantic,published,context,gBuild,observed⟩ := support
  have selected : generatedHeap.nodeRecords generatedEntry.key =
      some (.mu generatedEntry generatedBody generatedDepth generatedOrdinary) := by
    rw [←generated_shape]
    exact generated_new.2
  obtain ⟨called,builtG,missing,present,event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,
      unrecorded,startPath,depthPath,ordinaryPath,bodyPath,growth,issued,raw,rawAfter,rawBuilt,filtered,
      callbackContext,callbackReached,rows,unfolds⟩ :=
    SourceCurrentNativeGeneratedRowCaptureBackedge.generated_row_capture_backedge expression root request fuel
      before current outerPair siteBody siteNext built_done good history trace available generated generatedHeap
      generated_done gBuild generatedEntry generatedBody generatedDepth generatedOrdinary generated_new.1 selected
      generatedHeap observed
  have eventBody := recovered_body reached
  obtain ⟨rawRow,source,terminalExpression,terminalInputs,terminalBefore,terminalRaw,terminalAfter,
      terminalSource,terminalBuild,nonunion,terminalContext,terminalReached,bound,suffix,suffixIssued,cases⟩ :=
    rows storedRow generated_row
  rcases cases with ⟨expressions,same⟩ | ⟨smart,body,same⟩ | capturedFacts
  · rw [same] at terminalSource terminalReached
    exact (no_terminal_node terminalReached terminalSource).elim
  · rw [same] at terminalReached bound
    exact (no_terminal_binder terminalReached eventBody bound).elim
  · obtain ⟨slot,captured,crossings,originalSlot,same,slotLookup,inside,path,offset,poolLookup,closedCapture,backedge⟩ := capturedFacts
    obtain ⟨rfl,rfl⟩ := pool_row poolLookup inside
    have choices := variable_path path
    have slotSame : slot = 2 := by omega
    subst slot
    have crossingLength : crossings.length = 1 := by omega
    rw [same] at terminalSource terminalBuild terminalReached bound
    obtain ⟨storedInside,captureAvailable,captureResident,different,origin⟩ := backedge entry stored depth ordinary rfl
    rcases origin with initialOrigin | earlier
    · refine ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,good,history,located_fuel,rfl,
        actual_prefix,trace,available,?_,initial_capture.1,initial_capture.2.2,generated_used,
        row_fields.1,row_fields.2.1,row_fields.2.2,generated_row,called,builtG,missing,present,
        event,reached,keySame,entrySame,bodySame,depthSame,ordinarySame,unrecorded,startPath,depthPath,
        ordinaryPath,bodyPath,growth,issued,raw,rawAfter,rawBuilt,filtered,callbackContext,callbackReached,
        rows,?_,unfolds⟩
      · simpa only [←actual_index] using found
      · exact ⟨terminalInputs,terminalBefore,terminalRaw,terminalAfter,crossings,terminalSource,terminalBuild,
          terminalContext,terminalReached,bound,suffix,suffixIssued,slotLookup,path,crossingLength,poolLookup,
          storedInside,captureAvailable,captureResident,different,initialOrigin⟩
    · obtain ⟨prefixFuel,suffixFuel,priorPair,parent,next,siteBefore,siteAfter,result,otherHeap,
        count,less,earlierTrace,earlierSemantic,parentAvailable,executed,advanced,one,laterTrace,
        absent,recorded,prefixGrowth,rest⟩ := earlier
      have retained := prefixGrowth.nodeRecords entry.key (.mu entry stored depth ordinary) initial_capture.1
      rw [absent] at retained
      cases retained
'''
claim=facts+out
s=base+helpers+'\nprivate theorem checked_witness :\n    '+claim+proof
s+='''
/-- The actual generated callback reaches its shared initial used Mu through the same selected capture and original node row call. -/
theorem actual_generated_initial_capture_backedge :
    '''+claim+' := checked_witness\n\nend MicroCFTA.GeneratedRowCaptureBackedgeFixture\n'
(p/'backedge-kernels-final-draft.lean').write_text(s)
(p/'backedge-claim.txt').write_text(claim)
