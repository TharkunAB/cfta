from pathlib import Path
import re
h=Path('/tmp/mcfta-native-compiled-mu-generation-fixture')
s=(h/'compiled-mu-calculation.lean').read_text().split('end MicroCFTA.CompiledMuGenerationFixture')[0]
s=s.replace('open InternedNestedConstruction (Syntax)','''open InternedNestedConstruction (Syntax)
open InternedStoredSubstitution (leaves encode)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCompletedBuildRootedWriters (Written)''')
s='''/-!
# A compiled recursive request installs a new used Mu

Both closed operands retain one recursive row and a distinct nullary row.
Actual checked intersection keeps the common recursive row. Its repeated
pair reference remains free before the optional instruction executes.
The selected full Mu is absent initially and present after execution.
-/
'''+s
# Imports must precede module documentation.
a=s.index('import MicroCFTA.'); b=s.index('noncomputable section')
s=s[a:b]+s[:a]+s[b:]
s+='''
private theorem source_facts : InternedNestedFacts.Facts heap :=
  (InternedFreshOrdinaryFacts.closed_verified expression).facts
private theorem root_available : Available heap root :=
  (InternedFreshOrdinaryFacts.closed_verified expression).result root heap built_done
private theorem children_shape : children root = [left,right] := by cbv
private theorem left_available : Available heap left :=
  root_available.children left (by rw [children_shape]; simp only [List.mem_cons, true_or])
private theorem right_available : Available heap right :=
  root_available.children right (by rw [children_shape]; simp)
private theorem closed : left.free = [] ∧ right.free = [] := by constructor <;> cbv
private theorem operands_used :
    (match left with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    (match right with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) := by
  constructor <;> (cbv; exact List.mem_cons_self)
private theorem operands_distinct : left ≠ right := by
  intro same
  have identities := congrArg SourceRecursiveIntersectionControl.identity same
  change some 2 = some 6 at identities
  cases identities
private theorem top_field : SourceCurrentConjunctionEquality.FieldAvailable allocatedOps top :=
  (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid).2.2
private theorem allocated_valid : SourceEqualityConstraintMemoAllocation.Valid allocatedOps :=
  (SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    SourceEqualityConstraintMemoAllocation.empty SourceEqualityConstraintMemoAllocation.empty_valid).1
private theorem fields : SourceCurrentConjunctionEquality.Fields allocatedOps heap := by
  apply SourceEqualityAnnotationConstruction.build _ expression _ [] empty
    (SourceEqualityAnnotationHeap.empty_heap _)
  simp only [expression,recursive,SourceEqualityAnnotationConstruction.Allowed,
    SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed,
    top_field,and_self,and_true,true_and]
private theorem semantic : SemanticHeap heap :=
  SourceRecursiveIntersectionSemanticHeap.constructed expression root heap built_done
private theorem semantic_ready : SourceEqualityRequiredSemanticCache.SemanticReady heap :=
  SourceEqualityRequiredSemanticCache.constructed expression root heap built_done
private theorem good : SourceCurrentAllocatedNativePhysicalCompletion.Good before := by
  refine ⟨?_,semantic_ready.ready,allocated_valid,fields⟩
  exact SourceCurrentAllocatedNativePhysicalCache.initial_valid machine ⟨source_facts,Cache.empty_valid⟩
private theorem history : SourceCurrentNativeEdgeWriterGrowth.History before := .initial _ _
private theorem left_original : SourceRecursiveIntersectionInputView.Original left :=
  SourceRecursiveIntersectionOriginalOutput.closed_original left heap source_facts.coherent left_available closed.1
private theorem right_original : SourceRecursiveIntersectionInputView.Original right :=
  SourceRecursiveIntersectionOriginalOutput.closed_original right heap source_facts.coherent right_available closed.2
private def inventory := SourceRecursiveIntersectionSourceInventory.domains heap
private theorem resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources 126 heap inventory machine.domains := by
  refine ⟨source_facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed heap source_facts,
    Cache.empty_valid,?_,?_,?_⟩
  · cbv
  · cbv
  · rw [inventory,SourceRecursiveIntersectionSourceInventory.domains_length]
    cbv
private theorem certificate : SourceCurrentAllocatedRecursivePrefixControl.Certified heap inventory control
    before.native.machine (fun final output => Available final.heap output) :=
  SourceCurrentAllocatedRecursivePrefixCode.request_node heap inventory request machine
    ⟨empty_domain _,left_available,right_available⟩
    (initial_scope heap left right left_original right_original left_available right_available)
    (SourceRecursiveIntersectionSourceInventory.empty_mem heap)

'''
raw=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentNativeOriginGeneration.lean').read_text().split('    ∃ prefixFuel',1)[1].split(' := by',1)[0]
raw='    ∃ prefixFuel'+raw
raw=re.sub(r'\bbody\b','stored',raw)
raw=raw.replace('nodeRecords key','nodeRecords entry.key').replace('call.state key (','call.state entry.key (')
head='''    InternedFreshOrdinaryConstruction.build expression [] empty = .done root heap ∧
    children root = [left,right] ∧ left.free = [] ∧ right.free = [] ∧ left ≠ right ∧
    (match left with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    (match right with | .mu selected bodyValue _ _ => Reference.interned selected.identity ∈ bodyValue.free | _ => False) ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    execute 64 control before = .done value after ∧ value = .mu entry stored depth ordinary ∧
    heap.nodeRecords entry.key = none ∧
    after.native.machine.heap.nodeRecords entry.key = some (.mu entry stored depth ordinary) ∧
    Reference.interned entry.identity ∈ stored.free ∧
    ∃ count, count ≤ 64 ∧
      SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before ∧
      execute count control before = .done value after ∧\n'''
proof=''' := by
  obtain ⟨steps,bounded,rawTrace⟩ := done_trace 64 control before after value returned
  have initial := SourceCurrentAllocatedRecursivePrefixState.initial heap inventory before good semantic_ready rfl
  have checked := SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources steps control before
    (.code (.pure value)) after (fun final output => Available final.heap output)
    initial certificate (fun _ => trivial) rawTrace
  have plan := checked.trace.plan
  have completed := trace_done steps control before after value rawTrace
  have selected : (execute (steps+1) control before).state.native.machine.heap.nodeRecords entry.key =
      some (.mu entry stored depth ordinary) := by
    rw [completed]
    exact new_mu.2.2.1
  rcases SourceCurrentNativeOriginGeneration.execute request plan good history semantic entry.key entry
    stored depth ordinary selected with prior | generated
  · rw [new_mu.2.1] at prior
    cases prior
  · exact ⟨built_done,children_shape,closed.1,closed.2,operands_distinct,
      operands_used.1,operands_used.2,good,history,returned,new_mu.1,new_mu.2.1,
      new_mu.2.2.1,new_mu.2.2.2,steps+1,by omega,plan,completed,generated⟩
'''
s+='private theorem checked_witness :\n'+head+raw+proof
s+='\n/-- Actual recursive compilation produces one new used Mu with its same owner and rooted writer. -/\ntheorem actual_compiled_generation :\n'+head+raw+' := checked_witness\n\nend MicroCFTA.CompiledMuGenerationFixture\n'
(h/'compiled-mu-kernels.lean').write_text(s)
