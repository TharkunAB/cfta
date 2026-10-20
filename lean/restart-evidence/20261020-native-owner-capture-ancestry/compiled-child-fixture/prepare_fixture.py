from pathlib import Path
p=Path('/tmp/mcfta-native-consistent-owner-fixture/consistent-kernels.lean')
s=p.read_text().split('private theorem checked_witness :',1)[0]
s=s.replace('import MicroCFTA.SourceCurrentNativeConsistentOptionalOwner','import MicroCFTA.SourceCurrentNativeOptionalChildOrigin\nimport MicroCFTA.SourceEqualityAnnotationConstruction\nimport MicroCFTA.SourceCurrentConjunctionFieldAllocation')
s=s.replace('private def firstSource', '''private def allocatedOps :=
  SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty

private def firstSource''',1)
s=s.replace('⟨initial 8 ⟨heap,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.empty⟩','⟨initial 8 ⟨heap,Cache.emptyState⟩,allocatedOps⟩')
s += '''private theorem ready : SourceEqualityRequiredCache.Ready heap := by
  refine ⟨semantic, ?_, ?_⟩
  · exact InternedFreshOrdinaryCoverage.build_covered secondSource [] firstHeap
      first_facts.coherent.valid
      (InternedFreshOrdinaryCoverage.closed_covered firstSource left firstHeap first_done)
      right heap second_done
  · exact (InternedOpenDepthExecution.build_depth secondSource [] firstHeap first_context.base
      first_context.depth (InternedOpenDepthExecution.closed_heap firstSource)).heap

private theorem operation_valid : SourceEqualityConstraintMemoAllocation.Valid allocatedOps :=
  (SourceCurrentConjunctionFieldAllocation.empty_field SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid).1

private theorem top_field : SourceCurrentConjunctionEquality.FieldAvailable allocatedOps
    (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) :=
  (SourceCurrentConjunctionFieldAllocation.empty_field SourceEqualityConstraintMemoAllocation.empty
    SourceEqualityConstraintMemoAllocation.empty_valid).2.2

private theorem fields : SourceCurrentConjunctionEquality.Fields allocatedOps heap := by
  exact SourceEqualityAnnotationConstruction.build _ secondSource
    (by exact ⟨top_field,True.intro,True.intro⟩) [] firstHeap
    (SourceEqualityAnnotationConstruction.build _ firstSource True.intro [] empty
      (SourceEqualityAnnotationHeap.empty_heap _))

private theorem good : SourceCurrentAllocatedNativePhysicalCompletion.Good before :=
  ⟨physical,ready,operation_valid,fields⟩

private theorem history : SourceCurrentNativeEdgeWriterGrowth.History before :=
  .initial _ _

private theorem site_owner (handle : Nat) (queried : NodeRequest Symbol Guard)
    (present : after.native.nodes.cells handle = some ⟨queried,.evaluating⟩) :
    queried = request := by
  cases handle with
  | zero =>
      change some ⟨request,.evaluating⟩ = some ⟨queried,.evaluating⟩ at present
      exact (congrArg FlatMemoThunk.Cell.request (Option.some.inj present)).symm
  | succ handle =>
      cases handle with
      | zero =>
          change some ⟨child,.returned .empty⟩ = some ⟨queried,.evaluating⟩ at present
          cases present
      | succ handle =>
          change none = some ⟨queried,.evaluating⟩ at present
          cases present

'''
origin=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentNativeOptionalChildOrigin.lean').read_text().split(' : Prop :=\n',1)[1].split('\n/-- Initial history',1)[0]
origin=origin.replace('Checked width','Checked 8').replace('State width Symbol Guard','State 8 Symbol Guard').replace('lookupNode width','lookupNode 8').replace('fuel = queryFuel','4 = queryFuel').replace('siteBody','.empty').replace('siteBefore','after').replace('siteNext','finish')
origin+=' ∧\n      ∃ childHandle, after.native.nodes.cells childHandle =\n        some ⟨⟨entered.1,body queried.left,body queried.right⟩,.returned .empty⟩ ∧\n        SourceCurrentNativeWriterReadyRetention.Written (width := 8) childHandle\n          ⟨entered.1,body queried.left,body queried.right⟩ .empty after.native'
head='''    allocatedOps = SourceEqualityMkEdgeAllocation.emptyField SourceEqualityConstraintMemoAllocation.empty ∧
    firstBuilt = .done left firstHeap ∧ secondBuilt = .done right heap ∧
    (∃ entry stored depth ordinary, left = .mu entry stored depth ordinary) ∧
    (∃ entry stored depth ordinary, right = .mu entry stored depth ordinary) ∧
    left ≠ right ∧ SourceRecursiveIntersectionControl.decision request.domain.key left right = .bothMu ∧
    SemanticHeap heap ∧ Available heap left ∧ Available heap right ∧
    SourceCurrentAllocatedNativePhysicalCompletion.Good before ∧
    SourceCurrentNativeEdgeWriterGrowth.History before ∧
    Nonempty (SourceCurrentNativeMuPublication.History empty heap) ∧
    Trace 4 (.code (requestNode request.domain left right)) before
      (.code (.optionalBinder pair .empty finish)) after ∧\n'''
proof=''' := by
  obtain ⟨queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,leftIdentity,rightIdentity,pairEq,enterInputs,enterStep,
    childTrace,continuation,retained,forwarded⟩ :=
    SourceCurrentNativeOptionalChildOrigin.request request 4 before after pair .empty finish good history actual
  let compiler : Checked 8 := ⟨running,queryBefore.operations⟩
  let localDomain := SourceRecursiveIntersectionEnvironment.enter compiler.native.machine.domains
    queried.domain.key queried.left queried.right first second
  have same : queried = request := site_owner handle queried retained
  have keyed : SourceRecursiveIntersectionMemo.requestKey 8 localDomain.1
      (body queried.left) (body queried.right) ≠ none := by
    rw [same]
    unfold SourceRecursiveIntersectionMemo.requestKey
    rw [IntersectionFlatMemoKeyDomain.sourceKey_complete 8 _ _ _ .empty (.node 1) rfl rfl]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  obtain ⟨childHandle,childCell,childWriter⟩ := forwarded.2.resolve_left (fun direct => keyed direct.1)
  exact ⟨rfl,first_done,second_done,shapes.1,shapes.2.1,shapes.2.2,decision,
    semantic,left_available,second_available,good,history,publication_history,actual,
    queryFuel,childFuel,queried,callerNext,queryBefore,handle,chosen,running,
    first,second,total,earlier,inputs,selected,demanded,suspended,evaluating,machine,
    queryStep,recursive,leftIdentity,rightIdentity,pairEq,enterInputs,enterStep,
    childTrace,continuation,retained,forwarded,childHandle,childCell,childWriter⟩
'''
s+='private theorem checked_witness :\n'+head+origin+proof
s+='\n/-- Actual source construction supplies the same active owner and its keyed child writer. -/\ntheorem actual_consistent_site :\n'+head+origin+' := checked_witness\n\nend MicroCFTA.NativeConsistentOwnerFixture\n'
s=s.replace('Initial publication history come','Initial publication history come')
s=s.replace('initial publication history come from the actual source builds.','initial publication history come from the actual source builds. An actual Top-field\nallocation supplies the initial loaded field. The actual child returns Empty.')
p.write_text(s)
