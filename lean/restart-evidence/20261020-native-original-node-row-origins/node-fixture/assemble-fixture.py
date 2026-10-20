from pathlib import Path
h=Path(__file__).resolve().parent
s=(h/'node-row-origins-kernels.lean').read_text().split('-- The fixed producer API',1)[0]
api=Path('/tmp/mcfta-native-original-node-row-origins/SourceCurrentNativeOriginalNodeRowOrigins.lean').read_text()
claim=api.split('    ∃ path : Path empty sourceHeap,',1)[1].split(' := by\n',1)[0]
claim='    ∃ path : Path empty sourceHeap,'+claim
last='      ∀ (index : Nat) outer, (events path)[index]? = some outer →\n        ∀ row, RowAt outer.body row →'
assert claim.count(last)==1
claim=claim.replace(last,last.replace('      ∀','      (∀',1))+') ∧\n'
lead=Path('/tmp/mcfta-native-original-publication-trace-fixture/publication-trace-kernels.lean').read_text().split('private theorem checked_witness :\n',1)[1].split('    ∃ path : Path empty sourceHeap,',1)[0]
explicit='''      ∃ outerIndex : Nat, ∃ outer : @Publication Symbol Guard _,
        (events path)[outerIndex]? = some outer ∧
        Reached original [] (.binder outer.smart outer.expression) outer.environment outer.before ∧
        outerEvent.key = outer.key ∧ outerEvent.candidate = outer.candidate ∧
        outer.afterBody.nodeRecords outer.key = none ∧
        Nonempty (Path empty outer.before) ∧
        Nonempty (Path outer.before outer.afterDepth) ∧
        Nonempty (Path outer.afterDepth outer.cut) ∧
        Nonempty (Path outer.allocated outer.afterBody) ∧
        Grows outer.after sourceHeap ∧ Extends outer.after.nodes.issued sourceHeap.nodes.issued ∧
        ∃ callbackRaw callbackAfter,
          build outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated = .done callbackRaw callbackAfter ∧
          run (withoutSelfReference (.interned outer.entry.identity) callbackRaw) callbackAfter =
            (outer.body,outer.afterBody) ∧
          Context outer.allocated (.reference (.interned outer.entry.identity) :: outer.environment) ∧
          Reached original [] outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated ∧
          RowAt callbackRaw tagRow ∧
          SourceRow outer.expression (.reference (.interned outer.entry.identity) :: outer.environment)
            outer.allocated callbackRaw callbackAfter tagRow ∧
          outer.expression = Syntax.union [.var 0,.binder false bodySyntax] ∧
          ∃ producerIndex : Nat, ∃ producer : @Publication Symbol Guard _,
            ∃ expressions inputs before raw after rows middle,
            ∃ sourceIndex outputIndex : Nat, ∃ symbol guard children,
              producerIndex < outerIndex ∧ producerIndex ≤ outerIndex ∧
              (events path)[producerIndex]? = some producer ∧
              SyntaxBound (Syntax.node expressions) producer.expression ∧
              UnionDescent producer.expression (Syntax.node expressions) ∧
              Context before inputs ∧ Reached original [] (Syntax.node expressions) inputs before ∧
              SourceRow (Syntax.node expressions) inputs before raw after tagRow ∧
              build (Syntax.node expressions) inputs before = .done raw after ∧
              buildEdges expressions inputs before = .done rows middle ∧
              run (makeNode rows) middle = (raw,after) ∧
              (nodeEdges raw)[outputIndex]? = some tagRow ∧
              ∃ call : RowCall expressions inputs before rows middle after sourceIndex symbol guard children,
                call.output = tagRow ∧ Grows after outer.afterBody ∧
                Extends after.nodes.issued outer.afterBody.nodes.issued'''
whole=lead+claim+explicit
proof='''  obtain ⟨path,sites,finalWriters,origins⟩ :=
    SourceCurrentNativeOriginalNodeRowOrigins.build_node_row_origins original root sourceHeap source_done
  obtain ⟨outerIndex,selectedEvent,outerLookup,rooted,keySame,fullSame,missing,
    sourcePrefix,depthPath,ordinaryPath,bodyPath,growth,issued⟩ :=
    finalWriters event.key event.entry event.body event.depth event.ordinary outer_record
  have bodySame := (Value.mu.inj fullSame).2.1
  have selectedInside : RowAt selectedEvent.body row := by
    rw [← bodySame]
    exact outer_inside
  obtain ⟨observedRaw,observedAfter,built,filtered,context,reached,rawRow,source⟩ :=
    SourceCurrentPublicationBodySourceRows.publication_body_origin selectedEvent original [] rooted row selectedInside
  have outerExpression := fixed_outer_expression selectedEvent observedRaw observedAfter row rooted source filtered bodySame
  obtain ⟨producerIndex,producer,expressions,nodeInputs,nodeBefore,nodeRaw,nodeAfter,nodeRows,middle,
    sourceIndex,outputIndex,symbol,guard,children,producerBound,producerLookup,nodeBound,nodeDescent,
    nodeContext,nodeReached,nodeSource,nodeDone,builtRows,made,canonical,call,callSame,nodeGrowth,nodeIssued⟩ :=
    origins outerIndex selectedEvent outerLookup row selectedInside
  have strict : producerIndex < outerIndex := Nat.lt_of_le_of_ne producerBound (by
    intro sameIndex
    have sameLookup : (events path)[outerIndex]? = some producer := by
      simpa only [sameIndex] using producerLookup
    have sameEvent : producer = selectedEvent := Option.some.inj (sameLookup.symm.trans outerLookup)
    have route : UnionDescent outerBody (.node expressions) := by
      simpa only [sameEvent,outerExpression] using nodeDescent
    exact no_node_descent expressions route)
  refine ⟨nestedBody,original,firstMu,root,firstHeap,sourceHeap,event,firstEntry,firstBody,firstDepth,
    firstOrdinary,row,rfl,rfl,first_done,source_done,first_shape,?_,rfl,rfl,rfl,rfl,outer_shape,outer_done,
    nested_warm,outer_record,first_body_inside,row_fields.1,row_fields.2.1,row_fields.2.2,
    path,sites,finalWriters,origins,outerIndex,selectedEvent,outerLookup,rooted,keySame,fullSame,missing,
    sourcePrefix,depthPath,ordinaryPath,bodyPath,growth,issued,observedRaw,observedAfter,built,filtered,
    context,reached,rawRow,source,outerExpression,producerIndex,producer,expressions,nodeInputs,nodeBefore,
    nodeRaw,nodeAfter,nodeRows,middle,sourceIndex,outputIndex,symbol,guard,children,strict,producerBound,
    producerLookup,nodeBound,nodeDescent,nodeContext,nodeReached,nodeSource,nodeDone,builtRows,made,
    canonical,call,callSame,nodeGrowth,nodeIssued⟩
  simpa only [first_shape] using first_is_prior
'''
s+='private theorem checked_witness :\n'+whole+' := by\n'+proof
s+='''
/-- The same full nullary row has an actual original node call at a strictly earlier trace index. -/
theorem actual_strict_node_row_origin :
'''+whole+' := checked_witness\n\nend MicroCFTA.OriginalNodeRowOriginsFixture\n'
(h/'node-row-origins-kernels.lean').write_text(s)
print(len(s.splitlines()))
