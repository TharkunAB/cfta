from pathlib import Path
p=Path('/tmp/mcfta-native-original-binder-fixture/binder-kernels.lean')
s=p.read_text().replace('(by simp [original]) (by simp)','(by simp) (by simp)').replace('  · rfl\n\n/-- An actual warm nested','  · cbv\n\n/-- An actual warm nested')
marker='private theorem checked_witness :\n'
prefix,tail=s.split(marker,1)
type_text=tail.split(' := by\n',1)[0]
old='''      SourceCurrentNativeCapturedMuStoredRows.Stored program [] empty sourceHeap
        (muKey depth ordinary) entry body depth ordinary'''
new='''      ∃ published : @Publication Symbol Guard _,
        InternedFreshOrdinarySourceHistory.Reached program []
          (.binder published.smart published.expression) published.environment published.before ∧
        muKey depth ordinary = published.key ∧ entry = published.entry ∧ body = published.body ∧
        depth = published.depth ∧ ordinary = published.ordinary ∧
        published.afterBody.nodeRecords published.key = none ∧
        Nonempty (SourceCurrentNativeMuIssuedHistory.Path empty published.before) ∧
        Nonempty (SourceCurrentNativeMuIssuedHistory.Path published.before published.afterDepth) ∧
        Nonempty (SourceCurrentNativeMuIssuedHistory.Path published.afterDepth published.cut) ∧
        Nonempty (SourceCurrentNativeMuIssuedHistory.Path published.allocated published.afterBody) ∧
        Grows published.after sourceHeap ∧ Extends published.after.nodes.issued sourceHeap.nodes.issued ∧
        ∃ publishedRaw publishedAfter,
          build published.expression (.reference (.interned published.entry.identity) :: published.environment)
            published.allocated = .done publishedRaw publishedAfter ∧
          run (withoutSelfReference (.interned published.entry.identity) publishedRaw) publishedAfter =
            (published.body,published.afterBody) ∧
          Context published.allocated (.reference (.interned published.entry.identity) :: published.environment) ∧
          InternedFreshOrdinarySourceHistory.Reached program [] published.expression
            (.reference (.interned published.entry.identity) :: published.environment) published.allocated ∧
          (∀ selectedRow, RowAt body selectedRow → RowAt publishedRaw selectedRow ∧
            SourceRow published.expression (.reference (.interned published.entry.identity) :: published.environment)
              published.allocated publishedRaw publishedAfter selectedRow) ∧
          RowAt publishedRaw row ∧
          SourceRow published.expression (.reference (.interned published.entry.identity) :: published.environment)
            published.allocated publishedRaw publishedAfter row'''
assert type_text.count(old)==1
type_text=type_text.replace(old,new)
# The actual warm request consumes the existing full record. Its callbacks use the same heap.
prefix=prefix.replace('private theorem warm_key :','''private theorem warm_request : request false firstDepth firstOrdinary (callback nestedBody inputs) event.allocated =
    .done firstMu event.allocated := by cbv
private theorem warm_key :''')
type_text=type_text.replace('      event.allocated.nodes.table (muKey depth ordinary) = some entry ∧','''      request false depth ordinary (callback bodySyntax inputs) event.allocated = .done first event.allocated ∧
      event.allocated.nodes.table (muKey depth ordinary) = some entry ∧''')
s=prefix+marker+type_text+''' := by
  obtain ⟨published,rooted,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,
    earlier,depthPath,ordinaryPath,bodyPath,growth,issued,publishedRaw,publishedAfter,
    built,filtered,context,reached,rows⟩ := resumed.2
  have concrete := rows row first_body_inside
  refine ⟨nestedBody,original,firstMu,root,firstHeap,sourceHeap,event,callbackRaw,callbackAfter,
    inputs,row,firstEntry,firstBody,firstDepth,firstOrdinary,rfl,rfl,first_done,source_done,
    first_shape,first_is_prior,rfl,rfl,rfl,rfl,outer_shape,outer_done,rfl,raw_context,callback_reached,
    raw_done,raw_filter,?_,nested_warm,?_,warm_depth,warm_ordinary,warm_request,warm_key,warm_record,
    terminal_source,union_source,first_body_inside,row_fields.1,row_fields.2.1,row_fields.2.2,
    callback_suffix.1,callback_suffix.2,enclosing_suffix.1,enclosing_suffix.2,resumed.1,
    published,rooted,keySame,entrySame,bodySame,depthSame,ordinarySame,missing,earlier,
    depthPath,ordinaryPath,bodyPath,growth,issued,publishedRaw,publishedAfter,built,filtered,
    context,reached,rows,concrete.1,concrete.2⟩
  · cbv
  · cbv

/-- An actual warm nested binder retains its earlier full payload and one fixed original stored-row callback. -/
theorem actual_warm_binder :
'''+type_text+''' := checked_witness

end MicroCFTA.OriginalBinderFixture
'''
p.write_text(s)
