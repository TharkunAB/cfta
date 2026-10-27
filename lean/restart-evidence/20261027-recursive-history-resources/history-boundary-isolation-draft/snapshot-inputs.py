from pathlib import Path
import datetime
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-recursive-history-resources-20261027/history-boundary-isolation-draft')
specs = [
 ('SourcePruningEnumerationFiniteHistoryContract.lean', [(31,63,'original admission and actual ordinary receipt'),(65,132,'all four actual resource-history constructors'),(154,179,'entire universal resource-history contract')]),
 ('SourcePruningEnumerationHistoryReceiptIsolation.lean', [(31,63,'actual entry, completed head and callback isolation')]),
 ('SourcePruningEnumerationPrefixIsolatedHistory.lean', [(108,207,'actual valid parked and narrowed prefix isolation')]),
 ('SourcePruningEnumerationIsolatedBoundary.lean', [(17,49,'native candidate disables the isolated boundary'),(79,108,'original packet and actual restart select a different root')]),
 ('SourcePruningEnumerationIsolatedPending.lean', [(18,59,'certificate, discharge contradiction and transports')]),
 ('SourcePruningEnumerationRestart.lean', [(11,48,'exact restart decision, row and same-counter frame')]),
 ('SourcePruningEnumerationNodes.lean', [(14,32,'exact native handle lookup'),(49,75,'lookup preserved by actual heap effects')]),
 ('SourceCurrentAllocatedPartialInvariant.lean', [(37,47,'Post retains current context and actual physical effects'),(64,76,'actual Post composition')]),
 ('SourcePruningEnumerationCapturedIsolation.lean', [(61,145,'resource-backed completed head isolation at the same actual cache')]),
 ('SourcePruningEnumerationHeadAdmission.lean', [(70,104,'completed head retains actual full native Post and packets')]),
 ('SourcePruningEnumerationSelectedStepCompletion.lean', [(306,350,'PrefixValid full parked receipt and narrowed shape')]),
 ('SourcePruningEnumerationPrefixCompletion.lean', [(27,47,'PrefixValid includes actual finished observation and endpoint invariants')]),
 ('SourcePruningEnumerationFiniteHistoryResources.lean', [(27,79,'finite depth induction and entire public producer packet')]),
 ('SourcePruningEnumerationSelectedStep.lean', [(41,102,'actual prefix runtime, check, adapter and Right callback order')]),
 ('SourcePruningEnumerationRecursive.lean', [(36,45,'each output retains its own cache and native endpoint')]),
 ('SourcePruningEnumerationRendering.lean', [(21,25,'full structural discharge excludes every native pending handle')]),
]
rows = []
for name, spans in specs:
    source = root / 'lean' / 'MicroCFTA' / name
    data = source.read_bytes()
    lines = data.splitlines(keepends=True)
    copy = area / 'sources' / name
    copy.parent.mkdir(parents=True, exist_ok=True)
    if copy.exists():
        assert copy.read_bytes() == data
    else:
        copy.write_bytes(data)
    row = {'source_path': str(source), 'copy': str(copy.relative_to(area)), 'sha256': hashlib.sha256(data).hexdigest(),
           'bytes': len(data), 'lines': len(lines), 'review_scope': 'focused literal cuts; full copy retained as source provenance', 'cuts': []}
    for first, last, purpose in spans:
        assert 1 <= first <= last <= len(lines), (name, first, last, len(lines))
        cut_data = b''.join(lines[first-1:last])
        cut = area / 'cuts' / f'{source.stem}-L{first}-L{last}.lean'
        cut.parent.mkdir(parents=True, exist_ok=True)
        if cut.exists():
            assert cut.read_bytes() == cut_data
        else:
            cut.write_bytes(cut_data)
        row['cuts'].append({'path': str(cut.relative_to(area)), 'first_line': first, 'last_line': last,
                            'bytes': len(cut_data), 'sha256': hashlib.sha256(cut_data).hexdigest(), 'purpose': purpose})
    rows.append(row)
index = {'created_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'policy': 'source-only; no repository edits, Lean, builds, Git, network or board activity',
         'full_copies': len(rows), 'cut_count': sum(len(r['cuts']) for r in rows),
         'cut_lines': sum(c['last_line']-c['first_line']+1 for r in rows for c in r['cuts']), 'sources': rows}
(area / 'source-index.json').write_text(json.dumps(index, indent=2)+'\n')
print(json.dumps({k: index[k] for k in ['full_copies','cut_count','cut_lines']}))
