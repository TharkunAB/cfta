from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib
import json

AREA = Path('/tmp/mcfta-opaque-finalizer-attachment-20261027')
OUT = AREA / 'stable-prefix-review'
REPO = Path('/home/tritlo/Code/mcfta')
EXPECTED = '168a87ad62cb933d730733ce6ec42db64945114c06462e7f7a015b06632a2fed'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def save(relative, data):
    path = OUT / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return {'snapshot': str(path), 'bytes': len(data), 'sha256': digest(data)}

def json_save(relative, value):
    return save(relative, (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode())

records = []
def capture(source, relative, spans, scope):
    source = Path(source)
    data = source.read_bytes()
    record = {'source': str(source), **save(relative, data), 'scope': 'whole source',
              'reviewed_scope': scope, 'cuts': []}
    lines = data.splitlines(keepends=True)
    for first, last, label in spans:
        cut = b''.join(lines[first-1:last])
        assert 1 <= first <= last <= len(lines)
        leaf = f'cuts/{source.stem}-{first}-{last}.txt'
        record['cuts'].append({'first_line': first, 'last_line': last,
            **save(leaf, cut), 'scope': 'literal cut', 'purpose': label})
    records.append(record)
    return data

new = capture(AREA / 'opaque-suffix-draft/SourcePruningEnumerationOpaqueStablePrefixResources.lean',
    'whole/SourcePruningEnumerationOpaqueStablePrefixResources.lean',
    [(23,92,'full theorem admission and conclusion'), (93,132,'two original calls and common bound'),
     (133,173,'actual complete-trace endpoint alignment and full prefix Packet'),
     (175,183,'fixed prefix result family')], 'whole module read')
assert digest(new) == EXPECTED
old = capture(REPO / 'lean/MicroCFTA/SourcePruningEnumerationOpaquePrefixResources.lean',
    'whole/SourcePruningEnumerationOpaquePrefixResources.lean',
    [(35,52,'existing full PrefixAdmission'), (55,119,'full old theorem admission and conclusion'),
     (120,200,'full old proof including both original producer calls')], 'whole module read')
trace = capture(REPO / 'lean/MicroCFTA/SourcePruningEnumerationChildTraversal.lean',
    'whole/SourcePruningEnumerationChildTraversal.lean',
    [(14,68,'actual traversal result/run/Trace and trace_complete')],
    'lines 1-180 read; focused use is Result/run/Trace/trace_complete at lines 14-68; whole copy retained for identity')
checked = capture(AREA / 'strict-stable-prefix-1/MicroCFTA/SourcePruningEnumerationOpaqueStablePrefixResources.lean',
    'strict/SourcePruningEnumerationOpaqueStablePrefixResources.lean', [],
    'whole strict source byte-equal to reviewed draft')
assert checked == new
report = capture(AREA / 'strict-stable-prefix-1/report.json', 'strict/report.json', [], 'whole actual strict report read')
raw = capture(AREA / 'strict-stable-prefix-1/raw.log', 'strict/raw.log', [], 'whole empty strict log read')
strict = json.loads(report)
assert strict['exit_code'] == 0 and strict['source_sha256'] == EXPECTED
assert strict['bytes'] == len(raw) == 0 and strict['sha256'] == digest(raw)
assert strict['cgroup_limits'] == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}

def theorem(data, name):
    start = data.index(('theorem ' + name + '\n').encode())
    head_end = data.index(b' := by\n', start)
    end = data.index(b'\nend MicroCFTA.', head_end)
    return data[start:head_end], data[head_end+len(b' := by\n'):end]

oh, ob = theorem(old, 'complete_with_prefix_resources')
nh, nb = theorem(new, 'complete_with_stable_prefix_resources')
kept, appendix = nh.rsplit(' ∧\n      ∃ prefixResult :'.encode(), 1)
assert kept.endswith(b'eventBefore eventQueries)')
recovered_header = kept[:-1].replace(
    b'theorem complete_with_stable_prefix_resources\n', b'theorem complete_with_prefix_resources\n', 1).replace(
    '      (∀ {Typing : Type}'.encode(), '      ∀ {Typing : Type}'.encode(), 1)
assert recovered_header == oh
base, added_proof = nb.split('  · refine ⟨prefixResult, ?_⟩'.encode(), 1)
assert base.endswith(b'\n\n')
recovered_body = base[:-1].replace(
    'references, pendingHistory, fragmentBounds, shape, returnedFits, returnedKnown, ?_, ?_⟩'.encode(),
    'references, pendingHistory, fragmentBounds, shape, returnedFits, returnedKnown, ?_⟩'.encode(), 1)
assert recovered_body == ob
save('comparison/old-contract.txt', oh)
save('comparison/recovered-old-contract.txt', recovered_header)
save('comparison/new-contract.txt', nh)
save('comparison/added-conclusion.txt', '      ∃ prefixResult :'.encode()+appendix)
save('comparison/old-proof-body.txt', ob)
save('comparison/recovered-old-proof-body.txt', recovered_body)
save('comparison/added-proof.txt', '  · refine ⟨prefixResult, ?_⟩'.encode()+added_proof)
producer = b'SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources seed formulas solver'
assert ob.count(producer) == nb.count(producer) == 2
admission_end = b'    (splitInputs : inputs = consumed ++ remaining) :\n'
def admission(header):
    return header[:header.index(admission_end)+len(admission_end)]
normalized_new_admission = admission(nh).replace(
    b'theorem complete_with_stable_prefix_resources\n', b'theorem complete_with_prefix_resources\n', 1)
assert normalized_new_admission == admission(oh)
comparison = {
    'status':'PASS', 'new_sha256':digest(new), 'old_sha256':digest(old),
    'header_convention':'theorem keyword through immediately before space := by; UTF-8 exact bytes',
    'old_header':{'bytes':len(oh),'sha256':digest(oh)},
    'recovered_old_header':{'bytes':len(recovered_header),'sha256':digest(recovered_header)},
    'admission_equal_after_name_only':True, 'whole_contract_recovery_exact':True,
    'header_mapping':[
        'Remove the final conjunction and existential prefixResult stable family.',
        'Remove only the grouping parentheses around the retained final observer.',
        'Rename complete_with_stable_prefix_resources to complete_with_prefix_resources.'
    ],
    'body_recovery_exact':True, 'old_body':{'bytes':len(ob),'sha256':digest(ob)},
    'body_mapping':[
        'Remove the final prefixResult proof bullet and its one extra separator LF.',
        'Remove the additional ?_ in the existing final refine tuple.'
    ],
    'old_producer_calls':ob.count(producer), 'new_producer_calls':nb.count(producer),
    'producer_arguments_unchanged':True,
    'producer_calls':['full original inputs with original reservation',
                      'consumed inputs with reservationSplit.prefix and consumedGenuine'],
    'strict_source_matches_reviewed_draft':True, 'strict_exit_code':0,
    'strict_raw_bytes':0,'strict_actual_memory_max':4294967296,'strict_actual_swap_max':0
}
json_save('contract-comparison.json', comparison)
json_save('source-index.json', {'schema':'whole sources and explicit literal cuts',
    'cut_convention':'one-based inclusive lines; splitlines(keepends=True); original LF bytes retained',
    'sources':records})
now = datetime.now(ZoneInfo('Europe/Stockholm')).isoformat()
text = f'''[{now}] CLEAR for the reviewed stable-prefix theorem. This review remains OPEN for the later suffix theorem.

The reviewed draft is 185 lines, SHA256 {digest(new)}. The checked strict snapshot is byte-identical. strict-stable-prefix-1 exits 0 with an empty raw log. Its actual memory.max and memory.high are 4,294,967,296 bytes, with swap disabled. No build or Lean evaluation was run for this review.

The full prior theorem contract recovers literally: {len(oh):,} bytes, SHA256 {digest(oh)}. The mapping removes only the appended fixed-prefix-result conjunct, removes the grouping parentheses around the existing observer, and restores the old theorem name. The initial admission is identical after the name change. No old conclusion clause is lost. The full old proof body also recovers literally after removing the new final goal/proof bullet and its separator LF. Both versions make the same two original traversal producer calls: the full inputs, then the consumed prefix with its derived original reservation. The added stability proof reuses prefixRunning.

The existing full stable traversal result, complete-or-rejection shape, Post with full Memos, query equality, roots, storage, realization, counts, flags, origin, Protected, references, pending history, fragment bounds, complete-only Safe and fragment history, and final Fits/guard carrier are retained. The actual complete Trace identifies the same canonical prefix caller, cache, queries and full prefix Memos. PrefixAdmission carries the remaining original reservation and genuine remaining inputs at that actual endpoint. The initial Packet is an antecedent of the returned observer; it is not a new producer premise.

The new field chooses one prefixResult before every extra-fuel quantifier. It certifies the same consumed-prefix execution at the returned five-axis diagonal bound plus any extra. It does not assert that prefixResult completes: the original producer permits a stopped rejection. Safe is used only after the actual complete Trace rules out that stopped case. The proof derives the sufficient common bound from both original producers and does not infer arbitrary low-fuel uniqueness or Safe from Frame.

No source issue was found. This result does not yet prove marker persistence through the remaining suffix, residual write or finalizer. It does not prove whole recursive acceptance, coverage, or physical Haskell correspondence. No publication or push outcome is asserted. The previous marker-attachment area was not modified.

Evidence: source-index.json has exact whole source/check identities and labeled literal cuts. contract-comparison.json records the exact recovery mapping. The review is deliberately not sealed until the requested later suffix review.
'''
save('report.txt', text.encode())
json_save('OPEN.json', {'status':'OPEN','reviewed_at':now,'review_result':'CLEAR',
    'reason':'Parent requested this area remain open for later final suffix theorem review.',
    'reviewed_source_sha256':digest(new),'source_checkpoint_context':'d60f6c1607d39fa114ae83a489af7b34d832ad23',
    'publication_status':'not evaluated or predicted'})
print(json.dumps({'status':'CLEAR / OPEN', 'report':str(OUT/'report.txt'),
 'report_sha256':digest((OUT/'report.txt').read_bytes()),'source_index_sha256':digest((OUT/'source-index.json').read_bytes()),
 'old_header_bytes':len(oh),'old_header_sha256':digest(oh),'source_records':len(records),
 'literal_cuts':sum(len(r['cuts']) for r in records)},indent=2))
