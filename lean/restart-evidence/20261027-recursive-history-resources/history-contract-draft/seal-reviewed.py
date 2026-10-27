from pathlib import Path
import hashlib,json,datetime,shutil
base=Path('/tmp/mcfta-recursive-history-resources-20261027/history-contract-draft');area=base.parent;repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');assert not (base/'FROZEN.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest();now=datetime.datetime.now().astimezone().isoformat(timespec='seconds')
checked=[]
for name,family,expected in [
 ('SourcePruningEnumerationFiniteHistoryContract.lean','strict-history-contract-2','60c89778ae2f4d22865c9145ded1e5d1854e663aab199a367d9586a7e05937e4'),
 ('SourcePruningEnumerationFiniteCallbackHistory.lean','strict-callback-history-1','634d2266327dc813d03b1ca4d8a3e5a329a26f6496faf1f759c8440afa05f7e9')]:
 b=(repo/name).read_bytes();e=area/family;report=json.loads((e/'report.json').read_text());raw=(e/'raw.log').read_bytes()
 assert b==(e/'MicroCFTA'/name).read_bytes() and sha(b)==expected==report['source_sha256'] and report['exit_code']==0 and len(raw)==report['bytes']==0
 (base/'checked-source'/name).write_bytes(b)
 d=base/'evidence'/family;d.mkdir(exist_ok=True)
 for f in ['report.json','raw.log']:shutil.copyfile(e/f,d/f)
 shutil.copyfile(e/'MicroCFTA'/name,d/name)
 ranges=[(34,130),(135,151),(155,179),(182,242)] if 'Contract' in name else [(38,90),(91,137)]
 cuts=[]
 for first,last in ranges:
  assert last<=len(b.splitlines());cut=b''.join(b.splitlines(keepends=True)[first-1:last]);p=base/'cuts'/f'{name}.checked.{first}-{last}.txt';p.write_bytes(cut)
  cuts.append({'scope':'literal checked source cut','first_line':first,'last_line':last,'snapshot':str(p),'bytes':len(cut),'sha256':sha(cut)})
 checked.append({'source':str(repo/name),'snapshot':str(base/'checked-source'/name),'scope':'whole checked source','reviewed_scope':'whole','bytes':len(b),'sha256':sha(b),'line_count':len(b.splitlines()),'strict_family':family,'cuts':cuts})
# Copy the actual dependency installation check; retain its old dependency warning.
fam='build-history-contract-1';e=area/fam;d=base/'evidence'/fam;d.mkdir(exist_ok=True)
for f in ['report.json','raw.log']:shutil.copyfile(e/f,d/f)
r=json.loads((e/'report.json').read_text());b=(e/'raw.log').read_bytes();assert r['exit_code']==0 and len(b)==r['bytes'] and sha(b)==r['sha256'] and b'1987 jobs' in b
(base/'checked-source-index.json').write_text(json.dumps({'created':now,'cut_convention':'One-based inclusive, splitlines(keepends=True), trailing LF retained.','sources':checked},indent=2)+'\n')
report=f'''[{now}] CLEAR — checked finite history contract, genuine zero base and callback composition.

Final checked identities:
- SourcePruningEnumerationFiniteHistoryContract.lean, 242 lines, SHA256 60c89778ae2f4d22865c9145ded1e5d1854e663aab199a367d9586a7e05937e4; Root strict-history-contract-2 exit 0/raw 0.
- SourcePruningEnumerationFiniteCallbackHistory.lean, 139 lines, SHA256 634d2266327dc813d03b1ca4d8a3e5a329a26f6496faf1f759c8440afa05f7e9; Root strict-callback-history-1 exit 0/raw 0.
Both source snapshots equal the live installed bytes. Reports use Lean 4.34.1 with warnings fatal/all linters and memory.max=memory.high=4294967296, swap 0. The actual contract Lake installation passes 1987 jobs and retains an earlier dependency warning. No check was run by this draft/review task.

HistoryAdmission is exactly current Packet/full Memos, Fits, native guard Heap, mass ceiling and finite Reserved. ResourceHistory mirrors the actual stopped/done/parked/ordinary OutputHistory tags and adds actual original resource admission at every recursive input. Parked carries actual PrefixValid, the literal parked singleton and its smaller-depth tail at the same native Caller/full Memos. Ordinary carries actual prefix validity/execution, original-to-ordinary full Post, actual OrdinaryInvocation, callback input admission and a smaller-depth tail at the SAME returned Inventory/Caller/full Memos/framed cache/seed/ceiling.

The rich local head is not discarded. OrdinaryHistoryReceipt retains the actual entry singleton at the same W, SAME entered captured cache, narrowed and entered full Packets, aggregate ordinary-to-local-head native Post/full Memos, actual CapturedEdge.run completion at W, and the full CompletedHeadReceipt with head seed, inherited bound, local input Inventory/Caller/full Memos, stable local bound and returned Inventory/full Memos. The ordinary tag's callback admission and tail use those exact returned witnesses. Query equality is not used as full Memos equality. ResourceHistory.forget retains the SAME original operation equations and output in the existing raw OutputHistory.

CompleteWithHistory preserves the original Complete universal input sequence and original stable run/OutcomeResources conclusion prefix literally. Its additional field supplies admitted histories at its OWN chosen bound+extra. CompleteWithHistory.forget calls the stronger contract once and returns its exact chosen bound/outcome/running/resources. It does not replace that bound with an independent old bound or assume an inequality between them.

zero_complete_with_history uses actual resume_zero_outcome_resources once. Actual stop and done outputs receive their corresponding admitted tags at unchanged caller/cache/metadata. Stuck and zero-depth expansion emit no outputs. The proof does not claim that Done is Discharged or that zero-depth truncation accepts a whole original language. The original mass/reservation/selector inputs remain in the contract; no future successful action is an admission premise.

callback_finite_complete_resources_with_history preserves the ENTIRE old finite callback output proposition literally. Its only input change is the stronger smaller-depth proof IH CompleteWithHistory in place of Complete. All runtime/resource admissions stay unchanged. The proof calls callback_complete once, then calls the stronger IH once only in the actual false branch at the returned framed cache and updated metadata. Frame.values supplies the same original mass ceiling. Frame.counter retains the fragment bound. Caller/full Memos/native heap, original seed and reservation remain unchanged.

The false-branch common bound is callbackFuel+resumeFuel, chosen before every extra/output quantifier. The recording family is specialized at resumeFuel+extra; the smaller-depth runtime and history families are specialized at callbackFuel+extra. Explicit arithmetic identifies both with the SAME W. Thus the actual concrete continuation equation and the smaller-depth admitted output history use one common work fuel and one actual outcome. The true branch keeps the original normal prune with no outputs. It does not assume semantic truth of rejection. Actual updated RecursiveCallbackAdmission is also retained; it is input data, not a claim of a second callback execution or successful recursion.

Preserved revisions. V1 records the initial schema before the requested complete local head receipt. V2 records the rich schema submission and remains the top-level submitted contract. checked-source and revisions/root-v3 retain the authoritative installed variant. Root-v3 removes only two redundant rw[chosen] lines in the zero proof after cases already rewrites the target. Strict1 failed input/raw/report, strict2 success, exact forward/inverse patches and two reversible Unicode spans are retained. The callback initial draft equals its final checked source. The preparation report's pending status remains historical; this report establishes final status.

Boundary. This proves an honest stronger contract, the zero base and actual callback composition conditional on that smaller-depth contract. It does NOT prove positive-depth CompleteWithHistory. Genuine selected-prefix/parked/head/sibling/ordinary producers must still derive these full resource histories, including their original reservations and full local head receipts. The new root ParkedHistory extension is reviewed separately. No Canonical/arity/retention/Satisfies/future success is added to original resource admission. Interpretation still needs explicit structural semantic gates and exact loss obligations. Whole recursive acceptance, coverage and physical correspondence are not claimed. There is no Safe-from-Frame or Safe-on-rejection assertion.

Seven exact old input sources/eight cuts and both checked sources/six cuts are pinned. Old full Complete and callback contracts and literal retention checks are retained. No repository runtime/old source, Git/network state, builds or prior frozen area was changed by this task. All writes stop with the final seal.
'''
(base/'final-review.txt').write_text(report)
(base/'final-status.json').write_text(json.dumps({'created':now,'status':'CLEAR / both Root strict checks PASS','contract_source_sha256':checked[0]['sha256'],'callback_source_sha256':checked[1]['sha256'],'positive_depth_closure_proved':False,'original_contract_prefixes_retained':True,'local_head_receipt_retained':True,'same_uniform_bound_before_histories':True,'report_sha256':sha(report.encode()),'checked_source_index_sha256':sha((base/'checked-source-index.json').read_bytes())},indent=2)+'\n')
# Recheck original inputs and all literal cuts before the final seal.
for idx in ['source-index.json','checked-source-index.json']:
 for rec in json.loads((base/idx).read_text())['sources']:
  b=Path(rec['source']).read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256'] and Path(rec['snapshot']).read_bytes()==b
  for c in rec['cuts']:
   cut=b''.join(b.splitlines(keepends=True)[c['first_line']-1:c['last_line']]);assert cut==Path(c['snapshot']).read_bytes() and len(cut)==c['bytes'] and sha(cut)==c['sha256']
files=sorted(p for p in base.rglob('*') if p.is_file() and p.name not in ['pins.json','FROZEN.json'])
pins={'created':now,'files':{str(p.relative_to(base)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in files}}
(base/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
frozen={'created':now,'status':'FROZEN / CLEAR','payload_count':len(files),'exact_file_count':len(files)+2,'pins_sha256':sha((base/'pins.json').read_bytes()),'final_review_sha256':sha((base/'final-review.txt').read_bytes()),'source_index_sha256':sha((base/'source-index.json').read_bytes()),'checked_source_index_sha256':sha((base/'checked-source-index.json').read_bytes()),'contract_source_sha256':checked[0]['sha256'],'callback_source_sha256':checked[1]['sha256']}
(base/'FROZEN.json').write_text(json.dumps(frozen,indent=2)+'\n')
for rel,r in pins['files'].items():b=(base/rel).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
assert len([p for p in base.rglob('*') if p.is_file()])==frozen['exact_file_count']
print(json.dumps({'area':str(base),'payload_count':len(files),'exact_file_count':len(files)+2,'FROZEN_sha256':sha((base/'FROZEN.json').read_bytes()),**{k:frozen[k] for k in ['pins_sha256','final_review_sha256','source_index_sha256','checked_source_index_sha256']}},indent=2))
