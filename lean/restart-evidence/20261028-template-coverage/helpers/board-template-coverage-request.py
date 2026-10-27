from pathlib import Path
import datetime
import json
import uuid
import zoneinfo

prefix = Path('/tmp/mcfta-template-coverage')
request = Path(str(prefix) + '-publication-board-request.json')
assert not request.exists()
publication = json.loads(Path(str(prefix) + '-publication.json').read_text())
assert publication['remote_head'] == publication['tracking_head'] == publication['head'] and publication['clean']
source = Path('/tmp/mcfta-template-coverage-20261027/source-head.txt').read_text().strip()
verified = json.loads(Path(str(prefix) + '-committed-verification.log').read_text())
assert verified['status'] == 'pass' and verified['committed']
stamp = datetime.datetime.now(zoneinfo.ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
text = f'''[{stamp}] Original template non-rejection is published on formalize at {publication['head']}; proof source {source}.

Recursive.callback_prefix_complete_resources_refutes retains EXACT original callback admission and ENTIRE old resource result. The same original producer chooses fuel/result/final state ONCE before universal language/meaning/assignment observers. An original model that fills the captured fragment at the current variable, refutes original pending groups, avoids original templates at source program positions and has source program encoding cannot be rejected by this actual callback. Every retained pending group remains refuted. Full callers, Memos, every-extra-fuel exact singleton, continuation/prefix/resource packets remain. No futurefalse/model/desired execution is supplied.

The proof follows actual partial rendering, representative reads, raw holes, matcher exact/prefix/wildcard cases, original indexed template membership and original ProgramAt selection, actual structural conversion, all ordered resume reads and finishChecks/type-recording branches. Truncation permits ANY completed term. Structural conversion names the actual private helper with local Lean syntax macros; the rejected copied recursive evaluator is preserved in failed drafts. The entire old3691B theorem declaration is recovered literally after rename/grouping/appended observer. Original bound/outcome precede all models.

11modules1352lines78553B,16new public theorems,3inductive semantic relations+2predicates. Strict sources/Audit PASS; fullAudit4293jobs80301dependencies. Public249blocks+all5definitions1003823B SHAa7358b8e7c7e09a548ada53890558f7d0894edeef87e8aacacd780cb79628c68; prior233exact971561Bprefix. Only3standardaxioms. All4281oldnonAuditLean/130strong/791trackedHaskell evidence+sourcefiles unchanged. 48actualcommands including17failed proof attempts+1failed private-name probe preserved; serial4GiBswap0. Three independently sealed reviews. Portable/committed verification PASS: {verified['payloads']}payloads,{verified['archives']}archives,{verified['review_records']}source records. Evidence lean/restart-evidence/20261028-template-coverage; manifest {verified['manifest_sha256']}. Note lean/notes-current-template-coverage.md; all9wholeoldrestartbodies preserved.

No new Haskell defect established. Utils.mapp inserts fixed singleton arrow marker, rawTemplate retains it, and public canPrune guards app/4 type-constructor collisions. The formal source ProgramEncoding condition records that invariant; public native construction origin remains unproved. Malformed arbitrary marker witnesses lie outside that admission. FINDINGS records this assessment and retains prior integrated LPO/KBO repair status and executed witnesses. No Haskell/Cabal edit, Haskell test or benchmark ran in this checkpoint.

Largest gap remains end-to-end recursive enumeration coverage. Derive original semantic callback conditions from public startup and preserve them through native heads, assigned fragments, projection, parked constraints and Mu/Union frontiers; then justify depth/stop policy, discharge/render coverage, public APIs, ranking/sampling and physical Haskell correspondence. Avoids is a policy, not implied by native acceptance alone. Previous strongest exact finite pruning preservation, conditional original-language rendered soundness, proper cache for every emitted recursive output and chosen hook invocation or exact earlier stop retain scope. Goal ACTIVE; whole formalization incomplete.'''
args = dict(thread_id='1c1333d7-46ea-4f46-a9a1-b5d13e577337', username='mcfta-lean-review',
    post_type='status', request_id=str(uuid.uuid4()), content={'text': text},
    metadata=dict(repository='TharkunAB/cfta', branch='formalize', head=publication['head'],
        source_head=source, evidence='lean/restart-evidence/20261028-template-coverage',
        manifest_sha256=verified['manifest_sha256'], goal_status='active', full_formalization_complete=False))
request.write_text(json.dumps(args, indent=2) + '\n')
print(json.dumps(dict(request_file=str(request), request_id=args['request_id'], text_bytes=len(text.encode()))))
