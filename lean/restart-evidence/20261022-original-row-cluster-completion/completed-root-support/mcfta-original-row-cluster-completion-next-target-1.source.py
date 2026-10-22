import datetime
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-original-row-cluster-completion'
def sha(data):
    return hashlib.sha256(data).hexdigest()
plan = here / 'next-row-meaning-plan'
index = json.loads((plan / 'source-index.json').read_text())
cuts = 0
for item in index:
    raw = (root / item['path']).read_bytes()
    assert sha(raw) == item['source_sha256'] and raw == (plan / item['snapshot']).read_bytes()
    for span in item['ranges']:
        excerpt = b''.join(raw.splitlines(True)[span['start'] - 1:span['end']])
        assert sha(excerpt) == span['sha256'] and excerpt == (plan / span['snapshot']).read_bytes()
        cuts += 1
assert len(index) == 13 and cuts == 21
erratum = here / 'next-row-meaning-plan-erratum'
for item in json.loads((erratum / 'source-index.json').read_text()):
    raw = (root / item['path']).read_bytes()
    excerpt = b''.join(raw.splitlines(True)[item['start'] - 1:item['end']])
    assert sha(raw) == item['source_sha256'] and sha(excerpt) == item['excerpt_sha256']
    assert excerpt == (erratum / item['snapshot']).read_bytes()
audit = here / 'next-row-meaning-plan-audit/review.md'
assert sha(audit.read_bytes()) == '2906b8606774ecd9969b06d664c30528645479e44a4746387b9427953917423a'
proof = (here / 'proof-commit.txt').read_text().strip()
assert len(proof) == 40 and json.loads((here / 'original-row-cluster-completion-audit-1.json').read_text())['exit_code'] == 0
target = '''# Next proof target

Continue toward the complete withoutRedundantEdges pass.
H17 cluster_complete now supplies genuine original-group execution and its full returned packet.
It does not supply physical language preservation.

After refreshing upstream and recording a fresh baseline, prepare only the exact context,
one public row_inputs_meaning header and at most one private original_of_readback statement
for SourceCurrentOriginalRowPhysicalMeaning.lean. Review these before any body or compiler job.
Read next-row-meaning-plan, its additive erratum and its independent review in this checkpoint.

Use the existing concrete formula Symbol and Guard types. Quantify arbitrary holds.
Keep one source Facts and the SAME InputMeaning for view source holds.
Use one actual parent and row, OriginalInput source (inputOf parent), Available source parent,
parent.free=[], inputModel.valid (inputOf parent), and literal row membership in nodeEdges parent.
Conclude both original/admitted row children and exact RowLanguage equality with physical
edgeMeaning for every ambient environment and finite term. Retain literal child order and guard.
No width, state, cache, ranks, Room, completion or desired language law may be a premise.
Do not replace the fixed model of a populated state with a canonical model.

First eliminate non-node parents from literal row membership. The actual node codec is then
definitional. Only then use both payload_readback proofs to identify the original parent.
inputOf uses getD .empty; OriginalInput alone does not prove an arbitrary Value codec.
If the optional private helper is generic over Value, it must take the derived complete-codec
equality. Do not add that as a public premise. Derive child admission from row_valid and
the admitted parent. Derive child closedness from Facts.coherent, node_free and childFree_member.
Use original_meaning, copy_readback and the SAME model.copy_exact for child meaning.
Transport the ordered forest relation in both directions with existing public APIs.

Target90 to150 ordinary Lean lines. HARD STOP180 total lines before more source or a check.
Keep default declaration limits and all linters. Preserve every stopped draft and exact repair.
This adapter is the next step toward pruning semantics. Scan language invariants,
physical pruning, grouping, generated parents, Mu/full traversal and Haskell refinement remain.
H6 constructed_node_calls remains the strongest combined semantic theorem.
The whole goal remains active. Preserve all older proofs and the optimized core.
Keep the external Haskell repair index FIRST in FINDINGS. No Haskell repair is added.
Remote publication needs the pending fresh direct approval after the earlier automatic rejection.
'''
assert not (here / 'NEXT-TARGET.md').exists() and not (here / 'next-row-meaning-root-review.json').exists()
(here / 'NEXT-TARGET.md').write_text(target)
(here / 'next-row-meaning-root-review.json').write_text(json.dumps(dict(
    status='ROOT_ACCEPTED_FOR_FRESH_BASELINE_AND_EXACT_STATEMENT_PROPOSAL_ONLY',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), checked_h17_proof_commit=proof,
    root_read_complete_contract_context_selected_route_erratum_budget_and_independent_review=True,
    live_indexed_sources=13, exact_original_cuts=21, exact_erratum_cuts=3,
    independent_review_sha256=sha(audit.read_bytes()), next_target_sha256=sha(target.encode()),
    target_module='SourceCurrentOriginalRowPhysicalMeaning.lean', public_theorem='row_inputs_meaning',
    optional_private_helper='original_of_readback', target_lines=[90,150], hard_stop_lines=180,
    codec_order_erratum_required=True, same_model_admission_required=True,
    bodies_or_compiler_authorized=False, haskell_changes=False, whole_goal_complete=False), indent=2) + '\n')
print(json.dumps(dict(status='PASS', live_sources=13, cuts=24, next_scope='exact statement proposal only')))
