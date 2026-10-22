import datetime
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
audit = Path('/tmp/mcfta-original-row-group-chain-public-type-audit')
assert hashlib.sha256((audit / 'review.md').read_bytes()).hexdigest() == sys.argv[1]
for pin in json.loads((audit / 'pins.json').read_text()):
    data = (audit / pin['path']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(audit), 'public-type-audit'], check=True)
source = (HERE / 'SourceCurrentOriginalRowGroupChain.lean').read_bytes()
sha = hashlib.sha256(source).hexdigest()
assert sha == '45ee19aba69aec9339203917841052791a389fe46f511ab9574105c8f3d254bb' and len(source.splitlines()) == 257
assert source == (HERE / 'original-row-group-chain-strict-1.source.lean').read_bytes()
assert (HERE / 'original-row-group-chain-strict-1.log').read_bytes() == b''
report = json.loads((HERE / 'public-readback/original-row-group-chain-full-readback.json').read_text())
head = report['heads'][0]
assert head['head'] == 'MicroCFTA.SourceCurrentOriginalRowGroupChain.groups_complete'
checked = (HERE / 'public-readback/original-row-group-chain-groups_complete-public-type.txt').read_bytes()
printed = (HERE / 'public-readback/original-row-group-chain-groups_complete-printed-public-type.txt').read_bytes()
assert len(checked) == 111557 and len(checked.splitlines()) == 1156
assert hashlib.sha256(checked).hexdigest() == head['checked_type_sha256']
assert checked == printed and head['check_print_type_byte_identity']
assert not any(marker in checked.decode() for marker in ['_private', '✝', '†', '‡', 'MicroCFTA.SourceCurrentOriginalRowGroupChain.bucket_readback'])
assert head['actual_axioms'] == ['Classical.choice','Quot.sound','propext']
assert hashlib.sha256((HERE / 'original-row-group-chain-public-1.log').read_bytes()).hexdigest() == report['log_sha256']
review = json.loads((HERE / 'verifier-preparation/root-full-review-schema.json').read_text())['required_actual_root_review_fields']
review.update(source_sha256=sha, source_lines=257,
    types_sha256={'groups_complete':head['checked_type_sha256']}, full_raw_sha256=report['log_sha256'],
    actual_axioms_by_head={'groups_complete':head['actual_axioms']},
    raw_type_byte_identity_by_head={'groups_complete':True}, root_printed_type_byte_identity_verified=True,
    observed_at=datetime.datetime.now().astimezone().isoformat(),
    independent_review='public-type-audit/review.md', independent_review_sha256=sys.argv[1],
    complete_checked_type_lines=1156, complete_checked_type_bytes=111557,
    root_manual_read_scope='Complete checked TYPE: lines1-100 with original spacing, lines101-1156 with leading ASCII spaces removed for display only. Every token and line was displayed. Raw bytes are retained unchanged. Axiom slice read. Printed TYPE and whole BODY checked programmatically, without a second manual TYPE or whole BODY read.')
(HERE / 'root-full-review.json').write_text(json.dumps(review, indent=2) + '\n')
name = 'lean/MicroCFTA/SourceCurrentOriginalRowGroupChain.lean'
snapshot = HERE / 'selected-sources/SourceCurrentOriginalRowGroupChain.lean'
assert not snapshot.exists() and not (ROOT / name).exists()
snapshot.parent.mkdir()
snapshot.write_bytes(source)
(HERE / 'selected-source-gate.json').write_text(json.dumps(dict(status='ROOT_ACCEPTED',path=name,sha256=sha,lines=257,snapshot=str(snapshot.relative_to(HERE))),indent=2)+'\n')
(HERE / 'selected-sources.json').write_text(json.dumps({name:dict(sha256=sha,lines=257,strict='original-row-group-chain-strict-1',full='original-row-group-chain-public-1')},indent=2)+'\n')
(HERE / 'frozen-modules.json').write_text(json.dumps({'SourceCurrentOriginalRowGroupChain':sha},indent=2)+'\n')
original = (HERE / 'original-sources/Audit.original.lean.txt').read_bytes()
assert hashlib.sha256(original).hexdigest() == '4c54e8f578cc9e12084e7306671e6c6410150811a3868fc128b90805ae5452e1'
target = ROOT / 'lean/MicroCFTA/Audit.lean'
assert target.read_bytes() == original
addition = b'import MicroCFTA.SourceCurrentOriginalRowGroupChain\n'
assert addition not in original
(ROOT / name).write_bytes(source)
target.write_bytes(addition + original)
assert target.read_bytes().replace(addition,b'',1) == original
with (HERE / 'current-progress.md').open('a') as out:
    out.write('\n## Accepted public theorem\n\n')
    out.write('The257-line proof passes its first strict with a literal-empty log.\n')
    out.write('The sole FULL and metadata reader pass. Complete checked TYPE has1156 lines\n')
    out.write('and111557 bytes. Both raw TYPE views are identical. Actual axioms are\n')
    out.write('Classical.choice, Quot.sound and propext. Root and independent whole-TYPE\n')
    out.write('reviews pass. Complete BODY remains retained and checked programmatically.\n')
    out.write('The official module is installed with the sole Audit import. Audit is pending.\n')
    out.write('No Haskell changes or whole-goal completion is claimed.\n')
print(json.dumps({'status':'PASS','source_lines':257,'public_type_lines':1156,'installed':name,'Audit':'PENDING'}))
