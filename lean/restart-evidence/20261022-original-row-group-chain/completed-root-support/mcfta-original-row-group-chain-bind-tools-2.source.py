import ast
import datetime
import difflib
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
package = Path('/tmp/mcfta-original-row-group-chain-bound-preparation')
audit = Path('/tmp/mcfta-original-row-group-chain-bound-audit')
assert hashlib.sha256((audit / 'review.md').read_bytes()).hexdigest() == sys.argv[1]
for name, path in [('bound-preparation',package),('bound-audit',audit)]:
    assert (path / 'FROZEN.json').is_file()
    manifest = json.loads((path / 'pins.json').read_text())
    pins = [dict(path=name,**pin) for name,pin in manifest['files'].items()] if isinstance(manifest,dict) else manifest
    for pin in pins:
        data = (path / pin['path']).read_bytes()
        assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256'], pin['path']
    subprocess.run(['/usr/bin/python3',str(HERE / 'archive-extra.py'),str(path),name],check=True)
summary = json.loads((package / 'static-bindings-summary.json').read_text())
bindings = json.loads((package / 'literal-bindings.json').read_text())['tokens']
assert len(bindings) == 26 and len(summary['scripts']) == 9
line_count = assertion_count = 0
for name, pin in summary['scripts'].items():
    source = (package / 'predecessors' / name).read_text()
    for token, binding in bindings.items():
        if binding['kind'] == 'whole_quoted_json_literal':
            for quote in ['"', "'"]:
                source = source.replace(quote + token + quote,repr(json.dumps(binding['value'])))
        else:
            assert binding['kind'] == 'literal_text'
            source = source.replace(token,str(binding['value']))
    assert source.encode() == (package / name).read_bytes(), name
    assert hashlib.sha256(source.encode()).hexdigest() == pin['sha256']
    assert '__H22_' not in source
    lines = len(source.splitlines())
    assertions = sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(source)))
    assert lines == pin['lines'] and assertions == pin['assertions']
    line_count += lines
    assertion_count += assertions
    assert not (HERE / name).exists(), name
assert (line_count,assertion_count) == (809,273)
proposal = json.loads((package / 'proposed-source-history-gate.json').read_text())
assert proposal['status'] == 'PROPOSED_ONLY_PENDING_ROOT_REVIEW_NOT_INSTALLED'
history = proposal['proposed_root_gate']
assert history['status'] == 'ROOT_ACCEPTED' and len(history['variants']) == 2 and len(history['artifacts']) == 125
assert not history['patches'] and not history['rejected_public_types']
for pin in history['variants'] + history['artifacts']:
    path = Path(pin['path'])
    assert not path.is_absolute() and '..' not in path.parts
    data = (HERE / path).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], pin['path']
    if 'bytes' in pin:
        assert len(data) == pin['bytes']
    else:
        assert len(data.splitlines()) == pin['lines'] == 257
assert len({pin['sha256'] for pin in history['variants']}) == 1
assert history == bindings['__H22_SOURCE_HISTORY_JSON__']['value']
assert bindings['__H22_ACTUAL_JOBS__']['value'] == 3
assert bindings['__H22_AUDIT_BUILD_JOBS__']['value'] == 3639
assert bindings['__H22_AUDIT_DEPENDENCIES__']['value'] == 75499

metrics_path = HERE / 'actual-job-metrics.json'
before = metrics_path.read_text()
metrics = json.loads(before)
assert metrics['jobs']['original-row-group-chain-audit-1'][4] == 0
assert (HERE / 'original-row-group-chain-audit-1.log').read_text().count('\nwarning:') == 1
metrics['jobs']['original-row-group-chain-audit-1'][4] = 1
metrics['metadata_failures'] = 1
after = json.dumps(metrics,indent=2) + '\n'
diagnostics = HERE / 'metadata-diagnostics'
diagnostics.mkdir()
(diagnostics / 'actual-job-metrics-before-warning-fix.json').write_text(before)
(diagnostics / 'actual-job-metrics-warning-count.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='before',tofile='after')))
(diagnostics / 'note.md').write_text('# Audit warning count correction\n\nThe auxiliary root ledger used the source diagnostic format for Audit.\nAudit uses one warning prefix before its source location.\nCorrect its warning count from0 to1. Keep both bytes and the exact diff.\nThe bound verifier ledger already has the correct count.\nSource warnings, proof job totals and every proof result stay unchanged.\nNo prepared tool or proof command failed.\n')
failed = Path('/tmp/mcfta-original-row-group-chain-bind-tools-1.source.py')
fixed = Path(__file__)
shutil.copyfile(failed,diagnostics / 'bind-tools-failed-source.py')
shutil.copyfile(fixed,diagnostics / 'bind-tools-fixed-source.py')
(diagnostics / 'bind-tools-schema-fix.patch').write_text(''.join(difflib.unified_diff(failed.read_text().splitlines(True),fixed.read_text().splitlines(True),fromfile='bind-tools-before',tofile='bind-tools-after')))
with (diagnostics / 'note.md').open('a') as out:
    out.write('\nThe first root metadata installer failed before any package archive or tool installation.\nIt treated the bound package files dictionary as a list of pin rows.\nThe correction reads that dictionary and keeps the list schema for the independent audit.\nThe failed source, fixed source and exact diff remain. This is one metadata job failure.\nIt is not a Lean or prepared verifier failure.\n')
metrics_path.write_text(after)
assert metrics['jobs'] == bindings['__H22_JOBS_JSON__']['value']
for name in summary['scripts']:
    shutil.copyfile(package / name,HERE / name)
assert not (HERE / 'source-history-gate.json').exists()
(HERE / 'source-history-gate.json').write_text(json.dumps(history,indent=2)+'\n')
gate = dict(status='ROOT_ACCEPTED',observed_at=datetime.datetime.now().astimezone().isoformat(),
    root_whole_actual_bound_scripts_read=9,root_whole_actual_bound_lines_read=809,assertions=273,
    exact_literal_bindings=26,independent_review='bound-audit/review.md',independent_review_sha256=sys.argv[1],
    source_history_root_accepted=True,actual_jobs=3,failed_jobs=0,mathematical_repairs=0,
    audit_warning_count_correction_retained=True,prepared_tools_executed_at_gate=0,
    local_checkpoint_execution_authorized=True,network_commands_in_publisher=0,
    root_formalize_push_authorized=True,whole_goal_complete=False)
(HERE / 'bound-tools-review.json').write_text(json.dumps(gate,indent=2)+'\n')
with (HERE / 'current-progress.md').open('a') as out:
    out.write('\n## Bound metadata tools\n\nThe first root installer failed on the manifest schema before any archive or tool installation.\nThe corrected installer retains both sources and their exact diff.\nThe auxiliary Audit warning count is corrected from0 to1. Source warnings remain0.\nThe actual three proof jobs remain passed and unchanged.\n')
print(json.dumps(gate))
