from pathlib import Path
import ast
import datetime
import gzip
import hashlib
import json
import shlex
import subprocess

work = Path(__file__).parent
old = Path('lean/restart-evidence/20261115-native-cm-producer-and-auxiliary-assembly-checkpoint-work')
base = 'bb5ff7040064398e548cac454b75da5084522ac3'
code = subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip()
assert code == '84c2d9d38cd42d43856d0d7d33302622e1eeb6df'
public = Path('lean/restart-evidence/20261115-authentic-inner-histories-publication')
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in result['checks'])
assert result['general_C_M_history_theorem_proved']
surface = json.loads((work / 'public-surface.json').read_text())
config = json.loads((old / 'checkpoint-config.json').read_text())
config.update(result)
config.update({'checked_code': code, 'public_run': str(public.resolve()), 'public_gates': 5,
               'explicit_reports': surface['expected_explicit_reports'],
               'source_files': surface['sources'], 'direct_audit_imports': surface['direct_audit_imports'],
               'new_public_modules': 5, 'new_public_statements': 5,
               'new_public_theorem_probes': 5, 'new_shared_helper_probes': 2,
               'visibility_exports': 2, 'new_public_definition_probes': 0,
               'general_C_M_history_theorem_proved': True,
               'native_CM_memo_history_all_actual_prefixes_proved': True,
               'full_worker_and_joint_finite_completion_still_open': True})
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
prior = Path('lean/restart-evidence/20261115-native-cm-producer-and-auxiliary-assembly-checkpoint')
pins = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
count = 0
exports = {item['path']: item for item in json.loads((work / 'visibility-exports.json').read_text())}
for name, digest in pins.items():
    if not name.startswith('lean/MicroCFTA/') or name.endswith('/Audit.lean'):
        continue
    if name in exports:
        item = exports[name]
        before = subprocess.check_output(['git', 'show', base + ':' + name]).decode()
        assert hashlib.sha256(before.encode()).hexdigest() == digest == item['before_sha256']
        expected = before
        for theorem in item['exports']:
            marker = 'private theorem ' + theorem
            assert expected.count(marker) == 1
            expected = expected.replace(marker, 'theorem ' + theorem, 1)
        assert Path(name).read_text() == expected
        assert hashlib.sha256(expected.encode()).hexdigest() == item['after_sha256']
    else:
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
        count += 1
assert count == 6112
(work / 'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({
    'base': base, 'checked_code': code, 'prior_non_audit_sources_and_headers_byte_exact': count,
    'visibility_only_modified_sources': len(exports), 'visibility_exports': list(exports.values()),
    'all_logical_signatures_and_proof_texts_unchanged': True,
    'other_modified_existing_sources': []}, indent=2) + '\n')
extra = ['current-board-request.json', 'current-board-canonical.json', 'PUBLIC-API-COMPATIBILITY.json',
         'retention-sample.json', 'usage-sample.json', 'upstream-heads.json', 'upstream-fetch.txt',
         'terminal-object-cleanup-preview.json', 'terminal-object-cleanup.json', 'WIP.json',
         'visibility-exports.json', 'promotion.json', 'code-commits.json', 'prior-working-roots.json',
         'public-surface.json', 'checkpoint-note-template.md', 'prepare-private.py', 'prepare-public.py',
         'remaining-full-proof-template.md', 'terminal-handles.json', 'modified-public.json',
         'EndpointWarmProbes.lean.txt', 'independent-examples.json', 'CURRENT-SCOPE.md', 'SCOPE-REVIEW.md',
         'WORKER-FRONTIER.md', 'plan-helper-visibility-before.lean.txt', 'plan-helper-visibility.patch',
         'prepare-checkpoint.py']
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    driver = (old / name).read_text()
    driver = driver.replace('20261115-native-cm-producer-and-auxiliary-assembly-checkpoint',
                            '20261115-native-general-cm-history-checkpoint')
    driver = driver.replace("BASE = '299db36637ea5997b592488aad1c8e16134764c0'", "BASE = '" + base + "'")
    driver = driver.replace('# Mixed native producer cases checkpoint', '# Full native C/M history checkpoint')
    if name == 'assemble.py':
        begin = driver.index('EXTRA = ')
        end = driver.index('\nSKIP_DIRS', begin)
        driver = driver[:begin] + 'EXTRA = [Path(__file__).parent / name for name in ' + repr(extra) + ']' + driver[end:]
    (work / name).write_text(driver)
roots = ['20261115-current-diagonal-authentic-finish-draft',
         '20261115-native-authentic-diagonal-outer-finish-check',
         '20261115-current-authentic-body-first-inner-histories-draft',
         '20261115-current-authentic-coherent-inner-history-draft',
         '20261115-authentic-inner-histories-first-check',
         '20261115-current-general-m-node-finish-draft',
         '20261115-native-general-m-node-finish-check',
         '20261115-current-general-cm-actual-prefix-assembly-draft',
         '20261115-native-general-cm-actual-prefix-assembly-check',
         '20261115-authentic-inner-histories-publication',
         '20261115-full-source-coupled-integration-audit-draft']
assert all((Path('lean/restart-evidence') / name).is_dir() for name in roots)
(work / 'archive-roots.json').write_text(json.dumps(['lean/restart-evidence/' + name for name in roots], indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'selected_roots': len(roots), 'all_promotion_parents_included': True,
    'active_next_writers_excluded': True, 'compiled_objects_excluded': True,
    'all_prior_failures_counterexamples_and_repairs_retained_in_immutable_ancestors': True,
    'original_full_native_CM_header_preserved': True,
    'marked_open_worker_targets_retained_without_proof_credit': True}, indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({
    'prior_archives_not_copied': True, 'this_work_root_excluded': True,
    'excluded_next_tasks': ['Actual source-worker admission and warm histories',
                            'Actual prepared ROWS resources at original arbitrary budget',
                            'One compatible finite accepted completion and Haskell correspondence']}, indent=2) + '\n')
(work / 'prior-working-roots.json').write_text(json.dumps({'previous_work_root': str(old),
    'prior_immutable_checkpoint': str(prior)}, indent=2) + '\n')
commits = [dict(zip(['commit', 'subject'], line.split('\0', 1))) for line in
           subprocess.check_output(['git', 'log', '--reverse', '--format=%H%x00%s', base + '..HEAD']).decode().splitlines()]
(work / 'code-commits.json').write_text(json.dumps(commits, indent=2) + '\n')
preview = []
runs = [('20261115-native-authentic-diagonal-outer-finish-check', 64655, 0),
        ('20261115-authentic-inner-histories-first-check', 2224, 0),
        ('20261115-native-general-m-node-finish-check', 86321, 0),
        ('20261115-native-general-cm-actual-prefix-assembly-check', 60992, 0)]
for run, session, exitcode in runs:
    tree = ast.parse((Path('lean/restart-evidence') / run / 'check.py').read_text())
    jobs = next(ast.literal_eval(node.value) for node in ast.walk(tree) if isinstance(node, ast.Assign)
                and any(isinstance(target, ast.Name) and target.id == 'jobs' for target in node.targets))
    outputs = [shlex.split(command)[shlex.split(command).index('-o') + 1] for _, command, _ in jobs if '-o ' in command]
    objects = Path(outputs[0]).parent
    assert all(Path(output).parent == objects for output in outputs)
    files = list(objects.rglob('*'))
    assert not any(path.is_symlink() for path in files)
    preview.append({'run': run, 'session': session, 'exit': exitcode, 'objects': str(objects),
                    'file_bytes': sum(path.stat().st_size for path in files if path.is_file())})
(work / 'terminal-object-cleanup-preview.json').write_text(json.dumps({
    'at': datetime.datetime.now().astimezone().isoformat(), 'targets': preview}, indent=2) + '\n')
print(json.dumps({'checked_code': code, 'prior_sources_preserved': count,
                  'archive_roots': len(roots), 'cleanup_preview': preview}))
