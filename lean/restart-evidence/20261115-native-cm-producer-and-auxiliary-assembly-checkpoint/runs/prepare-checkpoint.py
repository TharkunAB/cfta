from pathlib import Path
import ast
import datetime
import gzip
import hashlib
import json
import shlex
import subprocess

work = Path(__file__).parent
old = Path('lean/restart-evidence/20261115-native-semantic-finish-cases-checkpoint-work')
base = '299db36637ea5997b592488aad1c8e16134764c0'
code = subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip()
public = Path('lean/restart-evidence/20261115-native-cm-producer-and-auxiliary-assembly-publication-final')
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in result['checks'])
surface = json.loads((work / 'public-surface.json').read_text())
config = json.loads((old / 'checkpoint-config.json').read_text())
config.update(result)
config.update({'checked_code': code, 'public_run': str(public.resolve()), 'public_gates': 5,
               'explicit_reports': surface['expected_explicit_reports'],
               'source_files': surface['sources'], 'direct_audit_imports': surface['direct_audit_imports'],
               'new_public_modules': 4, 'new_public_statements': 4,
               'new_public_theorem_probes': 4, 'new_shared_helper_probes': 5, 'visibility_exports': 5, 'new_public_definition_probes': 0,
               'private_c_ordinary_public_promotion_pending': False,
               'private_node_child_span_theorem_proved': True,
               'general_C_M_history_theorem_proved': False})
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
prior = Path('lean/restart-evidence/20261115-native-semantic-finish-cases-checkpoint')
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
(work / 'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({
    'base': base, 'checked_code': code, 'prior_non_audit_sources_and_headers_byte_exact': count,
    'visibility_only_modified_sources': len(exports), 'visibility_exports': list(exports.values()),
    'all_logical_signatures_and_proof_texts_unchanged': True,
    'other_modified_existing_sources': []}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    driver = (old / name).read_text()
    driver = driver.replace('20261115-native-semantic-finish-cases-checkpoint',
                            '20261115-native-cm-producer-and-auxiliary-assembly-checkpoint')
    driver = driver.replace("BASE = '26accea6aaa4f475bdac67f8721affea161bcb13'", "BASE = '" + base + "'")
    driver = driver.replace('# Native semantic finish cases checkpoint',
                            '# Mixed native producer cases checkpoint')
    if name == 'assemble.py':
        driver = driver.replace("'promote-ordered-consumers.py', 'promote-results.py'", "'promote.py'")
        driver = driver.replace(", 'build-edge-query-dispatch.py'", "")
        driver = driver.replace("'SCOPE-REVIEW.md'", "'SCOPE-REVIEW.md', 'AUTHENTIC-AUXILIARY-DEPENDENCIES.md', 'build-m-union.py', 'prepare-public-final.py', 'shared-helper-visibility-before.lean.txt', 'shared-helper-visibility.patch', 'qualified-key-visibility-before.lean.txt', 'qualified-key-visibility.patch'")
    (work / name).write_text(driver)
roots = ['20261115-current-general-m-ordinary-finish-draft', '20261115-current-general-m-ordinary-explicit-entry-control-repair', '20261115-current-general-m-union-finish-draft', '20261115-current-general-c-node-finish-draft', '20261115-current-general-c-node-finish-universe-and-reset-repair', '20261115-current-general-c-node-finish-mu-normalization-repair', '20261115-native-m-ordinary-shared-helper-consumer-check', '20261115-native-m-ordinary-explicit-entry-control-check', '20261115-native-general-c-node-finish-check', '20261115-native-general-c-and-m-union-finish-check', '20261115-native-cm-producer-and-auxiliary-assembly-publication', '20261115-current-general-m-reference-node-finish-draft', '20261115-native-c-node-mu-and-m-reference-finish-check', '20261115-native-cm-producer-and-auxiliary-assembly-publication-final', '20261115-current-diagonal-authentic-finish-draft', '20261115-native-authentic-diagonal-outer-finish-check']
assert all((Path('lean/restart-evidence') / name).is_dir() for name in roots)
(work / 'archive-roots.json').write_text(json.dumps(['lean/restart-evidence/' + name for name in roots], indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps({
    'selected_roots': len(roots), 'all_promotion_parents_included': True,
    'active_next_writers_excluded': True, 'compiled_objects_excluded': True,
    'earlier_failed_span_raw_and_failed_CM_support_retained_in_prior_checkpoint': True,
    'narrow_body_first_packet_preserved_without_full_scope_credit': True}, indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({
    'prior_archives_not_copied': True, 'this_work_root_excluded': True,
    'excluded_next_tasks': ['All C node finish cases', 'Remaining authentic body-first-key and diagonal auxiliary cases',
                            'Full strengthened C/M history assembly']}, indent=2) + '\n')
(work / 'prior-working-roots.json').write_text(json.dumps({'previous_work_root': str(old),
    'prior_immutable_checkpoint': str(prior)}, indent=2) + '\n')
commits = [dict(zip(['commit', 'subject'], line.split('\0', 1))) for line in
           subprocess.check_output(['git', 'log', '--reverse', '--format=%H%x00%s', base + '..HEAD']).decode().splitlines()]
(work / 'code-commits.json').write_text(json.dumps(commits, indent=2) + '\n')
(work / 'remaining-full-proof-template.md').write_bytes((old / 'remaining-full-proof-template.md').read_bytes())
preview = []
runs = [('20261115-native-m-ordinary-shared-helper-consumer-check', 44409, 1), ('20261115-native-m-ordinary-explicit-entry-control-check', 58802, 0), ('20261115-native-general-c-node-finish-check', 1619, 1), ('20261115-native-general-c-and-m-union-finish-check', 54058, 1), ('20261115-native-c-node-mu-and-m-reference-finish-check', 19864, 0)]
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
