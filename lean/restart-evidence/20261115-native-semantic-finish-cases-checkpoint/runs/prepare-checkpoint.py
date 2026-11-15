from pathlib import Path
import ast
import datetime
import gzip
import hashlib
import json
import shlex
import subprocess

work = Path(__file__).parent
old = Path('lean/restart-evidence/20261115-native-ordered-consumers-and-edge-dispatch-checkpoint-work')
base = '26accea6aaa4f475bdac67f8721affea161bcb13'
code = subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip()
public = Path('lean/restart-evidence/20261115-native-semantic-finish-cases-publication')
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
               'new_public_theorem_probes': 4, 'new_public_definition_probes': 0,
               'private_c_ordinary_public_promotion_pending': False,
               'private_node_child_span_theorem_proved': True,
               'general_C_M_history_theorem_proved': False})
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
prior = Path('lean/restart-evidence/20261115-native-ordered-consumers-and-edge-dispatch-checkpoint')
pins = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
count = 0
for name, digest in pins.items():
    if name.startswith('lean/MicroCFTA/') and not name.endswith('/Audit.lean'):
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
        count += 1
(work / 'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps({
    'base': base, 'checked_code': code, 'prior_non_audit_sources_and_headers_byte_exact': count,
    'visibility_exports': [], 'modified_existing_sources': []}, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    driver = (old / name).read_text()
    driver = driver.replace('20261115-native-ordered-consumers-and-edge-dispatch-checkpoint',
                            '20261115-native-semantic-finish-cases-checkpoint')
    driver = driver.replace("BASE = '7b7bd483fde3234f3202e55d8b0779805cedc213'", "BASE = '" + base + "'")
    driver = driver.replace('# Ordered source consumers and actual edge events checkpoint',
                            '# Native semantic finish cases checkpoint')
    if name == 'assemble.py':
        driver = driver.replace("'promote-ordered-consumers.py', 'promote-results.py'", "'promote.py'")
        driver = driver.replace(", 'build-edge-query-dispatch.py'", "")
        driver = driver.replace("'publication-assembly-failures.json'", "'publication-assembly-failures.json', 'SCOPE-REVIEW.md'")
    (work / name).write_text(driver)
roots = [
    '20261115-current-general-c-ordinary-control-code-repair',
    '20261115-current-node-child-span-count-rewrite-repair',
    '20261115-current-general-cm-edge-finish-draft',
    '20261115-current-body-first-authentic-finish-draft',
    '20261115-current-body-first-authentic-finish-whole-history-repair',
    '20261115-native-general-c-ordinary-finish-check',
    '20261115-native-general-c-ordinary-control-code-check',
    '20261115-native-node-child-span-before-finish-check',
    '20261115-native-observed-span-edge-and-authentic-body-first-check',
    '20261115-native-semantic-finish-cases-publication',
]
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
runs = [('20261115-native-general-c-ordinary-finish-check', 44028, 1),
        ('20261115-native-general-c-ordinary-control-code-check', 8041, 0),
        ('20261115-native-node-child-span-before-finish-check', 46027, 1),
        ('20261115-native-observed-span-edge-and-authentic-body-first-check', 16779, 0)]
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
