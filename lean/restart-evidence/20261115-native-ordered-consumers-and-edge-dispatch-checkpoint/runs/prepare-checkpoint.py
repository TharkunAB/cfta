from pathlib import Path
import ast
import datetime
import gzip
import hashlib
import json
import shlex
import subprocess

work = Path(__file__).parent
old = Path('lean/restart-evidence/20261115-native-edge-and-mu-profile-checkpoint-work')
base = '7b7bd483fde3234f3202e55d8b0779805cedc213'
code = subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip()
public = Path('lean/restart-evidence/20261115-native-ordered-consumers-and-edge-dispatch-publication')
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in result['checks'])
surface = json.loads((work / 'public-surface.json').read_text())
config = json.loads((old / 'checkpoint-config.json').read_text())
config.update(result)
config.update({'checked_code': code, 'public_run': str(public.resolve()), 'public_gates': 5,
               'explicit_reports': surface['expected_explicit_reports'],
               'source_files': surface['sources'], 'direct_audit_imports': surface['direct_audit_imports'],
               'new_public_modules': len(surface['modules']), 'new_public_statements': surface['new_statements']})
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
prior = Path('lean/restart-evidence/20261115-native-edge-and-mu-profile-checkpoint')
pins = json.loads(gzip.decompress((prior / 'source-pins.json.gz').read_bytes()))
count = 0
for name, digest in pins.items():
    if name.startswith('lean/MicroCFTA/') and not name.endswith('/Audit.lean'):
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
        count += 1
compatibility = {'base': base, 'checked_code': code, 'prior_non_audit_sources_and_headers_byte_exact': count,
                 'visibility_exports': [], 'modified_existing_sources': []}
(work / 'PUBLIC-API-COMPATIBILITY.json').write_text(json.dumps(compatibility, indent=2) + '\n')
for name in ['assemble.py', 'finalize.py', 'verify.py']:
    driver = (old / name).read_text()
    driver = driver.replace('20261115-native-edge-and-mu-profile-checkpoint',
                            '20261115-native-ordered-consumers-and-edge-dispatch-checkpoint')
    driver = driver.replace("BASE = '439604901ad0c1cc7fa30b6e6cfbc4e637097d60'", "BASE = '" + base + "'")
    driver = driver.replace('# Checked edge and Mu profiles with actual event receipts checkpoint',
                            '# Ordered source consumers and actual edge events checkpoint')
    (work / name).write_text(driver)
driver = (work / 'assemble.py').read_text().replace("'build-node-query-dispatch.py'", "'build-edge-query-dispatch.py'").replace("'promote.py'", "'promote-ordered-consumers.py', 'promote-results.py'").replace(", 'prepare-private-canonical.py'", "")
(work / 'assemble.py').write_text(driver)
roots = ['20261115-source-ordered-mixed-ordinary-child-qualification-draft', '20261115-current-ordered-finite-prefix-reference-control-draft', '20261115-current-ordered-mixed-reference-node-profile-draft', '20261115-original-m-native-union-profile-draft', '20261115-current-edge-query-dispatch-origin-draft', '20261115-current-general-cm-history-draft', '20261115-current-general-cm-history-width-pin-draft', '20261115-current-general-cm-history-support-proof-repair', '20261115-native-ordered-source-consumers-check', '20261115-native-ordered-reference-union-and-cm-definitions-check', '20261115-native-ordered-results-edge-dispatch-and-cm-support-check', '20261115-native-ordered-consumers-and-edge-dispatch-publication', '20261115-current-general-c-ordinary-finish-draft', '20261115-current-general-c-ordinary-control-code-repair', '20261115-native-general-c-ordinary-finish-check', '20261115-native-general-c-ordinary-control-code-check', '20261115-current-node-child-span-before-finish-draft', '20261115-native-node-child-span-before-finish-check']
assert all((Path('lean/restart-evidence') / name).is_dir() for name in roots)
selection = {'selected_roots': len(roots), 'all_promotion_parents_included': True,
             'active_next_writers_excluded': True, 'compiled_objects_excluded': True}
(work / 'archive-roots.json').write_text(json.dumps(['lean/restart-evidence/' + name for name in roots], indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps(selection, indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({
    'prior_archives_not_copied': True, 'this_work_root_excluded': True,
    'excluded_next_tasks': ['Complete C-ordinary semantic finish', 'Syntactic actual child-span bound', 'Authentic body-first outer finish', 'Full strengthened C/M history assembly']}, indent=2) + '\n')
(work / 'prior-working-roots.json').write_text(json.dumps({'previous_work_root': str(old),
    'prior_immutable_checkpoint': str(prior)}, indent=2) + '\n')
commits = [dict(zip(['commit', 'subject'], line.split('\0', 1))) for line in
           subprocess.check_output(['git', 'log', '--reverse', '--format=%H%x00%s', base + '..HEAD']).decode().splitlines()]
(work / 'code-commits.json').write_text(json.dumps(commits, indent=2) + '\n')
(work / 'remaining-full-proof-template.md').write_bytes((old / 'remaining-full-proof-template.md').read_bytes())
preview = []
runs = [('20261115-native-ordered-source-consumers-check', 19451, 0), ('20261115-native-ordered-reference-union-and-cm-definitions-check', 13578, 1), ('20261115-native-ordered-results-edge-dispatch-and-cm-support-check', 34798, 0)]
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
