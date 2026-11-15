from pathlib import Path
import ast
import datetime
import gzip
import hashlib
import json
import shlex
import subprocess

work = Path(__file__).parent
old = Path('lean/restart-evidence/20261115-native-producer-origins-and-closed-reset-checkpoint-work')
base = '6e467466aec2919af58c2c904660e05bd7af36d1'
code = subprocess.check_output(['git', 'rev-parse', 'HEAD']).decode().strip()
public = Path('lean/restart-evidence/20261115-native-edge-producers-and-mixed-cases-publication')
result = json.loads((public / 'checked.json').read_text())
assert len(result['checks']) == 5
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in result['checks'])
config = json.loads((old / 'checkpoint-config.json').read_text())
config.update(result)
config.update({'checked_code': code, 'public_run': str(public.resolve()), 'public_gates': 5,
               'explicit_reports': 369, 'source_files': 6091, 'direct_audit_imports': 5091,
               'new_public_modules': 3, 'new_public_statements': 4})
(work / 'checkpoint-config.json').write_text(json.dumps(config, indent=2) + '\n')
pins = json.loads(gzip.decompress(Path('lean/restart-evidence/20261115-native-producer-origins-and-closed-reset-checkpoint/source-pins.json.gz').read_bytes()))
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
    driver = driver.replace('20261115-native-producer-origins-and-closed-reset-checkpoint',
                            '20261115-native-edge-producers-and-mixed-cases-checkpoint')
    driver = driver.replace("BASE = 'f7c8de38c27fced37fe893a11d8aa645b866a328'", "BASE = '" + base + "'")
    driver = driver.replace('# Native producer origins and closed reset checkpoint', '# Checked edge producers and native mixed cases checkpoint')
    (work / name).write_text(driver)
driver = (work / 'assemble.py').read_text().replace("'promote.py', 'publication-assembly-failures.json'",
                                                   "'promote.py', 'publication-assembly-failures.json', 'prepare-checkpoint.py'")
(work / 'assemble.py').write_text(driver)
(work / 'publication-assembly-failures.json').write_text('[]\n')
roots = [
    '20261115-current-edge-compile-dispatch-origin-draft',
    '20261115-current-ordinary-node-profile-raw-producer-draft',
    '20261115-current-ordinary-node-profile-index-generalization-repair',
    '20261115-current-ordinary-node-profile-isolated-list-induction-repair',
    '20261115-original-m-reference-node-profile-draft',
    '20261115-original-m-reference-node-profile-bound-repair',
    '20261115-native-original-m-reference-node-profile-check',
    '20261115-native-edge-compiled-origin-ordinary-profile-check',
    '20261115-native-edge-ordinary-mixed-reference-check',
    '20261115-native-edge-ordinary-mixed-reference-repaired-check',
    '20261115-native-edge-producers-and-mixed-cases-publication',
]
assert all((Path('lean/restart-evidence') / name).is_dir() for name in roots)
selection = {'selected_roots': len(roots), 'all_promotion_parents_included': True,
             'active_next_writers_excluded': True, 'compiled_objects_excluded': True}
(work / 'archive-roots.json').write_text(json.dumps(['lean/restart-evidence/' + name for name in roots], indent=2) + '\n')
(work / 'selection-review.json').write_text(json.dumps(selection, indent=2) + '\n')
(work / 'skipped-published-roots.json').write_text(json.dumps({'prior_archives_not_copied': True, 'this_work_root_excluded': True,
    'excluded_next_tasks': ['Actual-prefix-scoped dual Returned induction', 'Original-M row-child admission', 'Closed union producer']}, indent=2) + '\n')
(work / 'prior-working-roots.json').write_text(json.dumps({'previous_work_root': str(old),
    'prior_immutable_checkpoint': 'lean/restart-evidence/20261115-native-producer-origins-and-closed-reset-checkpoint'}, indent=2) + '\n')
commits = [dict(zip(['commit', 'subject'], line.split('\0', 1))) for line in
           subprocess.check_output(['git', 'log', '--reverse', '--format=%H%x00%s', base + '..HEAD']).decode().splitlines()]
(work / 'code-commits.json').write_text(json.dumps(commits, indent=2) + '\n')
for name in ['remaining-full-proof-template.md']:
    (work / name).write_bytes((old / name).read_bytes())
preview = []
runs = [('20261115-native-original-m-reference-node-profile-check', 54904, 1),
        ('20261115-native-edge-compiled-origin-ordinary-profile-check', 7653, 1),
        ('20261115-native-edge-ordinary-mixed-reference-check', 9011, 1),
        ('20261115-native-edge-ordinary-mixed-reference-repaired-check', 9841, 0)]
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
(work / 'terminal-object-cleanup-preview.json').write_text(json.dumps({'at': datetime.datetime.now().astimezone().isoformat(), 'targets': preview}, indent=2) + '\n')
print(json.dumps({'checked_code': code, 'prior_sources_preserved': count, 'archive_roots': len(roots), 'cleanup_preview': preview}))
