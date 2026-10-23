exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import datetime
import difflib
import re
import shutil
cut = load(Path('/tmp/mcfta-cluster-admission-proof-verifier-plan/actual-cut.json'))
metadata = HERE / 'root-metadata-history'
assert not metadata.exists()
metadata.mkdir()
metadata_jobs = {}
for path in sorted(Path('/tmp').glob('mcfta-cluster-admission-*.json')):
    if not path.is_file():
        continue
    item = load(path)
    if not isinstance(item, dict) or 'wrapper' not in item or 'exit_code' not in item:
        continue
    assert Path(item['command'][0]).name not in {'lean', 'lake'}
    for suffix in ['.json', '.log', '.limits.json', '.usage.json', '.source.py', '.peaks.txt']:
        original = path.with_name(path.stem + suffix)
        assert original.is_file(), original
        shutil.copy2(original, metadata / original.name)
        assert sha(original) == sha(metadata / original.name)
    metadata_jobs['root-metadata-history/' + path.name] = item['exit_code']
failed_metadata = {key for key, value in metadata_jobs.items() if value}
assert failed_metadata == {'root-metadata-history/mcfta-cluster-admission-boundary-body-gate-1.json', 'root-metadata-history/mcfta-cluster-admission-outer-body-gate-1.json'}
save('root-metadata-history-cut.json', {
    'status': 'COMPLETE_TERMINAL_METADATA_CUT_BEFORE_CLOSING_TOOLS',
    'observed_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'jobs': metadata_jobs, 'failed_jobs': len(failed_metadata),
    'later_receipts': 'The final one-time completed-root-support collection retains closing receipts after this cut.',
})
jobs = {}
for row in cut['jobs']:
    stem = row['stem']
    receipt = load(HERE / (stem + '.json'))
    assert receipt['exit_code'] == row['exit_code']
    assert sha(HERE / receipt['log']) == row['raw']['sha256']
    jobs[stem] = dict(kind=row['kind'], module=row['module'], exit_code=receipt['exit_code'],
        source_sha256=receipt.get('sha256'), log_sha256=sha(HERE / receipt['log']),
        errors=row['errors'], source_warnings=row['source_warnings'])
actual = {}
for path in HERE.glob('*.json'):
    item = load(path)
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item and Path(item['command'][0]).name in {'lean', 'lake'}:
        actual[path.stem] = item
assert set(actual) == set(jobs) and len(jobs) == 12
save('job-history.json', jobs)
variants = []
for row in cut['variants']:
    path = Path(row['path'])
    assert sha(path) == row['sha256'] and len(path.read_bytes().splitlines()) == row['lines']
    variants.append(dict(module=row['module'], path=str(path.relative_to(HERE)),
        sha256=sha(path), lines=row['lines'], reason={
            'execution-source-v1': 'Initial reviewed body; strict1 rejected notation in simp function position.',
            'execution-source-v2': 'Selected exact-name simp repair; declarations and approved local statements unchanged.',
            'boundary-source-v1': 'Initial reviewed boundary; strict1 rejected notation quotation and dotted notation application.',
            'boundary-source-v2': 'Reviewed explicit constructor and parent-admission notation repair; strict2 still rejected projection quotation.',
            'boundary-source-v3': 'Selected reviewed Prod.fst and Prod.snd context repair; proof body unchanged from V2.',
            'outer-source-v1': 'Original reviewed strong-length induction and exact completed-state adapter; strict1 passed unchanged.',
        }[path.parent.name]))
patches = []
for row in cut['patches']:
    path = Path(row['patch']['path'])
    before, after = Path(row['before']), Path(row['after'])
    lines = path.read_text().splitlines()
    fromfile, tofile = lines[0][4:], lines[1][4:]
    expected = ''.join(difflib.unified_diff(before.read_text().splitlines(True), after.read_text().splitlines(True), fromfile=fromfile, tofile=tofile))
    assert path.read_text() == expected and sha(path) == row['patch']['sha256']
    patches.append(dict(module=row['module'], before=str(before.relative_to(HERE)),
        after=str(after.relative_to(HERE)), path=str(path.relative_to(HERE)), sha256=sha(path),
        reason=next(item['reason'] for item in variants if item['path'] == str(after.relative_to(HERE))),
        fromfile=fromfile, tofile=tofile))
artifacts = set()
def retain(path):
    assert path.is_file()
    artifacts.add(str(path.relative_to(HERE)))
for path in HERE.iterdir():
    if path.is_file() and (path.suffix == '.py' or path.name.startswith(('root-', 'actual-')) or path.name.endswith('-selected-source-gate.json') or path.name in {'selected-sources.json', 'frozen-modules.json', 'original-source-index.json', 'job-history.json'}):
        retain(path)
for stem, job in jobs.items():
    for suffix in ['.json', '.log', '.limits.json', '.usage.json']:
        retain(HERE / (stem + suffix))
    if job['source_sha256']:
        retain(HERE / (stem + '.source.lean'))
for directory in ['public-readback', 'root-metadata-history', 'original-sources',
    'execution-source-v1', 'execution-source-v2', 'boundary-source-v1', 'boundary-source-v2', 'boundary-source-v3', 'outer-source-v1']:
    for path in (HERE / directory).rglob('*'):
        if path.is_file():
            retain(path)
for directory in ['execution-declaration-plan', 'boundary-declaration-v3', 'outer-declaration-plan-v3',
    'execution-body-v2-audit', 'boundary-body-v3-audit', 'outer-body-audit',
    'execution-full-audit', 'boundary-full-audit', 'outer-full-audit',
    'execution-full-preparation', 'boundary-full-preparation-v3', 'outer-full-preparation']:
    for path in (HERE / directory).iterdir():
        if path.is_file():
            retain(path)
    selected = HERE / directory / 'selected'
    if selected.is_dir():
        for path in selected.iterdir():
            if path.is_file():
                retain(path)
selection = load(HERE / 'selected-sources.json')
save('source-history-gate.json', {
    'status': 'ROOT_ACCEPTED',
    'selected_sources': {path: record['sha256'] for path, record in selection.items()},
    'variants': variants,
    'artifacts': [dict(path=path, bytes=(HERE / path).stat().st_size, sha256=sha(HERE / path)) for path in sorted(artifacts)],
    'patches': patches, 'rejected_public_types': [],
})
print(json.dumps(dict(status='PASS', actual_jobs=len(jobs), source_jobs=sum(row['kind'] in {'strict', 'full'} for row in jobs.values()),
    focused_build_jobs=2, audit_jobs=1, failed_jobs=sum(row['exit_code'] != 0 for row in jobs.values()),
    metadata_jobs=len(metadata_jobs), failed_metadata_jobs=2, variants=len(variants), patches=len(patches), artifacts=len(artifacts),
    source_history_sha256=sha(HERE / 'source-history-gate.json'))))
