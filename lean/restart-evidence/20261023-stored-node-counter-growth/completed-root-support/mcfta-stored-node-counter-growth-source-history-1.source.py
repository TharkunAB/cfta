exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import datetime, re, shutil
metadata = HERE / 'root-metadata-history'
metadata.mkdir()
metadata_jobs = {}
for path in sorted(Path('/tmp').glob('mcfta-stored-node-counter-growth-*.json')):
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
failures = [path for path, code in metadata_jobs.items() if code != 0]
assert failures == []
save('root-metadata-history-cut.json', dict(status='COMPLETE_TERMINAL_METADATA_CUT_BEFORE_CLOSING_TOOLS',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), jobs=metadata_jobs, failed_jobs=len(failures),
    later_receipts='The one-time completed-root-support collection retains all closing receipts after this cut.'))
specs = {'strict1': ('strict', NAME), 'FULL1': ('full', NAME), 'audit1': ('audit', None)}
actual = {}
for path in HERE.glob('*.json'):
    item = load(path)
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item and Path(item['command'][0]).name in {'lean', 'lake'}:
        actual[path.stem] = item
assert set(actual) == set(specs)
jobs = {}
for stem, (kind, module) in specs.items():
    receipt = actual[stem]
    raw = (HERE / receipt['log']).read_text()
    jobs[stem] = dict(kind=kind, module=module, exit_code=receipt['exit_code'], source_sha256=receipt.get('sha256'),
        log_sha256=sha(HERE / receipt['log']),
        errors=len(re.findall(r'^.+?:\d+:\d+: error(?:\([^)]*\))?:', raw, re.M)),
        source_warnings=len(re.findall(r'^.+?:\d+:\d+: warning(?:\([^)]*\))?:', raw, re.M)))
    assert load(HERE / receipt['limits']) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
    usage = load(HERE / (stem + '.usage.json'))
    assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
assert (HERE / 'strict1.log').read_bytes() == b''
assert all(job['exit_code'] == job['errors'] == job['source_warnings'] == 0 for job in jobs.values())
save('job-history.json', jobs)
variant_path = 'variants/v1/' + NAME + '.lean'
source = HERE / variant_path
lines = len(source.read_bytes().splitlines())
assert lines == 82 and lines <= 160
variants = [dict(module=NAME, path=variant_path, sha256=sha(source), lines=lines,
    reason='The single reviewed body passed the first strict check and the sole complete public-output check unchanged.')]
assert sha(source) == sha(HERE / (NAME + '.lean')) == load(HERE / 'selected-source-gate.json')['source_sha256']
preparation = load(HERE / 'canonical-preparation-history.json')
assert preparation['status'] == 'EARLY_EVIDENCE_COPY_RETAINED_BEFORE_MATERIALIZER'
assert preparation['sha256'] == sha(source) and (HERE / preparation['retained_copy']).read_bytes() == source.read_bytes()
assert all(preparation[key] for key in ['no_guard_changed', 'no_Lean_source_changed', 'no_proof_job_repeated'])
excluded = {'source-history-gate.json', 'actual-proof-cut.json', 'archived-components.json', 'current-progress.md', variant_path}
artifacts = []
for path in sorted(HERE.rglob('*')):
    if path.is_file() and str(path.relative_to(HERE)) not in excluded:
        artifacts.append(dict(path=str(path.relative_to(HERE)), bytes=path.stat().st_size, sha256=sha(path)))
assert not {row['path'] for row in variants} & {row['path'] for row in artifacts}
assert preparation['retained_copy'] in {row['path'] for row in artifacts}
assert 'canonical-preparation-history.json' in {row['path'] for row in artifacts}
selection = load(HERE / 'selected-sources.json')
save('source-history-gate.json', dict(status='ROOT_ACCEPTED', selected_sources={p: r['sha256'] for p, r in selection.items()},
    variants=variants, artifacts=artifacts, patches=[], rejected_public_types=[]))
raw = (HERE / 'audit1.log').read_text()
build = re.search(r'Build completed successfully \((\d+) jobs\)\.', raw)
dependencies = re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems', raw)
assert build and dependencies
warnings = re.findall(r'(?m)^warning: .+$', raw)
assert len(warnings) == 1 and 'InternedFreshOrdinaryClosedCompletion.lean:24:5:' in warnings[0]
metrics = dict(actual_jobs=len(jobs), source_jobs=sum(j['kind'] in {'strict', 'full'} for j in jobs.values()),
    focused_build_jobs=sum(j['kind'] == 'focused_build' for j in jobs.values()), audit_jobs=sum(j['kind'] == 'audit' for j in jobs.values()),
    failed_jobs=sum(j['exit_code'] != 0 for j in jobs.values()),
    warned_source_exit_zero_jobs=sum(j['kind'] in {'strict', 'full'} and j['exit_code'] == 0 and j['source_warnings'] > 0 for j in jobs.values()),
    rejected_public_type_jobs=0)
save('actual-proof-cut.json', dict(status='ACTUAL_AUDIT_AND_HISTORY_BOUND', metrics=metrics,
    audit=dict(stem='audit1', build_jobs=int(build.group(1)), dependencies=int(dependencies.group(1)), log_sha256=sha(HERE / 'audit1.log'), warnings=warnings),
    metadata_jobs=len(metadata_jobs), failed_metadata_jobs=len(failures), metadata_failure_paths=failures,
    variants=len(variants), patches=0, artifacts=len(artifacts), source_history_sha256=sha(HERE / 'source-history-gate.json'),
    original_Audit_sha256=sha(HERE / 'original-sources/Audit.original.lean.txt')))
print(json.dumps(load(HERE / 'actual-proof-cut.json')))
