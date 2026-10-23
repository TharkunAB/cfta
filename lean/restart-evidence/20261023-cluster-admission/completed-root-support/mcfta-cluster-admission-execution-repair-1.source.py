exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import difflib
before = Path('/tmp/mcfta-cluster-admission-execution-source-v1') / (NAME + '.lean')
owner = Path('/tmp/mcfta-cluster-admission-execution-source-v2')
assert not owner.exists()
owner.mkdir()
old = before.read_text()
new = old.replace('[execute,', '[SourceCurrentOriginalRowClusterScan.execute,').replace('[Nat.succ_add, execute,', '[Nat.succ_add, SourceCurrentOriginalRowClusterScan.execute,')
assert new != old and len(new.splitlines()) == 64
path = owner / (NAME + '.lean')
path.write_text(new)
(owner / 'repair.patch').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True), fromfile='source-v1.lean', tofile='source-v2.lean')))
(owner / 'repair.md').write_text('Strict1 failed because local notation in simp theorem position elaborates to a function with an implicit width argument. Use the fully qualified execute declaration in every simp list. The mathematical headers, local declarations, induction schemas and line count are unchanged. Strict1 and its exact source remain retained. No FULL was run.\n')
pins = [{'path': p.name, 'bytes': p.stat().st_size, 'sha256': sha(p)} for p in sorted(owner.iterdir())]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_REPAIR_PENDING_INDEPENDENT_REVIEW', 'source_sha256': sha(path), 'pins_sha256': sha(owner / 'pins.json')}, indent=2) + '\n')
print(json.dumps({'source_sha256': sha(path), 'pins_sha256': sha(owner / 'pins.json'), 'frozen_sha256': sha(owner / 'FROZEN.json')}))
