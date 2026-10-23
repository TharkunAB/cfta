exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil

assert git('rev-parse', 'HEAD').strip() == START
packages = [
    ('/tmp/mcfta-original-row-scan-admission-route-audit', 'scan-admission-route-audit',
     'c22eb480575247245cff12be6735d0f3ff2373d3756cc11f3e032a9b6ead42bb',
     '58d139d41d05800ed9d6913972acf1d108814b464ff08ff650bc6e8e4ecdea09'),
    ('/tmp/mcfta-scan-admission-decomposition-assessment', 'scan-admission-decomposition-assessment',
     '89c71b3200efa75636fde2b001de1ac7a36c234b63cb33bc9bf9f45cf93efc00',
     'a68c3d99c7b6cfbf144260707f0ae76ecaffcda8d92e18a8e27bccc6f2a851bc'),
    ('/tmp/mcfta-cluster-admission-runner-plan', 'runner-plan',
     '974ab954f9abd316fc96a912e92a3f626ab9b3ca77b2f93ad30bb09ad9cfa83a',
     'f6b02cb6ca98db57a1e0ca13f573200dbe2199675a521360ce734ea18b808267'),
    ('/tmp/mcfta-cluster-admission-runner-audit', 'runner-audit',
     'cebc72ac22111fab66cb33372b6247223b186978cca86cf929bdb4c60d017b3c',
     'aced2083ab4011e2eb9ab7fd32366c7886bfd26b3b17659add806ba4591471ba'),
]
for raw, name, pins, frozen in packages:
    owner = Path(raw)
    checked_package(owner, pins, frozen)
    if (owner / 'source-index.json').exists():
        index = load(owner / 'source-index.json')
        sources = index['sources']
        source_map = sources if isinstance(sources, dict) else {s['id']: s for s in sources}
        for item in source_map.values():
            actual = Path(item['path'])
            if not actual.is_absolute():
                actual = ROOT / actual
            assert sha(actual) == item['sha256']
            assert actual.stat().st_size == item['bytes']
        for cut in index.get('cuts', []):
            if 'source' in cut and cut['source'] in source_map and 'start_line' in cut:
                actual = Path(source_map[cut['source']]['path'])
                if not actual.is_absolute():
                    actual = ROOT / actual
                content = ''.join(actual.read_text().splitlines(keepends=True)[cut['start_line']-1:cut['end_line']]).encode()
                assert hashlib.sha256(content).hexdigest() == cut['sha256']
    archive(owner, name)
audit = load(Path(packages[3][0]) / 'review.json')
assert audit['status'] == 'CLEAR' and audit['whole_selected_source_lines_read'] == 31
selected = Path(packages[2][0]) / 'selected/root-run-check.py'
assert sha(selected) == '37784c72c779cac7e5cbd2bfdbfaf10bf90a1cda37c117debe04495b74d604ff'
target = HERE / 'root-run-check.py'
assert not target.exists()
shutil.copy2(selected, target)
assert sha(target) == sha(selected)
save('root-source-route-and-runner-gate.json', {
    'status': 'ACCEPTED_SOURCE_ONLY_AND_RUNNER_INSTALLED',
    'root_whole_assessments_and_runner_read': True,
    'live_source_and_package_hashes_verified': True,
    'source_cuts_manual_root_scope': 'Bounded defining APIs; no whole-source review of every inventory is claimed.',
    'runner_sha256': sha(target),
    'compiler_activation': False,
    'new_math_declaration_or_body_approval': False,
    'scope': 'Staged actual Scan equality then actual admission; same H20/H22/H23 witness correlation remains a proof obligation.',
    'goal_status': 'ACTIVE_INCOMPLETE',
})
print('PASS: source-only route accepted; unchanged reviewed runner installed; compiler inactive')
