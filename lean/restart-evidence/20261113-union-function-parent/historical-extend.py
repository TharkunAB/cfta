from pathlib import Path
import datetime
import hashlib
import json
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
OLD = Path('/tmp/mcfta-union-shape-history-20261113-1430/packet')
PACKET = HERE / 'packet'
ROOT = Path('/home/tritlo/Code/mcfta')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(relative, data):
    p = PACKET / relative
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data)
    return relative


def delta(before, after, relative):
    left, right = HERE / 'diff-before.txt', HERE / 'diff-after.txt'
    left.write_bytes(before)
    right.write_bytes(after)
    got = subprocess.run(['diff', '--unified=0', '--label', 'source.lean',
        '--label', 'source.lean', str(left), str(right)], capture_output=True, check=False)
    assert got.returncode == 1, got.stderr.decode()
    return write(relative, got.stdout)


old_manifest_hash = sha((OLD / 'source-history.json').read_bytes())
old_checker_hash = sha((OLD / 'check.py').read_bytes())
shutil.copytree(OLD, PACKET)
manifest = json.loads((PACKET / 'source-history.json').read_text())
assert len(manifest['families']) == 4

spec = [
    ('140-base', '/tmp/mcfta-type-child-prefix-output-20261113-1312/SourceSynthesisActualOrdinaryTypeSubtrace.lean',
     '58f5025b7c03be9ddd6fb60634ef349f3a95cd4065338284cd9525ce72c4abe4',
     '/tmp/mcfta-type-child-prefix-output-20261113-1312', 0),
    ('325-initial', '/tmp/mcfta-identity-type-read-prefix-20261113-1425/SourceSynthesisActualOrdinaryTypeSubtrace.lean',
     '27f85518', '/tmp/mcfta-type-read-prefix-check-20261113-1428', 1),
    ('327-alias', '/tmp/mcfta-identity-type-read-prefix-alias-20261113-1430/SourceSynthesisActualOrdinaryTypeSubtrace.lean',
     'e30d30832ae856dac6762e9f7d0cf27396b7c599bdf0d81dd75757548771f427',
     '/tmp/mcfta-type-read-prefix-check2-20261113-1433', 0),
]
family = {'name': 'type-prefix', 'stages': []}
previous = None
for index, (name, source, expected, checker, code) in enumerate(spec):
    data = Path(source).read_bytes()
    assert sha(data).startswith(expected)
    status = 'FAILED' if code else 'STRICT_PRIVATE_PASS'
    record = dict(name=name, sha256=sha(data), lines=len(data.splitlines()),
                  status=status, original_source=source)
    if previous is None:
        record['file'] = write('history/type-prefix/base.lean.txt', data)
        family['base'] = record
    else:
        record['patch'] = delta(previous, data, f'history/type-prefix/{index:02d}-{name}.patch')
        family['stages'].append(record)
    previous = data

    checker = Path(checker)
    report = json.loads((checker / 'draft-checked.json').read_text())
    assert report['compiler_exit'] == code
    checked = Path(report['source']).read_bytes()
    assert sha(checked) == report['sha256']
    log = (checker / 'draft-output.txt').read_bytes()
    groups = [sorted(x.strip() for x in group.split(',') if x.strip())
              for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', log.decode(), re.S)]
    if code == 0:
        assert groups and all(set(group) <= ALLOWED for group in groups)
    prefix = f'diagnostics/type-prefix/{name}'
    files = []
    for filename in ['draft-checked.json', 'draft-output.txt', 'check-draft.py', 'source-pins.json']:
        p = checker / filename
        if p.exists():
            files.append(write(prefix + '/' + filename, p.read_bytes()))
    instrumentation = delta(data, checked, prefix + '/instrumentation.patch')
    manifest['diagnostics'].append(dict(family='type-prefix', stage=name,
        raw_sha256=sha(data), checked_sha256=sha(checked), compiler_exit=code,
        printed_axioms=groups, historical_check_passed=code == 0,
        failed_axiom_prints_are_not_proofs=code != 0,
        observation='instrumented-same-source', checked_variant=instrumentation, files=files))
manifest['families'].append(family)

pending = []
pending_spec = [
    ('293-initial', '/tmp/mcfta-first-filter-backward-origin-body-20261113-1418/SourceSynthesisFirstFilterCurrentAppSourceAncestor.lean',
     '9076239a', '/tmp/mcfta-first-filter-origin-check-20261113-1426'),
    ('292-repair', '/tmp/mcfta-first-filter-backward-origin-repair-20261113-1427/SourceSynthesisFirstFilterCurrentAppSourceAncestor.lean',
     '2cedce28', '/tmp/mcfta-first-filter-origin-check2-20261113-1430'),
]
for name, source, expected, checker in pending_spec:
    data = Path(source).read_bytes()
    assert sha(data).startswith(expected)
    checker = Path(checker)
    report = json.loads((checker / 'draft-checked.json').read_text())
    assert report['compiler_exit'] == 1
    checked = Path(report['source']).read_bytes()
    assert sha(checked) == report['sha256']
    prefix = f'pending-first-filter/{name}'
    raw_file = write(prefix + '/raw.lean.txt', data)
    checked_patch = delta(data, checked, prefix + '/instrumentation.patch')
    files = []
    for filename in ['draft-checked.json', 'draft-output.txt', 'check-draft.py', 'source-pins.json']:
        p = checker / filename
        if p.exists():
            files.append(write(prefix + '/' + filename, p.read_bytes()))
    pending.append(dict(name=name, raw_file=raw_file, raw_sha256=sha(data),
        checked_patch=checked_patch, checked_sha256=sha(checked), files=files,
        status='FAILED_PENDING_REPAIR', proof_credit=False, required_check=False))
manifest['pending_first_filter'] = pending

attachment_roots = [
    Path('/tmp/mcfta-identity-type-read-prefix-plan-20261113-1420'),
    Path('/tmp/mcfta-first-filter-backward-origin-20261113-1404'),
    Path('/tmp/mcfta-first-filter-backward-origin-body-20261113-1418'),
    Path('/tmp/mcfta-first-filter-backward-origin-repair-20261113-1427'),
]
for parent in attachment_roots:
    for path in sorted(parent.iterdir()):
        if not path.is_file() or path.suffix == '.lean':
            continue
        data = path.read_bytes()
        relative = 'attachments/' + sha(data) + ('.json' if path.suffix == '.json' else '.txt')
        write(relative, data)
        manifest['attachments'].append(dict(file=relative, sha256=sha(data), original_source=str(path),
            status='PENDING_FIRST_FILTER_NO_PROOF_CREDIT' if 'first-filter' in str(parent)
                   else 'APPROVED_TYPE_PREFIX_HEADER_OR_PLAN'))
header = Path('/tmp/mcfta-identity-type-read-prefix-plan-20261113-1420/proposed-header.lean.txt').read_bytes()
assert len(header.splitlines()) == 76
assert sha(header) == 'b0c81e3be7cded701f2166ca6c6593e03be4f378e41c8d4558ff621140f2bf11'

script = (PACKET / 'check.py').read_text()
needle = '    return stages, checked, replays\n'
replacement = '''    for row in manifest.get("pending_first_filter", []):
        raw = (packet / row["raw_file"]).read_bytes()
        assert sha(raw) == row["raw_sha256"]
        apply(raw, row["checked_patch"], work / "pending" / row["name"] / "source.lean",
              row["checked_sha256"])
        assert row["proof_credit"] is False and row["required_check"] is False
    assert len(replays) == manifest["expected_total_gnu_replays"]
    return stages, checked, replays
'''
assert script.count(needle) == 1
script = script.replace(needle, replacement)
needle = '    probe = work / "public-import-check.lean"\n'
replacement = '''    private_prefix = checked["type-prefix", "327-alias"]
    run("private-identity-type-prefix", "exec lake env lean -j1 -DwarningAsError=true " + shlex.quote(str(private_prefix)), 1)
    probe = work / "public-import-check.lean"
'''
assert script.count(needle) == 1
script = script.replace(needle, replacement)
write('check.py', script.encode())

manifest['prepared_at'] = datetime.datetime.now().astimezone().isoformat()
manifest['extension'] = dict(unchanged_four_family_packet=str(OLD),
    original_manifest_sha256=old_manifest_hash, original_checker_sha256=old_checker_hash,
    original_families_and_diagnostics_retained=True,
    type_prefix_private=True, first_filter_is_not_a_required_check=True,
    compiler_run=False, live_edits=False, git_called=False)
manifest['expected_source_stages'] = 17
manifest['expected_history_patches'] = 12
manifest['expected_instrumentation_patches'] = 10
manifest['expected_pending_instrumentation_patches'] = 2
manifest['expected_total_gnu_replays'] = 24
manifest['historical_check_associations'] = 15
manifest['distinct_historical_check_runs'] = 14
manifest['scope']['private_identity_type_prefix_observers'] = 1
manifest['scope']['first_filter_origin_proved'] = False
manifest['preparation']['gnu_patch_replay_run'] = False
manifest['preparation'].pop('reconstruction_only_report_sha256', None)

sources = sorted((ROOT / 'lean/MicroCFTA').glob('*.lean'))
rows = [p.name + ' ' + sha(p.read_bytes()) for p in sources]
assert len(sources) == 5900
manifest['root_aggregate_pins'] = dict(live_modules=len(sources),
    source_tree_sha256=sha(('\n'.join(rows) + '\n').encode()))
for relative, expected in manifest['live_sources'].items():
    assert sha((ROOT / relative).read_bytes()) == expected
write('source-history.json', (json.dumps(manifest, indent=2) + '\n').encode())
for p in [HERE / 'diff-before.txt', HERE / 'diff-after.txt']:
    p.unlink()
assert sha((OLD / 'source-history.json').read_bytes()) == old_manifest_hash
assert sha((OLD / 'check.py').read_bytes()) == old_checker_hash
print(json.dumps(dict(packet=str(PACKET), families=len(manifest['families']),
    source_stages=manifest['expected_source_stages'],
    source_history_patches=manifest['expected_history_patches'],
    pending_first_filter_variants=len(pending),
    live_modules=len(sources), aggregate=manifest['root_aggregate_pins']), indent=2))
