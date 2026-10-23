exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import difflib
owner = Path('/tmp/mcfta-cluster-admission-history-revision-v2')
assert not owner.exists()
owner.mkdir()
old = HERE / 'source-history-gate.json'
assert sha(old) == '55ba0b24066411facb800da6554acf7690710bfd1ab6fdc9a36688cdf0d2b2e6'
before = old.read_bytes()
original = json.loads(before)
variant_paths = {item['path'] for item in original['variants']}
removed = [item for item in original['artifacts'] if item['path'] in variant_paths]
assert len(variant_paths) == len(removed) == 6
revised = {**original, 'artifacts': [item for item in original['artifacts'] if item['path'] not in variant_paths]}
assert len(original['artifacts']) == 591 and len(revised['artifacts']) == 585
assert not variant_paths & {item['path'] for item in revised['artifacts']}
for key in original:
    if key != 'artifacts':
        assert original[key] == revised[key]
after = (json.dumps(revised, indent=2) + '\n').encode()
(owner / 'source-history-v1.json').write_bytes(before)
(owner / 'source-history-v2.json').write_bytes(after)
for source, target, fromfile, tofile, filename in [
    (before, after, 'source-history-v1.json', 'source-history-v2.json', 'revision.patch'),
    (after, before, 'source-history-v2.json', 'source-history-v1.json', 'revision.inverse.patch'),
]:
    (owner / filename).write_text(''.join(difflib.unified_diff(source.decode().splitlines(True), target.decode().splitlines(True), fromfile=fromfile, tofile=tofile)))
(owner / 'revision.json').write_text(json.dumps(dict(status='SOURCE_ONLY_METADATA_REVISION_PENDING_INDEPENDENT_REVIEW',
    before_sha256=sha(owner / 'source-history-v1.json'), after_sha256=sha(owner / 'source-history-v2.json'),
    removed_duplicate_artifact_records=removed, variants_unchanged=True, jobs_unchanged=True,
    all_other_artifacts_unchanged=True, proof_sources_unchanged=True,
    reason='The inherited verifier requires disjoint variant and artifact categories. Each removed artifact is still an unchanged retained mathematical variant.',
    active_history_not_changed=True, selected_verifier_not_executed=True), indent=2) + '\n')
pins = [dict(path=path.name, bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.iterdir())]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_SOURCE_ONLY_METADATA_REVISION', pins_sha256=sha(owner / 'pins.json'), no_future_writes=True), indent=2) + '\n')
print(json.dumps(dict(pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'), revised_history_sha256=sha(owner / 'source-history-v2.json'))))
