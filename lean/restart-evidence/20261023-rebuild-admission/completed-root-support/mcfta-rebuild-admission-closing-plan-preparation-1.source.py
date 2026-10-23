exec(compile(open('/tmp/mcfta-rebuild-admission-root-common.py').read(), '/tmp/mcfta-rebuild-admission-root-common.py', 'exec'))
import datetime
owner = Path('/tmp/mcfta-rebuild-admission-closing-tool-plan')
assert not owner.exists()
owner.mkdir()
(owner / 'basis').mkdir()
(owner / 'review-cut').mkdir()
(owner / 'plan.md').write_bytes(Path('/tmp/mcfta-rebuild-admission-closing-plan.md').read_bytes())
references = []
previous = ROOT / 'lean/restart-evidence/20261023-group-admission'
for name in ['verify-preservation.py', 'archive-support.py', 'seal-checkpoint.py', 'verify-seal.py', 'verify-checkpoint.py']:
    source = previous / name
    target = owner / 'basis' / name
    target.write_bytes(source.read_bytes())
    references.append(dict(path=str(source), snapshot='basis/' + name, bytes=source.stat().st_size, sha256=sha(source)))
for source in [HERE / 'baseline-counts.json', HERE / 'selected-source-gate.json', HERE / 'original-source-index.json',
               HERE / 'starting-head.txt', HERE / 'starting-main.txt', HERE / 'starting-local-main.txt',
               HERE / 'starting-stashes.txt', HERE / 'starting-worktrees.txt', previous / 'frozen-modules.json']:
    target = owner / 'review-cut' / source.name
    target.write_bytes(source.read_bytes())
    references.append(dict(path=str(source), snapshot='review-cut/' + source.name, bytes=source.stat().st_size, sha256=sha(source)))
(owner / 'input-map.json').write_text(json.dumps(dict(status='SOURCE_ONLY_PLAN_PENDING_ROOT_AND_INDEPENDENT_REVIEW',
    whole_basis_lines=236, target_lines=236, hard_stop=260, references=references,
    future_proof_metrics=None, future_Audit=None, selected_authoring_authorized=False,
    prepared_execution_authorized=False), indent=2) + '\n')
pins = [dict(path=str(p.relative_to(owner)), bytes=p.stat().st_size, sha256=sha(p)) for p in sorted(owner.rglob('*')) if p.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FINAL_FROZEN_SOURCE_ONLY_PLAN',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), pins_sha256=sha(owner / 'pins.json'), pins_count=len(pins)), indent=2) + '\n')
print(json.dumps(dict(owner=str(owner), pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'))))
