exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import difflib
import shutil
old = HERE / 'boundary-declaration-plan'
owner = Path('/tmp/mcfta-cluster-admission-boundary-declaration-v2')
assert not owner.exists()
shutil.copytree(old, owner)
(owner / 'pins.json').unlink()
(owner / 'FROZEN.json').unlink()
changes = [
    ('    ⟨IntersectionEmptyDomain.emptyDomain, pair.1, pair.2⟩)',
     '    (SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain pair.1 pair.2))'),
    ('have parentAdmitted : inputs.valid (inputOf parent)',
     'have parentAdmitted : (inputs).valid (inputOf parent)'),
]
changed = []
for path in sorted(owner.glob('*.lean.txt')):
    text = path.read_text()
    revised = text
    for before, after in changes:
        revised = revised.replace(before, after)
    if revised != text:
        path.write_text(revised)
        changed.append(path.name)
contracts = load(owner / 'contracts.json')
for name in contracts:
    contracts[name] = sha(owner / name)
(owner / 'contracts.json').write_text(json.dumps(contracts, indent=2) + '\n')
insertion = load(owner / 'insertion-map.json')
for record in insertion['compiled_fragments']:
    record['sha256'] = sha(owner / record['file'])
    assert record['lines'] == len((owner / record['file']).read_text().splitlines())
(owner / 'insertion-map.json').write_text(json.dumps(insertion, indent=2) + '\n')
patch = ''.join(''.join(difflib.unified_diff((old / name).read_text().splitlines(keepends=True), (owner / name).read_text().splitlines(keepends=True), fromfile='v1/' + name, tofile='v2/' + name)) for name in changed)
(owner / 'declaration-repair.patch').write_text(patch)
api = ROOT / 'lean/MicroCFTA/SourceRecursiveIntersectionThunks.lean'
(owner / 'repair-request-constructor.lean.txt').write_text(''.join(api.read_text().splitlines(keepends=True)[22:26]))
(owner / 'repair-inputs.json').write_text(json.dumps({
    'status': 'DECLARATION_ONLY_REPAIR_PENDING_REVIEW',
    'original_declaration_owner': 'Arity', 'repair_author': 'Root',
    'old_package_pins_sha256': sha(old / 'pins.json'),
    'changed_declaration_files': changed,
    'actual_failed_strict_receipt': {'path': str(HERE / 'boundary-strict1.json'), 'sha256': sha(HERE / 'boundary-strict1.json')},
    'actual_failed_strict_log': {'path': str(HERE / 'boundary-strict1.log'), 'sha256': sha(HERE / 'boundary-strict1.log')},
    'public_constructor_source': {'path': str(api), 'sha256': sha(api), 'cut_lines': [23, 26]},
    'default_limits_and_all_linters': True,
    'no_body_rewrite_or_compiler_authorized': True,
}, indent=2) + '\n')
review = load(owner / 'review.json')
review['status'] = 'FROZEN_DECLARATION_V2_PROPOSAL_ONLY'
review['repair_scope'] = 'Use public explicit request constructor in notation; parenthesize inputs before .valid. No mathematical premise, induction or output changes.'
review['body_authorized'] = False
(owner / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
pins = [{'path': str(p.relative_to(owner)), 'bytes': p.stat().st_size, 'sha256': sha(p)} for p in sorted(owner.rglob('*')) if p.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_DECLARATION_V2_ONLY', 'pins_sha256': sha(owner / 'pins.json'), 'contracts_sha256': sha(owner / 'contracts.json')}, indent=2) + '\n')
print(json.dumps({'owner': str(owner), 'changed': changed, 'pins_sha256': sha(owner / 'pins.json'), 'frozen_sha256': sha(owner / 'FROZEN.json'), 'contracts_sha256': sha(owner / 'contracts.json'), 'context_sha256': sha(owner / 'context.lean.txt')}))
