exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import difflib
import shutil
old = HERE / 'boundary-declaration-v2'
owner = Path('/tmp/mcfta-cluster-admission-boundary-declaration-v3')
assert not owner.exists()
shutil.copytree(old, owner)
(owner / 'pins.json').unlink()
(owner / 'FROZEN.json').unlink()
first = 'SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain pair.1 pair.2'
second = 'SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain (Prod.fst pair) (Prod.snd pair)'
changed = []
patches = []
for path in sorted(owner.glob('*.lean.txt')):
    text = path.read_text()
    revised = text.replace(first, second)
    if revised != text:
        path.write_text(revised)
        changed.append(path.name)
        patches.extend(difflib.unified_diff(text.splitlines(keepends=True), revised.splitlines(keepends=True), fromfile='v2/' + path.name, tofile='v3/' + path.name))
(owner / 'declaration-v3-repair.patch').write_text(''.join(patches))
contracts = load(owner / 'contracts.json')
for name in contracts:
    contracts[name] = sha(owner / name)
(owner / 'contracts.json').write_text(json.dumps(contracts, indent=2) + '\n')
insertion = load(owner / 'insertion-map.json')
for record in insertion['compiled_fragments']:
    record['sha256'] = sha(owner / record['file'])
    assert record['lines'] == len((owner / record['file']).read_text().splitlines())
(owner / 'insertion-map.json').write_text(json.dumps(insertion, indent=2) + '\n')
toolchain = Path('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean')
apis = [('Init/Prelude.lean', 554, 562), ('Lean/Elab/Quotation/Precheck.lean', 126, 141), ('Lean/Elab/Binders.lean', 667, 677)]
records = []
for index, (name, start, end) in enumerate(apis):
    path = toolchain / name
    target = owner / ('repair-v3-api-' + str(index) + '.lean.txt')
    target.write_text(''.join(path.read_text().splitlines(keepends=True)[start-1:end]))
    records.append({'path': str(path), 'source_sha256': sha(path), 'start': start, 'end': end, 'cut': target.name, 'cut_sha256': sha(target)})
(owner / 'repair-v3-inputs.json').write_text(json.dumps({'status': 'DECLARATION_ONLY_V3_PENDING_REVIEW', 'changed': changed, 'old_pins_sha256': sha(old / 'pins.json'), 'strict2_receipt_sha256': sha(HERE / 'boundary-strict2.json'), 'strict2_log_sha256': sha(HERE / 'boundary-strict2.log'), 'primary_local_APIs': records, 'scope': 'Use public pair projection functions only inside the PairInputs notation. Public proposition, all other fragments, IH, proof tactics and limits are unchanged. No body rewrite or compiler yet.'}, indent=2) + '\n')
pins = [{'path': str(p.relative_to(owner)), 'bytes': p.stat().st_size, 'sha256': sha(p)} for p in sorted(owner.rglob('*')) if p.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps({'status': 'FROZEN_DECLARATION_V3_ONLY', 'pins_sha256': sha(owner / 'pins.json'), 'contracts_sha256': sha(owner / 'contracts.json')}, indent=2) + '\n')
print(json.dumps({'changed': changed, 'pins_sha256': sha(owner / 'pins.json'), 'frozen_sha256': sha(owner / 'FROZEN.json'), 'contracts_sha256': sha(owner / 'contracts.json'), 'context_sha256': sha(owner / 'context.lean.txt')}))
