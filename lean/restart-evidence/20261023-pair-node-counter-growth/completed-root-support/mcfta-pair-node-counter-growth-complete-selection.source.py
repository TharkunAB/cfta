exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
selected_path = HERE / 'selected-sources.json'
before = selected_path.read_bytes()
snapshot = HERE / 'selected-sources.before-full-link.json'
assert not snapshot.exists()
selected = load(selected_path)
assert len(selected) == 1
entry = selected['lean/MicroCFTA/' + NAME + '.lean']
assert set(entry) == {'sha256','lines','strict'}
full_stem = 'root-pair-node-counter-growth-full-1'
receipt = load(HERE / (full_stem + '.json'))
assert receipt['exit_code'] == 0
assert receipt['sha256'] == sha(HERE / (full_stem + '.source.lean'))
assert load(HERE / 'full-readback/pair-node-counter-growth-full-readback.json')['source_sha256'] == entry['sha256']
snapshot.write_bytes(before)
entry['full'] = full_stem
selected_path.write_text(json.dumps(selected,indent=2) + '\n')
save('selection-metadata-correction.json',dict(status='ACTUAL_FULL_RECEIPT_LINK_ADDED',
    before_path=snapshot.name,before_sha256=sha(snapshot),after_path=selected_path.name,after_sha256=sha(selected_path),
    only_change='Add the actual full receipt stem to the selected source record.',
    proof_source_changed=False,new_Lean_job=False,generic_selection_guard_preserved=True))
print('Added the actual FULL receipt link. Retained the complete earlier metadata bytes.')
