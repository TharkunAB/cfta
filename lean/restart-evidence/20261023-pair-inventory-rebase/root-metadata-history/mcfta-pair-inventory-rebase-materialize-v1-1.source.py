exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
gate = load(HERE / 'root-declaration-gate.json')
assert gate['status'] == 'ACCEPTED_EXACT_DECLARATIONS_BEFORE_BODY'
plan = HERE / 'declaration-plan'
body = '''
  let next : Inventory := SourceCurrentAllocatedNativeInventoryRebase.extend inventory
    state.checked.native.machine.heap good.native.machine.1 current.growth current.history
    left right leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨nextCurrent, sameSource, sameRoots, leftValid, rightValid⟩ :=
    SourceCurrentAllocatedNativeInventoryRebase.rebase formulas solver inventory state.checked
      good current left right leftAvailable rightAvailable leftClosed rightClosed
  have included : ∀ root ∈ inventory.roots, root ∈ next.roots := by
    intro root member
    exact List.mem_append.mpr (Or.inl member)
  have agreement : SourceCurrentAllocatedNativeContextRebase.Agreement oldInputs (next.inputs holds) := by
    exact SourceCurrentAllocatedNativeAdmittedQuery.inventory_agreement
      inventory.source state.checked.native.machine.heap inventory.facts good.native.machine.1
      current.growth current.history holds inventory.roots inventory.originals
      inventory.available inventory.closed next.roots next.available next.closed included
  exact ⟨nextCurrent,
    SourceCurrentSameSymbolEdgeModelTransport.rebase oldInputs (next.inputs holds)
      agreement holds state stable admitted,
    (fun handle pair value stored => agreement.edge_inputs (admitted handle pair value stored)),
    sameSource, sameRoots, leftValid, rightValid, agreement⟩
'''
source = (plan / 'context.lean.txt').read_text() + '\n' + (plan / 'public-header.lean.txt').read_text().rstrip('\n') + ' := by\n' + body.lstrip('\n') + '\nend MicroCFTA.' + NAME + '\n'
assert len(source.splitlines()) <= 180
target = Path('/tmp/mcfta-pair-inventory-rebase-source-v1')
assert not target.exists()
target.mkdir()
(target / (NAME + '.lean')).write_text(source)
(target / 'body.txt').write_text(body.lstrip('\n'))
(target / 'gate-before-body.json').write_bytes((HERE / 'root-declaration-gate.json').read_bytes())
pins = [dict(path=str(p.relative_to(target)), bytes=p.stat().st_size, sha256=sha(p)) for p in sorted(target.iterdir())]
(target / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(target / 'FROZEN.json').write_text(json.dumps(dict(status='SOURCE_ONLY_BODY_V1_FROZEN',
    source_sha256=sha(target / (NAME + '.lean')), lines=len(source.splitlines()),
    prior_declaration_gate_sha256=sha(HERE / 'root-declaration-gate.json'),
    pins_sha256=sha(target / 'pins.json')), indent=2) + '\n')
print(json.dumps(dict(source=str(target / (NAME + '.lean')), sha256=sha(target / (NAME + '.lean')),
    lines=len(source.splitlines()), pins_sha256=sha(target / 'pins.json'), frozen_sha256=sha(target / 'FROZEN.json'))))
