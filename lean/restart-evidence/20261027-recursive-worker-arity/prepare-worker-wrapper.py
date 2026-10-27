from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-recursive-worker-arity-20261027')
original = (root / 'lean/MicroCFTA/SourceCurrentAllocatedPartialWorkerActual.lean').read_text()
old_namespace = 'MicroCFTA.SourceCurrentAllocatedPartialWorkerActual'
new_namespace = 'MicroCFTA.SourcePruningEnumerationPartialWorkerArity'
scope = original[original.index('namespace ' + old_namespace):original.index('private def NodeCallAt')]
scope = scope.replace(old_namespace, new_namespace)
scope = scope.replace('local notation "Symbol"', 'open SourcePruningEnumerationArityOrigins (Heap)\nlocal notation "Symbol"', 1)
lines = ['import MicroCFTA.SourceCurrentAllocatedPartialWorkerActual',
    'import MicroCFTA.SourcePruningEnumerationPartialActualArity', '', '/-!',
    '# Arity at literal completed recursive worker returns', '',
    'Each theorem retains the complete original admission and result.',
    'The actual read graph derives arity for the same returned native heap.',
    'Only a genuine initial arity-valid heap is added to the input.', '-/', scope]
pairs = [('nodeCall', 'node_call', 'available'), ('nodeBody', 'node_body', 'available'),
    ('edgeCall', 'edge_call', 'resident'), ('edgeBody', 'edge_body', 'resident'),
    ('rows', 'rows', 'resident'), ('descendants', 'descendants', 'resident'),
    ('children', 'children', 'available'), ('walk', 'walk', 'available')]
records = []
for literal, actual, values in pairs:
    name = literal + '_verified'
    header = original.split('theorem ' + name, 1)[1].split(' := by', 1)[0]
    needle = '= .done result after) :\n'
    assert header.count(needle) == 1
    modified = header.replace(needle, '= .done result after)\n'
        '    (heap : Heap before.checked.native.machine.heap) :\n')
    modified += ' ∧\n      Heap after.checked.native.machine.heap'
    lines += ['/-- The literal completed ' + literal + ' retains its full receipt and derives returned arity. -/',
        'theorem ' + name + modified + ' := by',
        '  obtain ⟨next, final, actual, reads, checks, post, output, law⟩ :=',
        '    SourceCurrentAllocatedPartialWorkerActual.' + name + ' formulas solver initial inheritedReady ' + values + ' ranges done',
        '  exact ⟨next, final, actual, reads, checks, post, output, law,',
        '    SourcePruningEnumerationPartialActualArity.' + actual + '_heap formulas solver reads inventory checks initial',
        '      inheritedReady ' + values + ' heap⟩', '']
    restored = modified.removesuffix(' ∧\n      Heap after.checked.native.machine.heap').replace(
        '= .done result after)\n    (heap : Heap before.checked.native.machine.heap) :\n', needle)
    assert restored == header
    records.append(dict(theorem=name, original_namespace=old_namespace, new_namespace=new_namespace,
        original_header=header, new_header=modified, original_admission_and_result_preserved=True))
lines += ['end ' + new_namespace, '']
data = '\n'.join(lines).encode()
name = 'SourcePruningEnumerationPartialWorkerArity.lean'
path = area / 'partial-worker-wrapper-revisions/v1' / name
path.parent.mkdir(parents=True)
path.write_bytes(data)
(area / name).write_bytes(data)
(area / 'literal-worker-header-comparison.json').write_text(json.dumps(records, indent=2) + '\n')
print(json.dumps(dict(lines=len(data.splitlines()), bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
    preserved_complete_admissions_and_results=len(records))))
