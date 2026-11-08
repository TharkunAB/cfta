"""Check that tuple physical proofs do not import the outer caller layer."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[3]
base = root / 'lean/MicroCFTA'
graph = {}
for source in base.glob('*.lean'):
    graph['MicroCFTA.' + source.stem] = re.findall(
        r'^(?:public )?import\s+([\w.]+)', source.read_text(), re.MULTILINE)

starts = ['SourceCurrentConjunctionTupleMemo', 'SourceCurrentConjunctionTupleGlobalMemos',
          'SourceCurrentConjunctionTupleWorkerProbes']
forbidden = {'MicroCFTA.' + name for name in ['SourceCurrentAllocatedConjunctionMemo',
    'SourceCurrentConjunctionClassScan', 'SourceCurrentAllocatedPartialInvariant']}
checks = []
for name in starts:
    pending = ['MicroCFTA.' + name]
    reached = set()
    while pending:
        node = pending.pop()
        if node in reached:
            continue
        reached.add(node)
        pending.extend(graph.get(node, []))
    assert not (reached & forbidden), (name, sorted(reached & forbidden))
    checks.append({'module': name, 'closure_size_including_self': len(reached),
                   'all_three_outer_modules_absent': True})
print(json.dumps({'checks': checks, 'forbidden_modules': sorted(forbidden),
                  'prohibited_paths_absent': 9}, indent=2))
