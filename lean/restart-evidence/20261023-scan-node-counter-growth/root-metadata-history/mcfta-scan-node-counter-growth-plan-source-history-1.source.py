import ast
import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
old = root / 'lean/restart-evidence/20261023-pair-node-counter-growth'
here = root / 'lean/restart-evidence/20261023-scan-node-counter-growth'
packet = Path('/tmp/mcfta-scan-node-counter-growth-source-history-scope-plan')
assert not packet.exists()
plan = '''H38 source-history collector scope only. No selected collector is authored or run.
Retain the complete sealed H37 collector, 78 ordinary lines and fourteen assertions.
Retain its complete Root common basis and the exact current H38 common helper.
Target78 lines, hard90. Add no framework or generic guard exception.
Adapt only the common helper path, checkpoint prefix, three actual proof stems and source80/cap140 literals.
Use SourceCurrentOriginalRowClusterScanNodeCounterGrowth at the accepted H38 HERE and START.
The actual strict stem is root-scan-node-counter-growth-strict-1. Its empty log is accepted.
The planned FULL and Audit stems have no outcome at this scope cut. Reject until actual results exist.
Retain dynamic discovery of every Lean/Lake receipt and equality with the actual three-stem set.
Retain all owned source/log hashes, anchored errors/warnings, cgroup limits and fresh usage checks.
Retain every completed Root metadata attempt, including failed next-consumer reader attempt1 and corrected attempt2.
Keep each terminal metadata receipt/log/limits/usage/source/peaks bundle separate from proof jobs.
Derive metadata counts and failures at the actual cut. Do not freeze a forecast as the final count.
Stage variants/v1/NAME.lean from the unchanged selected80-line source before collection.
Keep exact equality with canonical NAME.lean and the accepted strict-source gate.
The current mathematical history is one unchanged variant and zero patches or rejected public TYPEs.
Keep author and reviewer diagnostics separate from mathematical changes and compiler failures.
Retain the complete dynamic HERE artifact inventory and only the existing five exclusions.
Retain variant/artifact disjointness, exact bytes/hashes, original Audit pin and selected-source map.
Keep existing source-history, job-history, metadata-cut and actual-proof-cut output schemas.
Parse the actual Audit counts and warning list. Do not copy H37 results.
Keep the known older replay warning check. Require no new source warning or error.
The collector receipt follows its own historical cut. Final support retains it and later receipts once.
Keep all save/mkdir nonoverwrite guards. Root and peer scope review precede selected authoring.
Whole selected-source review precedes execution. No compiler or publication is authorized here.
The complete formalization goal remains ACTIVE and incomplete.
'''
payloads = {'plan.md': plan.encode()}
for name, path in [('basis/source-history.py', old / 'source-history.py'),
                   ('basis/root-common.py', old / 'root-common.py'),
                   ('known-inputs/root-common.py', here / 'root-common.py'),
                   ('known-inputs/selected-source-gate.json', here / 'selected-source-gate.json'),
                   ('known-inputs/root-body-gate.json', here / 'root-body-gate.json')]:
    payloads[name] = path.read_bytes()
basis_source = payloads['basis/source-history.py'].decode()
guards = sorted((node for node in ast.walk(ast.parse(basis_source)) if isinstance(node, ast.Assert)), key=lambda node:node.lineno)
assert len(basis_source.splitlines()) == 78 and len(guards) == 14
crosswalk = [{'line':node.lineno, 'expression':ast.unparse(node.test),
              'treatment':'Retain exact expression except approved checkpoint and source80/cap140 literals.'} for node in guards]
payloads['guard-crosswalk.json'] = (json.dumps(crosswalk, indent=2) + '\n').encode()
inputs = {'status':'SCOPE_ONLY_BEFORE_FULL_AND_AUDIT',
          'module':'SourceCurrentOriginalRowClusterScanNodeCounterGrowth',
          'target_lines':78, 'hard_stop':90, 'source_lines':80, 'source_cap':140,
          'strict_stem':'root-scan-node-counter-growth-strict-1',
          'full_stem':'root-scan-node-counter-growth-full-1',
          'audit_stem':'root-scan-node-counter-growth-audit-1',
          'FULL_result':'__H38_ACTUAL_FULL_RESULT__', 'Audit_result':'__H38_ACTUAL_AUDIT_RESULT__',
          'variants':1, 'patches':0, 'rejected_public_types':0,
          'metadata_counts':'DYNAMIC_AT_ACTUAL_CUT',
          'known_failed_metadata_attempt':'mcfta-scan-node-counter-growth-accept-next-consumer-investigation-1',
          'selected_authorship_authorized':False, 'selected_activation_authorized':False}
payloads['input-map.json'] = (json.dumps(inputs, indent=2) + '\n').encode()
packet.mkdir()
for name, raw in payloads.items():
    path = packet / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
pins = {name:{'bytes':len(raw), 'sha256':hashlib.sha256(raw).hexdigest()} for name, raw in sorted(payloads.items())}
(packet / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
freeze = {'status':'FROZEN_SOURCE_ONLY_SCOPE', 'files':len(pins),
          'pins_sha256':hashlib.sha256((packet / 'pins.json').read_bytes()).hexdigest(),
          'selected_source_authored_or_executed':False}
(packet / 'FROZEN.json').write_text(json.dumps(freeze, indent=2) + '\n')
print(json.dumps({'pins_sha256':freeze['pins_sha256'],
                  'FROZEN_sha256':hashlib.sha256((packet / 'FROZEN.json').read_bytes()).hexdigest(),
                  'files':len(pins), 'guards':len(guards)}))
