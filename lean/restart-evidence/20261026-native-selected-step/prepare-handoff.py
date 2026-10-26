import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-selected-step-20261026')
evidence = root / 'lean/restart-evidence/20261026-native-selected-step'
base = (area / 'base.txt').read_text().strip()
sha = lambda data: hashlib.sha256(data).hexdigest()
old = lambda rel: subprocess.check_output(['git', 'show', base + ':' + rel], cwd=root)
checks = {p.parent.name: json.loads(p.read_text()) for p in sorted(area.glob('*/report.json'))}
modules = ['SourcePruningEnumerationNarrowAdapter', 'SourcePruningEnumerationSelectedStep',
           'SourcePruningEnumerationSelectedStepCompletion', 'SourcePruningEnumerationNativeContinuations', 'Audit']
sources = ['lean/MicroCFTA/' + module + '.lean' for module in modules]
finals = {}
for module, rel in zip(modules, sources):
    current = (root / rel).read_bytes()
    candidates = [name for name, report in checks.items() if name.startswith('strict-')
                  and not report['exit_code'] and report.get('source_sha256') == sha(current)
                  and (area / name / 'MicroCFTA' / (module + '.lean')).is_file()]
    assert candidates, module
    final = sorted(candidates)[-1]
    assert (area / final / 'MicroCFTA' / (module + '.lean')).read_bytes() == current
    finals[module] = final
    if module != 'Audit':
        assert not re.search(rb'\b(sorry|admit|axiom)\b', current)
for name, report in checks.items():
    raw = (area / name / 'raw.log').read_bytes()
    assert len(raw) == report['bytes'] and sha(raw) == report['sha256']
    if name.startswith(('public-', 'aggregate-audit', 'helper-build-')):
        assert report['exit_code'] == 0, name
public_bytes = (area / 'public-final-2/raw.log').read_bytes()
public = public_bytes.decode()
declarations = (area / 'public-final-2/public.lean').read_text().count('#check ')
assert len(re.findall(r'depends on axioms:|does not depend on any axioms', public)) == declarations
assert '⋯' not in public and '...' not in public
for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]', public):
    assert set(re.findall(r'[A-Za-z_.]+', axioms)) <= {'propext', 'Classical.choice', 'Quot.sound'}
audit_log = (area / 'aggregate-audit-2/raw.log').read_text()
audit_dependencies = int(re.search(r'Checked axiom dependencies of (\d+) MicroCFTA theorems\.', audit_log).group(1))
assert (root/'lean/MicroCFTA/Audit.lean').read_text() == old('lean/MicroCFTA/Audit.lean').decode().replace(
    'import MicroCFTA.SourcePruningEnumerationParkedRestart\n',
    'import MicroCFTA.SourcePruningEnumerationParkedRestart\nimport MicroCFTA.SourcePruningEnumerationSelectedStepCompletion\nimport MicroCFTA.SourcePruningEnumerationNativeContinuations\n',1)
unchanged = ['lean/MicroCFTA/' + module + '.lean' for module in [
    'SourcePruningEnumerationSelectedOrdinary', 'SourcePruningEnumerationSelectedNarrow',
    'SourcePruningEnumerationRecursion', 'SourcePruningEnumerationNativeBranches',
    'SourcePruningEnumerationNativeBranchCompletion', 'SourcePruningEnumerationNativeOrdinary',
    'SourcePruningEnumerationCapturedEdge', 'SourcePruningCallbackCompletion',
    'SourcePruningRecordTypes', 'SourcePruningEnumerationNativeIndex', 'EnumerationCompressionFrame',
    'EnumerationPendingOrder', 'EnumerationPendingReplacement', 'EnumerationFragmentHistory',
    'EnumerationOrder', 'EnumerationPureSelection', 'EnumerationIndexSelection',
    'EnumerationDriver', 'SourceCurrentColdFiniteWarmCalls',
]]
unchanged += ['cfta/src/Data/CFTA/' + name for name in [
    'Enumeration.hs', 'Interned/Type.hs', 'Interned/Cache.hs', 'Interned/Memo.hs', 'Interned/Operations.hs',
]]
for rel in unchanged:
    assert old(rel) == (root / rel).read_bytes(), rel
subprocess.run(['git', 'diff', '--quiet', base, '--', 'cfta', 'cfta-generator', '*.cabal'], cwd=root, check=True)
main = subprocess.check_output(['git', 'rev-parse', 'origin/main'], cwd=root).decode().strip()
subprocess.run(['git', 'merge-base', '--is-ancestor', main, 'HEAD'], cwd=root, check=True)
content = json.loads((area / 'handoff-content.json').read_text())
assert 'TODO' not in content['note']
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/COVERAGE.md', 'lean/API-COVERAGE.md',
             'lean/notes-current-system-claim.md', 'lean/notes-proof-status-20261017.md']
for rel in documents:
    path = root / rel
    text = path.read_text()
    marker = '## Concrete callbacks and parked recursion reach source restart'
    assert marker in text and content['block'].splitlines()[0] not in text
    path.write_text(text.replace(marker, content['block'] + marker, 1))
path = root / 'FINDINGS.md'
text = path.read_text()
marker = '### Callback and repeated-recursion restart boundary'
assert marker in text and content['findings'].splitlines()[0] not in text
path.write_text(text.replace(marker, content['findings'] + marker, 1))
assert path.read_text().index('## Haskell fix handoff') < path.read_text().index(content['block'].splitlines()[0])
(root / 'lean/notes-current-pruning-enumeration-selected-step.md').write_text(content['note'])
verification = dict(base=base, source_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root).decode().strip(),
                    recorded_main=main, checks=checks, final_strict_modules=finals,
                    failed_checks={name: report['exit_code'] for name,report in checks.items() if report['exit_code']},
                    public_declarations=declarations, public_lines=len(public.splitlines()),
                    public_bytes=len(public_bytes), public_sha256=sha(public_bytes),
                    audit_dependencies=audit_dependencies,
                    final_source_sha256={rel:sha((root/rel).read_bytes()) for rel in sources},
                    unchanged_source_sha256={rel:sha((root/rel).read_bytes()) for rel in unchanged},
                    goal_status='active', haskell_unchanged=True,
                    existing_runtime_workers_unchanged=True,
                    new_executable_workers=['NarrowAdapter.adapt','SelectedStep.run','NativeContinuations.run'])
(area / 'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
(area / 'proof-change.patch').write_bytes(subprocess.check_output(['git','diff',base,'HEAD','--',*sources],cwd=root))
for rel in sources:
    destination = area / 'sources' / rel
    destination.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(root / rel,destination)
destination = area / 'original-sources/lean/MicroCFTA/Audit.lean'
destination.parent.mkdir(parents=True,exist_ok=True)
destination.write_bytes(old('lean/MicroCFTA/Audit.lean'))
assert not evidence.exists()
shutil.copytree(area,evidence)
manifest = {str(p.relative_to(evidence)):dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes()))
            for p in sorted(evidence.rglob('*')) if p.is_file()}
(evidence/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(checks=len(checks),public_declarations=declarations,audit_dependencies=audit_dependencies,
                      payloads=len(manifest),bytes=sum(item['bytes'] for item in manifest.values()),
                      manifest_sha256=sha((evidence/'manifest.json').read_bytes()))))
