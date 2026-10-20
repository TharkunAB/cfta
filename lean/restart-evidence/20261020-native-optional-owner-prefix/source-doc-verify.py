"""Check exact source, document ranges, physical proof readbacks and accounting."""
import argparse
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = next((p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()), Path('/home/tritlo/Code/mcfta'))
EVIDENCE = Path('lean/restart-evidence/20261020-native-optional-owner-prefix')
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']
LIMITS = {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
TOOLCHAIN = '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/'
OLD_WARNING = 'warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced.'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def pins(base, entries):
    assert len({item['path'] for item in entries}) == len(entries)
    for item in entries:
        path = Path(item['path'])
        assert not path.is_absolute() and '..' not in path.parts
        data = (base / path).read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256'], item['path']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    root = args.root.resolve()
    evidence = root / EVIDENCE
    manifest = read(HERE / 'source-doc-source-pins.json')
    config = manifest['checks']
    assert config['finalized']
    pins(root, manifest['files'])
    pins(HERE, manifest['artifacts'])
    ranges = read(HERE / 'source-doc-ranges.json')['ranges']
    assert len(ranges) == config['range_count']
    assert len({item['text'] for item in ranges[:7]}) == 1
    for item in ranges:
        assert hashlib.sha256(item['text'].encode()).hexdigest() == item['sha256']
        assert len(item['text'].splitlines()) == item['end_line'] - item['start_line'] + 1
        if args.live:
            lines = (root / item['path']).read_text().splitlines(keepends=True)
            assert ''.join(lines[item['start_line'] - 1:item['end_line']]) == item['text'], item['path']

    def receipt(stem, code=0):
        path = Path(stem)
        base = evidence / path.parent
        meta = read(evidence / (stem + '.json'))
        assert meta['exit_code'] == code, stem
        assert meta['command'][0] in {TOOLCHAIN + 'lean', TOOLCHAIN + 'lake'}, stem
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G', stem
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m', stem
        assert read(base / meta['limits']) == LIMITS, stem
        if 'source' in meta:
            assert '-Dlinter.all=true' in meta['command']
            assert sha(base / meta['source']) == meta['sha256'], stem
        usage = base / (path.name + '.usage.json')
        assert usage.exists(), stem
        usage_data = read(usage)
        assert usage_data['age_seconds'] < 120 and usage_data['remaining_percent'] > 1
        return base, meta, (base / meta['log']).read_text()

    accounting = read(evidence / 'attempt-accounting.json')
    assert accounting == config['accounting']
    attempts = accounting['attempts']
    assert len(attempts) == config['lean_jobs']
    assert len({item['receipt'] for item in attempts}) == len(attempts)
    assert sum(item['exit_code'] != 0 for item in attempts) == config['failures']
    for item in attempts:
        base, meta, log = receipt(item['receipt'][:-5], item['exit_code'])
        assert (base / meta['log']).stat().st_size == item['raw_log_bytes']
        if item['exit_code']:
            assert re.search(r'\berror(?:\([^)]*\))?:', log), item['receipt']

    assert len(attempts) == 62 and sum(item['exit_code'] != 0 for item in attempts) == 17
    assert sum(item['failure_kind'] == 'elaboration' for item in attempts) == 16
    assert sum(item['failure_kind'] == 'missing_source_before_lean' for item in attempts) == 1
    assert accounting['all_attempts_terminal'] and accounting['fresh_commands'] == 62
    assert accounting['reused_prior_commands'] == 0
    assert accounting['auxiliary_snippet_pairs'] == 1
    assert accounting['successful_unselected_style_warning_attempts'] == [
        'optional-owner-direct-2.json', 'walk-prefix-prototype/walk-optional-direct-2.json']
    for relative in accounting['successful_unselected_style_warning_attempts']:
        _base, _meta, log = receipt(relative[:-5])
        assert re.search(r'\bwarning(?:\([^)]*\))?:', log), relative

    modules = read(evidence / 'frozen-modules.json')
    assert modules == config['module_hashes'] and len(modules) == 9
    assert read(evidence / 'new-modules.json') == list(modules)
    assert read(evidence / 'selected-strict.json') == config['selected_strict']
    assert read(evidence / 'selected-canonical.json') == config['selected_canonical']
    assert len(config['selected_strict']) == 9
    for module, stem in config['selected_strict'].items():
        base, meta, log = receipt(stem)
        assert not log and sha(base / meta['source']) == modules[module], stem
        assert sha(root / 'lean/MicroCFTA' / (module + '.lean')) == modules[module]
    constructed_strict = read(evidence / 'selected-constructed-strict.json')
    assert constructed_strict == config['constructed_strict'] and len(constructed_strict) == 1
    for stem, working in constructed_strict.items():
        base, meta, log = receipt(stem)
        assert not log and sha(base / meta['source']) == sha(evidence / working)
    canonical = list(dict.fromkeys(config['selected_canonical'].values()))
    assert len(canonical) == config['canonical_jobs']
    for stem in canonical + ['full-audit-1']:
        _base, _meta, log = receipt(stem)
        assert 'Build completed successfully' in log and not re.search(r'(^|\n)error:', log)
        assert re.findall(r'^warning:.*$', log, re.M) in [[], [OLD_WARNING]], stem
    audit = config['audit']
    assert read(evidence / 'selected-audit.json') == audit
    audit_log = (evidence / (audit['name'] + '.log')).read_text()
    assert f"Build completed successfully ({audit['jobs']} jobs)." in audit_log
    assert f"Checked axiom dependencies of {audit['dependency_checks']} MicroCFTA theorems." in audit_log
    assert read(evidence / (audit['name'] + '.json'))['command'][-1] == 'build'

    groups = read(evidence / 'selected-groups.json')
    assert groups == config['groups'] and len(groups) == 10
    assert sum(item['pairs'] for item in groups if item['kind'] == 'new-public') == 12
    assert sum(item['pairs'] for item in groups if item['kind'] == 'constructed') == 1
    heads = read(evidence / 'public-heads.json')
    assert heads == config['heads'] and len(heads) == 12
    seen = []
    for item in config['public']:
        base, meta, log = receipt(item['name'])
        printer = (base / meta['source']).read_text()
        if item['module']:
            assert printer.splitlines()[0] == 'import MicroCFTA.' + item['module']
        else:
            assert printer.encode().startswith((evidence / item['working']).read_bytes())
        for option in OPTIONS:
            assert 'set_option ' + option in printer, (item['name'], option)
        for pattern in [r'^#check @([^\s]+)', r'^#print (?!axioms )([^\s]+)', r'^#print axioms ([^\s]+)']:
            assert re.findall(pattern, printer, re.M) == item['heads']
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log), item['name']
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        free = re.findall(r"'([^']+)' does not depend on any axioms", log)
        assert len(reports) + len(free) == len(item['heads'])
        assert set(name for name, _ in reports) | set(free) == set(item['heads'])
        for head in item['heads']:
            assert re.search(r'(?:theorem|def) ' + re.escape(head) + r'(?:\.\{[^}]*\})?\s*:', log), head
        assert ':=' in log
        for _head, axioms in reports:
            names = re.sub(r'\.\{[^}]*\}', '', axioms)
            assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
        seen.extend(item['heads'])
    assert seen[:12] == heads and len(seen) == 13
    assert seen[-1] == 'MicroCFTA.NativeCompiledOwnerFixture.compiled_site'
    for item in config['auxiliary_public']:
        base, meta, log = receipt(item['name'])
        printer = (base / meta['source']).read_text()
        for option in OPTIONS:
            assert 'set_option ' + option in printer
        assert re.findall(r'^#check @([^\s]+)', printer, re.M) == item['heads']
        assert re.findall(r'^#print (?!axioms )([^\s]+)', printer, re.M) == item['heads']
        assert re.findall(r'^#print axioms ([^\s]+)', printer, re.M) == item['heads']
        assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        free = re.findall(r"'([^']+)' does not depend on any axioms", log)
        assert set(name for name, _ in reports) | set(free) == set(item['heads'])
        assert len(reports) + len(free) == len(item['heads']) == 1
        for _head, axioms in reports:
            names = re.sub(r'\.\{[^}]*\}', '', axioms)
            assert set(re.split(r',\s*', names.strip())) <= {'propext', 'Classical.choice', 'Quot.sound'}
    fixture = (evidence / 'compiled-owner-fixture/owner-kernels.lean').read_text()
    assert fixture.count('SourceCurrentNativeOptionalOwner.request request 4 before after') == 1
    assert 'Trace 4 (.code (requestNode request.domain left right)) before' in fixture
    assert 'firstBuilt = .done left firstHeap' in fixture and 'secondBuilt = .done right heap' in fixture
    assert 'left ≠ right' in fixture and '= .bothMu' in fixture
    assert 'theorem query_inputs' in fixture and 'theorem enter_inputs' in fixture
    assert 'theorem child_inputs' in fixture and 'theorem finish_inputs' in fixture
    assert 'SourceCurrentNativeOwnedGeneration.execute' not in fixture
    assert (evidence / 'compiled-owner-fixture/owner-kernels-selection.json').is_file()
    assert read(evidence / 'selection-status.json') == config['selection_status']
    assert config['selection_status']['finalized']
    assert (evidence / 'proof-commit.txt').read_text().strip() == config['proof_commit']
    assert (evidence / 'starting-head.txt').read_text().strip() == config['starting_head']
    imported = (root / 'lean/MicroCFTA/Audit.lean').read_text()
    for module in modules:
        assert 'import MicroCFTA.' + module in imported

    owner = (root / 'lean/MicroCFTA/SourceCurrentNativeOptionalOwner.lean').read_text()
    assert 'Nat.strongRecOn' in owner and 'sourceKey_complete' in owner
    assert '\ntheorem request ' in owner and 'actual : Trace fuel' in owner
    combined = (root / 'lean/MicroCFTA/SourceCurrentNativeOwnedGeneration.lean').read_text()
    assert combined.count('rcases SourceCurrentNativeMuStoppingGeneration.execute ') == 1
    assert 'SourceCurrentNativeOptionalOwner.request request prefixFuel before siteBefore' in combined
    assert 'before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨' in combined
    assert 'writer,owner⟩' in combined
    for path, phrases in config['document_phrases'].items():
        text = ' '.join((root / path).read_text().lower().split())
        for phrase in phrases:
            assert phrase.lower() in text, (path, phrase)
    findings = (root / 'FINDINGS.md').read_text()
    assert findings.index('## Haskell fix handoff for external work') < findings.index(config['findings_marker'])
    baseline = read(evidence / 'starting-sha256.json')
    haskell = {name for name in baseline if name.endswith('.hs')}
    packages = {'cfta', 'cfta-generator', 'cfta-ghc', 'decision-model'}
    active = {name for name in baseline if name.split('/', 1)[0] in packages}
    assert len(haskell) == 268 and len(active) == 207
    for name in haskell | active:
        assert sha(root / name) == baseline[name], name
    print(json.dumps({'status': 'PASS', 'live': args.live, 'ranges': len(ranges),
        'root_pins': len(manifest['files']), 'here_artifacts': len(manifest['artifacts']),
        'reused_public_pairs': 12, 'reused_constructed_pairs': 1,
        'all_archived_lean_lake_commands': config['lean_jobs'], 'all_archived_failures': config['failures'],
        'empty_selected_strict_logs': 10, 'unique_canonical_jobs': len(canonical),
        'audit_jobs': audit['jobs'], 'audit_dependency_checks': audit['dependency_checks'],
        'haskell_files_unchanged': 268, 'active_package_files_unchanged': 207,
        'new_lean_jobs': 0, 'new_proof_pairs': 0}))


if __name__ == '__main__':
    main()
