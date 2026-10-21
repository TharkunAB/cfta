import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '0bcad2715a1170cac3c7bf99423b716916c068a3a859e092d70258c368b40f39'
HEAD = 'MicroCFTA.SourceCurrentPositiveOwnerPair.same_child_pair'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256'], path
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'positive-owner-manifest.json').read_text())
    assert manifest['finalized']
    for item in manifest['files']:
        checked(HERE / item['path'], item)
    assert json.loads((HERE / 'positive-owner-source-pins.json').read_text())['sources'] == manifest['sources']
    for item in manifest['sources']:
        checked(HERE / item['snapshot'], item)
        if args.live:
            checked(args.root / item['path'], item)
    selection = json.loads((HERE / 'positive-owner-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == [HEAD]
    assert selection['selected_strict'] == 'positive-owner-direct-2'
    assert selection['selected_public'] == 'positive-owner-public-1'
    assert selection['attempts'] == {'positive-owner-direct-1': 1,
        'positive-owner-direct-2': 0, 'positive-owner-public-1': 0}
    assert selection['lean_jobs'] == 3 and selection['failed_checks'] == 1
    assert selection['warning_checks'] == selection['canonical_jobs'] == selection['constructed_pairs'] == 0
    assert selection['new_public_pairs'] == 1
    source = (HERE / selection['source']).read_bytes()
    assert digest(source) == FINAL and len(source.decode().splitlines()) == 124
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / selection['source']
        if installed.exists():
            assert installed.read_bytes() == source
    text = source.decode()
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['same_child_pair']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    public = text.split('theorem same_child_pair', 1)[1].split(':=', 1)[0]
    for token in ['congruenceStep classes = some classes', '(member : row ∈ rows)',
        'SourceMemoGate.plain row.entry.key.constraint = false',
        'back : ∀ q, PositiveAt (.node entry rows depth free) q',
        'row.children[j]? = some original ∧ PositiveAt original p',
        'Rel classes (index :: q) (j :: p)',
        'index :: left ∈ paths ∧ index :: right ∈ paths ∧ left ≠ right']:
        assert token in public, token
    for token in ['candidates', 'positivePaths', 'History', 'Current', 'Stored', 'enumeration']:
        assert token not in public, token
    for token in ['InternedValueMass.node_child_lt', 'InternedValueMass.union_member_lt',
        'SymbolicDriver.eraseDups_nodup', 'SourceCurrentNormalizedChildSeparation.child_separate',
        'SymbolicDriver.relation_cardinality_le']:
        assert text.count(token) == 1, token
    assert 'decide (PositiveAt value path)' in text and '.eraseDups' in text
    initial = (HERE / 'positive-owner-direct-1.source.lean').read_text()
    repaired = initial.replace('  by_contra absent\n', '  apply Classical.byContradiction\n  intro absent\n')
    repaired = repaired.replace('    by_contra different\n', '    apply Classical.byContradiction\n    intro different\n')
    assert repaired == text
    assert 'unknown tactic' in (HERE / 'positive-owner-direct-1.log').read_text()
    for stem, code in selection['attempts'].items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code
        assert digest((HERE / meta['source']).read_bytes()) == meta['sha256']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        start = datetime.datetime.fromisoformat(meta['started_at'])
        end = datetime.datetime.fromisoformat(meta['observed_at'])
        assert 0 <= (end - start).total_seconds() < 300
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['remaining_percent'] > 1 and usage['age_seconds'] < 120
        observed = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
        assert 0 <= (start - observed).total_seconds() < 120
    assert not (HERE / 'positive-owner-direct-2.log').read_bytes()
    assert (HERE / 'positive-owner-direct-2.source.lean').read_bytes() == source
    printer = (HERE / 'positive-owner-public-1.source.lean').read_bytes()
    assert printer.startswith(source) and printer == (HERE / 'positive-owner-public.lean').read_bytes()
    printer = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
        'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD + '\n') == 1
    data = (HERE / 'positive-owner-public-1.log').read_bytes()
    assert len(data) == selection['public_log_bytes'] == 49749
    assert digest(data) == selection['public_log_sha256'] == '6c4b63c93b28dc66ff00fa79957e5455a522517ea6bc537083d29e60dec95979'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    match = re.search("'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
    check, theorem = log.split('theorem ' + HEAD + ' : ', 1)
    typ, proof = theorem.split(':=', 1)
    assert '_private' not in typ and len(proof) > 1000
    assert re.sub(r'\s+', ' ', check.split(' : ', 1)[1]).strip() == re.sub(r'\s+', ' ', typ).strip()
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']), 'source_sha256': FINAL,
        'actual_lean_jobs': 3, 'failed_checks': 1, 'selected_strict_log_bytes': 0,
        'full_public_log_bytes': len(data), 'public_pairs': 1, 'constructed_pairs': 0,
        'canonical_jobs': 0, 'all_eight_printer_settings': True,
        'public_type_readback_identical': True, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
