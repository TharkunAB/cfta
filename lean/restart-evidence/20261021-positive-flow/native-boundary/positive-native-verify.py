import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = 'positive-native'
SOURCE = 'positive-native-kernels.lean'
FINAL = 'a2c8ff74346aabde69bfe0e550225bb9049198650ad78ed33c3e402907cebf0a'
PRINTER = '1a440bce1f26915cfb8d90301349a08f9ebc3e6c6d15d4721af2e984b2d46c47'
FULL = 'MicroCFTA.PositiveNativeSupportKernels.actual_opaque_mu_counterexample'
ATTEMPTS = {'positive-native-direct-1': 1, 'positive-native-direct-2': 1,
            'positive-native-direct-3': 1, 'positive-native-direct-4': 0,
            'positive-native-public-1': 0}
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
           'pp.maxSteps 10000000']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(base, pin):
    data = (base / pin['path']).read_bytes()
    assert len(data) == pin['bytes'], ('bytes', pin['path'])
    assert digest(data) == pin['sha256'], ('hash', pin['path'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    for item in manifest['files']:
        check(HERE, item)
    for item in manifest['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    pins = json.loads((HERE / (PREFIX + '-source-pins.json')).read_text())
    assert pins['sources'] == manifest['sources']
    assert not any(p['path'] == PREFIX + '-peaks.txt' for p in manifest['files'])
    actual = {p.stem for p in HERE.glob(PREFIX + '-*.json')
              if re.fullmatch(PREFIX + r'-(?:direct|public)-\d+', p.stem)}
    assert actual == set(ATTEMPTS), actual
    for stem, code in ATTEMPTS.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code, stem
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert Path(meta['command'][-1]).name == meta['source']
        assert digest((HERE / meta['source']).read_bytes()) == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        start = datetime.datetime.fromisoformat(meta['started_at'])
        end = datetime.datetime.fromisoformat(meta['observed_at'])
        assert 0 <= (end - start).total_seconds() < 300
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        observed = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
        assert 0 <= (start - observed).total_seconds() < 120
        if code:
            assert 'error:' in (HERE / (stem + '.log')).read_text()
    assert not (HERE / 'positive-native-direct-4.log').read_bytes()
    source = (HERE / SOURCE).read_bytes()
    assert digest(source) == FINAL
    assert source == (HERE / 'positive-native-direct-4.source.lean').read_bytes()
    text = source.decode()
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    assert not re.search(r'\b(?:sorry|axiom|native_decide)\b|_private', text)
    checked = text.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
    public = text.split('theorem actual_opaque_mu_counterexample :\n', 1)[1].split(' := checked_witness', 1)[0]
    assert checked == public, 'public/private full statement identity'
    for token in [
        'private def first : Syntax Symbol Guard := .binder false',
        'private def second : Syntax Symbol Guard := .binder false',
        '(∃ entry body depth ordinary, left = .mu entry body depth ordinary ∧ body.free = [])',
        '(∃ entry body depth ordinary, right = .mu entry body depth ordinary ∧ body.free = [])',
        '(∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt left path)',
        '(∀ path, ¬ SourceCurrentRequiredPositivePosition.PositiveAt right path)',
        'initial = ⟨SourceRecursiveIntersectionThunks.initial 130 ⟨source,Cache.emptyState⟩,operations⟩',
        'execute 64 (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) initial = .done result final',
        'SourceCurrentRequiredPositivePosition.PositiveAt result []',
        'SourceCurrentNativeKeyAdmission.node_done 128 64 before initial_good']:
        assert token in text, token
    assert text.count('SourceCurrentNativeKeyAdmission.node_done') == 1
    printer = (HERE / 'positive-native-public.lean').read_bytes()
    assert printer.startswith(source) and digest(printer) == PRINTER
    assert printer == (HERE / 'positive-native-public-1.source.lean').read_bytes()
    for option in OPTIONS:
        assert 'set_option ' + option in printer.decode()
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert directive + FULL in printer.decode()
    log = (HERE / 'positive-native-public-1.log').read_text()
    assert len(log.encode()) == 59080
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert re.search(r'^theorem ' + re.escape(FULL), log, re.M)
    axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(axioms) == 1
    actual_axioms = {re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in axioms[0].split(',') if a.strip()}
    assert actual_axioms == {'propext', 'Classical.choice', 'Quot.sound'}, actual_axioms
    peaks = (HERE / 'positive-native-peaks-final.txt').read_text().splitlines()
    assert len(peaks) == 5 and all(' 4G ' in line for line in peaks)
    assert [line.rsplit(' ', 1)[1] for line in peaks] == ['1', '1', '1', '0', '0']
    selection = json.loads((HERE / 'positive-native-selection.json').read_text())
    assert selection['finalized'] and selection['source'] == SOURCE
    assert selection['selected_strict'] == 'positive-native-direct-4'
    assert selection['selected_public'] == 'positive-native-public-1'
    assert selection['source_sha256'] == FINAL
    assert selection['owned_lean_lake_commands'] == 5 and selection['nonzero_commands'] == 3
    assert selection['owned_canonical_jobs'] == 0 and selection['new_public_pairs'] == 0
    assert selection['constructed_pairs'] == 1
    assert selection['groups'] == [{'name': 'positive-native-public-1', 'pairs': 1,
                                    'kind': 'constructed', 'full_proof': True}]
    plan = (HERE / 'positive-native-support-plan.md').read_text()
    for token in ['Every proposed producer below is unproved', 'SupportStored',
                  'scalar guard-depth', 'Plain bindings', 'warm optional-constructor']:
        assert token in plan, token
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'owned_lean_lake_commands': 5,
                      'nonzero_commands': 3, 'new_public_pairs': 0, 'constructed_pairs': 1,
                      'selected_strict_log_bytes': 0, 'public_log_bytes': 59080,
                      'all_eight_options': True, 'standard_axioms_only': True,
                      'source_built_opaque_mu_counterexample': True,
                      'merge_positional_support_proved': False,
                      'finite_cap_native_positional_support_proved': False}))


if __name__ == '__main__':
    main()
