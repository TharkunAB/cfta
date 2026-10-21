import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = 'required-forest-projection-cap-review'
SOURCE = 'SourceCurrentRequiredForestProjectionCap.lean'
FINAL = '7569b823aa8b9d5a1935664fceb2630268fdd2641169d2f2e7bd87f9daee1e95'
HEADS = ['MicroCFTA.SourceCurrentRequiredForestProjectionCap.' + n
         for n in ['project']]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], ('bytes', item['path'])
    assert digest(data) == item['sha256'], ('hash', item['path'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        check(HERE, item)
    for item in manifest['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    pins = json.loads((HERE / 'source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    candidate = pins['candidate']
    data = (HERE / candidate['snapshot']).read_bytes()
    assert digest(data) == candidate['sha256'] == FINAL
    assert len(data) == candidate['bytes']
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / SOURCE
        if installed.is_file():
            assert installed.read_bytes() == data, 'installed candidate'
    text = data.decode()
    assert len(text.splitlines()) == 88
    assert len(re.findall(r'^theorem ', text, re.M)) == 1
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    public = text.split('theorem project ', 1)[1].split(':=', 1)[0]
    for token in [
        'SourceEqualityRequiredExecution.requireAll requiredFuel requiredReadFuel',
        '(SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap',
        '∀ paths ∈ selected, ClassTrace source reaches originals paths scanHeap false scanHeap',
        'chosenClass ∈ selected', 'index :: path ∈ chosenClass',
        'Keeps preparedHeap currentHeap', 'SemanticReady currentHeap', 'CostHeap currentHeap',
        'Guards currentHeap',
        'Forest ((index :: path).map Int.ofNat) prepared currentHeap result afterHeap',
        '∃ depth, Cap Plain depth result']:
        assert token in public, token
    assert public.count('Cap Plain') == 1
    assert 'Origin original prepared' not in public and 'free = []' not in public
    for token in [
        'SourceCurrentRequiredHeapEffects.requireAll',
        'SourceEqualityRequiredExecution.requireAll_execution_iff',
        'SourceCurrentRequiredPrimaryExposure.selected_domain',
        'SourceCurrentRequiredRowOrigins.children graph',
        'later.available value (requiredEffects.2.2.2.2 value member)',
        'SourceEqualityProjectionLanguage.all₂_selected related index _ natural',
        'SourceCurrentRequiredPrimaryExposure.false_class_paths originals chosenClass scanHeap scanHeap',
        'SourceCurrentRequiredPrimaryExposure.false_selected traced originalFound',
        'SourceCurrentOriginalGateProjectionCap.project path original _ scanHeap scanHeap',
        '| missing absent => exact ⟨0, .plain 0 .empty⟩']:
        assert text.count(token) == 1, token
    owner = HERE / 'inputs/owner'
    for stem in ['forest-cap-direct-2', 'forest-cap-public-1']:
        meta = json.loads((owner / (stem + '.json')).read_text())
        assert meta['exit_code'] == 0
        assert digest((owner / meta['source']).read_bytes()) == meta['sha256']
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        assert json.loads((owner / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        start = datetime.datetime.fromisoformat(meta['started_at'])
        end = datetime.datetime.fromisoformat(meta['observed_at'])
        assert 0 <= (end - start).total_seconds() < 300
        usage = json.loads((owner / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        observed = datetime.datetime.fromisoformat(usage['observed_at'].replace('Z', '+00:00'))
        assert 0 <= (start - observed).total_seconds() < 120
    assert not (owner / 'forest-cap-direct-2.log').read_bytes()
    assert (owner / 'forest-cap-direct-2.source.lean').read_bytes() == data
    selection = json.loads((owner / 'forest-cap-selection.json').read_text())
    assert selection['finalized'] is True
    assert selection['source_sha256'] == FINAL and selection['public_heads'] == HEADS
    assert selection['selected_strict'] == 'forest-cap-direct-2'
    assert selection['selected_public'] == 'forest-cap-public-1'
    assert selection['lean_jobs'] == 2 and selection['failed_checks'] == 0
    assert selection['new_public_pairs'] == 1 and selection['constructed_pairs'] == 0
    ledger = json.loads((owner / 'forest-cap-attempts.json').read_text())
    assert ledger['actual_lean_jobs'] == 2 and ledger['actual_lean_failures'] == 0
    assert ledger['infrastructure_attempts'] == 1
    entries = {entry['stem']: entry for entry in ledger['entries']}
    assert set(entries) == {'forest-cap-direct-1', 'forest-cap-direct-2', 'forest-cap-public-1'}
    first = entries['forest-cap-direct-1']
    assert first['launched'] is False and first['classification'] == 'infrastructure_bus_denial'
    assert not (owner / 'forest-cap-direct-1.limits.json').exists()
    assert (owner / 'forest-cap-direct-1.log').read_bytes() == b'Failed to connect to bus: Operation not permitted\n'
    assert (owner / 'forest-cap-direct-1.source.lean').read_bytes() == data
    assert json.loads((owner / 'forest-cap-direct-1.json').read_text())['exit_code'] == 1
    for stem, entry in entries.items():
        for field in ['receipt', 'log', 'source', 'usage']:
            check(owner, entry[field])
        if stem != 'forest-cap-direct-1':
            assert entry['launched'] is True and entry['classification'] == 'lean_check'
    assert selection['infrastructure_attempts'] == ['forest-cap-direct-1']
    assert selection['infrastructure_attempt_count'] == 1
    printer = (owner / 'forest-cap-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (owner / 'forest-cap-public-1.log').read_text()
    assert len(log.encode()) == 295880
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1
        report = re.search(r"'" + re.escape(head) + r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
        assert report, head
        names = set() if report.group(1) is None else {
            re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in report.group(1).split(',') if n.strip()}
        assert names == {'propext', 'Classical.choice', 'Quot.sound'}, (head, names)
        kind = 'theorem'
        block = log.split(kind + ' ' + head, 1)[1].split("'" + head + "'", 1)[0]
        typ, proof = block.split(':=', 1)
        assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'review': 'independent', 'material_issues': 0,
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'reused_full_public_pairs': 1, 'selected_strict_log_bytes': 0,
                      'full_public_log_bytes': 295880, 'standard_axioms_only': True, 'reused_actual_lean_jobs': 2,
                      'reused_lean_failures': 0, 'reused_infrastructure_attempts': 1}))


if __name__ == '__main__':
    main()
