import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentClassCorridorChronology.lean'
FINAL = 'aaa17d7fb9280fd7f027ee18b17b363824c2c9d0990433a7b7a47d16af99e080'
HEADS = ['MicroCFTA.SourceCurrentClassCorridorChronology.' + name for name in ['fold', 'pass', 'indexed_phase']]


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
    assert manifest['owned_lean_lake_commands'] == 0 and manifest['owned_public_pairs'] == 0
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
        if installed.exists():
            assert installed.read_bytes() == data
    text = data.decode()
    assert len(text.splitlines()) == 197
    assert len(re.findall(r'^theorem ', text, re.M)) == 3
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    for name in ['fold', 'pass', 'indexed_phase']:
        public = text.split('theorem ' + name + ' ', 1)[1].split(':=', 1)[0]
        for token in ['SourceEqualityClassOrder.Coherent record', 'EqualityNormalize.Nontrivial record.paths',
                      'Ready before', 'At formulas solver inventory before',
                      'Values before.native.machine.heap values',
                      'ForestClosed (path.map Int.ofNat) values',
                      'PhysicalStored before.native.machine.heap memo',
                      'Current before', 'MergeStored memo',
                      'select values (Int.ofNat index) = some value → RawCorridor (path.map Int.ofNat) value',
                      '∀ path, RawCorridor path original → RawCorridor path result']:
            assert token in public, (name, token)
        for token in ['History', 'ClassTrace', 'NodeTrace', 'Preserves', 'Masks', 'Cap Plain']:
            assert token not in public, (name, token)
    for token in [
        'SourceEqualityProjectionLanguage.all₂_signed related (Int.ofNat index) value found',
        'masks_selected retained.2.2 record (masks record List.mem_cons_self)',
        'SourceCurrentClassEndpointCorridors.class_reads formulas solver next record',
        'receipt.domains _ (domains record List.mem_cons_self path member)',
        'relation_trans retained.2.2 related',
        'relation_trans related (propagate_relation _)',
        'SourceCurrentClassPassPhaseLineage.fold_indexed reads selected',
        '∃ tail : Fold (records.drop (index + 1)) values before memo phaseValues phaseState phaseMemo',
        '∃ later : Fold (records.take index) headValues headState headMemo results after saved',
        'Receipt formulas solver phaseInventory (records.drop (index + 1)) values before memo',
        'tail, call, later, next, tailReads, callReads, laterReads, receipt, phaseCurrent, phaseMerged, related']:
        assert text.count(token) == 1, token
    assert 'fold_phase' not in text and 'History' not in text
    owner = HERE / 'inputs/owner'
    for stem in ['chronology-direct-1', 'chronology-direct-2', 'chronology-public-1']:
        meta = json.loads((owner / (stem + '.json')).read_text())
        assert meta['exit_code'] == (1 if stem.endswith('direct-1') else 0)
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
    assert not (owner / 'chronology-direct-2.log').read_bytes()
    assert (owner / 'chronology-direct-2.source.lean').read_bytes() == data
    selection = json.loads((owner / 'chronology-selection.json').read_text())
    assert selection['finalized'] is True and selection['source_sha256'] == FINAL
    assert selection['public_heads'] == HEADS
    assert selection['selected_strict'] == 'chronology-direct-2'
    assert selection['selected_public'] == 'chronology-public-1'
    assert selection['lean_jobs'] == 3 and selection['failed_checks'] == 1
    assert selection['new_public_pairs'] == 3 and selection['constructed_pairs'] == 0
    printer = (owner / 'chronology-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (owner / 'chronology-public-1.log').read_text()
    assert len(log.encode()) == selection['public_log_bytes'] == 588479
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1
        report = re.search(r"'" + re.escape(head) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
        assert report, head
        names = {re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in report.group(1).split(',') if name.strip()}
        assert names == {'propext', 'Classical.choice', 'Quot.sound'}
        block = log.split('theorem ' + head, 1)[1].split("'" + head + "'", 1)[0]
        typ, proof = block.split(':=', 1)
        assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'review': 'independent', 'material_issues': 0,
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'reused_full_public_pairs': 3, 'reused_actual_lean_jobs': 3,
                      'reused_lean_failures': 1, 'selected_strict_log_bytes': 0,
                      'full_public_log_bytes': len(log.encode()), 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
