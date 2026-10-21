import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = 'SourceCurrentRequiredSharedTargetCap.lean'
FINAL = 'e6a2c3bb9ce0123877feee3e836770a1ddd24f10a2dd057ef3441feda9bb42cb'
HEADS = ['MicroCFTA.SourceCurrentRequiredSharedTargetCap.' + name
         for name in ['Stored', 'initial_stored', 'force_receipt']]


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
    assert manifest['owned_lean_lake_commands'] == 0
    assert manifest['owned_public_pairs'] == 0
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
    assert len(text.splitlines()) == 198
    assert len(re.findall(r'^structure ', text, re.M)) == 1
    assert len(re.findall(r'^theorem ', text, re.M)) == 2
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    invariant = text.split('structure Stored ', 1)[1].split('theorem initial_stored ', 1)[0]
    for token in ['current : Current state.checked', 'merge : MergeStored state.memo',
                  'slots : ∀ path value, state.targets path = some value → ∃ depth, Cap Plain depth value']:
        assert token in invariant, token
    public = text.split('theorem force_receipt', 1)[1].split(':=', 1)[0]
    for token in [
        '(SourceEqualitySelectedRequired.paths selected) originals scanHeap = .done prepared preparedHeap',
        'ClassTrace source reaches originals paths scanHeap false scanHeap',
        'record.paths ∈ selected', 'SourceEqualityClassOrder.Coherent record',
        'EqualityNormalize.Nontrivial record.paths',
        'SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record prepared receiptBase action',
        'Ready formulas solver inventory record prepared preparedHeap before',
        '(stored : Stored before)', 'Stored after ∧ ∃ depth, Cap Plain depth value']:
        assert token in public, token
    assert public.count('Cap Plain') == 1
    for token in [
        'SourceCurrentRequiredHeapEffects.requireAll',
        'SourceCurrentRequiredForestProjectionCap.project data.required data.semantic data.normal',
        'SourceCurrentConstrainedCapCurrentNative.advance Plain before middle current',
        'SourceCurrentConstrainedCapMergeJointEffects.merge Plain formulas solver inventory',
        'SourceCurrentConstrainedCapMemoMerge.retained Plain',
        'ih data receipt.ready (captured.trans receipt.effects.keeps)',
        'SourceCurrentConstrainedCapCurrentNative.step (max headDepth tailDepth)',
        'SourceEqualityClassTarget.operandPaths_nonroot record coherent active action path member',
        'cases receipt.reads with',
        '| hit present => exact ⟨stored,stored.slots action value present⟩',
        'target_cap data reads ready.checked ready.captured ready.stored stored.merge stored.current proper']:
        assert text.count(token) == 1, token
    owner = HERE / 'inputs/owner'
    all_stems = ['shared-cap-direct-1', 'shared-cap-direct-2', 'shared-cap-public-1']
    for stem in all_stems:
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
    assert not (owner / 'shared-cap-direct-2.log').read_bytes()
    assert (owner / 'shared-cap-direct-2.source.lean').read_bytes() == data
    first_log = (owner / 'shared-cap-direct-1.log').read_text()
    assert 'error:' in first_log and 'missing doc string for public field' in first_log
    selection = json.loads((owner / 'shared-cap-selection.json').read_text())
    assert selection['finalized'] is True
    assert selection['source_sha256'] == FINAL and selection['public_heads'] == HEADS
    assert selection['selected_strict'] == 'shared-cap-direct-2'
    assert selection['selected_public'] == 'shared-cap-public-1'
    assert selection['lean_jobs'] == 3 and selection['failed_lean_checks'] == 1
    assert selection['public_pairs'] == 3 and selection['constructed_pairs'] == 0
    printer = (owner / 'shared-cap-public-1.source.lean').read_text()
    assert printer.startswith(text)
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert 'set_option ' + option in printer
    log = (owner / 'shared-cap-public-1.log').read_text()
    assert len(log.encode()) == 138683
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1
        report = re.search(r"'" + re.escape(head) + r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
        assert report, head
        names = set() if report.group(1) is None else {
            re.sub(r'\.\{[^}]*\}', '', name.strip()) for name in report.group(1).split(',') if name.strip()}
        assert names == {'propext', 'Classical.choice', 'Quot.sound'}, (head, names)
        kind = 'structure' if head.endswith('.Stored') else 'theorem'
        block = log.split(kind + ' ' + head, 1)[1].split("'" + head + "'", 1)[0]
        if kind == 'structure':
            assert 'fields:' in block and 'constructor:' in block and '_private' not in block
        else:
            typ, proof = block.split(':=', 1)
            assert typ.strip() and proof.strip() and '_private' not in typ
    print(json.dumps({'status': 'PASS', 'pins': len(manifest['files']) + len(manifest['sources']),
                      'live': args.live, 'review': 'independent', 'material_issues': 0,
                      'owned_lean_lake_commands': 0, 'owned_public_pairs': 0,
                      'reused_full_public_pairs': 3, 'selected_strict_log_bytes': 0,
                      'full_public_log_bytes': 138683, 'standard_axioms_only': True,
                      'reused_actual_lean_jobs': 3, 'reused_lean_failures': 1,
                      'reused_infrastructure_attempts': 0}))


if __name__ == '__main__':
    main()
