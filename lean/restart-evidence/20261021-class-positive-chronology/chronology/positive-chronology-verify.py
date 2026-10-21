import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '38f14f1c54e09147d4a19f79b5f938f71ae28eaad3bf102f5b1d37b3f28b1d7a'
HEADS = ['MicroCFTA.SourceCurrentClassPositiveChronology.fold',
         'MicroCFTA.SourceCurrentClassPositiveChronology.pass']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(path, item):
    data = path.read_bytes()
    assert len(data) == item['bytes'] and digest(data) == item['sha256'], path
    return data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'positive-chronology-manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        check(HERE / item['path'], item)
    assert json.loads((HERE / 'positive-chronology-source-pins.json').read_text())['sources'] == manifest['sources']
    for item in manifest['sources']:
        check(HERE / item['snapshot'], item)
        if args.live:
            check(args.root / item['path'], item)
    selection = json.loads((HERE / 'positive-chronology-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == FINAL and selection['public_heads'] == HEADS
    assert selection['selected_strict'] == 'positive-chronology-direct-1'
    assert selection['selected_public'] == 'positive-chronology-public-1'
    assert selection['attempts'] == {'positive-chronology-direct-1': 0, 'positive-chronology-public-1': 0}
    assert selection['lean_jobs'] == 2 and selection['failed_checks'] == selection['warning_checks'] == 0
    assert selection['canonical_jobs'] == selection['constructed_pairs'] == 0 and selection['new_public_pairs'] == 2
    source = (HERE / selection['source']).read_bytes()
    assert digest(source) == FINAL and len(source.decode().splitlines()) == 213
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / selection['source']
        if installed.exists():
            assert installed.read_bytes() == source
    text = source.decode()
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['fold', 'pass']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    for name in ['fold', 'pass']:
        public = text.split('theorem ' + name + ' ', 1)[1].split(':=', 1)[0]
        for token in ['NativeSupport before.native.machine.heap before.native',
                      'History empty before.native.machine.heap', 'MergeSupport memo',
                      'NativeSupport after.native.machine.heap after.native',
                      'Nonempty (History empty after.native.machine.heap)', 'MergeSupport saved',
                      'results[outputIndex]? = some result', 'values[inputIndex]? = some original',
                      'PositiveAt original originalPath',
                      'Rel (records.map SourceEqualityClassOrder.Record.paths) (outputIndex::residual) (inputIndex::originalPath)']:
            assert token in public, (name, token)
    for token in ['SourceCurrentClassPositiveAncestry.class_reads',
                  'headBack outputIndex result found residual positive',
                  'tailBack middleIndex middleValue middleFound middlePath middlePositive',
                  'exact .trans headFull tailFull', 'propagate_back back']:
        assert text.count(token) == 1, token
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
    assert not (HERE / 'positive-chronology-direct-1.log').read_bytes()
    assert (HERE / 'positive-chronology-direct-1.source.lean').read_bytes() == source
    printer = (HERE / 'positive-chronology-public-1.source.lean').read_bytes()
    assert printer.startswith(source) and printer == (HERE / 'positive-chronology-public.lean').read_bytes()
    printer = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head + '\n') == 1
    data = (HERE / 'positive-chronology-public-1.log').read_bytes()
    assert len(data) == selection['public_log_bytes'] == 884592
    assert digest(data) == selection['public_log_sha256'] == '3f14eb7f6f44b5c95aa4a57bb926a3ccedd24fe497b7181751ea0cb1fd26202e'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for i, head in enumerate(HEADS):
        marker = '@' + head + ' : '
        block = log.split(marker, 1)[1]
        if i + 1 < len(HEADS):
            block = block.split('@' + HEADS[i + 1] + ' : ', 1)[0]
        checked, theorem = block.split('theorem ' + head + ' : ', 1)
        typ, proof = theorem.split(':=', 1)
        assert '_private' not in typ and len(proof) > 1000
        assert re.sub(r'\s+', ' ', checked).strip() == re.sub(r'\s+', ' ', typ).strip()
        match = re.search("'" + re.escape(head) + r"' depends on axioms:\s*\[([^\]]*)\]", block)
        assert match
        assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']), 'source_sha256': FINAL,
        'actual_lean_jobs': 2, 'failed_checks': 0, 'selected_strict_log_bytes': 0,
        'full_public_log_bytes': len(data), 'public_pairs': 2, 'constructed_pairs': 0,
        'canonical_jobs': 0, 'all_eight_printer_settings': True,
        'public_type_readback_identical': True, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
