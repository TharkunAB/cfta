import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
FINAL = '3afe4498787d5434cd0eda6821eeca85811f4a2c4f7b1c2dbcc9a2d0bd4a6fe4'
HEAD = 'MicroCFTA.SourceCurrentRequiredPositiveChronology.pass'


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
    manifest = json.loads((HERE / 'required-positive-manifest.json').read_text())
    assert manifest['finalized'] is True
    for item in manifest['files']:
        check(HERE / item['path'], item)
    assert json.loads((HERE / 'required-positive-source-pins.json').read_text())['sources'] == manifest['sources']
    for item in manifest['sources']:
        check(HERE / item['snapshot'], item)
        if args.live:
            check(args.root / item['path'], item)
    selection = json.loads((HERE / 'required-positive-selection.json').read_text())
    assert selection['finalized'] and selection['source_sha256'] == FINAL and selection['public_heads'] == [HEAD]
    assert selection['selected_strict'] == 'required-positive-direct-1'
    assert selection['selected_public'] == 'required-positive-public-1'
    assert selection['attempts'] == {'required-positive-direct-1': 0, 'required-positive-public-1': 0}
    assert selection['lean_jobs'] == 2 and selection['failed_checks'] == selection['warning_checks'] == 0
    assert selection['canonical_jobs'] == selection['constructed_pairs'] == 0 and selection['new_public_pairs'] == 1
    source = (HERE / selection['source']).read_bytes()
    assert digest(source) == FINAL and len(source.decode().splitlines()) == 115
    if args.live:
        installed = args.root / 'lean/MicroCFTA' / selection['source']
        if installed.exists():
            assert installed.read_bytes() == source
    text = source.decode()
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['pass']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private', text)
    public = text.split('theorem pass ', 1)[1].split(':=', 1)[0]
    for token in ['originalValues preparedValues scan prepared', 'current : Current scan',
                  'NativeSupport scan.native.machine.heap scan.native', 'History empty scan.native.machine.heap',
                  'Pass records preparedValues prepared memo results after saved',
                  'NativeSupport after.native.machine.heap after.native',
                  'Nonempty (History empty after.native.machine.heap)', 'MergeSupport saved',
                  'originalValues[inputIndex]? = some original',
                  'Rel selected (outputIndex::residual) (inputIndex::originalPath)']:
        assert token in public, token
    for token in ['preparedCurrent', 'preparedSupport', 'preparedHistory', 'guards :', 'advanceHeap', 'composed']:
        assert token not in public, token
    for token in ['SourceCurrentClassPositiveChronology.pass',
                  'SourceCurrentRequiredForestPositive.requireAll actualRequired',
                  'SourceCurrentRequiredGuard.children Plain graph',
                  'SourceCurrentRequiredPublicationHistory.children graph',
                  'SourceCurrentNativePositiveSupportAdvance.advance scan prepared',
                  'SourceCurrentConstrainedCapCurrentNative.advance Plain scan prepared',
                  'required.stable']:
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
    assert not (HERE / 'required-positive-direct-1.log').read_bytes()
    assert (HERE / 'required-positive-direct-1.source.lean').read_bytes() == source
    printer = (HERE / 'required-positive-public-1.source.lean').read_bytes()
    assert printer.startswith(source) and printer == (HERE / 'required-positive-public.lean').read_bytes()
    printer = printer.decode()
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
                   'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD + '\n') == 1
    data = (HERE / 'required-positive-public-1.log').read_bytes()
    assert len(data) == selection['public_log_bytes'] == 601861
    assert digest(data) == selection['public_log_sha256'] == '07031226069d2a0a131d9807bdb0041af9049f4fcc215b2e23d9d48b0106cb9b'
    log = data.decode()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    match = re.search("'" + re.escape(HEAD) + r"' depends on axioms:\s*\[([^\]]*)\]", log)
    assert match
    assert {re.sub(r'\.\{[^}]*\}', '', n.strip()) for n in match.group(1).split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
    checked, theorem = log.split('theorem ' + HEAD + ' : ', 1)
    typ, proof = theorem.split(':=', 1)
    assert '_private' not in typ and len(proof) > 1000
    assert re.sub(r'\s+', ' ', checked.split(' : ', 1)[1]).strip() == re.sub(r'\s+', ' ', typ).strip()
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'pins': len(manifest['files']) + len(manifest['sources']), 'source_sha256': FINAL,
        'actual_lean_jobs': 2, 'failed_checks': 0, 'selected_strict_log_bytes': 0,
        'full_public_log_bytes': len(data), 'public_pairs': 1, 'constructed_pairs': 0,
        'canonical_jobs': 0, 'all_eight_printer_settings': True,
        'public_type_readback_identical': True, 'standard_axioms_only': True}))


if __name__ == '__main__':
    main()
