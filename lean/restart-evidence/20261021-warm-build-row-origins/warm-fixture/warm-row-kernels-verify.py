import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = 'warm-row-kernels'
NAME = 'MicroCFTA.WarmBuildRowFixture.actual_warm_entry_row'
FINAL = 'a01b57d6cdec60b9ee8e49837a5dbc42cdeca1d50e23555adbb86d7a30c43934'
PRINTER = 'bce08022da0bea2e931aabfd1be9271e34da5e74f9480c0e65ffa87b315a904e'
DEPENDENCY = 'ae6b1f3bfa3474ba6035039cf61e7bf7edf5492ca85c5f123c2d682203b6d41b'
ATTEMPTS = {PREFIX + '-direct-' + str(i): 1 if i < 5 else 0 for i in range(1, 6)}
ATTEMPTS[PREFIX + '-public-1'] = 0
OPTIONS = ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true',
           'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true',
           'pp.maxSteps 10000000']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(base, item):
    data = (base / item['path']).read_bytes()
    assert len(data) == item['bytes'], ('bytes', item['path'])
    assert digest(data) == item['sha256'], ('sha256', item['path'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=next(
        (p for p in HERE.parents if (p / 'lean/MicroCFTA').is_dir()),
        Path('/home/tritlo/Code/mcfta')))
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / (PREFIX + '-manifest.json')).read_text())
    selection = json.loads((HERE / (PREFIX + '-selection.json')).read_text())
    for item in manifest['files']:
        check(HERE, item)
    for item in manifest['sources']:
        check(HERE, dict(item, path=item['snapshot']))
        if args.live:
            check(args.root, item)
    pins = json.loads((HERE / (PREFIX + '-source-pins.json')).read_text())
    assert manifest['sources'] == pins['sources']
    assert manifest['sources'][0]['sha256'] == DEPENDENCY
    assert not any(p['path'] == PREFIX + '-peaks.txt' for p in manifest['files'])
    actual = {p.stem for p in HERE.glob(PREFIX + '-*.json')
              if re.fullmatch(PREFIX + r'-(?:direct|public)-\d+', p.stem)}
    assert actual == set(ATTEMPTS), actual
    started = {}
    for stem, code in ATTEMPTS.items():
        meta = json.loads((HERE / (stem + '.json')).read_text())
        assert meta['exit_code'] == code, (stem, meta['exit_code'])
        assert meta['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert '-Dlinter.all=true' in meta['command']
        assert Path(meta['command'][-1]).name == meta['source']
        assert digest((HERE / meta['source']).read_bytes()) == meta['sha256']
        assert json.loads((HERE / meta['limits']).read_text()) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        assert meta['wrapper'][meta['wrapper'].index('--mem') + 1] == '4G'
        assert meta['wrapper'][meta['wrapper'].index('--time') + 1] == '5m'
        first = datetime.datetime.fromisoformat(meta['started_at'])
        last = datetime.datetime.fromisoformat(meta['observed_at'])
        assert 0 <= (last - first).total_seconds() < 300
        started[stem] = first
        usage = json.loads((HERE / (stem + '.usage.json')).read_text())
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
    source = (HERE / (PREFIX + '.lean')).read_text()
    assert digest(source.encode()) == FINAL
    assert source.encode() == (HERE / (PREFIX + '-direct-5.source.lean')).read_bytes()
    assert not (HERE / (PREFIX + '-direct-5.log')).read_bytes()
    assert not re.search(r'\b(?:sorry|axiom)\b', source)
    assert 'native_decide' not in source and '_private' not in source
    assert len(re.findall(r'^theorem ', source, re.M)) == 1
    assert source.count('SourceCurrentWarmBuildRowOrigins.build_row_origins outer [] firstHeap first_context event.candidate event.after outer_done') == 1
    for forbidden in ['build_trace_warm_target', 'build_trace_warm ', 'build_trace_writers',
                      'SourceCurrentNativeOriginalObservedResume.of_observed']:
        assert forbidden not in source, forbidden
    private_type = source.split('private theorem checked_witness :\n', 1)[1].split(' := by\n', 1)[0]
    public_type = source.split('theorem actual_warm_entry_row :\n', 1)[1].split(' := checked_witness', 1)[0]
    assert private_type == public_type
    for token in [
        'build nested [] (empty : Heap) = .done firstMu firstHeap ∧ Context firstHeap []',
        'firstHeap.nodeRecords event.key = none',
        'build outer [] firstHeap = .done event.candidate event.after',
        'row.entry.key.symbol = ("tag17",.top)', 'row.children = []',
        '∃ path : Path before after,',
        '(∀ (index : Nat) event, (events path)[index]? = some event',
        '(∀ key entry body depth ordinary,',
        '(∀ (index : Nat) outer, (events path)[index]? = some outer',
        '∀ row, RowAt outer.body row → RowOrigin original initial before path index outer row',
        '(events path)[targetIndex]? = some selected',
        'event.key = selected.key ∧ event.candidate = selected.candidate',
        'producerIndex ≤ targetIndex ∧ (events path)[producerIndex]? = some producer',
        'producer.expression = outerBody',
        'SourceRow terminalExpression terminalInputs terminalStart terminalValue terminalStop row',
        'Grows producer.allocated terminalStart',
        'terminalInputs = (.reference (.interned producer.entry.identity) :: producer.environment)',
        'SyntaxBound terminalExpression producer.expression',
        'UnionDescent producer.expression terminalExpression',
        'terminalExpression = .binder smart body ∧ terminalExpression = nested',
        'smart = false ∧ body = nestedBody',
        'before.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary)',
        'Value.mu tEntry tBody tDepth tOrdinary = firstMu',
        'Grows before tCut',
        'tCut.nodes.table (muKey tDepth tOrdinary) = some tEntry',
        'tCut.nodeRecords (muKey tDepth tOrdinary) = some (.mu tEntry tBody tDepth tOrdinary)',
        'terminalStop = tCut ∧ terminalValue = firstMu',
        'request smart tDepth tOrdinary (callback body terminalInputs) tCut = .done firstMu tCut']:
        assert token in public_type, token
    assert 'sizeOf terminalExpression' not in public_type
    for token in [
        'writers event.key event.entry event.body event.depth event.ordinary selected',
        'origins targetIndex selected lookup row inside',
        'event_expression path producer producerIndex producerLookup (sites _ _ producerLookup)',
        'forced_terminal routeOuter nonunion',
        'only_first_full _ tEntry tBody tDepth tOrdinary prior',
        'event_before path producer (List.mem_of_getElem? producerLookup)',
        '(grows_trans (publication_allocated producer) entryGrowth)',
        'have toCut := grows_trans sourceGrowth (grows_trans depthGrowth ordinaryGrowth)',
        'simp only [request,cutKey,cutRecord]',
        'callback nestedBody inputs name firstHeap = .done firstDepth firstHeap := by cbv',
        'InternedFreshOrdinaryReplay.callback_replays nestedBody inputs name firstHeap state firstDepth firstHeap']:
        assert token in source, token
    assert source.count('origins targetIndex selected lookup row inside') == 1
    predecessor = HERE / 'inputs/indexed-resumption-kernels.predecessor.lean'
    assert digest(predecessor.read_bytes()) == 'd1e37939d0fe8e9b7ae0924665a08341ac7a195cd9e861764c04f9835c832818'
    prior = predecessor.read_text()
    for name in ['top', 'nestedBody', 'nested', 'outerBody', 'outer', 'firstRun', 'firstMu',
                 'firstHeap', 'depthRun', 'depth', 'afterDepth', 'ordinaryRun', 'ordinary',
                 'cut', 'reserved', 'allocated', 'bodyRun', 'storedBody', 'afterBody']:
        pattern = r'^private def ' + re.escape(name) + r'\b[^\n]*'
        assert re.search(pattern, source, re.M).group() == re.search(pattern, prior, re.M).group(), name
    printer = (HERE / (PREFIX + '-public.lean')).read_text()
    assert printer.startswith(source) and digest(printer.encode()) == PRINTER
    assert printer.encode() == (HERE / (PREFIX + '-public-1.source.lean')).read_bytes()
    for option in OPTIONS:
        assert 'set_option ' + option in printer
    for pattern in [r'^#check @', r'^#print (?!axioms )', r'^#print axioms ']:
        assert len(re.findall(pattern, printer, re.M)) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert directive + NAME in printer
    log = (HERE / (PREFIX + '-public-1.log')).read_text()
    assert len(log.encode()) == 1188108
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    assert re.search(r'^theorem ' + re.escape(NAME), log, re.M)
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(reports) == 1
    axioms = set(re.split(r',\s*', re.sub(r'\.\{[^}]*\}', '', reports[0]).strip()))
    assert axioms == {'propext', 'Classical.choice', 'Quot.sound'}, axioms
    assert selection['finalized'] and selection['public_heads'] == [NAME]
    assert selection['source_sha256'] == FINAL and selection['printer_sha256'] == PRINTER
    assert selection['source'] == PREFIX + '.lean'
    assert selection['attempts'] == list(ATTEMPTS) and selection['expected_exit_codes'] == ATTEMPTS
    assert selection['strict'] == selection['selected_strict'] == PREFIX + '-direct-5'
    assert selection['selected_public'] == PREFIX + '-public-1'
    assert selection['groups'] == [dict(name=PREFIX + '-public-1', pairs=1, kind='constructed', full_proof=True)]
    assert selection['lean_jobs'] == 6 and selection['failed_attempts'] == 4
    assert selection['production_pairs'] == 0 and selection['constructed_pairs'] == 1
    assert selection['canonical'] is None and selection['canonical_jobs'] == 0
    assert selection['same_prior_source_family'] and selection['same_returned_cut_cache_hit']
    assert selection['source_only'] and selection['distinct_new_source_examples'] == 0
    peaks = (HERE / (PREFIX + '-peaks-final.txt')).read_text().splitlines()
    order = sorted(ATTEMPTS, key=started.get)
    assert len(peaks) == 6
    assert [int(row.split()[-1]) for row in peaks] == [ATTEMPTS[stem] for stem in order]
    assert all(row.split()[2] == '4G' for row in peaks)
    print(json.dumps(dict(status='PASS', pins=len(manifest['files']) + len(manifest['sources']),
                          lean_jobs=6, failed_attempts=4, production_pairs=0, constructed_pairs=1,
                          canonical_jobs=0, mode='live' if args.live else 'ordinary')))


if __name__ == '__main__':
    main()
