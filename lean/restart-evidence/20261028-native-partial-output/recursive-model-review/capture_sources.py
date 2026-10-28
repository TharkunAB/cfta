from pathlib import Path
from hashlib import sha256
from datetime import datetime
import json

ROOT = Path('/home/tritlo/Code/mcfta')
OUT = Path('/tmp/mcfta-native-partial-output-20261028/recursive-model-review')
# Whole copies retain bytes. Inspection is limited to the named literal cuts.
SPECS = [
 ('cfta/src/Data/CFTA/Enumeration.hs', [(713,747),(776,805),(880,903),(953,1007)], True),
 ('cfta/src/Data/CFTA/Interned/Operations.hs', [(140,181)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationRecursive.lean', [(47,128)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteContract.lean', [(27,56)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryContract.lean', [(34,132),(154,180)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryResources.lean', [(27,79)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteRunHistoryStep.lean', [(27,103)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteExpansionResources.lean', [(40,65),(118,192)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationOrdinaryFallbackResources.lean', [(32,99)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationNativeOrdinaryContinuations.lean', [(20,63)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationEntry.lean', [(16,33)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationNativeIndex.lean', [(16,28)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationInitialModel.lean', [(32,73)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationPrefixModels.lean', [(25,103)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationAcceptedHeadModels.lean', [(42,72),(211,249)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteSiblingCoverage.lean', [(97,172)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationHistoryBoundaryIsolation.lean', [(54,69),(100,136)], True),
 ('lean/MicroCFTA/EnumerationProgress.lean', [(17,51)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationNativeProgress.lean', [(24,39)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationCachedTerminalAdapter.lean', [(32,83)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationTerminal.lean', [(33,66)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationChildDispatch.lean', [(34,71)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationCachedPrepare.lean', [(10,29)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationShallowChild.lean', [(17,36)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFinalize.lean', [(16,36)], True),
 ('lean/MicroCFTA/SourceEqualityRequiredHead.lean', [(15,33),(67,76)], True),
 ('lean/MicroCFTA/SourceEqualityRequiredHeadLanguage.lean', [(19,26),(82,88)], True),
 ('lean/MicroCFTA/InternedFreshOrdinaryStoredSubstitution.lean', [(75,86)], True),
 ('lean/MicroCFTA/InternedGuardedStoredExecution.lean', [(40,65)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteReservation.lean', [(55,92)], True),
 ('lean/MicroCFTA/SourcePruningEnumerationTerminalChildCoverage.lean', [(33,92)], True),
 ('lean/MicroCFTA/SourceCurrentAllocatedPartialInvariant.lean', [(24,45)], True),
 ('lean/notes-current-accepted-prefix-models.md', [(54,80),(187,200)], True),
 ('NEXT-PROMPT.md', [(52,73)], False),
 ('FINDINGS.md', [(3328,3353),(5671,5698)], False),
]
records = []
for relative, ranges, keep_whole in SPECS:
    source = ROOT / relative
    data = source.read_bytes()
    digest = sha256(data).hexdigest()
    lines = data.splitlines(keepends=True)
    record = dict(source=str(source), bytes=len(data), sha256=digest,
                  inspection='Focused literal cuts; whole-copy preservation is not a claim of whole-source review.', cuts=[])
    if keep_whole:
        whole = Path('inputs') / relative
        (OUT / whole).parent.mkdir(parents=True, exist_ok=True)
        (OUT / whole).write_bytes(data)
        record['whole'] = dict(path=str(whole), bytes=len(data), sha256=digest)
    for first, last in ranges:
        last = min(last,len(lines))
        if first > last:
            raise ValueError((relative,first,last))
        cut = b''.join(lines[first-1:last])
        cutpath = Path('cuts') / (source.name + f'.L{first}-L{last}.txt')
        (OUT / cutpath).parent.mkdir(parents=True, exist_ok=True)
        (OUT / cutpath).write_bytes(cut)
        record['cuts'].append(dict(path=str(cutpath), first_line=first, last_line=last,
                                   bytes=len(cut), sha256=sha256(cut).hexdigest(), source_sha256=digest,
                                   span_convention='1-based inclusive; original line endings retained'))
    records.append(record)
(OUT / 'source-index.json').write_text(json.dumps(dict(schema='sources-with-whole-and-literal-cuts',
    captured_at=datetime.now().astimezone().isoformat(), sources=records), indent=2)+'\n')
# Pin already installed original contracts, without inventing a new wrapper.
contracts = []
for relative, name in [
 ('lean/MicroCFTA/SourcePruningEnumerationOrdinaryFallbackResources.lean','fallback_complete_resources'),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteExpansionResources.lean','selected_finite_complete_resources'),
 ('lean/MicroCFTA/SourcePruningEnumerationFiniteHistoryResources.lean','run_finite_complete_resources_with_history'),
]:
    data = (ROOT / relative).read_bytes()
    start = data.index(('theorem '+name).encode())
    finish = data.index(b' := by',start)
    declaration = data[start:finish]
    dest = Path('contracts') / (name+'.declaration.txt')
    (OUT / dest).parent.mkdir(parents=True,exist_ok=True)
    (OUT / dest).write_bytes(declaration)
    contracts.append(dict(source=str(ROOT/relative), source_sha256=sha256(data).hexdigest(),
        theorem=name, path=str(dest), first_byte=start,last_byte_exclusive=finish,
        bytes=len(declaration),sha256=sha256(declaration).hexdigest(),
        status='Literal installed declaration, unchanged. No new producer or contract substitution was made.'))
(OUT/'original-contracts.json').write_text(json.dumps(dict(contracts=contracts),indent=2)+'\n')
print(json.dumps(dict(sources=len(records),whole_copies=sum('whole' in r for r in records),
                     literal_cuts=sum(len(r['cuts']) for r in records),contracts=len(contracts))))
