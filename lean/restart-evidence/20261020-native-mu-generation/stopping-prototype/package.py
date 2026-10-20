from pathlib import Path
import hashlib, json, shutil

root=Path('/home/tritlo/Code/mcfta')
here=Path(__file__).resolve().parent
inputs=here/'inputs'
inputs.mkdir()
names=[
 'SourceCurrentCompletedBuildRootedWriters',
 'SourceCurrentNativeMuIssuedHistory',
 'SourceCurrentNativeMuIssuedWriters',
 'SourceCurrentNativeMuPublication',
 'SourceCurrentNativeMuPublicationCallbacks',
 'SourceCurrentNativeMuGrowthHistory',
 'SourceCurrentConstrainedCapSourceHistory',
 'InternedFreshOrdinaryConstruction',
 'InternedFreshOrdinaryFacts',
 'InternedFreshOrdinaryActiveOrigins',
 'InternedFreshOrdinarySourceHistory',
 'InternedFreshProbeKeys',
 'InternedConstructionProvenance',
 'InternedShallowHeap',
 'InternedStoredMuOrigins',
 'InternedNestedConstruction',
 'InternedNestedRequestFacts',
 'InternedConstructorTemplates',
 'InternedProbeProvenance',
]
def pin(path):
 b=path.read_bytes()
 return dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
sources=[]
for name in names:
 rel='lean/MicroCFTA/'+name+'.lean'
 snapshot='inputs/'+name+'.lean'
 shutil.copyfile(root/rel,here/snapshot)
 sources.append(dict(path=rel,snapshot=snapshot,**pin(root/rel)))
shutil.copyfile(root/'lean/lean-toolchain',inputs/'lean-toolchain')
sources.append(dict(path='lean/lean-toolchain',snapshot='inputs/lean-toolchain',**pin(root/'lean/lean-toolchain')))
(here/'stopping-rooted-source-pins.json').write_text(json.dumps(dict(schema=1,ROOT='repository root',HERE='package directory',sources=sources),indent=2)+'\n')
shutil.copyfile(here/'stopping-rooted-peaks.txt',here/'stopping-rooted-peaks-final.txt')
selection=dict(finalized=True,source='SourceCurrentStoppingBuildRootedWriters.lean',
 strict='stopping-rooted-direct-1',canonical=None,
 groups=[dict(name='stopping-rooted-public-1',pairs=1,full_proof=True,kind='prototype-public')],
 public_heads=['MicroCFTA.SourceCurrentStoppingBuildRootedWriters.build_writer_or_prior'],
 lean_jobs=2,failed_attempts=0,constructed_pairs=0,canonical_jobs=0)
(here/'stopping-rooted-selection.json').write_text(json.dumps(selection,indent=2)+'\n')
(here/'stopping-rooted-review.md').write_text('''# Stopping-build rooted writers

Reviewed and checked on 2026-10-20 at 17:48 CEST.

## Result

`SourceCurrentStoppingBuildRootedWriters.build_writer_or_prior` selects an arbitrary complete Mu cell at `(build root initial before).state`. It assumes the actual rich `Context before initial`. It has no completed-build equation. It returns the exact same full cell at `before`, or the existing `CompletedBuildRootedWriters.Written root initial before stoppingState key fullMu` receipt.

The theorem applies to both constructors of `Outcome`. It does not prove source completion. It does not infer that a native operation invoked this source build.

## Proof review

This is an author review. It is not an independent mathematical review.

The new private support proof follows the existing completed-build proof. It retains a rooted annotation on the same actual issued path. It handles pending callback, source-list, and source-row states before selecting a writer. The selection proof traverses this correlated path once. It returns the same publication, rooted `Reached` receipt, first-write fact, callback issued intervals, and physical and issued suffixes. It does not identify two independent publication witnesses.

The copied private span from `private def Rooted` through `writers` is byte-identical to the old source. The new namespace gives it new private declarations. The implementation references no generated private name. It imports the old public `Written` type. No previous source file changes.

`build_supported` handles all source syntax constructors. Source bind stops at a pending state. Completed prefixes carry actual forward growth into later source routes. A pending body after reservation retains all completed inner publications. Reservation changes no full Mu record. Ordinary node, union, edge and self-filter work uses the existing `NoNewMu` facts.

The public proof takes the path at the actual `Outcome.state` directly. It does not rewrite that state with a successful result equation.

## Checks

Two Lean jobs ran. Both used Lean 4.34.1, all linters, memory.max and memory.high 4294967296, memory.swap.max 0, and a five-minute cap. Usage was fresh and above one percent before each job.

`stopping-rooted-direct-1` returned zero with a zero-byte log. `stopping-rooted-public-1` returned zero. It printed the one public declaration with all eight required options, full proof, and axiom report. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The full log has 7102 bytes. No warning, omitted term, failed print, or admitted proof occurs.

There are no failed attempts, constructed proof pairs, or canonical build jobs in this prototype package. The parent owns official promotion and canonical checks.

## Remaining boundary

A native generator must still locate the actual source-build owner and entry state. In particular, this theorem does not derive a `compileMu` body-query receipt from arbitrary native memo history. It preserves the initial full-cell alternative. It does not derive original-root ancestry for native encoded captures or claim a strict source rank for earlier writers.

## Preservation

All work is under this temporary package. The prior interface audit remains separate and unchanged. The mutable peaks file is excluded. The manifest pins its final two-row snapshot instead. Foundation snapshots permit standalone verification. `--live-root` also compares those snapshots with the live repository. Receipt command strings retain their original temporary paths.
''')
print('prepared',len(sources),'foundation snapshots')
