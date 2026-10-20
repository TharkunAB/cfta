from pathlib import Path
import json,hashlib,shutil
h=Path('/tmp/mcfta-native-compiled-terminal-generation-fixture');r=Path('/home/tritlo/Code/mcfta');old=Path('/tmp/mcfta-native-compiled-mu-generation-fixture')
def write(name,obj):(h/name).write_text(json.dumps(obj,indent=2)+'\n')
write('terminal-mu-kernels-selection.json',dict(finalized=True,public_heads=['MicroCFTA.CompiledTerminalMuGenerationFixture.actual_terminal_generation'],strict='terminal-mu-kernels-direct-1',groups=[dict(name='terminal-mu-kernels-public-1',pairs=1,kind='constructed',full_proof=True)],attempts=['terminal-mu-kernels-direct-1','terminal-mu-kernels-public-1'],lean_jobs=2,failed_attempts=0,production_pairs=0,constructed_pairs=1,canonical=None,canonical_jobs=0,source_sha256='0f0a1fb6db623a7e1716245829a0beef42d0303c08e28386cf93f272c667aff5',prior_fixture_sha256='5c04290afac1d2339752010a8364db8689b1e22433390999110246b74af27b32'))
(h/'terminal-mu-kernels-review.md').write_text('''# Actual new Mu with the same terminal child writer

This is a separate strengthened fixture. The earlier compiled-Mu package remains unchanged. The concrete source, allocation, execution, selected result, and physical admission helpers are byte-identical to that fixture after the namespace/import prefix. Both source operands are closed used Mu values. Each has `rec[self]` and its own distinct nullary row. Actual `execute 64` returns a new full used Mu. Its selected record is absent initially and present finally. The returned body's free names contain its own interned binder.

The actual Top-field allocation and completed closed source build derive `Good`. Empty native tables derive `History.initial`. The same actual completed run derives a raw trace. Existing source-resource admission derives its physical checks. The fixture supplies no desired owner, writer, generation, or internal History premise.

The fixture calls `TerminalGeneration.execute` once. It does not call the older generation producer. The initial absence excludes the prior-cell arm. The same returned tuple keeps the actual generating optional site, used intersection placeholder, maybeMu call, source build, rooted writer, and fully expanded owner/child/terminal origin. The terminal facts are inside that same existential. They include the actual entered-child Route, exact terminal returned cell and strong writer, non-swap and non-reset decisions, both key-codec witnesses, and a terminal handle distinct from the evaluating owner's handle. All these facts concern the returned optional site. The fixture does not replace its site or terminal with a separately chosen witness.

The public theorem is an alias of its checked private witness. Both have exactly the same complete type. The source keeps the full raw owner-child-terminal tuple in that type. It does not hide that tuple behind the Origin predicate.

This is a physical generation and terminal-writer example. It does not prove universal site uniqueness, original-root syntax ancestry, productivity or finite acceptance, arbitrary later owner retention, outer completion, or Haskell refinement. It does not identify every existential field with a chosen literal constant. No native evaluation axiom is used.

Selected strict `terminal-mu-kernels-direct-1` is terminal 0 with a literal-empty raw log. Selected public `terminal-mu-kernels-public-1` is terminal 0 with one complete full-proof pair, all eight settings, standard three axioms, and no warnings or omissions. There are two owned Lean commands, no failures, and no canonical job. Both commands used pinned Lean 4.34.1 under effective 4 GiB max/high, zero swap, and a five-minute cap, with fresh usage receipts. The mutable peaks file is excluded. A dedicated final two-row peaks snapshot is pinned. The portable verifier performs no Lean jobs.
''')
shutil.copyfile(h/'terminal-mu-kernels-peaks.txt',h/'terminal-mu-kernels-peaks-final.txt')
(h/'inputs').mkdir(exist_ok=True)
sources=json.loads((old/'compiled-mu-kernels-source-pins.json').read_text())['sources']
paths=[s['path'] for s in sources if not s['path'].endswith('/SourceCurrentNativeOriginGeneration.lean')]
paths+=['lean/MicroCFTA/SourceCurrentNativeTerminalGeneration.lean','lean/MicroCFTA/SourceCurrentNativeOptionalTerminalOrigin.lean','lean/MicroCFTA/SourceCurrentNativeActiveQueryForwarding.lean','lean/MicroCFTA/SourceCurrentNativeQueryRowOrigins.lean']
pins=[]
for path in paths:
 d=(r/path).read_bytes();snapshot='inputs/'+Path(path).name;(h/snapshot).write_bytes(d)
 pins.append(dict(path=path,snapshot=snapshot,bytes=len(d),sha256=hashlib.sha256(d).hexdigest()))
(h/'inputs/prior-compiled-mu-kernels.lean').write_bytes((old/'compiled-mu-kernels.lean').read_bytes())
write('terminal-mu-kernels-source-pins.json',dict(sources=pins))
