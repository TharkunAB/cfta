import runpy
globals().update(runpy.run_path('/tmp/mcfta-cluster-admission-root-common.py'))
owner = Path('/tmp/mcfta-cluster-admission-execution-plan')
assert not owner.exists()
owner.mkdir()
fragments = {
'context.lean.txt': '''import MicroCFTA.SourceCurrentOriginalRowClusterScan

namespace MicroCFTA.SourceCurrentOriginalRowClusterExecution
open InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "Control" => SourceCurrentOriginalRowClusterScan.Control
local notation "execute" => SourceCurrentOriginalRowClusterScan.execute
local notation "step" => SourceCurrentOriginalRowClusterScan.step
variable {width : Nat}
''',
'yielded-header.lean.txt': '''theorem yielded_add
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (used rest : Nat) (control next : Control) (before middle : Wrapper width)
    (observed : execute used control before = .yielded next middle) :
    execute (used + rest) control before = execute rest next middle
''',
'yielded-same.lean.txt': '''      have same : control = next ∧ before = middle
''',
'yielded-case.lean.txt': '''      cases one : step control before <;>
''',
'done-header.lean.txt': '''theorem done_stable
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel extra : Nat) (control : Control) (before after : Wrapper width)
    (kept : List Edge) (observed : execute fuel control before = .done kept after) :
    execute (fuel + extra) control before = .done kept after
''',
'done-case.lean.txt': '''      cases one : step control before <;>
''',
'unique-header.lean.txt': '''theorem completed_unique
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (firstFuel secondFuel : Nat) (control : Control)
    (before firstAfter secondAfter : Wrapper width) (firstRows secondRows : List Edge)
    (first : execute firstFuel control before = .done firstRows firstAfter)
    (second : execute secondFuel control before = .done secondRows secondAfter) :
    firstRows = secondRows ∧ firstAfter = secondAfter
''',
'unique-first.lean.txt': '''  have firstStable : execute (firstFuel + secondFuel) control before = .done firstRows firstAfter
''',
'unique-second.lean.txt': '''  have secondStable : execute (secondFuel + firstFuel) control before = .done secondRows secondAfter
''',
}
for filename, text in fragments.items():
    (owner / filename).write_text(text)
schema = dict(status='DECLARATIONS_ONLY_PENDING_ROOT_AND_INDEPENDENT_REVIEW', module=NAME,
    public_heads=['yielded_add', 'done_stable', 'completed_unique'], private_helpers=[],
    global_definitions=[], typed_haves=['same', 'firstStable', 'secondStable'],
    local_lets=[], local_obtains=[], local_by_cases=[], typed_show_fragments=[],
    case_equation_names_by_theorem={'yielded_add':['one'], 'done_stable':['one'], 'completed_unique':[]},
    induction=[dict(theorem='yielded_add', variable='used', generalizing=['control','before'],
        exact_IH='∀ (control : Control) (before : Wrapper width), execute used control before = .yielded next middle → execute (used + rest) control before = execute rest next middle'),
        dict(theorem='done_stable', variable='fuel', generalizing=['control','before'],
        exact_IH='∀ (control : Control) (before : Wrapper width), execute fuel control before = .done kept after → execute (fuel + extra) control before = .done kept after')],
    branch_binders_by_theorem={
        'yielded_add': {'following':'Control','after':'Wrapper width'},
        'done_stable': {'following':'Control','middle':'Wrapper width'}},
    source_estimate=[75,100], whole_source_hard_stop=130,
    default_declaration_limits=True, all_linters=True,
    mathematical_bodies_present=False, compiler_authorized=False,
    scope='The actual Scan interpreter at one control, full initial Wrapper and fixed instances. Full returned list and state equality. No semantic, admission, resource or completion existence premise is supplied.')
(owner / 'declaration-schema.json').write_text(json.dumps(schema, indent=2) + '\n')
contracts = {name: dict(lines=len(text.splitlines()), sha256=sha(owner / name)) for name,text in fragments.items()}
(owner / 'contracts.json').write_text(json.dumps(contracts, indent=2) + '\n')
sources = {
    'Scan': ('lean/MicroCFTA/SourceCurrentOriginalRowClusterScan.lean', [(19,39),(41,79),(82,120)]),
    'Language': ('lean/MicroCFTA/SourceCurrentOriginalRowClusterLanguage.lean', [(20,40)]),
    'NativePattern': ('lean/MicroCFTA/SourceCurrentAllocatedNativeColdClosedExact.lean', [(24,36)]),
    'NativeStable': ('lean/MicroCFTA/SourceEqualityNativeDemand.lean', [])}
(owner / 'cuts').mkdir()
index = []
for label,(relative,ranges) in sources.items():
    path = ROOT / relative
    assert path.is_file()
    data = path.read_bytes()
    entry = dict(id=label, source=relative, bytes=len(data), lines=len(data.splitlines()), sha256=sha(path), cuts=[])
    for start,end in ranges:
        name = f'cuts/{label}-{start}-{end}.lean.txt'
        cut = b''.join(data.splitlines(keepends=True)[start-1:end])
        (owner / name).write_bytes(cut)
        entry['cuts'].append(dict(path=name,start=start,end=end,sha256=sha(owner / name)))
    index.append(entry)
(owner / 'source-index.json').write_text(json.dumps(index, indent=2) + '\n')
(owner / 'note.md').write_text('''# Actual cluster execution declarations

These declarations form a prerequisite for cluster admission conservation.
They use the literal Scan.execute and full Wrapper. They supply no new run.
The yielded prefix law copies the public shape of the older private helper.
Done stability and full completed equality follow the existing native proof pattern.
They do not assume cross-fuel uniqueness. The future proof must derive it.
Every public header, typed local, named equation and induction contract is listed.
There is no private helper, callback, extra predicate, proof body or compiler result.
The expected whole source is 75 to 100 lines. The proposed hard stop is 130.
Root and independent declaration review must precede every body and compiler job.
The overall cluster/group/rebuild target remains open after these declarations.
''')
pins = [dict(path=str(path.relative_to(owner)), bytes=path.stat().st_size, sha256=sha(path)) for path in sorted(owner.rglob('*')) if path.is_file()]
(owner / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
(owner / 'FROZEN.json').write_text(json.dumps(dict(status='FROZEN_DECLARATIONS_ONLY', pins_sha256=sha(owner / 'pins.json')), indent=2) + '\n')
print(json.dumps(dict(status='DECLARATIONS_ONLY', module=NAME, public_heads=3, source_cap_proposed=130,
    pins_sha256=sha(owner / 'pins.json'), frozen_sha256=sha(owner / 'FROZEN.json'))))
