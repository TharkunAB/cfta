import datetime
import hashlib
import json
import re
import sys
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
here = root / 'lean/restart-evidence/20261022-prepend-grouping'
package = here / 'source-proposal-v2'
review = here / 'source-audit-v2/review.md'
assert hashlib.sha256(review.read_bytes()).hexdigest() == sys.argv[1]
assert json.loads((here / 'root-declaration-review.json').read_text())['mathematical_body_authorized']
pins = json.loads((package / 'pins.json').read_text())
assert len(pins) == 96
for name, pin in pins.items():
    raw = (package / name).read_bytes()
    assert len(raw) == pin['bytes'] and hashlib.sha256(raw).hexdigest() == pin['sha256']
source = (package / 'SourceCurrentPrependGrouping.lean').read_bytes()
assert hashlib.sha256(source).hexdigest() == 'e902b0688085906c13d7150f11e55b1ae181cecadba32a2f9584149c717c089a'
assert len(source.splitlines()) == 85 <= 240
before = (here / 'source-proposal/SourceCurrentPrependGrouping.lean').read_bytes()
assert source.count(b'cases table rowKey <;> simp') == 1
assert source.replace(b'cases table rowKey <;> simp', b'cases table query <;> simp', 1) == before
context = (here / 'signature-plan/context.lean.txt').read_bytes()
declarations = (here / 'signature-plan/declarations.lean.txt').read_bytes()
assert source.startswith(context)
markers = list(re.finditer(rb'(?m)^/--[^\n]*-/\n(def|theorem) ([^\s(\[{:=]+)', declarations))
order = [('insertWith','def'),('fromRows','def'),('reverseTable','def'),('pair_fold','theorem'),
    ('reverse_insert_singleton','theorem'),('reverse_fold','theorem'),('reverse_fromRows','theorem'),
    ('iteration_reverse','theorem'),('iteration_permutation','theorem')]
assert [(m.group(2).decode(),m.group(1).decode()) for m in markers] == order
positions = []
inverse = context
for i, marker in enumerate(markers):
    end = markers[i+1].start() if i+1 < len(markers) else declarations.rindex(b'\nend MicroCFTA.')
    header = declarations[marker.start():end].rstrip(b'\n')
    compiled = header + (b' :=\n' if order[i][1] == 'def' else b' := by\n')
    assert source.count(compiled) == 1
    positions.append(source.index(compiled))
    inverse += header + b'\n\n'
inverse += b'end MicroCFTA.SourceCurrentPrependGrouping\n'
assert inverse == declarations and positions == sorted(positions)
assert b'  fun query => if query = entry.1 then some (entry.2 ++ (table query).getD []) else table query\n' in source
assert b'  rows.foldl (fun table row => insertWith table (key row, [row])) (fun _ => none)\n' in source
assert b'  fun query => (table query).map List.reverse\n' in source
assert source.count(b'induction rows generalizing table with') == 1
assert not re.search(rb'\b(sorry|axiom|opaque|unsafe|partial|private|set_option)\b', source)
assert not re.search(rb'(?m)^\s*(have|let)\s', source)
assert source.rstrip().endswith(b'end MicroCFTA.SourceCurrentPrependGrouping')
assert not (root / 'lean/MicroCFTA/SourceCurrentPrependGrouping.lean').exists()
record = dict(status='ROOT_WHOLE_SOURCE_REVIEW_CLEAR',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source='source-proposal-v2/SourceCurrentPrependGrouping.lean',source_sha256=hashlib.sha256(source).hexdigest(),
    source_lines=85,root_read_all_source_lines=True,independent_review='source-audit-v2/review.md',
    independent_review_sha256=sys.argv[1],pins_verified=96,exact_headers_and_definition_equations=True,
    deletion_inverse_exact=True,default_declaration_limits=True,private_helpers=[],
    first_root_strict_check_authorized=True,full_check_authorized=False,
    official_installation_authorized=False,whole_goal_complete=False)
target = here / 'root-source-review.json'
assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(status='PASS',source_lines=85,pins=96,strict_authorized=True)))
