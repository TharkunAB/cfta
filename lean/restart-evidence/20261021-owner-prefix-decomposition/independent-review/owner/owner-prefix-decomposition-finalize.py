#!/usr/bin/env python3
"""Freeze selected proof evidence. This command does not run Lean."""
from __future__ import annotations
import hashlib
import json
import re
import runpy
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/tritlo/Code/mcfta')
PREFIX = 'owner-prefix-decomposition-'
SOURCE = 'SourceCurrentOuterOwnerPrefix.lean'
HEAD = 'MicroCFTA.SourceCurrentOuterOwnerPrefix.first_child'

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write(name: str, value: object) -> None:
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

source = HERE / SOURCE
assert sha(source) == 'e790cbbaab2d2dd73a45738d950f45463102c2a7048f8bd59b5a95d6f3e965c6'
proposal = (HERE / 'inputs/plan/proposed-signature.lean.txt').read_text()
assert source.read_text().split('theorem first_child\n', 1)[1].split(' := by', 1)[0] == proposal.split('theorem first_child\n', 1)[1].split('\nend MicroCFTA.', 1)[0]
strict, public = PREFIX + 'direct-3', PREFIX + 'public-1'
assert not (HERE / (strict + '.log')).read_bytes()
readback = runpy.run_path(str(HERE / (PREFIX + 'readback.py')))['check'](source, HERE / (public + '.source.lean'), HERE / (public + '.log'))
write(PREFIX + 'readback.json', readback)
write('final-type-comparison.json', dict(source_sha256=sha(source), source_lines=203, public_header_byte_exact_frozen_proposal=True, proposal_elaborated_before_draft=False, public_checked_printed_type_identical=True))
attempts=[]
for stem in [PREFIX + 'direct-1', PREFIX + 'direct-2', strict, public]:
    receipt=json.loads((HERE / (stem + '.json')).read_text())
    usage=json.loads((HERE / (stem + '.usage.json')).read_text())
    log=(HERE / (stem + '.log')).read_text()
    attempts.append(dict(name=stem, owner='required_memos', kind='lean', lean_launched=True,
      exit_code=receipt['exit_code'], receipt_sha256=sha(HERE / (stem + '.json')),
      source_sha256=receipt['sha256'], log_sha256=sha(HERE / (stem + '.log')),
      warning_diagnostics=len(re.findall(r'\bwarning(?:\([^)]*\))?:',log)),
      error_diagnostics=len(re.findall(r': error',log)), usage_remaining_percent=usage['remaining_percent']))
write(PREFIX + 'attempt-ledger.json', dict(attempts=attempts, infrastructure_attempts=[], actual_lean_jobs=4, failed_checks=2, copies_add_lean_jobs=0, canonical_jobs=0))
selection=dict(finalized=True, source=SOURCE, source_sha256=sha(source), source_lines=203,
 public_heads=[HEAD], selected_strict=strict, selected_public=public, lean_jobs=4, failed_checks=2,
 warning_checks=0, infrastructure_attempts=0, canonical_jobs=0, new_public_pairs=1, constructed_pairs=0,
 public_header_byte_exact_frozen_proposal=True, proposal_elaborated_before_draft=False,
 public_log_bytes=readback['public_log_bytes'], public_log_sha256=readback['public_log_sha256'],
 axioms_by_head=readback['axioms_by_head'], official_edits_by_author=False, prelaunch_proof_commands=0,
 source_repairs='Bind private graph parameters before review; replace three eliminated constructor names and qualify nodeEdges after strict1; inline same prefix proof in expected tuple after strict2. No public header or premise change.')
write(PREFIX + 'selection.json', selection)
sources=json.loads((HERE / 'inputs/plan/source-pins.json').read_text())['sources']
for item in sources:
    item['snapshot']='inputs/plan/' + item['snapshot']
    assert sha(HERE / item['snapshot']) == sha(ROOT / item['path']) == item['sha256']
for path, spans in [('lean/MicroCFTA/InternedEdgeResidency.lean', [(10,19)]), ('lean/MicroCFTA/' + SOURCE, [(1,203)])]:
    actual = ROOT / path
    if path.endswith('/' + SOURCE):
        assert actual.read_bytes() == source.read_bytes(), 'Wait for exact root installation before finalization.'
    snapshot = HERE / 'inputs/root' / path
    snapshot.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(actual,snapshot)
    lines = snapshot.read_bytes().splitlines(keepends=True)
    sources.append(dict(path=path,snapshot=str(snapshot.relative_to(HERE)),bytes=snapshot.stat().st_size,sha256=sha(snapshot),lines=len(lines),
      reviewed_ranges=[dict(start=lo,end=hi,sha256=hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()) for lo,hi in spans]))
write(PREFIX + 'source-pins.json', dict(sources=sources))
files=[]
for path in sorted(HERE.rglob('*')):
    if path.is_file() and path.name != PREFIX + 'manifest.json' and '__pycache__' not in path.parts:
        files.append(dict(path=str(path.relative_to(HERE)),bytes=path.stat().st_size,sha256=sha(path)))
write(PREFIX + 'manifest.json', dict(finalized=True, files=files, sources=sources, lean_jobs=4, failed_checks=2, canonical_jobs=0, infrastructure_attempts=0, new_public_pairs=1, constructed_pairs=0))
print(json.dumps(dict(status='FROZEN',local_pins=len(files),root_pins=len(sources),manifest_sha256=sha(HERE / (PREFIX + 'manifest.json')),selection_sha256=sha(HERE / (PREFIX + 'selection.json'))),indent=2))
