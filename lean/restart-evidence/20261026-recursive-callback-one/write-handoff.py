from pathlib import Path
import json
root=Path('/home/tritlo/Code/mcfta');area=Path('/tmp/mcfta-recursive-callback-one-20261026')
commits=json.loads((area/'source-commits.json').read_text());ids=[c['commit'] for c in commits]
block=f'''## Main is current and callbacks now execute one recursive expansion

Main `6c080537a` is imported by `843c4f891`.
Exact suspended mass: `{ids[0][:9]}`. Actual callback: `{ids[1][:9]}`.
The goal stays ACTIVE. H6 remains the strongest end-to-end language theorem.

Main adds a memo for template edge copies. Its key retains all varying
arguments. The existing native template tests pass 26 examples, including
14 properties with 100 cases each. The Sized documentation repair is now
merged in PR #178 at `70a8a67dc`. Upstream `aef8ff730` matches local
`af6369a9e` exactly. No external patch remains for that repair.

The actual fragment callback now records its result and executes the real
depth-one recursive driver at one common work bound and every larger fuel.
Its full earlier callback certificate remains available for arbitrary
continuations. The reservation is computed from the current callback-input
cache. Exact stored-slot equality transports it to the returned cache.
No future success, resource bound or callback result is an initial premise.

Distinct pending-slot assimilation preserves total suspended mass, including
duplicates. Incoming replacement adds exactly incoming.length. A completed
subtree retains the same captured sibling cache and metadata at its actual
returned native caller and full memos. General finish retains arbitrary
stopped outputs and nested reasons. Absent endpoints remain absent.

All three new sources and Audit pass strict checks. Aggregate Audit passes
3850 jobs and checks 77474 theorem dependencies. Installed readback covers
11 declarations and 12 full definitions or structures. H6, earlier APIs and
runtime workers remain unchanged. Only the imported Haskell memo changes.
FINDINGS retains all earlier repairs and marks the Sized repair as merged.

Next derive numeric counter and pending-bucket bounds from actual completed
child and edge producers. These bounds must come from the outer captured
cache. Then reserve subtree work before each next sibling. The old edge-only
cost does not pay that work. The complete depth-two scan, general finite
recursive capacity, whole-enumerator language and Haskell correspondence
remain open. Details: `lean/notes-current-pruning-recursive-callback.md`.

'''
findings='''### Main template memo and positive recursive callbacks

Main `6c080537a` is imported. Template.refine now memoizes its pure edge-copy
calculation by wanted parts, unwanted parts, symbol and child shapes. The
projection functions remain fixed in the refine closure. The source retains
the same calculated obligations and their order. Hashing can demand child
shapes earlier and the table retains its keys and results. Arbitrary lazy
forcing and physical memo correspondence remain outside the formal claim.
The existing native suite passes 26 examples and fourteen 100-case properties.
No new Haskell defect is established. No additional patch is proposed.

The formal callback now executes one real recursive expansion under its
original callback-input reservation. Exact cache-mass equations and actual
subtree Post transport support later sibling composition. They do not yet
reserve a full depth-two scan from its initial outer cache.
External Haskell action: all earlier merged repairs remain valid. The Sized
documentation repair is now merged in PR #178. No pending patch remains for
that item. Details: `lean/notes-current-pruning-recursive-callback.md`.

'''
p=root/'FINDINGS.md';s=p.read_text();start=s.index('Main `153e1a211b56dd78bd22f6b427fb78e673041d55` is imported.');end=s.index('The formal gate soundness and exact API equality proofs are separate.',start)
statusBefore=s[start:end]
statusAfter='''Main `6c080537a1a758cd4c4d9b6583c3470024b96850` is imported.
PR #177 adds the bottom-up deterministic shortcut before the product check.
The gate counts every `(symbol, ordered child states)` occurrence globally.
The no-constraint check remains required. Duplicate rows fail the shortcut.
The existing native Sized suite passes: 11 examples and four properties
with 300 cases each. No output defect is found in the shortcut.

The documentation repair is merged in PR #178 at `70a8a67dc`.
Upstream `aef8ff730` is byte-identical to local
`af6369a9e0ecd70acf4da1dffec45c32e6ce7b7b` in both changed files.
It removes the unsupported linear bound for the ordered Data.Set check.
The module comment, helper comment and changelog describe the key set.
All executable Haskell expressions remain unchanged by this repair.
Fourmolu and cabal-gild checks pass inside nix-shell.
External action: no additional patch. Keep the original repair and evidence.
'''
header=f'''# Actual recursive callbacks and current main

Previous published head: bb0b4772b0e2b1b0b26dd64d01e6d1a5686142ce.
Main: 6c080537a1a758cd4c4d9b6583c3470024b96850.
Main integration: 843c4f8910d42ee7ef9a746c8470789807ad87c8.
Exact mass: {ids[0]}.
Concrete callback and subtree effects: {ids[1]}.
The goal stays ACTIVE. Full formalization remains incomplete.

'''
content={'block':block,'findings':findings,'statusBefore':statusBefore,'statusAfter':statusAfter,'noteHeader':header}
(area/'handoff-content.json').write_text(json.dumps(content,indent=2)+'\n')
marker='## The actual recursive driver now has a depth-one resource theorem'
docs=['NEXT-PROMPT.md','HANDOFF.md','FINDINGS.md','lean/README.md','lean/SYSTEM.md','lean/COVERAGE.md','lean/API-COVERAGE.md','lean/notes-current-system-claim.md','lean/notes-proof-status-20261017.md']
for rel in docs:
 p=root/rel;s=p.read_text();assert s.count(marker)==1 and block.splitlines()[0] not in s,rel;p.write_text(s.replace(marker,block+marker,1))
p=root/'FINDINGS.md';s=p.read_text();marker='### The actual depth-one driver retains output packets and resources';assert s.count(marker)==1 and s.count(statusBefore)==1
p.write_text(s.replace(marker,findings+marker,1).replace(statusBefore,statusAfter,1))
print('Updated nine status files and current external Haskell repair status.')

body=(area/'note-body.md').read_text()
content['note']=header+body
(area/'handoff-content.json').write_text(json.dumps(content,indent=2)+'\n')
(root/'lean/notes-current-pruning-recursive-callback.md').write_text(content['note'])
