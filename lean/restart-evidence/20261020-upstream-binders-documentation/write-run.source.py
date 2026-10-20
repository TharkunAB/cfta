from pathlib import Path
import datetime
import json
from zoneinfo import ZoneInfo

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
stamp = datetime.datetime.now(ZoneInfo('Europe/Stockholm')).strftime('%Y-%m-%d %H:%M %Z')
merge = json.loads((HERE / 'merge.json').read_text())
block = f'''## Current upstream documentation integration

Updated: {stamp}. Merge checkpoint: `{merge['head'][:9]}`.
Main `794903b3f` and PR #97 are now imported into formalize.
The latest proof checkpoint remains `0b533a718`.
Read `lean/notes-current-upstream-binders-documentation.md`, then
`lean/notes-current-native-original-union-descent.md` for the proof.

The imported Typing.hs, README and CHANGELOG patch qualifies Binders
size ordering by a subterm rule. It advises upToSize for finite acyclic
languages. The Haskell code outside Haddock comments is unchanged.
No fresh Haskell runtime validation is claimed. FINDINGS records the
merged repair first and preserves the earlier unvalidated local example.

Every Lean source and prior evidence file retains its bytes. The latest
strict, full-printer and default Audit results remain valid for those
same sources: 3536 jobs and 74283 theorem dependency checks. No Lean build
is repeated for the imported comments. The preservation check reruns
the existing selected-proof evidence verifier.

The next proof must derive one rooted actual build trace with common
publication indices. Earlier selected writers must occur at smaller
indices within that same trace. This source chronology remains unproved.
It is separate from global native renewal and active-owner exclusion,
final retention, outer completion, convergence and Haskell refinement.
The full goal stays active. Pushes to formalize remain authorized.

'''
names = ['NEXT-PROMPT.md', 'HANDOFF.md', 'lean/README.md', 'lean/SYSTEM.md',
         'lean/API-COVERAGE.md', 'lean/COVERAGE.md', 'lean/notes-proof-status-20261017.md',
         'lean/notes-current-system-claim.md']
for name in names:
    path = ROOT / name
    text = path.read_text()
    if name == 'NEXT-PROMPT.md':
        prefix = 'Continue the cfta formalization in /home/tritlo/Code/mcfta.\n\n'
        assert text.startswith(prefix)
        text = prefix + block + text[len(prefix):]
    else:
        first, rest = text.split('\n', 1)
        text = first + '\n\n' + block + rest.lstrip('\n')
    path.write_text(text)
finding = f'''External Haskell documentation repair imported: {stamp}.
PR #97 merged commit7469183231da3a9c7aefc115c9cc818f4867bd9d into
main794903b3fbad3becb8b28736fc33463760731fc7. Formalize now imports
that main at merge{merge['head']}. The exact upstream Typing.hs,
README and CHANGELOG bytes are retained. Only Haddock comments change
in the Haskell module. Code outside those comments is unchanged.
This closes the documentation follow-up below. The earlier failed local
runtime reproduction remains historical and unvalidated. No fresh
runtime result or production runtime defect is claimed.
Every Lean source, proof, draft, counterexample and prior evidence file
retains its bytes. Latest proof remains0b533a718. Current native outer
completion and production Haskell refinement remain open.
Read `lean/notes-current-upstream-binders-documentation.md`.
Preserve the complete earlier repair registry and validation evidence.

'''
(HERE / 'findings-update.md').write_text(finding)
path = ROOT / 'FINDINGS.md'
text = path.read_text()
prefix = '# Current formalization findings\n\n## Haskell fix handoff for external work\n\n'
assert text.startswith(prefix)
path.write_text(prefix + finding + text[len(prefix):])
note = '# Upstream Binders documentation repair and proof preservation\n\n' + block + '''## Source and proof scope

The import is main794903b3fbad3becb8b28736fc33463760731fc7, which merges
documentation commit7469183231da3a9c7aefc115c9cc818f4867bd9d through PR #97.
Only cfta-generator/README.md, CHANGELOG.md and the Haddock comments in
src/Data/CFTA/Gen/Typing.hs change. The source baseline from the previous
proof was main9769fe3e921d63836a0be337f19edd3c601f076e.

The previous publication succeeded while upstream main advanced. Its two
fixed-ref closure failures and final source-baseline closure are preserved
here with their raw logs, scripts, usage, limits and receipts. The final
closure verified all 45220 tracked blobs and modes, all evidence, the
exact published formalize ref and the new main ref. It explicitly left
this import pending. This integration now completes that pending step.

The integration adds no theorem or constructed example. All existing
Lean files, selected strict/full readbacks, counterexamples, repairs and
marked drafts retain their bytes. The existing proof evidence is checked
again without rebuilding unchanged Lean sources. The imported Haskell
module must match upstream exactly and must preserve code outside its
Haddock blocks. This check does not establish Haskell runtime refinement.

## Full target and next work

For every public operation, valid supported initial inputs must imply
that execution terminates and satisfies its intended specification.
Support cannot assume a future successful result. Construction,
transformations, reduction, size classes, counts, ranks, enumeration,
generation, probability, external interfaces and the optimized interned
core remain in scope. The older constructor and equality work remains.

The latest local proof gives one observed source writer, correlated
union descent to the same terminal and actual node or selected binder
receipts. The warm source example forces that returned binder branch.
Those source facts are not a global native runtime rank.

Read the unproved shared-trace plan in the previous proof evidence:
lean/restart-evidence/20261020-native-original-union-descent/next-publication-plan/plan.md.
Derive one actual rooted build path and its postorder publication list.
Retain final selected writers and earlier precompletion writers with
their positions in that same list. Independent existential writers do
not establish this order. Reservation identities do not order completion.

General generated-capture original ancestry, preceding native histories,
residual Mu observations, ordinary continuations, global renewal and
active-owner exclusion, final owner retention, outer termination,
convergence and production Haskell refinement remain open. The full
goal stays active. Declaration counts do not measure completion.
'''
new_name = 'lean/notes-current-upstream-binders-documentation.md'
(ROOT / new_name).write_text(note)
(HERE / 'current-documents.json').write_text(json.dumps(names + ['FINDINGS.md', new_name], indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'documents': 10, 'merge': merge['head']}))
