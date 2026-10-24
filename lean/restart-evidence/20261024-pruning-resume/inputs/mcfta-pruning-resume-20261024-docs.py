import hashlib
import json
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-pruning-resume-20261024')
(root / 'lean/notes-current-pruning-resume.md').write_text('''# Ordered pruning resume observations

Updated: 2026-10-24. Start: `74104221af2bdc2d0ccf454658170dd9a253545a`.
Proof: `6b168d41cc9a5e7c1a7f2eb0db6f0e395edebe32`.
Main: `0db62d26b87e8e55b6c2719f6312ece6f93ed31b`.
Merge: `504523e47a9b85c5dc5f24a396dbf12baf54f290`.

## Checked result

SourcePruningPartialMatch uses the existing Pattern, Term and PartialSymbol
representations. Its branch order follows Pruning.matchPartial. Hole and the
empty AnyPrefix accept every shape before the raw-hole and truncation cases.
Other patterns park on a raw hole leaf with the original ID. Exact patterns
check equal arity. Prefix patterns check sufficient arity and ignore trailing
children. Pending pieces retain child order and repeated entries.
Four branch lemmas expose both wildcard exceptions without extra premises.

SourcePruningResume models Pruning.resume. It reads every parked representative
in input order. It then sequences the pure optional results and concatenates
their pending lists. A rejected match is an Option value inside the state
action. It does not skip later representative reads. A failed bounded read
still fails through the existing action. The part compares the returned root
to the unchanged raw current. It calls the actual imported partial matcher.
There is no matcher callback or canonical-current premise.

resume_frame preserves the complete compression Frame after every successful
resume. The frame retains the allocation counter, stored values, obligations,
both ancestry fields, and every root representative with its stored size.
The parent paths can differ. Left forest totality is an explicit premise.
The frame derives totality for the related input and each intermediate state.

resume_agrees gives exact optional output equality and a complete final frame
for two successful executions on framed inputs. They use the same raw current,
partial term and pending list. Their successful bounds can differ.
resume_transport constructs a finite matching execution in the related input
from one actual successful execution. Right success is not a premise.
The proof constructs each actual intermediate state in source order. It raises
the head and tail actions to the sum of their finite bounds. Their exact
endpoints remain. resume_moreFuel retains the exact result and final state.

## Boundaries and next work

These are observation results. They do not prove that a rejected partial match
has no required completion or that every pruning template is safe. No Safe,
Finished or accepted-completion premise is added. The result includes successful
actions whose optional result is none. It does not equate bounded error rows,
callback traces or whole result streams. The Haskell source comparison is
reviewed correspondence, not verified extraction or a native runtime proof.

The next target is the actual templateOracle callback. Compose its partial
render, ordered resume traversal and ordered new-match production. Then cover
typedTypes and its unexpanded-node reads. Preserve template and program order,
raw IDs, duplicate entries and actual intermediate states. The separate
selected-current protection invariant still needs its cached-driver composition.
Complete canonical mutation histories and the cached-driver bridge remain open.

H6 SourceCurrentColdFiniteWarmCalls.constructed_node_calls remains the strongest
combined theorem. Covered closed construction and a valid allocation history
supply finite repeated node calls at a sufficient mathematical width and fuel,
with exact finite-tree language preservation under the formal guards.
It excludes withoutRedundantEdges and does not prove convergence. Full-pipeline
composition, complete resources, practical widths, Haskell and solver refinement,
phase-4 correctness and general convergence remain open. H23 is still queued.
The full formalization goal is active and incomplete.

## Upstream and validation

PR #169 is integrated. Read notes-current-upstream-lpo.md. Both recorded LPO
failure mechanisms have source repairs and focused native validation. General
order and pruning proofs remain separate. FINDINGS keeps the external repair
index first and records the merged status. All older reports remain historical.
No additional Haskell source patch or committed test is introduced locally.

Pinned Lean 4.34.1 checked both final sources with warnings as errors and all
linters. The resume passed its first strict check. The matcher needed only two
escaped prefix proof-case names. The executable definition did not change.
The original failed attempt, author preflight draft and exact patches remain.
The installed aggregate Audit passed: 3673 jobs and 75792 dependency checks.
It replayed one older unused-variable warning in
InternedFreshOrdinaryClosedCompletion.lean:24. No new-source warning occurs.
All 11 public signatures and eight axiom reports were read in full. Their
axioms are limited to propext and Quot.sound. No project axiom or proof-limit
override is added. Independent source and public reviews are retained.

Evidence is in restart-evidence/20261024-pruning-resume. It retains the original
baseline, exact upstream changes, checks, failed harness attempts, cap receipts,
source reviews, public output and the preceding checkpoint publication receipts.
The verifier checks exact preservation of every baseline file. It permits only
the recorded upstream changes, document updates and one Audit import.
This record precedes the evidence commit and authorized push to formalize.
''')
(root / 'lean/notes-current-upstream-lpo.md').write_text('''# Main LPO repairs integrated

Updated: 2026-10-24. Main: `0db62d26b87e8e55b6c2719f6312ece6f93ed31b`.
Merge: `504523e47a9b85c5dc5f24a396dbf12baf54f290`.
Base: `74104221af2bdc2d0ccf454658170dd9a253545a`.
Backup: `codex/backup-lpo-main-20261024-0248`.

PR #169 changes only Specftacular.Rewriting and its README. Every other
baseline file and the new untracked matcher were preserved at the merge.
The 127096-file baseline check found 127094 unchanged files and the two exact
upstream replacements. Earlier proofs, drafts, counterexamples, repairs and
the optimized interned core remain. No local Haskell patch is added.

## Repair behavior

Commit 70a252537 uses erased program equality in the LPO subterm and equal-prefix
comparisons. The retained typed annotation-cycle witness now gives [GT, LT, LT],
both before and after canonicalTypes. A focused public-API probe checked every
comparison pair and every transitivity triple on those three terms and their
canonicalized forms. This finite check does not prove the general order laws.

Commit f484c0ca0 retains the uncurried path order. Its recorded function-context
reversal remains: f a > a and (f a) x < a x. The repair changes its consumers.
rewriteStep carries the actual application context through function positions.
It tests the instantiated rewrite in that context. addEquation requires an
additional appliedGreater check before one-way orientation. Both the principal
and specialized pruning-template branches require the same check.

The public addLawRules/reducible/pruningTemplates probe uses the retained valid
f a = a equation. The local f a is reducible. The enclosing (f a) x is not
reducible by that increasing change. The reverse a x is reducible to its
smaller application. No pruning template is produced for the unsafe direction.
The check therefore tests the changed rewrite and pruning behavior, rather
than require the underlying comparator reversal to disappear.

Commit 3ea886098 corrects the README schedule count. It lists eight separately
seeded cases, 40 boundary/list cases and 16 predicate/list cases: 64 extras.
The implementation schedule is unchanged. Finite testing does not prove laws.

## Verification and remaining obligations

The Specftacular goldens passed inside nix-shell with strict GHC warnings.
They include the existing LPO and KBO cases in checked and unchecked modes.
These cases use phase 1 and do not establish phase-4 pruning correctness.
Fourmolu passed for the changed Haskell path. Cabal-gild passed for the active
Specftacular Cabal file. No Cabal source changed. The unrelated CFTA suite was
not rerun for this two-file repair.

Both native probes compiled with -Wall -Werror and passed. The first probe
harness attempt did not expose cfta. The second exposed two text packages and
failed on ambiguity. The successful attempt hid unrelated packages and used
the exact package IDs from the current Cabal plan. All attempts and raw logs
remain in the evidence. These harness failures are not product failures.

General transitivity and well-foundedness on the intended typed term domain,
substitution stability, argument-context compatibility and the appliedGreater
criterion remain formal proof obligations. The criterion must also justify
longer spines and its synthetic variable names. No new native defect is claimed.
Template production, compiled pruning and partial-match pruning soundness need
separate proofs. The matching and observer theorems concern supplied templates.
They do not prove the safety of this producer.

FINDINGS marks both recorded LPO repairs as merged in PR #169. External work
needs no additional patch for the retained witnesses. Keep those witnesses and
the general proof obligations. H6 remains strongest combined. The full goal is
active and incomplete. Read notes-current-pruning-resume.md for the next target.
''')
prefix = '''
## Ordered pruning resume and main LPO repairs

Updated: 2026-10-24. Proof: `6b168d41cc9a5e7c1a7f2eb0db6f0e395edebe32`.
Main: `0db62d26b`. Merge: `504523e47a`. Start: `74104221af`.
Read `lean/notes-current-pruning-resume.md` and `lean/notes-current-upstream-lpo.md`.

The actual partial matcher and ordered Pruning.resume are now modeled.
Successful resumes preserve the complete compression frame. Framed inputs give
exactly equal ordered optional results at independent successful bounds.
One actual success constructs a finite matching run in the related input.
All representative reads precede pure Option sequencing, including after none.
Raw current and hole IDs, pending order and duplicates remain explicit.
No canonical-current, Safe, completion or desired right-success premise is added.

Both final sources passed strict Lean checks. Audit passed: 3673 jobs and
75792 dependency checks, one older warning and no new-source warning.
All 11 public signatures and eight axiom reports were read in full.
PR #169 repairs both recorded LPO failure mechanisms. Goldens, formatting and
focused public-API repair probes passed. The application comparator reversal
remains; contextual rewriting and template admissibility prevent its unsafe use.
FINDINGS keeps the external repair index FIRST and marks both repairs merged.
General order laws and pruning soundness remain unproved. No local Haskell patch.

Next, compose actual templateOracle behavior and typedTypes observations.
Complete canonical mutation histories and the cached-driver bridge remain open.
H6 remains strongest combined. H23 remains queued. Full-pipeline, resource,
practical-width, Haskell/solver, phase-4 and convergence gaps remain.
The full goal is ACTIVE and incomplete. This record precedes the authorized push.

'''
names = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
         'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
         'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
changes = {}
for name in names:
    path = root / name
    before = path.read_text()
    assert '## Ordered pruning resume and main LPO repairs' not in before
    position = before.index('\n## Partial rendering:') if name == 'FINDINGS.md' else before.index('\n') + 1
    after = before[:position] + prefix + before[position:]
    path.write_text(after)
    changes[name] = dict(insertion_character=position, inserted=prefix,
                         before_sha256=hashlib.sha256(before.encode()).hexdigest(),
                         after_insertion_sha256=hashlib.sha256(after.encode()).hexdigest())
path = root / 'FINDINGS.md'
text = path.read_text()
replacements = [
('The negative type-depth repair is merged in PR #168 at `a5fbb66eec`.\nUpstream `75cfc19b8` has the same source as local `058b11fe8f`.\nTwo optional LPO repairs remain open. Native counterexamples are retained below.',
 'The negative type-depth repair is merged in PR #168 at `a5fbb66eec`.\nUpstream `75cfc19b8` has the same source as local `058b11fe8f`.\nBoth recorded LPO repairs are merged in PR #169 at `0db62d26b`.\nFocused native repair probes pass. Historical counterexamples remain below.'),
('| Optional LPO comparator transitivity | OPEN. Native well-typed terms give `s < t < u < s`, also after canonicalTypes. | Repair annotation handling and the order fallback. See the retained comparator regression. |',
 '| Optional LPO comparator transitivity | Fixed by `70a252537`, merged in PR #169 at `0db62d26b`. The recorded typed cycle is gone, also after canonicalTypes. | No additional patch for this witness. Keep the general order-law proof obligation. |'),
('| Optional LPO application context | OPEN. Native terms give `f a > a` and `(f a) x < a x`. | Establish an order compatible with function application and actual rewriting. The annotation repair alone is insufficient. |',
 '| Optional LPO application context | Fixed by `f484c0ca0`, merged in PR #169 at `0db62d26b`. The comparator reversal remains; contextual rewriting and template gates prevent its unsafe use. | No additional patch for this witness. Keep general context, substitution and pruning proof obligations. |'),
('All three completed repairs are in the imported main history. The\ntype-depth fix and both open LPO repairs are recorded in the current note.\nAll earlier repair entries and evidence remain below.',
 'All five listed repairs are in the imported main history. The current notes\nrecord the type-depth and LPO validation. General proofs remain separate.\nAll earlier repair entries and evidence remain below.')]
for old,new in replacements:
    assert text.count(old) == 1
    text = text.replace(old,new,1)
path.write_text(text)
(area / 'findings-index-repair.json').write_text(json.dumps(replacements,indent=2)+'\n')
for name in names:
    changes[name]['after_sha256'] = hashlib.sha256((root/name).read_bytes()).hexdigest()
(area / 'document-changes.json').write_text(json.dumps(changes,indent=2)+'\n')
print(json.dumps(dict(documents=names,prefix_lines=len(prefix.splitlines()),findings_replacements=len(replacements))))
