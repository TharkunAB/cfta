import datetime
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
start = (HERE / 'starting-head.txt').read_text().strip()
proof = (HERE / 'proof-commit-pair.txt').read_text().strip()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
update = f'''## Current same-child pairs from finite positive paths

Updated: {now}. Proof checkpoint: `{proof[:10]}`.
Start: `{start[:10]}`. Imported main remains `794903b3f`.
Read `lean/notes-current-positive-owner-pair.md`.

The pure same_child_pair theorem now derives one fixed equality class with
two distinct suffixes through the chosen child. It consumes positive
ancestry from a literal ordinary owner to one SAME member row's child
forest. The row has a nonplain guard. No common anchor, finite enumeration,
choice map or count bound is supplied by the caller.

A private exact list deduplicates PositiveAt PATHS across rows and unions.
The nonplain row gives its positive root. Every source child path lifts
through that SAME row to a nonempty positive owner path. If every class
dropped at the chosen child, child_separate would make the total ancestry
relation injective into the same finite path set with its root removed.
The checked finite-relation cardinality theorem gives a contradiction.
Structural mass bounds only private enumeration. It is not a runtime rank.

Root strict is empty. Complete FULL1, independent review and default Audit
pass: 3586 jobs and 74877 dependencies. The sole head uses the standard
three axioms. Five actual Lean/Lake commands include one retained unknown-
tactic failure. Two explicit contradiction introductions fix that failure.
Copies add no jobs. Only the old ClosedCompletion Audit warning remains.
Counts do not measure completion. All older sources, registries, evidence,
Haskell/package files, stashes, other worktrees and main remain.
All sealed raw logs must be indexed.

This is a geometry CONSUMER. Actual execution must supply its ancestry,
SAME source row and normalized class-family Covers. Historical writer/Scan
native stores and causal History remain missing execution producers.
The next plan isolates native store preservation for actual uncapped
Scan queries. Their PRIMARY gate can be true while SECONDARY is false.
Later kept primary-false gates do not cap those query inputs. Conditional
cache laws can remain valid without a result cap or unrestricted OR law.
A small public interface to the existing conditional induction is planned.
It remains unproved. Unfinished cuts, actual owner exclusion, renewal,
retention, outer completion, convergence and Haskell refinement remain open.

Keep the Haskell repair index FIRST in FINDINGS. Insert proof updates AFTER it.
No new Haskell source, runtime result or external repair. All earlier repair
entries remain. The full goal is active. Regular formalize pushes are authorized.
'''
findings = f'''Current proof update: {now}. Proof checkpoint: `{proof[:10]}`.
Pure finite positive-path geometry now derives a SAME-child pair in one
fixed class from total backwards ancestry into a SAME nonplain owner's
member-row child forest. Paths are deduplicated across rows and unions.
The positive root is omitted by every lifted nonempty source path.
child_separate supplies collision injectivity; finite relation cardinality
gives the contradiction. No common anchor or caller enumeration is assumed.
This consumes ancestry. It does not derive historical execution laws.
Root strict, complete FULL1, independent review and Audit pass:
3586 jobs and 74877 dependencies. The public head uses standard3.
Five actual Lean/Lake commands include one retained unavailable-tactic
failure. Two explicit Classical contradiction introductions preserve scope.
Copies add no jobs. No Haskell source or runtime result changes.
Next is native store preservation for actual Scan queries that may lack
finite caps. Their conditional cache laws differ from a result OR claim.
Actual source/family Covers and historical writer/Scan laws, unfinished
cuts, owner exclusion, renewal, retention, outer completion, convergence
and Haskell refinement remain open. Goal active.
Read `lean/notes-current-positive-owner-pair.md`. Repair index stays FIRST.
'''
note = f'''# Same-child pairs from finite positive paths

Updated: {now}. Selected proof: `{proof}`.
SourceCurrentPositiveOwnerPair has 124 lines and one public same_child_pair.

The theorem is a pure geometry consumer. It takes an actual congruence
fixed-point class family, a literal ordinary owner, one member row with a
nonplain guard, a chosen child index, and total positive ancestry to that
SAME row's literal child forest. It concludes that one class contains two
different path suffixes through the chosen child index.

For every PositiveAt owner q, the ancestry premise must give an exact child
lookup row.children[j]?, a positive source suffix p in that child, and
Rel classes (index::q) (j::p). This is the shape produced by the checked
original-forest ancestry adapter once its actual row and class family are
connected. This module does not claim to derive that execution premise.
It adds no caller-supplied enumeration, choice map, common anchor or bound.

The private candidates function recurses on fuel. Ordinary nodes enumerate
actual raw rows and zipIdx child positions. Child paths gain their SAME
natural index. Union alternatives contribute their paths without an extra
component. Candidates may include extra roots. A private Classical filter
retains exactly PositiveAt paths. eraseDups removes duplicate paths across
rows, repeated children and union alternatives. Mu bodies and references
stay opaque because PositiveAt has no constructor for them.

Completeness inducts on PositiveAt. The existing node_child_lt and
union_member_lt bounds justify the smaller fuel in each real recursive
case. Final fuel is literal structural mass plus one. Filtering gives
soundness. Deduplication gives Nodup. This is a finite list of paths,
not row occurrences, derivations, observational paths or runtime work.
The structural mass is only an internal enumeration bound.

The nonplain member row gives PositiveAt owner [] and therefore a root in
the exact list. Every ancestry witness lifts j::p through that SAME row
and exact child lookup to PositiveAt owner (j::p). Its target is nonempty.
Assume no same-child pair exists in the fixed family. This yields precisely
the dropped premise of NormalizedChildSeparation.child_separate. At a
collision target, that theorem equates the two source suffixes. Thus the
ancestry relation is injective from all positive owner paths into the same
finite list with its positive root erased.

SymbolicDriver.relation_cardinality_le gives the impossible length bound.
Its fallback [] need not be in the target list. Root membership proves an
actual one-element length decrease. The contradiction returns one actual
class, both actual member paths, and different suffixes. A common source
is used only locally to check a collision. It is not assumed as an input.
A nullary selected row needs no special premise: ancestry already fails at
the positive root. Overlapping paths across raw rows do not affect counts.

Root reviewed all 122 draft lines and the complete final delta. The first
strict failed at an unavailable by_contra tactic. The final source replaces
both uses with Classical.byContradiction and intro. Enumeration and the
public type are unchanged. Final SHA256 is
0bcad2715a1170cac3c7bf99423b716916c068a3a859e092d70258c368b40f39.
Selected and root strict logs are literally empty. Complete FULL1 has
49749 bytes, all eight printer settings, complete public type and proof,
no omissions or private public type names, and standard3 only:
propext, Classical.choice and Quot.sound. Independent review found no
material issue and authored none of the direct foundations.
All portable ordinary/live verifiers pass.

Two owner strict checks, one owner FULL1, one root strict and one default
Audit are five actual Lean/Lake commands. One strict attempt failed.
Copies add no jobs. There are no constructed consumers or extra canonical
builds. Audit passes with 3586 jobs and 74877 theorem dependencies.
Only the old ClosedCompletion unused-input warning remains. Each actual
command retains its source, raw log, receipt, fresh usage observation and
verified 4 GiB memory/high limits, zero swap and five-minute cap.

The next archived plan concerns conditional native store preservation.
Actual Scan invokes seeded queries when PRIMARY is true and SECONDARY is
false. The later kept records' primary-false gates do not cover those
queries. A constrained closed Mu endpoint can pass those actual gates
without a finite Plain cap. The existing capped query observer therefore
cannot supply the needed Scan store transition at every query.

The existing private completed native induction retains conditional node
and edge stores without requiring caps on the CURRENT outer query. Its
public call asks caps when it specializes the conditional result law.
A narrow public store interface and a current-heap adapter are planned.
They must retain actual causal History, unchanged captured cell identity,
and old-source Origins before rebasing. They must not assert a finite
result cap or an unrestricted positive OR theorem for an uncapped query.
The opaque-Mu counterexample remains valid. This interface is still
unproved, and this checkpoint changes no older proof source.

An actual owner-exclusion consumer must also derive the nonplain selected
row and use whole-component Covers to lift the selected relation into the
SAME actual normalized fixed family. Normalization can merge classes;
individual path membership or literal selected-family inclusion is not
sufficient. DelayedCombinedOwnerProgress then needs the actual prefix,
later growth and indexed descent receipts at that combined payload.

The warm historical Parent ledger still lacks Current/native positive
Support/causal History at its same writer and Scan return. Current reader
laws do not imply these past laws. Arbitrary internal failed prefixes,
actual owner exclusion, renewal, rank progress, final retention, outer
completion, convergence and Haskell refinement remain open.
No Haskell source, runtime result or external repair changes.
FINDINGS keeps its external repair index first. All older evidence remains.
'''
documents = ['NEXT-PROMPT.md', 'HANDOFF.md', 'FINDINGS.md', 'lean/README.md',
             'lean/SYSTEM.md', 'lean/API-COVERAGE.md', 'lean/COVERAGE.md',
             'lean/notes-proof-status-20261017.md', 'lean/notes-current-system-claim.md']
for name in documents:
    original = subprocess.check_output(['git', 'show', start + ':' + name], cwd=ROOT, text=True)
    assert (ROOT / name).read_text() == original, name
    if name == 'FINDINGS.md':
        prefix = '# Current formalization findings\n\n## Haskell fix handoff for external work\n'
        marker = prefix + '\n' + (HERE / 'haskell-repair-index.md').read_text().rstrip() + '\n'
        assert original.startswith(marker)
        rest = original[len(marker):]
        assert rest.startswith('\n')
        changed = marker + '\n' + findings + '\n' + rest[1:]
        assert changed.replace(findings + '\n', '', 1) == original
    else:
        first, rest = original.split('\n', 1)
        changed = first + '\n\n' + update + rest
        assert changed.replace(update + '\n', '', 1) == original
    (ROOT / name).write_text(changed)
(HERE / 'current-update.md').write_text(update)
(HERE / 'findings-update.md').write_text(findings)
(ROOT / 'lean/notes-current-positive-owner-pair.md').write_text(note)
print('Updated nine documents and focused note. All prior text remains.')
