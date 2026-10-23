import runpy
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

for label, live in [('normal', False), ('live', True)]:
    report = load(HERE / ('proof-evidence-' + label + '.json'))
    assert report['status'] == 'PASS' and report['live'] is live
assert load(HERE / 'root-next-inventory-review.json')['status'] == 'ROOT_SOURCE_ONLY_NEXT_ROUTE_CLEAR'
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof
subprocess.run(['/usr/bin/python3', str(HERE / 'update-documents.py')], check=True)
target = HERE / 'NEXT-TARGET.md'
assert not target.exists()
target.write_text('''# Current proof and next target

The whole formalization goal remains ACTIVE. This component makes PROGRESS.
H27 completed_hit_checked reads the SAME observed completed H7 hit call.
Initial Stable and a published original or reversed key remain premises.
The exact supplied fuel, result and full after stay fixed.
The conclusion is after.checked = before.checked. The pair memo can change.
The proof derives reverse-only order from canonical presence and original absence.
It does not identify captured payloads or choose another completion.
Strict1 has an empty log. The sole FULL1 and Audit1 pass with default limits.
The public TYPE has102 logical lines and7032 bytes. Both reviewers read it all.
Checked and printed TYPE bytes match. BODY evidence remains programmatic only.
Actual axioms are Classical.choice, Quot.sound and propext.
Audit has3644 jobs and75507 dependencies. Only the old inputs warning remains.
There are three actual Lean/Lake jobs and no failed or warned source job.
Both147-line proposal drafts and the exact two-name precompiler patch remain.
No compiler repair or Haskell source change was needed.
FINDINGS keeps its external Haskell repair index first.
H6 constructed_node_calls remains the strongest combined semantic theorem.

Next append native Covered to one H15 original_rows_complete result.
Read next-inventory, next-inventory-audit and root-next-inventory-review.json.
These files supply a reviewed source-only route. They authorize no declaration.
Keep one source, holds, FiniteInput and its exact finite model and ranks.
Require genuine admission of both actual closed original parents and incoming Covered.
Keep arbitrary initialDomains, its Cache.Valid proof, the populated Wrapper,
the SAME global domain allocation Trace and one genuine initial Room at fixed width.
Call H15 once. Preserve the exact fuel/result/full after/done and all12 outputs.
On hits, use H27 on that SAME done and transport Covered by checked equality.
On BOTH misses, public H7 miss_readback gives raw native Steps of that SAME done.
H18 and public residency/readiness APIs derive exact request scope and admission.
Derive Resources and Current from the actual initial global packet.
Public edge_body, Fields and prefixes supply the physical Trace at the same endpoints.
Trace.covered and derived public branch certificates then give final native Covered.
Raw Steps alone do not supply a physical Trace or contextual Receipt.
Only this emptyDomain request has no binding obligations. The source can have others.
Do not choose a second H15/H26 result or project a hidden contextual receipt.
The180 to215-line estimate and proposed230-line stop need a fresh exact
declaration, local-type, import and whole-source budget gate before any body.
The route proposes no new global helper or induction.

H25 can later add captured-pair Requests and canonical returned-cell admission
to that SAME result. Genuine old returned-cell admission remains a premise.
Native Covered does not supply that pair-memo premise.
H20/H22 hide internal pair runs. Do not project those runs or import a local IH.
Generated-root admission, source/model/rank agreement, new Room and WordRanges,
literal Mu/full pass, practical width, solver and Haskell correspondence,
and convergence remain open. No whole-implementation claim is supported.

The user authorizes pushes to origin/formalize. The local publisher has no
network command. Root push follows seal and local checkpoint verification.
Keep all older proofs, counterexamples, drafts, repairs and optimized code.
Do not post to the board, send messages, update memory or create an ADR.
''')
print(json.dumps(dict(status='PASS', proof=proof, documents=9, focused_note=1,
    next_target='Same-H15-result native Covered', whole_goal_complete=False)))
