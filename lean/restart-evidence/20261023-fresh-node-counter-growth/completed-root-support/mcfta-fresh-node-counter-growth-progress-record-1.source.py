exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import datetime
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof and git('rev-parse', proof + '^').strip() == START
for mode, live in [('normal', False), ('live', True)]:
    result = load(HERE / ('proof-evidence-' + mode + '.json'))
    assert result['status'] == 'PASS' and result['live'] is live
    assert result['actual_jobs'] == 5 and result['new_lean_lake_jobs'] == 0
verified, preserved = [load(HERE / name) for name in ['verification.json', 'preservation-final.json']]
assert verified['status'] == preserved['status'] == 'PASS'
assert verified['audit_build_jobs'] == 3652 and verified['audit_dependencies'] == 75541
assert preserved['baseline_files'] == 113643 and preserved['frozen_entries'] == 1413
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
failures = []
for path in sorted(Path('/tmp').glob('mcfta-fresh-node-counter-growth-*.json')):
    item = load(path)
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item and item['exit_code'] != 0:
        failures.append(path.name)
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
text = f'''
## Actual checked checkpoint before final review and seal

Updated: {stamp}. Proof commit: {proof}.
The SAME117-line selected V4 source passed clean strict3 and sole FULL1.
Strict1 failed with six errors and two warnings. Strict2 exited zero with one warning.
All four bounded variants and three exact source patches remain.
The selected strict3 log is empty. Public declarations use default limits and all linters.
The sole aggregate Audit passed3652 build jobs and75541 dependency checks.
Its sole replay warning belongs to the unchanged older ordinary-completion module.
Root and Required read all three complete checked public TYPEs, thirteen lines each.
Each printed TYPE is byte-identical. Four-ASCII lexical identity is also checked.
All twelve retained slices reconstruct the complete FULL raw output.
BODYs are retained and checked programmatically. No whole BODY manual read is claimed.
Each head uses only Classical.choice, Quot.sound and propext.
The actual ledger retains five proof jobs: four source jobs and one Audit.
It retains one failed source job, one warned exit-zero source job and no rejected TYPE.
The final source history has four variants, three labeled patches and2283 artifacts.
The historical metadata cut has23 jobs and one failed empty-log selection.
That failure is separate from the Lean ledger. All six metadata artifacts remain.
The initial history record omitted three pairs of diff labels. Its exact gate and cut remain.
The metadata repair adds the actual labels and two preserved original artifacts.
It changes no proof job or generic exact-diff guard. Both collectors passed.
The saved verifier has402 lines and212 assertions, within target410 and hard430.
Its528-line bound data uses actual H33 schemas, counts, hashes and complete local inventories.
Completed capped Root failure receipts at this progress cut: {failures}.
Both saved modes passed from cwd / before the exact two-file proof commit and document writes.
All nine additive document inverses and the FINDINGS Haskell repair index FIRST remain.
The first checkpoint replay passed both modes and complete baseline preservation.
Preservation covers113643 files/modes,3650 older Lean sources,298 Haskell files and207 package files.
It checks317 frozen registries,1413 entries and five exact archive overrides.
No Haskell repair was needed. H32 remains pushed and remote-verified at {START}.
This record precedes final independent documentation review, support collection, seal and H33 push.
It claims no result for those later actions. Later Root support is collected separately once.
The three theorems bound the node counter in the SAME repaired constructor outcomes.
They cover arbitrary heaps and environments, including pending, without a success or validity premise.
They derive the binder callback bound. No final counter oracle occurs publicly.
Native/Scan/H23 lifting, fixed-source initial order, global Trace and resources remain separate.
The stored/optional-binder counter proposal is source-only. No next proof result is claimed.
H6 constructed_node_calls remains strongest combined. The whole goal is ACTIVE and incomplete.
'''
path = HERE / 'current-progress.md'
assert '## Actual checked checkpoint before final review and seal' not in path.read_text()
path.write_text(path.read_text() + text)
print('Recorded actual proof, dual-mode, document and preservation results before final review and seal.')
