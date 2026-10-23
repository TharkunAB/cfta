exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
import datetime
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof and git('rev-parse', proof + '^').strip() == START
for mode, live in [('normal', False), ('live', True)]:
    result = load(HERE / ('proof-evidence-' + mode + '.json'))
    assert result['status'] == 'PASS' and result['live'] is live
    assert result['actual_jobs'] == 3 and result['new_lean_lake_jobs'] == 0
verified, preserved = [load(HERE / name) for name in ['verification.json', 'preservation-final.json']]
assert verified['status'] == preserved['status'] == 'PASS'
assert verified['audit_build_jobs'] == 3653 and verified['audit_dependencies'] == 75553
assert preserved['baseline_files'] == 116844 and preserved['frozen_entries'] == 1414
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
text = f'''
## Actual checked checkpoint before final review and seal

Updated: {stamp}. Proof commit: {proof}.
The same82-line V1 source passed strict1 and the sole FULL1 without changes.
The strict log is empty. Default declaration limits and all linters apply.
The sole aggregate Audit passed3653 build jobs and75553 dependency checks.
Its only replay warning belongs to the unchanged older ordinary-completion module.
Root and Required read all37 complete public TYPE lines:13,12,12.
Raw TYPE byte identity and four-ASCII lexical identity are checked separately.
The12 retained slices reconstruct all63534 raw FULL bytes.
BODY retention is programmatic. No whole BODY manual read is claimed.
Each actual axiom set is Classical.choice, Quot.sound and propext.
The actual ledger has3 proof jobs,2 source jobs,1 Audit and zero failures,
warned source jobs or rejected public TYPE jobs.
The source history retains1 variant,0 patches and856 artifacts.
The historical metadata cut retains13 jobs and zero failures.
The early canonical copy remains as an exact metadata draft.
It changed no proof source or guard and caused no repeated proof job.
The saved verifier has404 lines and212 assertions, with483 lines of actual bound data.
Both saved modes passed from cwd / before the exact two-file proof commit and documents.
All nine additive LF inverses and the FINDINGS Haskell repair index FIRST remain.
The first checkpoint replay passed both modes and complete baseline preservation.
Preservation covers116844 files/modes,3651 older Lean sources,298 Haskell files and207 package files.
It checks318 frozen registries,1414 entries and five archive overrides.
No Haskell repair was needed. H33 remains pushed and remote-verified at {START}.
This record precedes final independent documentation review, support collection, seal and H34 push.
It claims no outcome for those later actions. Later Root support is collected separately once.
The three theorems bound nodes.next in the SAME execute, unfold and maybeMu outcomes.
They cover pending outcomes and arbitrary heaps without validity, success or counter oracles.
Native/Scan/H23 lifting, fixed-source initial order, global Trace and resources remain separate.
The next native-counter investigation is read-only. No next theorem is claimed.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
'''
path = HERE / 'current-progress.md'
assert '## Actual checked checkpoint before final review and seal' not in path.read_text()
path.write_text(path.read_text() + text)
print('Recorded actual proof, dual-mode, document and preservation results before final review and seal.')
