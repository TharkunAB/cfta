exec(compile(open('/tmp/mcfta-pair-inventory-rebase-root-common.py').read(), '/tmp/mcfta-pair-inventory-rebase-root-common.py', 'exec'))
import datetime
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof and git('rev-parse', proof + '^').strip() == START
for mode, live in [('normal', False), ('live', True)]:
    result = load(HERE / ('proof-evidence-' + mode + '.json'))
    assert result['status'] == 'PASS' and result['live'] is live
    assert result['actual_jobs'] == 3 and result['new_lean_lake_jobs'] == 0
verified, preserved = [load(HERE / name) for name in ['verification.json', 'preservation-final.json']]
assert verified['status'] == preserved['status'] == 'PASS'
assert verified['audit_build_jobs'] == 3651 and verified['audit_dependencies'] == 75528
assert preserved['baseline_files'] == 112408 and preserved['frozen_entries'] == 1412
assert preserved['unchanged_haskell_files'] == 298 and preserved['unchanged_package_files'] == 207
assert (HERE / 'current-update.md').is_file()
failures = []
for path in sorted(Path('/tmp').glob('mcfta-pair-inventory-rebase-*.json')):
    item = load(path)
    if isinstance(item, dict) and 'wrapper' in item and 'exit_code' in item and item['exit_code'] != 0:
        failures.append(path.name)
stamp = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
text = f'''
## Actual checked checkpoint before final review and seal

Updated: {stamp}. Proof commit: {proof}.
The SAME77-line source passed strict1, sole FULL1 and sole audit1 without a source repair.
The strict log is empty. The aggregate Audit passed3651 jobs and75528 dependency checks.
The sole replay warning belongs to the unchanged older ordinary-completion module.
Root and Required read the complete652-line checked public TYPE.
The printed TYPE is byte-identical. All four slices reconstruct the entire FULL log.
The BODY is retained and checked programmatically. No whole BODY manual read is claimed.
The actual axioms are Classical.choice, Quot.sound and propext.
The ledger retains3 proof jobs,1 source variant,504 artifacts and the14/0 metadata cut.
Later completed Root support is collected separately once before the seal.
The saved verifier source has384 lines. Two required binder guards exceed its382-line soft target.
The400-line hard cap remains. Root accepted the deviation before independent final source review.
Separate author and reviewer static diagnostics are retained. They changed no Lean source or compiler result.
Completed capped Root failure receipts at this progress cut: {failures}.
Both saved modes passed from cwd / before the exact two-file proof commit and document writes.
The writer retained all nine old-text LF inverses and the FINDINGS Haskell repair index FIRST.
The first checkpoint replay passed both modes and complete baseline preservation.
Preservation covers112408 files/modes,3649 older Lean sources,298 Haskell files and207 package files.
It checks316 frozen registries,1412 entries and five exact archive overrides.
No Haskell repair was needed. H31 remains pushed and remote-verified at {START}.
This record precedes final independent documentation review, support collection, seal and H32 push.
It claims no result for those later actions.
The theorem retains native At, pair Stable, canonical captured admission and exact old ranks
in the computed inventory at the SAME full Wrapper. Its Agreement is derived.
It produces no new execution, Room, WordRanges, original global allocation Trace or strict domain growth.
The next counter/resource assessment is source-only. No next proof result is claimed.
H6 constructed_node_calls remains strongest combined. The whole goal is ACTIVE and incomplete.
'''
path = HERE / 'current-progress.md'
assert '## Actual checked checkpoint before final review and seal' not in path.read_text()
path.write_text(path.read_text() + text)
print('Recorded actual proof, dual-mode, document and preservation results before final review and seal.')
