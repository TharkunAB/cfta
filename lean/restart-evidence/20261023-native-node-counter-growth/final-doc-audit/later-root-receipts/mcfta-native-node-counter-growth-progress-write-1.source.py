exec(compile(open('/tmp/mcfta-native-node-counter-growth-root-common.py').read(), '/tmp/mcfta-native-node-counter-growth-root-common.py', 'exec'))
import datetime
proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof
assert git('rev-parse', proof + '^').strip() == START
for mode in ['normal', 'live']:
    assert load(HERE / ('proof-evidence-' + mode + '.json'))['status'] == 'PASS'
failed = Path('/tmp/mcfta-native-node-counter-growth-install-closing-publication-1')
corrected = Path('/tmp/mcfta-native-node-counter-growth-install-closing-publication-2')
assert load(Path(str(failed) + '.json'))['exit_code'] == 1
assert load(Path(str(corrected) + '.json'))['exit_code'] == 0
before = Path(str(failed) + '.source.py').read_bytes()
after = Path(str(corrected) + '.source.py').read_bytes()
old, new = b"owner / 'basis/verify-seal.py'", b"owner / 'pending-preparation/basis/verify-seal.py'"
assert before.count(old) == 1 and before.replace(old, new, 1) == after
save('closing-install-correction.json', dict(status='EXACT_ARCHIVED_BASIS_PATH_CORRECTION_ONLY',
    historical_metadata_cut_unchanged=True, post_cut_failed_attempt=failed.name,
    corrected_attempt=corrected.name, failed_source_sha256=sha(Path(str(failed) + '.source.py')),
    corrected_source_sha256=sha(Path(str(corrected) + '.source.py')),
    failed_before_any_closing_archive_or_install=True, same_verify_seal_byte_identity_guard=True,
    no_mathematical_source_change=True, no_Lean_or_Lake_job_repeated=True,
    both_complete_six_file_attempts_retained_in_final_support=True))
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
append = f'''
## Checked native counter proof

Updated: {now}. Proof commit: {proof}.
The same 79-line source passed its first strict and sole FULL checks.
All three complete public TYPEs were read by Root and an independent reviewer.
Checked TYPE lengths are 17, 17 and 18 lines.
Actual raw byte identity flags are true, false and false.
All pairs have four-ASCII-whitespace lexical identity. Both raw hashes remain.
All 12 slices reconstruct the complete 214732-byte FULL output.
Complete printed BODY retention was checked programmatically.
No whole printed BODY manual read is claimed.
The sole aggregate Audit passed with 3654 jobs and 75556 dependency checks.
Only the older unused-input warning was replayed.
The proof ledger has three jobs, two source jobs and one Audit job.
It has no failed proof job, warned source job or rejected public TYPE.
The immutable historical metadata cut has 13 jobs and no failure.
One later closing installation failed on an incorrect archived basis path.
It stopped before any closing archive or installation.
The corrected attempt passed with the same byte-identity guard.
Both complete attempt receipts and source snapshots remain for final support.
No mathematical source changed. No Lean or Lake job was repeated.
The reviewed saved verifier has 418 lines and 221 assertions.
It retains all 174 generic basis expressions.
Both standalone saved modes passed from cwd / before the exact proof commit.
No Haskell repair is required. FINDINGS keeps its repair index first.
Next, lift the bound through Scan/H23 and prove fixed-source initial counter order.
Global domain-history transport and resource upper bounds remain separate.
H6 constructed_node_calls remains strongest combined.
The goal remains ACTIVE and incomplete. Final seal and push are pending.
'''
journal = HERE / 'current-progress.md'
assert '## Checked native counter proof' not in journal.read_text()
journal.write_text(journal.read_text() + append)
print('Recorded the actual proof checkpoint and exact post-cut metadata correction.')
