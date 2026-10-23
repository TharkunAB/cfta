exec(compile(open('/tmp/mcfta-demand-node-counter-growth-root-common.py').read(), '/tmp/mcfta-demand-node-counter-growth-root-common.py', 'exec'))
import datetime

proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof and git('rev-parse', proof + '^').strip() == START
for mode in ['normal', 'live']:
    assert load(HERE / ('proof-evidence-' + mode + '.json'))['status'] == 'PASS'
cut = load(HERE / 'actual-proof-cut.json')
assert cut['metadata_jobs'] == 13 and cut['failed_metadata_jobs'] == 0
source = HERE / 'verify-proofs.py'
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
append = f'''
## Checked demand counter proof

Updated: {now}. Proof commit: {proof}.
The same 80-line source passed its first strict and sole FULL checks.
All three complete public TYPEs were read by Root and an independent reviewer.
Each checked TYPE has 33 logical lines, 32 LF bytes and no final LF byte.
All three actual raw byte identity flags are true.
All pairs have four-ASCII-whitespace lexical identity. Both raw hashes remain.
All 12 slices reconstruct the complete 696507-byte FULL output.
Complete printed BODY retention was checked programmatically.
No whole printed BODY manual read is claimed.
The sole aggregate Audit passed with 3655 jobs and 75560 dependency checks.
Only the older unused-input warning was replayed.
The proof ledger has three jobs, two source jobs and one Audit job.
It has no failed proof job, warned source job or rejected public TYPE.
The immutable historical metadata cut has 13 jobs and no failure.
Later closing receipts remain separate and must enter final support once.
The reviewed saved verifier has {len(source.read_bytes().splitlines())} lines.
It retains all 174 generic basis expressions.
A source review rejected one byte-regex identifier guard in the first preparation.
The corrected guard requires the exact reviewed external command line.
Both preparations and the rejection evidence remain.
No selected verifier was executed before this correction.
Both standalone saved modes passed from cwd / before the exact proof commit.
No Haskell repair is required. FINDINGS keeps its repair index first.
Next, lift the bound through pair/Scan/H23 and prove fixed-source initial counter order.
Global domain-history transport and resource upper bounds remain separate.
H6 constructed_node_calls remains strongest combined.
The goal remains ACTIVE and incomplete. Final seal and push are pending.
'''
journal = HERE / 'current-progress.md'
assert '## Checked demand counter proof' not in journal.read_text()
journal.write_text(journal.read_text() + append)
print('Recorded the actual checked-demand proof checkpoint. Final seal and push remain pending.')
