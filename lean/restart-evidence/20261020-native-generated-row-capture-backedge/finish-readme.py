import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
counts = json.loads((HERE / 'attempt-accounting.json').read_text())
assert json.loads((HERE / 'selection-status.json').read_text())['finalized']
items = json.loads((HERE / 'compressed-evidence.json').read_text())
path = HERE / 'README.md'
text = path.read_text()
start = text.index('## Current checkpoint state\n')
end = text.index('## Checked public proof\n')
text = text[:start] + '''## Current checkpoint state

The proof and Audit import are published at
57fe78e0e5f0d127f8ee350a6a485b8e2636e594 on formalize.
This evidence checkpoint retains one new public proof pair and one
constructed proof pair. Selected strict logs are empty. The complete
readbacks use all eight required printer options and standard axioms.
The root independently checks the frozen concrete source.

The actual example reaches the outer optional site at step 60.
Its optional operation creates a new used full Mu. Its same returned
capture selects variable slot two and original pool slot one. The same
full initial cell retains its same-row original node RowCall. All generic
stored-row and conditional unfold clauses remain. The example does not
run an unfold.

The complete goal stays active. These component results do not prove
global native termination or production Haskell refinement.

''' + text[end:]
old = '''The actual fixture and its independent review will be retained here
after their final source and readback pass. Receipt copies add no commands.
All actual Lean and Lake commands must enter attempt-accounting.json.
'''
new = f'''capture-fixture retains the final 1407-line concrete proof, all source
variants, all attempts and the complete selected readback. fixture-review
retains the source-pinned independent review. That review runs no Lean
command and adds no pair. The root selected strict check uses the same
source SHA256 1f3d2f37c7ab4de22dc9c6ad81230fdf27a98015e86b5cfd0b90ec79387e0d76.

There are {counts['capped_commands']} actual capped Lean and Lake commands, including
{counts['failed_commands']} commands with nonzero exit status. Diagnostic goals that
deliberately remain open, reduction-depth failures and capped memory
failures remain. They establish no native execution counterexample.
One zero-exit public printer is incomplete and rejected. Older successful
source checks remain unselected. Receipt copies add no commands.
'''
assert old in text
text = text.replace(old, new, 1)
text = text.replace('The current map restores three raw paths from two deterministic gzip\narchives.',
    f"The current map restores {len(items)} raw paths from {len({item['archive'] for item in items})} deterministic gzip\narchives.", 1)
start = text.index('## Finalization still required\n')
end = text.index('The starting checkpoint is ', start)
text = text[:start] + '''## Verification and publication

Run verify-checkpoint.py under a capped worker to check the retained
proofs, source pins, complete printers, process limits and attempt counts.
It restores the exact large logs first. Run verify-preservation.py to
check the declared changes and all retained baseline files and registries.
Run finalize.py to retain those results and write the physical checksums.

Use stage-checkpoint.py to stage the exact sealed physical paths. Commit
and push formalize without force. Then run verify-closure.py under a
capped worker. It checks every tracked filesystem, index and HEAD blob
and mode, all evidence checksums, selected proofs, preservation and clean
state. Its --remote-file option checks the exact formalize and main
remote identities. Publication receipts stay outside this sealed folder.
Keep the goal active after publication.

''' + text[end:]
path.write_text(text)
print(json.dumps({'status': 'PASS', 'capped_commands': counts['capped_commands'],
                  'failed_commands': counts['failed_commands']}))
