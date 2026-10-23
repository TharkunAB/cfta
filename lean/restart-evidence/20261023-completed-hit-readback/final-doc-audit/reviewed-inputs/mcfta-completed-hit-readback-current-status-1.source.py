import datetime
import runpy
globals().update(runpy.run_path('/tmp/mcfta-completed-hit-readback-root-common.py'))

proof = (HERE / 'proof-commit.txt').read_text().strip()
assert git('rev-parse', 'HEAD').strip() == proof == '7d9b7e8c93d1da48f97c6f94c45a84ad377f2856'
assert load(HERE / 'verification.json')['status'] == 'PASS'
preserved = load(HERE / 'preservation-final.json')
assert preserved['status'] == 'PASS' and preserved['baseline_files'] == 104210
for label, live in [('normal', False), ('live', True)]:
    report = load(HERE / ('proof-evidence-' + label + '.json'))
    assert report['status'] == 'PASS' and report['live'] is live
assert (ROOT / 'lean/notes-current-completed-hit-readback.md').exists()
assert (HERE / 'NEXT-TARGET.md').exists()
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Current measured checkpoint status\n\nMeasured: ' + now + '.\n')
    output.write('The earlier pending lists describe their historical cuts.\nProof commit `' + proof + '` is complete.\n')
    output.write('All nine tools are installed. Normal and live saved proofs passed before document writes.\nThe nine document prefixes, focused note and NEXT-TARGET are written.\nClosing checkpoint verification and baseline preservation pass.\nAll104210 baseline files/modes,3642 older non-Audit Lean sources,298 Haskell files\nand207 active package files pass preservation. FINDINGS keeps the repair index FIRST.\nThe next source-only H15 route and emptyDomain-only clarification are archived.\nFinal independent document approval, seal, local evidence commit and authorized push remain pending.\nThe whole formalization goal remains ACTIVE.\n')
print(json.dumps(dict(status='PASS', proof=proof, checkpoint_and_preservation='PASS',
    documents_written=True, seal_or_publication_claimed=False, whole_goal_complete=False)))
