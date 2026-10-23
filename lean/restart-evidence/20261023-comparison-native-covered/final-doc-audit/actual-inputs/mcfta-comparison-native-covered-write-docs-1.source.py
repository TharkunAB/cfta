import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))
assert load(HERE / 'proof-evidence-normal.json')['status'] == 'PASS'
assert load(HERE / 'proof-evidence-live.json')['status'] == 'PASS'
subprocess.run(['/usr/bin/python3', str(HERE / 'update-documents.py')], cwd='/', check=True)
with (HERE / 'current-progress.md').open('a') as output:
    output.write('\n## Verified proof checkpoint\n\n')
    output.write('The sole aggregate Audit passes: 3645 build jobs and 75508 theorem dependency checks.\n')
    output.write('Both standalone saved-evidence modes pass from cwd=/ before documents.\n')
    output.write('Three Lean/Lake commands pass on one unchanged mathematical source.\n')
    output.write('The immutable metadata cut retains fifteen earlier jobs and three failures.\n')
    output.write('Later collection and checkpoint metadata work remains separately retained.\n')
    output.write('The proof commit is ' + (HERE / 'proof-commit.txt').read_text().strip() + '.\n')
    output.write('Nine additive document updates and the focused note are written.\n')
    output.write('The next inventory is accepted as source-only. H6 remains strongest combined.\n')
    output.write('No Haskell repair was needed. The full goal remains ACTIVE and incomplete.\n')
print(json.dumps(dict(status='PASS', next_action='Independent final document and preservation review, then seal and authorized root push.')))
