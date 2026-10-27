from pathlib import Path
import json
import subprocess

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-native-history-proper-20261027')


def git(*args):
    return subprocess.check_output(['git', *args], cwd=root, stderr=subprocess.STDOUT)


assert git('branch', '--show-current').decode().strip() == 'formalize'
assert git('rev-parse', 'HEAD').decode().strip() == (area / 'integration-head.txt').read_text().strip()
assert not git('diff', '--cached', '--name-only', '-z')
assert json.loads((area / 'source-validation.json').read_text())['status'] == 'pass'
assert json.loads((area / 'public-validation.json').read_text())['status'] == 'pass'
groups = [
    (['TraversalEndpointProper', 'SelectedPrefixProper', 'PrefixProperHistory',
      'ChildResourcesProper', 'TraversalResourcesProper'],
     'Preserve proper caches through actual prefixes and stopped children'),
    (['SelectedEdgeEndpointProper', 'CapturedEdgeEndpointProper', 'NativeHeadProper',
      'NativeBranchProper', 'FiniteHeadProper'],
     'Retain proper endpoints in full native resource packets'),
    (['HeadReceiptProper', 'HistoryReceiptProper', 'ResourceHistoryProper', 'InitialRenderProper'],
     'Derive proper storage for every emitted output from native startup'),
]
commits = []
for index, (suffixes, message) in enumerate(groups):
    paths = ['lean/MicroCFTA/SourcePruningEnumeration' + suffix + '.lean' for suffix in suffixes]
    if index == len(groups) - 1:
        paths.append('lean/MicroCFTA/Audit.lean')
    git('add', '--', *paths)
    staged = {p.decode() for p in git('diff', '--cached', '--name-only', '-z').split(b'\0') if p}
    assert staged == set(paths), staged
    git('diff', '--cached', '--check')
    output = git('commit', '-m', message).decode()
    commits.append(dict(head=git('rev-parse', 'HEAD').decode().strip(), paths=paths, output=output))
(area / 'source-head.txt').write_text(commits[-1]['head'] + '\n')
(area / 'source-commits.json').write_text(json.dumps(commits, indent=2) + '\n')
print(json.dumps(commits))
