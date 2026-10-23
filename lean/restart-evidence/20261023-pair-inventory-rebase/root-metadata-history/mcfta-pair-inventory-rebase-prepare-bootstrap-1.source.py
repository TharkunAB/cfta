from pathlib import Path

source = Path('/tmp/mcfta-rebuild-admission-bootstrap.py').read_text()
changes = [('20261023-rebuild-admission', '20261023-pair-inventory-rebase'),
    ('20261023-group-admission', '20261023-rebuild-admission'),
    ('mcfta-rebuild-admission', 'mcfta-pair-inventory-rebase'),
    ('mcfta-group-admission', 'mcfta-rebuild-admission'),
    ('SourceCurrentOriginalRowRebuildAdmission', 'SourceCurrentAllocatedNativePairInventoryRebase'),
    ('SourceCurrentOriginalRowGroupAdmission', 'SourceCurrentOriginalRowRebuildAdmission'),
    ("START = '825d83243f4e69b39b2211598d92e15c427f88ed'", "START = 'fb1949b3cf44911f25ac105403879a259fc8056a'"),
    ('591bda7cd4028ee1ed22770c9974142294c92210', '825d83243f4e69b39b2211598d92e15c427f88ed'),
    ('backup-rebuild-admission-', 'backup-pair-inventory-rebase-'),
    ('111320', '112408'), ('3138', '3139'), ('3648', '3649'),
    ('0578808bf26b311291a002a52574fc77363ee84f1ba3f82f14ce270427965c2e', '3474b4adb87e8657faf95802a43938881ec79a19ee3835f44ba31ec6d8e54a01')]
for before, after in changes:
    assert before in source, before
    source = source.replace(before, after)
begin = source.index("(HERE / 'current-progress.md').write_text(")
end = source.index('print(json.dumps(counts))', begin)
progress = '# Same-state pair and native inventory rebase\n\nH31 was sealed, pushed and remote-verified at fb1949b3cf44911f25ac105403879a259fc8056a.\nThe target is one computed larger inventory at the SAME Wrapper.\nNative At, pair Stable and canonical captured-request admission remain genuine input certificates.\nThe new Agreement must be derived from actual heap growth and root inclusion.\nNo proof body or compiler result is claimed here.\nNew-source Room, WordRanges, global Trace rebasing, later generated execution, Mu/full pass,\npractical width, Haskell and solver correspondence, and convergence remain open.\nH6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.\nNo Haskell repair is proposed. FINDINGS keeps its external repair index first.\nNo board operation, memory write or ADR is added.\n'
source = source[:begin] + "(HERE / 'current-progress.md').write_text(" + repr(progress) + ')\n' + source[end:]
target = Path('/tmp/mcfta-pair-inventory-rebase-bootstrap.py')
assert not target.exists()
target.write_text(source)
print('Prepared next bootstrap with unchanged baseline, publication, caps, ref and archive guards.')
