from pathlib import Path

source = Path('/tmp/mcfta-pair-inventory-rebase-bootstrap.py').read_text()
changes = [
    ('20261023-pair-inventory-rebase', '20261023-fresh-node-counter-growth'),
    ('20261023-rebuild-admission', '20261023-pair-inventory-rebase'),
    ('mcfta-pair-inventory-rebase', 'mcfta-fresh-node-counter-growth'),
    ('mcfta-rebuild-admission', 'mcfta-pair-inventory-rebase'),
    ('SourceCurrentAllocatedNativePairInventoryRebase', 'InternedFreshOrdinaryNodeCounterGrowth'),
    ('SourceCurrentOriginalRowRebuildAdmission', 'SourceCurrentAllocatedNativePairInventoryRebase'),
    ('fb1949b3cf44911f25ac105403879a259fc8056a', 'ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a'),
    ('825d83243f4e69b39b2211598d92e15c427f88ed', 'fb1949b3cf44911f25ac105403879a259fc8056a'),
    ('backup-pair-inventory-rebase-', 'backup-fresh-node-counter-growth-'),
    ('112408', '113643'), ('3139', '3140'), ('3649', '3650'),
    ('3474b4adb87e8657faf95802a43938881ec79a19ee3835f44ba31ec6d8e54a01', 'c129edd43b22ca18d27ad31aa6c25051b82518f8b436d0f00c7d034655357d08')]
for index, (before, after) in enumerate(changes):
    assert before in source, before
    source = source.replace(before, '@@FRESH_COUNTER_BOOTSTRAP_' + str(index) + '@@')
for index, (before, after) in enumerate(changes):
    source = source.replace('@@FRESH_COUNTER_BOOTSTRAP_' + str(index) + '@@', after)
begin = source.index("(HERE / 'current-progress.md').write_text(")
end = source.index('print(json.dumps(counts))', begin)
progress = '''# Repaired nested constructor node-counter growth

H32 was sealed, pushed and remote-verified at ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a.
The next target is actual repaired build, buildMany and buildEdges node-counter monotonicity.
It must cover both completed and pending outcomes at the same literal returned heap.
No Dense, Valid, Facts, Good or success premise may replace the operational proof.
Private callback transport must cover the actual pending state as well as completed states.
Native/Scan/H23 lifting, fixed-source initial counter order and domain-history transport remain separate.
Room, WordRanges, complete resources, generated execution, Mu/full pass, practical width,
Haskell and solver correspondence, and convergence remain open.
No new declaration, body or compiler result is claimed at this bootstrap.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
No Haskell repair is proposed. FINDINGS keeps its external repair index first.
No board operation, memory write or ADR is added.
'''
source = source[:begin] + "(HERE / 'current-progress.md').write_text(" + repr(progress) + ')\n' + source[end:]
target = Path('/tmp/mcfta-fresh-node-counter-growth-bootstrap.py')
assert not target.exists()
target.write_text(source)
print('Prepared the next bootstrap with all baseline, publication, cap, ref and archive guards unchanged.')
