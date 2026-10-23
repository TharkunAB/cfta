from pathlib import Path

source = Path('/tmp/mcfta-fresh-node-counter-growth-bootstrap.py').read_text()
changes = [
    ('20261023-fresh-node-counter-growth', '20261023-stored-node-counter-growth'),
    ('20261023-pair-inventory-rebase', '20261023-fresh-node-counter-growth'),
    ('mcfta-fresh-node-counter-growth', 'mcfta-stored-node-counter-growth'),
    ('mcfta-pair-inventory-rebase', 'mcfta-fresh-node-counter-growth'),
    ('InternedFreshOrdinaryNodeCounterGrowth', 'InternedFreshOrdinaryStoredNodeCounterGrowth'),
    ('SourceCurrentAllocatedNativePairInventoryRebase', 'InternedFreshOrdinaryNodeCounterGrowth'),
    ('ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a', 'af73f5d67493168cbab9cdd58cbc625d80585a23'),
    ('fb1949b3cf44911f25ac105403879a259fc8056a', 'ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a'),
    ('backup-fresh-node-counter-growth-', 'backup-stored-node-counter-growth-'),
    ('113643', '116844'), ('3140', '3141'), ('3650', '3651'),
    ('c129edd43b22ca18d27ad31aa6c25051b82518f8b436d0f00c7d034655357d08', '8257a0517c3ead6de9329d49ccae6cfcf57622f652c2d14a2ff61b9caa3286fd')]
for index, (before, after) in enumerate(changes):
    assert before in source, before
    source = source.replace(before, '@@STORED_COUNTER_BOOTSTRAP_' + str(index) + '@@')
for index, (before, after) in enumerate(changes):
    source = source.replace('@@STORED_COUNTER_BOOTSTRAP_' + str(index) + '@@', after)
begin = source.index("(HERE / 'current-progress.md').write_text(")
end = source.index('print(json.dumps(counts))', begin)
progress = '''# Repaired stored and optional-binder node-counter growth

H33 was sealed, pushed and remote-verified at af73f5d67493168cbab9cdd58cbc625d80585a23.
The next target is actual repaired stored execute, unfold and maybeMu node-counter monotonicity.
Each result must cover both completed and pending outcomes at the same literal returned heap.
The actual callback bound must follow from H33 and Work counters. It must not be a public premise.
No Dense, Valid, Facts, Good, Available, closedness or success premise may replace the operational proof.
Both probes, ordinaryLevel selection, canonical request and record update must remain literal.
Native/Scan/H23 lifting, fixed-source initial counter order and domain-history transport remain separate.
Room, WordRanges, complete resources, generated execution, Mu/full pass, practical width,
Haskell and solver correspondence, and convergence remain open.
No new body or compiler result is claimed at this bootstrap.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
No Haskell repair is proposed. FINDINGS keeps its external repair index first.
No board operation, memory write or ADR is added.
'''
source = source[:begin] + "(HERE / 'current-progress.md').write_text(" + repr(progress) + ')\n' + source[end:]
target = Path('/tmp/mcfta-stored-node-counter-growth-bootstrap.py')
assert not target.exists()
target.write_text(source)
print('Prepared the next bootstrap with baseline, publication, caps, refs and archive guards retained.')
