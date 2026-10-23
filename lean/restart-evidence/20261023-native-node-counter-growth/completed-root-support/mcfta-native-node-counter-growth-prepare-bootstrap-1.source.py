from pathlib import Path

source = Path('/tmp/mcfta-stored-node-counter-growth-bootstrap.py').read_text()
changes = [
    ('20261023-stored-node-counter-growth', '20261023-native-node-counter-growth'),
    ('20261023-fresh-node-counter-growth', '20261023-stored-node-counter-growth'),
    ('mcfta-stored-node-counter-growth', 'mcfta-native-node-counter-growth'),
    ('mcfta-fresh-node-counter-growth', 'mcfta-stored-node-counter-growth'),
    ('InternedFreshOrdinaryStoredNodeCounterGrowth', 'SourceRecursiveIntersectionNativeNodeCounterGrowth'),
    ('InternedFreshOrdinaryNodeCounterGrowth', 'InternedFreshOrdinaryStoredNodeCounterGrowth'),
    ('af73f5d67493168cbab9cdd58cbc625d80585a23', 'a295f1f72153365c886484cbeea933809acbc3f7'),
    ('ab49ebd03b6f7530c4f48c3b0cff85b85c98b87a', 'af73f5d67493168cbab9cdd58cbc625d80585a23'),
    ('backup-stored-node-counter-growth-', 'backup-native-node-counter-growth-'),
    ('116844', '118574'), ('3141', '3142'), ('3651', '3652'),
    ('8257a0517c3ead6de9329d49ccae6cfcf57622f652c2d14a2ff61b9caa3286fd', '1f3a43b7fb26827dc930bdddc7d6ee2f0c543cc53821c897ad5062d776f3320f')]
for index, (before, after) in enumerate(changes):
    assert before in source, before
    source = source.replace(before, '@@NATIVE_COUNTER_BOOTSTRAP_' + str(index) + '@@')
for index, (before, after) in enumerate(changes):
    source = source.replace('@@NATIVE_COUNTER_BOOTSTRAP_' + str(index) + '@@', after)
begin = source.index("(HERE / 'current-progress.md').write_text(")
end = source.index('print(json.dumps(counts))', begin)
progress = '''# Native node-counter growth

H34 was sealed, pushed and remote-verified at a295f1f72153365c886484cbeea933809acbc3f7.
The next target is actual native step, finite execute and resume node-counter growth.
Compare state.machine.heap.nodes.next with that same projection of the actual returned outcome state.
Cover yielded, done, failed and blocked outcomes for arbitrary initial native states and widths.
Use existing Work run_next, H34 maybeMu_mono and public immediate memo machine-retention results.
Do not assume validity, readiness, successful completion, a callback bound or the desired counter bound.
Pending constructor work must retain its actual enlarged heap when native execution blocks.
Finite execution must compose the actual one-step state with its generalized fuel induction result.
No declaration, body or new compiler result is claimed at this bootstrap.
Scan/H23 lifting, fixed-source initial counter order and global domain-history transport remain separate.
Room, WordRanges, complete resources, generated execution, Mu/full pass, practical width,
Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
No Haskell repair is proposed. FINDINGS keeps its external repair index first.
No board operation, memory write or ADR is added.
'''
source = source[:begin] + "(HERE / 'current-progress.md').write_text(" + repr(progress) + ')\n' + source[end:]
target = Path('/tmp/mcfta-native-node-counter-growth-bootstrap.py')
assert not target.exists()
target.write_text(source)
print('Prepared the native bootstrap with all baseline, publication, caps, refs and archive guards retained.')
