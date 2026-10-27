from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-recursive-worker-arity-20261027')
original = (root / 'lean/MicroCFTA/SourcePruningEnumerationTerminalObservedResources.lean').read_text()
text = original.replace('import MicroCFTA.SourcePruningEnumerationTerminalAdmission',
    'import MicroCFTA.SourcePruningEnumerationTerminalObservedResources\n'
    'import MicroCFTA.SourcePruningEnumerationFoldArity\n'
    'import MicroCFTA.SourcePruningEnumerationIncomingNodeObservedArity', 1)
start = text.index('/-!')
end = text.index('-/', start) + 2
text = text[:start] + '''/-!
# Arity at actual terminal returns

The original fold and incoming query retain their exact caller heaps.
Early returns keep the reached heap even when the enum result is empty.
The theorem keeps every original resource admission.
-/''' + text[end:]
text = text.replace('/-- Original current facts bound the caller of every outer successful terminal observation. -/',
    '/-- The actual outer successful terminal endpoint retains whole native arity. -/', 1)
text = text.replace('theorem observed_resources', 'theorem observed_heap', 1)
known = '    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)\n'
assert text.count(known) == 1
text = text.replace(known, known + '    (arityHeap : SourcePruningEnumerationArityOrigins.Heap beforeCaller.checked.native.machine.heap)\n', 1)
old_goal = '''    Fits (advance seed ((first :: rest).length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed ((first :: rest).length + 1)).1)
        afterCaller.checked.native.machine.heap := by'''
assert text.count(old_goal) == 1
text = text.replace(old_goal, '    SourcePruningEnumerationArityOrigins.Heap afterCaller.checked.native.machine.heap := by', 1)
first = text.index('    refine ⟨fits.mono')
last = text.index('  · simp only [ite_eq_right empty]', first)
text = text[:first] + '    exact arityHeap\n' + text[last:]
first = text.index('                    have finalSeed')
last = text.index('                    cases possible with', first)
text = text[:first] + '''                    have padded := SourcePruningEnumerationFold.observed_heap seed formulas solver inventory
                      beforeCaller joined recorded checkEmpty n p h winner memos initial joinedRealized
                      winnerPending selected fits foldReservation known arityHeap foldObserved
''' + text[last:]
text = text.replace('SourcePruningEnumerationIncomingNode.observed_resources',
    'SourcePruningEnumerationIncomingNode.observed_heap')
assert text.count('foldBounds.2\n') == 1
text = text.replace('foldBounds.2\n', 'foldBounds.2 padded\n')
text = text.replace('rw [← callerSame, finalSeed]', 'rw [← callerSame]')
name = 'SourcePruningEnumerationTerminalArity.lean'
data = text.encode()
path = area / 'terminal-arity-revisions/v1' / name
path.parent.mkdir(parents=True)
path.write_bytes(data)
(area / name).write_bytes(data)
old = original.split('theorem observed_resources', 1)[1].split(' :\n    Fits', 1)[0]
new = text.split('theorem observed_heap', 1)[1].split(' :\n    SourcePruningEnumerationArityOrigins.Heap afterCaller', 1)[0]
extra = '    (arityHeap : SourcePruningEnumerationArityOrigins.Heap beforeCaller.checked.native.machine.heap)\n'
assert new.replace(extra, '', 1) == old
(area / 'terminal-header-comparison.json').write_text(json.dumps(dict(original=old, new=new,
    full_original_admission_preserved=True), indent=2) + '\n')
print(json.dumps(dict(lines=len(data.splitlines()), bytes=len(data), sha256=hashlib.sha256(data).hexdigest())))
