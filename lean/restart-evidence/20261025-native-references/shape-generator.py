from pathlib import Path
import re
root = Path('/home/tritlo/Code/mcfta')
path = root / 'lean/MicroCFTA/SourcePruningEnumerationFoldInvariants.lean'
text = path.read_text()
start = text.index('/-- A selected successful singleton retains storage and waiting counts. -/')
end = text.index('/-- Every returned outer fold state retains storage and waiting counts. -/')
block = text[start:end]
proof = block.split(' := by\n', 1)[1]
assert proof.count('exact ⟨storage, counts⟩') == 2
proof = proof.replace('exact ⟨storage, counts⟩', 'exact .inl rfl')
replacements = [
('none targetNode targetNode sourceScs targetScs', 'none, targetNode, targetNode, sourceScs, targetScs'),
('(some sourceHandle) none (some sourceHandle)\n                    sourceScs targetScs', 'some sourceHandle, none, some sourceHandle, sourceScs, targetScs'),
('(some sourceHandle) (some targetHandle)\n                              (some handle) sourceScs targetScs', 'some sourceHandle, some targetHandle, some handle, sourceScs, targetScs')]
mapping = {' '.join(old.split()): new for old, new in replacements}
def replace(match):
    key = ' '.join(match.group(1).split())
    return 'exact .inr ⟨same, ' + mapping[key] + ', sourceStored, targetStored, rfl⟩'
proof, count = re.subn(r'exact assimilated_preserves before source target\s+(.*?)\s+roots waiting storage counts sourceStored targetStored \(Ne.symm same\)', replace, proof, flags=re.S)
assert count == 6
assert 'storage' not in proof and 'counts' not in proof
header = '''import MicroCFTA.SourcePruningEnumerationDispatch

namespace MicroCFTA.SourcePruningEnumerationDispatchShape
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- An actual singleton retains the input or assimilates its two stored pending payloads. -/
theorem singleton
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    after = before ∨ source ≠ target ∧
      ∃ (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended),
        before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
        before.values[target]? = some (.unenumerated targetNode targetScs) ∧
        after = assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)) := by
'''
(root / 'lean/MicroCFTA/SourcePruningEnumerationDispatchShape.lean').write_text(header + proof +
    'end MicroCFTA.SourcePruningEnumerationDispatchShape\n')
replacement = block.split(' := by\n', 1)[0] + ''' := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact ⟨storage, counts⟩
  · exact assimilated_preserves before source target sourceNode targetNode merged sourceScs targetScs
      roots waiting storage counts sourceStored targetStored (Ne.symm different)

'''
text = text[:start] + replacement + text[end:]
text = text.replace('import MicroCFTA.SourcePruningEnumerationFold\n',
                    'import MicroCFTA.SourcePruningEnumerationFold\nimport MicroCFTA.SourcePruningEnumerationDispatchShape\n', 1)
path.write_text(text)
