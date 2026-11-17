from pathlib import Path
import re

ROOT = Path('/home/tritlo/Code/mcfta')
PACKET = Path(__file__).resolve().parent
BASE = ROOT / 'lean/restart-evidence'
cold = (ROOT / 'lean/MicroCFTA/SourceSynthesisCurrentUniverseColdNoNewMu.lean').read_text()
header = (BASE / '20261117-full-next-warm-no-new-mu-plan/FULL-FIRST-HEADER.lean.txt').read_text()
helpers = cold[cold.index('private theorem cold_lift_heap'):cold.index('theorem original_universe_cold_query_no_new_mu')]
helpers = helpers.replace('cold_lift_heap', 'warm_lift_heap').replace('cold_step_no_new_mu', 'warm_step_no_new_mu')
theorem = cold[cold.index('theorem original_universe_cold_query_no_new_mu'):cold.index('\nend MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation')]
body = theorem.split(' := by\n', 1)[1]
for old, new in [('rootRequest', 'newRoot'), ('fuel', 'newFuel'), ('inputs', 'newInputs'), ('fields', 'newFields')]:
    body = re.sub(r'\b' + old + r'\b', new, body)
body = body.replace('let initialState : Checked width := ⟨initial width machine, operations⟩',
                    'let initialState : Checked width := oldSnapshot')
body = body.replace('cold_step_no_new_mu', 'warm_step_no_new_mu')
old = '''    exact original_universe_optional_prefix_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      newRoot machine machineValid sourceGrowth rootDomain leftProfile rightProfile operations operationsValid
      newFuel used current binder siteBody resume room newInputs newFields past'''
new = '''    exact original_universe_next_warm_optional_prefix_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
      operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      newRoot newFuel newRootDomain newLeftAvailable newRightAvailable newLeftClosed newRightClosed
      newInputs newFields used current binder siteBody resume room past'''
assert body.count(old) == 1
body = body.replace(old, new)
assert 'rootDomain' not in body and 'leftProfile' not in body and 'rightProfile' not in body
preamble = '''import MicroCFTA.SourceSynthesisCurrentUniverseWarmOptionalNoNewMu
import MicroCFTA.SourceCurrentNativePublicationTrace

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [All actual warm query heaps]
Each nonoptional instruction preserves complete Mu records.
The actual source prefix theorem supplies the optional writer case.
The induction keeps the original retained start and full fuel bound.
It includes every terminal execute heap and every bounded trace prefix.
No caller supplies the target heap inventory or a future result law.
-/

'''
source = preamble + helpers + header.rstrip() + '\n := by\n' + body + '\nend MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation\n'
assert 'sorry' not in source and 'set_option max' not in source and 'set_option linter' not in source
(PACKET / 'SourceSynthesisCurrentUniverseWarmNoNewMu.lean').write_text(source)
(PACKET / 'FIRST-HEADER.lean.txt').write_text(header)
(PACKET / 'PROOF.lean.txt').write_text(body)
(PACKET / 'PREAMBLE.lean.txt').write_text(preamble)
(PACKET / 'STATUS.txt').write_text('OPEN DRAFT / UNCOMPILED / prospective warm optional dependency / zero theorem credit\n')
print({'lines': len(source.splitlines()), 'actual_outcome_and_all_prefixes': True, 'normal_source_changed': False})
