from pathlib import Path
import re

ROOT = Path('/home/tritlo/Code/mcfta')
PACKET = Path(__file__).resolve().parent
BASE = ROOT / 'lean/restart-evidence'
COLD = (ROOT / 'lean/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean').read_text()
PLAN = BASE / '20261117-full-next-warm-no-new-mu-plan'


def replace_once(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new, 1)


helpers = COLD[COLD.index('private theorem optional_closed_codec'):COLD.index('theorem original_universe_optional_prefix_no_new_mu')]
helpers = replace_once(helpers,
    '(rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)\n'
    '    (operations : SourceEqualityConstraintMemoAllocation.State) (wholeCount : Nat)',
    '(rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)')
helpers = helpers.replace('MixedQualified (width := width) rootRequest machine operations wholeCount',
                          'MixedQualifiedAt (width := width) rootRequest start wholeCount')
helpers = helpers.replace('AuthenticEntry (width := width) rootRequest machine operations wholeCount',
                          'AuthenticEntryAt (width := width) rootRequest start wholeCount')

literal = COLD[COLD.index('private theorem original_entry_from_literal_enter'):COLD.index('omit [DecidableEq Symbol]', COLD.index('private theorem original_entry_from_literal_enter'))]
literal = replace_once(literal, 'private theorem original_entry_from_literal_enter\n',
    'private theorem original_entry_from_literal_enter\n'
    '    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}\n'
    '    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)\n'
    '    (entry : Interned NodeKey) (body depth ordinary : Node)\n')
literal = literal.replace('(⟨initial width machine, operations⟩ : Checked width)', 'start')
literal = literal.replace('AuthenticEntry (width := width) rootRequest machine operations wholeCount',
                          'AuthenticEntryAt (width := width) rootRequest start wholeCount')
pattern = '''private theorem pattern_body_same (pattern : Node) (kind : tag pattern = 1 ∨ tag pattern = 3) :
    SourceRecursiveIntersectionKernel.body pattern = pattern := by
  cases pattern <;> simp_all [tag, SourceRecursiveIntersectionKernel.body]

'''

cold_theorem = COLD[COLD.index('theorem original_universe_optional_prefix_no_new_mu'):COLD.index('\nend MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation', COLD.index('theorem original_universe_optional_prefix_no_new_mu'))]
body = cold_theorem.split(' := by\n', 1)[1]
for old, new in [('rootRequest', 'newRoot'), ('fuel', 'newFuel'), ('inputs', 'newInputs'), ('fields', 'newFields')]:
    body = re.sub(r'\b' + old + r'\b', new, body)
body = replace_once(body,
    '  let initialState : Checked width := ⟨initial width machine, operations⟩',
    '  let initialState : Checked width := oldSnapshot')
body = replace_once(body,
    '  have initialPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid',
    '''  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  have coldPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid
  have oldOperations := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
    oldFuel oldCount (.code (.node oldRoot .pure)) oldControl .pure coldInitial oldSnapshot sourceHeap
    coldPhysical oldInputs oldFields operationsValid sourceGrowth
    (by simpa only [Control.bind_pure] using oldActual.steps) oldBound
  have initialPhysical := oldOperations.2.1
  have warmGrowth := oldOperations.2.2.2.1''')
body = body.replace('grows_trans sourceGrowth queryPhysical.2.heap', 'grows_trans warmGrowth queryPhysical.2.heap')
body = body.replace('grows_trans sourceGrowth readerPhysical.2.heap', 'grows_trans warmGrowth readerPhysical.2.heap')
body = replace_once(body,
    'SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_reader\n'
    '      nodeLaw edgeLaw newRoot machine machineValid operations newFuel used (queryUsed + 2) childCount',
    'SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader\n'
    '      nodeLaw edgeLaw newRoot oldSnapshot initialPhysical newFuel used (queryUsed + 2) childCount')
old_admission = '''  have admitted := original_universe_mu_query_prefix_admission
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    newRoot machine machineValid sourceGrowth rootDomain leftProfile rightProfile operations operationsValid
    newFuel used queryUsed readerControl current queried callerNext queryBefore (by omega) actual
    (by omega) queryActual selectedMu newInputs newFields'''
new_admission = '''  have warmAuxiliary := SourceCurrentNativeWarmAuxiliaryPrefixes.auxiliary_payloads_at_every_actual_warm_prefix
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyEntry.identity bodyIdentity oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    newRoot newFuel used readerControl current (by omega) newInputs newFields actual
    used readerControl current (Nat.le_refl _) actual
  have admitted := original_universe_next_warm_mu_query_prefix_admission
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    newRoot newFuel newRootDomain newLeftAvailable newRightAvailable newLeftClosed newRightClosed
    newInputs newFields used queryUsed readerControl current queried callerNext queryBefore
    (by omega) actual (by omega) queryActual selectedMu'''
body = replace_once(body, old_admission, new_admission)
body = body.replace('AuthenticEntry (width := width) newRoot machine operations used',
                    'AuthenticEntryAt (width := width) newRoot oldSnapshot used')
body = body.replace('MixedQualified (width := width) newRoot machine operations used',
                    'MixedQualifiedAt (width := width) newRoot oldSnapshot used')
body = body.replace('original_entry_from_literal_enter newRoot machine operations used',
                    'original_entry_from_literal_enter newRoot oldSnapshot used')
body = body.replace('newRoot machine operations used queryBefore.native.machine.heap entry body depth ordinary',
                    'newRoot oldSnapshot used queryBefore.native.machine.heap entry body depth ordinary')
old_gamma = '''      have cmPast := SourceCurrentAllocatedNativeGeneralCMHistory.current_stored_universe_general_cm_returned_at_every_actual_prefix
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        newRoot machine machineValid sourceGrowth operations operationsValid newFuel used readerControl current
        (by omega) newInputs newFields actual'''
new_gamma = '''      have cmPast := SourceCurrentNativeWarmCMHistory.current_stored_universe_warm_cm_returned_at_every_actual_prefix
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
        operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
        newRoot newFuel used readerControl current (by omega) newInputs newFields actual'''
body = replace_once(body, old_gamma, new_gamma)
bf = r'(?P<i> +)have past := SourceCurrentAllocatedNativeAuthenticBodyFirstInnerHistories\.body_first_inner_histories_at_authentic_prefix\n.*?\n(?P=i)  used readerControl current \(by omega\) actual'
co = r'(?P<i> +)have past := SourceCurrentAllocatedNativeAuthenticCoherentInnerHistory\.authentic_coherent_inner_returned_at_actual_root_prefix\n.*?\n(?P=i)  (?:queried\.domain|originalDomain) authentic \(by omega\) actual newInputs newFields'
def body_first(match):
    i = match['i']
    domain = 'queried.domain' if 'queried.domain authentic' in match[0] else 'originalDomain'
    return i + 'have payloads := warmAuxiliary pattern patternId ' + domain + ' authentic\n' + i + 'have past := And.intro payloads.1 payloads.2.1'
def coherent(match):
    i = match['i']
    domain = 'queried.domain' if 'queried.domain authentic' in match[0] else 'originalDomain'
    return i + 'have payloads := warmAuxiliary pattern patternId ' + domain + ' authentic\n' + i + 'have past := And.intro payloads.2.2.1 payloads.2.2.2'
body, bf_count = re.subn(bf, body_first, body, flags=re.S)
body, co_count = re.subn(co, coherent, body, flags=re.S)
assert (bf_count, co_count) == (2, 2)
assert 'rootDomain' not in body and 'leftProfile' not in body and 'rightProfile' not in body
assert 'keyed_child_law_at_actual_reader' not in body
assert 'GeneralCMHistory.current_stored_universe' not in body
assert 'AuthenticEntry (width' not in body and 'MixedQualified (width' not in body

preamble = '''import MicroCFTA.SourceSynthesisCurrentUniverseWarmMuAdmission
import MicroCFTA.SourceCurrentNativeWarmCMHistory
import MicroCFTA.SourceCurrentNativeWarmAuxiliaryPrefixes

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt MixedQualifiedAt)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Optional writers on the retained warm state]
The actual warm owner admission classifies the same literal optional site.
The C/M and auxiliary laws use its full actual prefix as one fixed history.
The child reader retains the same request, cell, value and before-finish state.
Each branch preserves the heap of the original optional writer.
The public theorem derives the warm start facts from the actual cold prefix.
-/

'''
header = (PLAN / 'OPTIONAL-FIRST-HEADER.lean.txt').read_text()
source = preamble + literal + pattern + helpers + header.rstrip() + '\n := by\n' + body + '\nend MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation\n'
assert 'sorry' not in source and 'set_option max' not in source and 'set_option linter' not in source
(PACKET / 'SourceSynthesisCurrentUniverseWarmOptionalNoNewMu.lean').write_text(source)
(PACKET / 'FIRST-HEADER.lean.txt').write_text(header)
(PACKET / 'PROOF.lean.txt').write_text(body)
(PACKET / 'PREAMBLE.lean.txt').write_text(preamble)
(PACKET / 'STATUS.txt').write_text('OPEN DRAFT / UNCOMPILED / prospective WarmMuAdmission dependency / zero theorem credit\n')
print({'lines': len(source.splitlines()), 'auxiliary_cases': bf_count + co_count, 'normal_source_changed': False})
