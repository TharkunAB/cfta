from pathlib import Path
import difflib
import hashlib
import json
import re

BASE = Path('/home/tritlo/Code/mcfta')
PACKET = Path(__file__).resolve().parent
source = (BASE / 'lean/MicroCFTA/SourceSynthesisCurrentUniverseNativeAllocation.lean').read_text()
cut = source.index('namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation',
                   source.index('theorem original_universe_mu_query_prefix_admission'))
source = source[:cut]
source = source[source.index('namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation'):]


def port(text):
    text = text.replace('SourceSynthesisCurrentUniverseNativeAllocation', 'SourceCurrentNativeWarmAdmission')
    text = text.replace('  have initialPhysical := SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid\n', '')
    text = text.replace('SourceCurrentAllocatedNativePhysicalCache.initial_valid (width := width) machine machineValid', 'initialPhysical')
    text = text.replace('(rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)', '(rootRequest : NodeRequest Symbol Guard) (start : Checked width)')
    text = text.replace('(machineValid : SourceRecursiveIntersectionKernel.Valid machine)', '(initialPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid start.native)')
    text = re.sub(r'\(operations : SourceEqualityConstraintMemoAllocation.State\)\s*', '', text)
    text = text.replace('(⟨initial width machine, operations⟩ : Checked width)', 'start')
    text = text.replace('rootRequest machine machineValid operations', 'rootRequest start initialPhysical')
    text = text.replace('rootRequest machine operations', 'rootRequest start')
    text = re.sub(r'(?<![.\w])machine\.heap', 'start.native.machine.heap', text)
    text = text.replace('machineValid.1', 'initialPhysical.machine.1')
    text = re.sub(r'\bmachineValid\b', 'initialPhysical', text)
    text = text.replace('SourceEqualityConstraintMemoAllocation.Valid operations', 'SourceEqualityConstraintMemoAllocation.Valid start.operations')
    text = text.replace('AuthenticEntry', 'AuthenticEntryAt').replace('MixedQualified', 'MixedQualifiedAt')
    text = text.replace('open SourceCurrentAllocatedNativeGeneralCMHistory (AuthenticEntryAt Qualified)', 'open SourceCurrentAllocatedNativeSourceWarmEntry (AuthenticEntryAt)\nopen SourceCurrentNativeWarmCMDefinitions (Qualified)')
    text = text.replace('open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified MixedQualifiedAt)', 'open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)\nopen SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)')
    text = text.replace('theorem original_universe_mu_query_prefix_admission\n', 'private theorem warm_mu_query_prefix_admission\n', 1)
    text = text.replace('one fixed cold-root trace', 'one fixed actual-root trace')
    return text


warm = port(source)
headers = '\n\n'.join(match.group(0).split(' := by')[0]
                      for match in re.finditer(r'^private theorem\b[\s\S]*? := by', warm, re.M)) + '\n'
assert headers == (PACKET / 'INTERNAL-FIRST-HEADERS.lean.txt').read_text(), 'private headers'
carrier = warm[warm.index('private def NodeAdmission'):warm.index('section CarrierProofs')].rstrip() + '\n'
assert carrier == (PACKET / 'CARRIER-FIRST.lean.txt').read_text(), 'carrier'
assert not re.search(r'(?<![.\w])machine\b', warm)
assert 'initial width machine' not in warm
for item in json.loads((PACKET / 'SOURCE-PINS.json').read_text()):
    assert hashlib.sha256((BASE / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']

(PACKET / 'PORT-COLD-TO-WARM.diff').write_text(''.join(difflib.unified_diff(
    source.splitlines(True), warm.splitlines(True), fromfile='cold-native-admission-family',
    tofile='warm-native-admission-family')))
public_header = (PACKET / 'FIRST-HEADER.lean.txt').read_text().rstrip('\n')
raw = ((PACKET / 'PREAMBLE.lean.txt').read_text() + warm + '\n'
       + (PACKET / 'PUBLIC-PREAMBLE.lean.txt').read_text()
       + public_header + (PACKET / 'PUBLIC-PROOF.lean.txt').read_text())
assert public_header + ' := by' in raw
target = PACKET / 'SourceSynthesisCurrentUniverseWarmMuAdmission.lean'
target.write_text(raw)
print(json.dumps({'lines': len(raw.splitlines()), 'sha256': hashlib.sha256(raw.encode()).hexdigest(),
                  'privateHeadersExact': True, 'carrierExact': True, 'publicHeaderExact': True,
                  'sourcePinsVerified': True}, indent=2))
