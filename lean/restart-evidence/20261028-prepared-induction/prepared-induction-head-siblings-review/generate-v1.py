from pathlib import Path
import json, hashlib
repo=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
own=Path('/tmp/mcfta-prepared-induction-20261028/prepared-induction-head-siblings-review')
out=own/'drafts/v1';out.mkdir(parents=True,exist_ok=True)
head=(repo/'SourcePruningEnumerationPreparedHeadResources.lean').read_text()
head=head.replace('import MicroCFTA.SourcePruningEnumerationFiniteReceiptResources','import MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptResources')
head=head.replace('import MicroCFTA.SourcePruningEnumerationSubtreeEffects\n','')
head=head.replace('namespace MicroCFTA.SourcePruningEnumerationNativeHookResources','namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources')
head=head.replace('end MicroCFTA.SourcePruningEnumerationNativeHookResources','end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources')
head=head.replace('open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume Complete OutcomeResources)', 'open SourcePruningEnumerationRecursive (Packet Output)\nopen SourcePruningEnumerationPreparedRecursive (Failure continueWith resume Complete OutcomeResources)')
head=head.replace('theorem head_finite_complete_resources_prepared','theorem head_finite_complete_resources')
head=head.replace(':= receipt_finite_complete_resources', ':= SourcePruningEnumerationPreparedRecursive.receipt_finite_complete_resources')
head=head.replace(':=\n      resources.post', ':=\n      resources.post')
head=head.replace('SourcePruningEnumerationRecursive.completed_captured_packet','SourcePruningEnumerationPreparedRecursive.completed_captured_packet')
head=head.replace('# An actual prepared edge followed by a finite callback','# Actual prepared heads with the new finite recursive callback')
head=head.replace('resources and callback effects share the same caller and full memo states.','resources and callback effects share the same caller and full memo states.\nThe smaller-depth contract uses the new recursive worker and failure type.')
assert 'SourcePruningEnumerationPreparedRecursive.receipt_finite_complete_resources' in head
(out/'SourcePruningEnumerationPreparedFiniteHeadResources.lean').write_text(head)

old=(repo/'SourcePruningEnumerationFiniteSiblingCertificates.lean').read_text()
pre=old[:old.index('/-- Each processed receipt')]
pre=pre.replace('import MicroCFTA.SourcePruningEnumerationFiniteHeadResources','import MicroCFTA.SourcePruningEnumerationFiniteSiblingCertificates\nimport MicroCFTA.SourcePruningEnumerationPreparedOutcomeResources')
pre=pre.replace('namespace MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources','namespace MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources')
pre=pre.replace('open SourcePruningEnumerationRecursive (Output Failure OutputResources OutcomeResources)', 'open SourcePruningEnumerationRecursive (Output)\nopen SourcePruningEnumerationPreparedRecursive (Failure OutcomeResources)\nopen SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt)')
pre=pre.replace('# Certificates at finite-depth sibling endpoints','# Exact stopped callbacks for prepared finite siblings')
definition=old[old.index('/-- A stopped callback'):old.index('variable {recursiveFuel')]
variables=old[old.index('variable {recursiveFuel'):old.index('/-- A suffix receipt')]
stop=old[old.index('/-- A stopped suffix'):old.index('end MicroCFTA.')]
cert=pre+definition+variables+stop+'end MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources\n'
(out/'SourcePruningEnumerationPreparedFiniteSiblingCertificates.lean').write_text(cert)

sibling=(repo/'SourcePruningEnumerationFiniteSiblingResources.lean').read_text()
sibling=sibling.replace('import MicroCFTA.SourcePruningEnumerationFiniteSiblingCertificates','import MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingCertificates\nimport MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadResources')
sibling=sibling.replace('namespace MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources','namespace MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources')
sibling=sibling.replace('end MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources','end MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources')
sibling=sibling.replace('open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint)', 'open SourcePruningEnumerationRecursive (Packet Output)\nopen SourcePruningEnumerationPreparedRecursive (Failure continueWith resume endpoint)\nopen SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt)')
sibling=sibling.replace('SourcePruningEnumerationRecursive.Complete','SourcePruningEnumerationPreparedRecursive.Complete')
sibling=sibling.replace('    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))','    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))\n    (parentClosed : free = [])')
sibling=sibling.replace('SourcePruningEnumerationNativeHookResources.head_finite_complete_resources','SourcePruningEnumerationPreparedNativeHookResources.head_finite_complete_resources')
sibling=sibling.replace('packet ready stored decoded\n','packet ready stored parentAvailable parentClosed\n')
sibling=sibling.replace('(lookupNode_keeps _ _ hookPost.effects.keeps handle _ decoded)', '(hookPost.effects.keeps.available (.node parentEntry storedEdges depth free) parentAvailable)')
sibling=sibling.replace('# Original resources for a finite-depth ordered sibling scan','# Resources for actual prepared finite-depth siblings')
sibling=sibling.replace('effects and full memos pass to the suffix.', 'effects and full memos pass to the suffix. The prepared parent remains\nseparate from the original stored handle. Its availability follows the actual Post.')
assert 'decoded' not in sibling
(out/'SourcePruningEnumerationPreparedFiniteSiblingResources.lean').write_text(sibling)

finish=(repo/'SourcePruningEnumerationFiniteSiblingFinishResources.lean').read_text()
finish=finish.replace('import MicroCFTA.SourcePruningEnumerationFiniteSiblingResources','import MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources')
finish=finish.replace('import MicroCFTA.SourcePruningEnumerationSubtreeEffects','import MicroCFTA.SourcePruningEnumerationPreparedOutcomeResources')
finish=finish.replace('namespace MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources','namespace MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources')
finish=finish.replace('end MicroCFTA.SourcePruningEnumerationNativeFiniteSiblingResources','end MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingResources')
finish=finish.replace('open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint)', 'open SourcePruningEnumerationRecursive (Packet Output)\nopen SourcePruningEnumerationPreparedRecursive (Failure continueWith resume endpoint)\nopen SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt)')
finish=finish.replace('SourcePruningEnumerationRecursive.Complete','SourcePruningEnumerationPreparedRecursive.Complete')
finish=finish.replace('    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))','    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))\n    (parentClosed : free = [])')
finish=finish.replace('packet ready stored decoded selected incoming','packet ready stored parentAvailable parentClosed selected incoming')
finish=finish.replace('SourcePruningEnumerationRecursive.OutcomeResources','SourcePruningEnumerationPreparedRecursive.OutcomeResources')
finish=finish.replace('SourcePruningEnumerationRecursive.finish','SourcePruningEnumerationPreparedRecursive.finish')
finish=finish.replace('SourcePruningEnumerationRecursive.finish_resources_general','SourcePruningEnumerationPreparedRecursive.finish_resources_general')
finish=finish.replace('# Resources after the actual finite-depth sibling scan finishes','# Resources after the actual prepared sibling scan finishes')
assert 'decoded' not in finish
(out/'SourcePruningEnumerationPreparedFiniteSiblingFinishResources.lean').write_text(finish)

status={'status':'UNTESTED owner source drafts; Root alone compiles', 'modules':[],'new_callback_import':'MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptResources','new_callback_theorem':'SourcePruningEnumerationPreparedRecursive.receipt_finite_complete_resources','forecast_scope':'Explicit local seed/HeadReserved/ScanReserved. No claim that the original pre-normalization envelope dominates SelectedValue preparation.'}
for source in sorted(out.glob('*.lean')):
 b=source.read_bytes();status['modules'].append({'path':str(source),'bytes':len(b),'lines':len(b.splitlines()),'sha256':hashlib.sha256(b).hexdigest()})
(out/'status.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status,indent=2))
