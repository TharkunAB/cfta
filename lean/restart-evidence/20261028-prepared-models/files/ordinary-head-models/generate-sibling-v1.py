from pathlib import Path
import hashlib,json,difflib
R=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA');O=Path('/tmp/mcfta-prepared-models-20261028/ordinary-head-models')
p=R/'SourcePruningEnumerationFiniteSiblingCoverage.lean';s=p.read_text()
s=s.replace('import MicroCFTA.SourcePruningEnumerationFiniteSiblingCertificates','import MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingCertificates')
s=s.replace('import MicroCFTA.SourcePruningEnumerationFiniteHeadCoverage','import MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadCoverage')
s=s.replace('SourcePruningEnumerationNativeFiniteSiblingResources','SourcePruningEnumerationPreparedFiniteSiblingResources')
s=s.replace('SourcePruningEnumerationFiniteReservation','SourcePruningEnumerationPreparedReservation')
s=s.replace('open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint)','open SourcePruningEnumerationRecursive (Packet Output)\nopen SourcePruningEnumerationPreparedRecursive (Failure continueWith resume endpoint)')
s=s.replace('SourcePruningEnumerationRecursive.Complete','SourcePruningEnumerationPreparedRecursive.Complete')
s=s.replace('SourcePruningEnumerationRecursive.OutcomeResources','SourcePruningEnumerationPreparedRecursive.OutcomeResources')
s=s.replace('SourcePruningEnumerationNativeHookResources.head_finite_complete_resources_accepting','SourcePruningEnumerationPreparedNativeHookResources.head_finite_complete_resources_accepting')
s=s.replace('    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))','    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))\n    (parentClosed : free = [])')
s=s.replace('edge packet ready stored decoded\n','edge packet ready stored parentAvailable parentClosed\n')
s=s.replace('(lookupNode_keeps _ _ hookPost.effects.keeps handle _ decoded)','(hookPost.effects.keeps.available (.node parentEntry storedEdges depth free) parentAvailable)')
s=s.replace('        headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, shape, headAccepting⟩ :=','        headResources, headAccepting⟩ :=')
needle='          capturedMass inherited initialMass inheritedLength reserved.head\n'
assert s.count(needle)==1
s=s.replace(needle,needle+'      obtain ⟨headRun, headPost, headQueries, admitted, pending, history, cacheBounds, headFits, headKnown, shape⟩ :=\n        headResources\n')
s=s.replace('# Coverage of an indexed finite recursive sibling scan','# Coverage of an indexed prepared finite recursive sibling scan')
s=s.replace('The chosen hook can stop after its head has been reached.','The chosen hook can stop after its head has been reached. The prepared\nparent remains separate from the original stored handle. Its availability\npasses through the actual completed callback Post. The callback uses the\nnew worker, its own finite contract and its new failure type.')
assert 'decoded' not in s
assert 'SourcePruningEnumerationRecursive.Complete' not in s
assert 'SourcePruningEnumerationFiniteReservation' not in s
q=O/'drafts/sibling-v1/SourcePruningEnumerationPreparedFiniteSiblingCoverage.lean';q.parent.mkdir();q.write_text(s)
# Check exact preservation of the entire current prepared sibling resource declaration.
old=(R/'SourcePruningEnumerationPreparedFiniteSiblingResources.lean').read_text()
a=old.index('theorem alternatives_finite_complete_resources\n');b=old.index(' := by\n',a);decl=old[a:b]
a=s.index('theorem alternatives_finite_complete_resources_accepting\n');b=s.index(' := by\n',a);new=s[a:b]
marker=' ∧\n      ∀ extra,\n        let work := bound + extra'
assert marker in new
recovered=new[:new.index(marker)].replace('theorem alternatives_finite_complete_resources_accepting\n','theorem alternatives_finite_complete_resources\n',1)
assert recovered==decl, ''.join(difflib.unified_diff(decl.splitlines(keepends=True),recovered.splitlines(keepends=True)))
for n,b in [('sibling-old-entire-declaration.txt',decl.encode()),('sibling-recovered-entire-declaration.txt',recovered.encode())]:
 (O/'contracts'/n).write_bytes(b)
meta={'status':'UNTESTED source-only proposal; exact complete existing prepared sibling declaration recovered by removing only appended observer and theorem-name suffix','original_bytes':len(decl.encode()),'original_sha256':hashlib.sha256(decl.encode()).hexdigest(),'new_admissions':[],'new_worker_used':True,'new_forecast_used':True,'explicit_semantic_alternative':'chosen original occurrence reached, OR exact strictly earlier stopped callback','future_callback_completion_assumed':False}
(O/'contracts/sibling-proposal-comparison.json').write_text(json.dumps(meta,indent=2)+'\n')
print(q);print(len(s.encode()),len(s.splitlines()),hashlib.sha256(s.encode()).hexdigest());print(json.dumps(meta))
