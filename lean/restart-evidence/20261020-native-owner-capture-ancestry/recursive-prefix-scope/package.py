import datetime
import hashlib
import json
from pathlib import Path

here=Path(__file__).resolve().parent
root=Path('/home/tritlo/Code/mcfta')
def pin(base,path):
    data=(base/path).read_bytes()
    return {'path':path,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
head='MicroCFTA.SourceCurrentAllocatedRecursivePrefixScope.node_scope'
sources=[
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixAdmission.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixInduction.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixReceipt.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixState.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixControl.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixCode.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursiveRequestStep.lean',
'lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalCompletion.lean',
'lean/MicroCFTA/SourceCurrentAllocatedNativeFieldClosure.lean',
'lean/MicroCFTA/SourceEqualityNativeDemandProtectedPrefix.lean',
'lean/MicroCFTA/SourceEqualityNativeDemandBodyYield.lean',
'lean/MicroCFTA/SourceRecursiveIntersectionRequestScope.lean',
'lean/MicroCFTA/SourceRecursiveIntersectionInputInventory.lean',
'lean/MicroCFTA/SourceEqualityNativeDemand.lean']
(here/'node-scope-source-pins.json').write_text(json.dumps({'files':[pin(root,p) for p in sources]},indent=2)+'\n')
selection={'finalized':True,'strict':'node-scope-direct-2','canonical':None,'groups':[{'name':'node-scope-public-1','pairs':1,'kind':'prototype-public','full_proof':True}],'public_heads':[head],'lean_jobs':3,'failed_attempts':1,'constructed_pairs':0,'production_pairs':1,'canonical_jobs':0,'unselected':[{'name':'node-scope-direct-1','reason':'The narrowed private Head conclusion did not infer four intermediate code controls. Explicit actual work/enter/read/optional continuations resolve those elaboration errors.'}]}
(here/'node-scope-selection.json').write_text(json.dumps(selection,indent=2)+'\n')
(here/'node-scope-peaks-final.txt').write_bytes((here/'node-scope-peaks.txt').read_bytes())
(here/'node-scope-review.md').write_text('''# Fixed-source scope at a reached node instruction

Reviewed on 2026-10-20 at 19:56 CEST.

The sole public theorem `node_scope` takes the existing Resources, Current, initial control Certified, Fields and an actual raw Steps prefix. The final control is the same supplied node instruction. The conclusion gives that queried request's NodeScope in the fixed source heap and its domain key's membership in the fixed inventory. NodeScope retains Original for both complete operands, Available for both operands in that source heap, and OriginalBindings for the request domain. No desired final scope occurs as an input.

The private Head predicate constrains only reached node instructions. It is True for other controls. This avoids a false claim that every intermediate protected finish frame has a full source certificate. A strong induction follows the actual raw prefix. Existing admission derives the physical checks and current effects for each yielded step. Actual bind-prefix and protected owner splits retain their exact body traces and continuation intervals. An unfinished inner trace uses the smaller-fuel Head induction. A completed inner trace uses the existing Admission.prefixes receipt for its current facts, actual extension, operation fields and returned postcondition. The actual continuation certificate then supports the remaining Head induction. The proof does not repeat the old receipt result for all remaining controls.

All direct, memoized ready and memoized evaluating node branches remain explicit. The edge-body and edge-query branches retain actual captured requests and protected finish frames. The work, enter, read and optional branches use their literal yielded controls. Pending optionalBinder cannot cross a yielded Steps constructor. The zero-length case extracts the node facts from the initial certificate. No future owner return, child History, guessed decomposition or final Certified premise is used.

This is an input-heap scope result. The word Original is the existing physical operand grammar. OriginalBindings refers to complete Mu values available in the fixed source heap. The result does not identify an original program binder occurrence, a source Path, a unique writer, or a current callback. Such source ancestry still requires the actual construction and publication provenance of that fixed heap. No runtime or Haskell defect, termination result, or stronger History-at-prefix conclusion is claimed.

Selected strict direct2 has an empty raw log. Full public1 checks the exact statement, complete proof and axiom list with all eight printer options and only the standard axioms. Three capped Lean jobs are retained. Direct1 failed at four elaboration sites because the narrowed Head result did not determine the intermediate Code control. Explicit actual continuations fix those sites. This package counts one generic head, no constructed heads, and no canonical jobs. Final source SHA256: f588c2f931c2b96052643048a637935643e0b6596bfdcab96dd8e175757a6039.
''')
old=Path('/tmp/mcfta-native-prefix-writer-maps/prefix-maps-verify.py').read_text()
verify=old.replace('prefix-maps','node-scope').replace('SourceCurrentNativePrefixWriterMaps.lean','SourceCurrentAllocatedRecursivePrefixScope.lean').replace('MicroCFTA.SourceCurrentNativePrefixWriterMaps.prefix',head)
verify=verify.replace("    assert 'History after' not in source.decode()", "    assert 'History after' not in source.decode()\n    assert 'theorem node_scope' in source.decode()\n    assert 'NodeScope source request ∧ request.domain.key ∈ inventory' in source.decode()")
(here/'node-scope-verify.py').write_text(verify)
files=['SourceCurrentAllocatedRecursivePrefixScope.lean','helpers.txt','node-scope-run-check.py','node-scope-capped-worker.py','node-scope-public.lean','node-scope-peaks-final.txt','node-scope-selection.json','node-scope-review.md','node-scope-source-pins.json','node-scope-verify.py','package.py']
for stem in ['node-scope-direct-1','node-scope-direct-2','node-scope-public-1']:
    files += [stem+suffix for suffix in ['.json','.limits.json','.usage.json','.source.lean','.log']]
manifest={'schema':1,'files':[pin(here,p) for p in files],'sources':[pin(root,p) for p in sources]}
(here/'node-scope-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
