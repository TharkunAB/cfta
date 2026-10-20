import hashlib,json,shutil
from pathlib import Path
h=Path(__file__).resolve().parent
r=Path('/home/tritlo/Code/mcfta')
shutil.copyfile('/tmp/mcfta-native-request-source-scope/SourceCurrentNativeRequestSourceScope.lean',h/'reviewed-source.lean')
def pin(base,path):
 data=(base/path).read_bytes()
 return {'path':path,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
paths=[
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixScope.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursiveWarmInitialRanges.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixAdmission.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixState.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixControl.lean',
'lean/MicroCFTA/SourceCurrentAllocatedRecursivePrefixCode.lean',
'lean/MicroCFTA/SourceRecursiveIntersectionRequestScope.lean',
'lean/MicroCFTA/SourceRecursiveIntersectionOriginalOutput.lean',
'lean/MicroCFTA/SourceCurrentNativeOptionalChildOrigin.lean',
'lean/MicroCFTA/SourceCurrentCompletedBuildRootedWriters.lean',
'lean/MicroCFTA/SourceCurrentSourceCaptureOriginalSlots.lean',
'lean/MicroCFTA/SourceCurrentNativeSelfCaptureSlots.lean']
(h/'source-pins.json').write_text(json.dumps({'files':[pin(r,p) for p in paths]},indent=2)+'\n')
(h/'review.md').write_text('''# Closed-root request scope and the remaining program ancestry obligation

Reviewed on 2026-10-20 at 19:58 CEST. No new Lean jobs or proof pairs.

No material mathematical or scope issue was found in the 63-line SourceCurrentNativeRequestSourceScope.node_prefix module. The reviewed source SHA256 is 8c3a4a931442dcb8771f11891123e2db0402010ed634a7cd405a03c982bb83f3. This package retains an exact copy. The parent corrected only the public NodeScope qualification during this review. The mathematical statement and proof remain the reviewed ones. The rejected intermediate hash check is retained. The parent owns validation of that module. This review does not count or infer a new successful check.

The theorem starts from the actual checked entry state. Good supplies complete physical heap facts and canonical domain-cache validity. SemanticReady remains explicit. Both initial operands are Available in that entry heap and closed. Existing closed_original derives their Original syntax grammar. The initial scope has an empty binding domain. Existing source_closed derives closure of the actual finite domain inventory. The explicit node, edge and domain-headroom bounds provide the old Resources. Initial Current uses the same heap and actual initial domain cache, with reflexive physical and issued extensions. request_node constructs the initial Certified proof. Initial Fields is the actual pure-continuation condition. The new node_scope theorem then consumes the same supplied raw Steps prefix and the same reached queried request and continuation. No final certificate, future return, History, idle table, assumed capture identity, or caller source-scope certificate is introduced.

The final scope contains Original for each queried operand, Available for each operand in the exact fixed entry heap, and OriginalBindings for that request's domain. Its key is in the same source inventory. Original is the existing payload grammar. It does not mean that the operand has a selected original-program binder occurrence. Closed generated values can satisfy that grammar.

The existing OptionalChildOrigin receipt retains an actual earlier Trace from its outer request to the SAME queried node instruction and continuation. For an empty-domain outer request with these closed-root initial operands and the stated resource conditions, earlier.steps is exactly the raw prefix input to node_prefix. ChildOrigin.request itself accepts an arbitrary outer domain. This closed-root specialization therefore does not apply to every ChildOrigin receipt without the corresponding start-control equality and initial premises. No fuel or intermediate-state witness is selected independently.

OriginalBindings.read is the next reusable value-level consumer. With the actual later heap facts and physical plus issued extensions, it recovers an exact complete Mu read, Original payload grammar and availability in that fixed entry heap for a bound domain name. It does not recover a source-program Path. The owner and retained child writer remain actual compiler provenance, not original syntax provenance.

A further original-program claim must supply the actual construction provenance of that fixed source heap. CompletedBuildRootedWriters.build_writer_or_prior then separates an exact prior full cell from a new publication rooted in that SAME actual completed source call. Eliminating the prior arm requires a real initial absence fact. Its Written receipt retains one actual publication and source Reached route. SourceCaptureOriginalSlots only transports a row-bearing capture through an already supplied source Path to the exact initial slot. It does not produce that Path. NativeSelfCaptureSlots only classifies actual stored self-substitution captures as the exact closed leaf or complete self Mu. It does not turn a generated encode root into the original closed program root. Historical warm winners, closed-leaf ancestry and generated callbacks therefore remain separate obligations. No unique source writer, generated-child decrease or general termination claim follows here.
''')
(h/'verify.py').write_text('''import argparse,hashlib,json\nfrom pathlib import Path\nh=Path(__file__).resolve().parent\np=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path('/home/tritlo/Code/mcfta'));a=p.parse_args()\nm=json.loads((h/'manifest.json').read_text())\nfor base,items in [(h,m['files']),(a.root,m['sources'])]:\n for e in items:\n  b=(base/e['path']).read_bytes();assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],e['path']\nassert hashlib.sha256((h/'reviewed-source.lean').read_bytes()).hexdigest()=='8c3a4a931442dcb8771f11891123e2db0402010ed634a7cd405a03c982bb83f3'\nprint(json.dumps({'status':'PASS','pins':len(m['files'])+len(m['sources']),'lean_jobs':0,'public_pairs':0,'constructed_pairs':0}))\n''')
files=['reviewed-source.lean','review.md','source-pins.json','verify.py','package.py','review.md.draft-1','manifest.json.draft-1','verify.py.draft-1','verification-draft-1.json']
(h/'manifest.json').write_text(json.dumps({'schema':1,'files':[pin(h,p) for p in files],'sources':[pin(r,p) for p in paths]},indent=2)+'\n')
