from pathlib import Path
import hashlib,json
repo=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-continuation-coverage-20261027/hook-policy-review');sha=lambda b:hashlib.sha256(b).hexdigest()
def put(rel,b):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b.encode() if isinstance(b,str) else b)
spec=[
('SourcePruningEnumerationNativeContinuations',[(17,71),(86,115),(118,163)],'Whole small module read. Exact run, current outside processed, hook stops and actual post-hook suffix endpoint.'),
('SourcePruningEnumerationHookInvocation',[(26,69),(71,161)],'Whole small module read. Real caller-threaded Invocation constructors; output-only origin theorem does not prove chosen coverage.'),
('SourcePruningEnumerationRecursive',[(23,77),(84,115)],'Whole small module read. Actual continueWith callback and recursive failure/output branches.'),
('SourcePruningEnumerationFiniteSiblingCertificates',[(39,81),(87,127)],'Whole small module read. Per-index own resources; StoppedAt is resource data, not literal invocation or original-index evidence.'),
('SourcePruningEnumerationFiniteSiblingResources',[(40,94),(96,223)],'Whole direct producer induction read. Original inputs, full packet, actual post-hook Memos/context, same common bound, explicit stops.'),
('SourcePruningEnumerationFiniteHeadResources',[(43,100),(102,165)],'Whole head producer read. Actual stable captured receipt and stable callback outcome; complete subtree supplies captured sibling Packet.'),
('SourcePruningEnumerationContinuationHead',[(18,53)],'Whole small module read. Actual complete-hook and advanceable noncomplete receipt equations.'),
('SourcePruningEnumerationNativeLanguage',[(40,98),(127,137)],'Whole small module read. Keeps transports the same realized original core in the correct iff direction.'),
('SourcePruningEnumerationNativeBranches',[(14,43)],'Whole small module read. Exactly complete, rejected and valid child raw-empty receipts advance.'),
('SourcePruningEnumerationNativeBranchCoverage',[(37,123),(136,166),(232,276)],'Whole proof reviewed in preceding frozen stage. Current contract and actual transport/index steps reread; no-hook result cannot be used as actual hook-aware run.'),
('SourcePruningEnumerationNativeHeadCoverage',[(39,120),(121,199)],'Whole proof reviewed previously and current acceptance logic reread. Accepted model excludes unsupported/rejected/raw-empty head on the same actual original core.'),
('SourcePruningEnumerationSubtreeEffects',[(29,43)],'Whole small module read. Full actual final Memos and Post restore the same captured cache/metadata; no query-only identification.'),
('SourceCurrentAllocatedPartialInvariant',[(24,84)],'Only Context/Post and composition definitions inspected. Other copied bytes are provenance.')]
rows=[]
for name,spans,scope in spec:
 src=repo/'lean/MicroCFTA'/f'{name}.lean';b=src.read_bytes();ls=b.splitlines(keepends=True);whole='sources/'+src.name;put(whole,b)
 row={'source':str(src),'whole':{'path':whole,'bytes':len(b),'sha256':sha(b)},'review_scope':scope,'cuts':[]}
 for a,z in spans:
  assert z<=len(ls);c=b''.join(ls[a-1:z]);dest=f'cuts/{src.name}.{a}-{z}.txt';put(dest,c);row['cuts'].append({'path':dest,'bytes':len(c),'sha256':sha(c),'first_line':a,'last_line':z})
 rows.append(row)
put('source-index.json',json.dumps({'sources':rows},indent=2)+'\n')
draft=out/'drafts/v1/SourcePruningEnumerationContinuationInvocation.lean';b=draft.read_bytes()
put('drafts/v1/status.json',json.dumps({'status':'UNTESTED BY REVIEWER; Root owns compiler checks','path':str(draft.relative_to(out)),'bytes':len(b),'lines':len(b.splitlines()),'sha256':sha(b),'public_name':'SourcePruningEnumerationNativeContinuations.complete_prefix_invocation','input_scope':'Literal actual prefix completion and next actual complete captured edge at the same bounds; generic structural helper, not producer admission.','length_helper':'Not added. Sibling owner derives prefix processed length directly by its actual induction.'},indent=2)+'\n')
print(json.dumps({'status':'PASS','whole_inputs':len(rows),'literal_cuts':sum(len(r['cuts']) for r in rows),'draft_sha256':sha(b)}))
