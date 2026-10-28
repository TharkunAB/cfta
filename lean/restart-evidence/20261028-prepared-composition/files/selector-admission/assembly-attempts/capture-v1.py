from pathlib import Path
import json,hashlib
root=Path('/home/tritlo/Code/mcfta');own=Path('/tmp/mcfta-prepared-composition-20261028/selector-admission')
sources=[
('lean/MicroCFTA/SourcePruningEnumerationSelectorLanguage.lean',[(16,51),(54,84)],'whole; mature selector lemmas reused, no duplicate implementation'),
('lean/MicroCFTA/SourcePruningEnumerationSelectedEdgeAdmission.lean',[(18,42),(51,108)],'whole; accepted chosen edge derives real projection and inherited arity'),
('lean/MicroCFTA/SourcePruningEnumerationConstraint.lean',[(9,39)],'whole; source-none means no accepted guard term'),
('lean/MicroCFTA/SourceEqualityGuardReadback.lean',[(15,25),(57,64)],'cached payload definition and source_cached; none is permitted'),
('lean/MicroCFTA/SourceEqualityRequiredCache.lean',[(18,42),(65,73),(93,110)],'whole; readiness and raw constructor preservation'),
('lean/MicroCFTA/SourceEqualityAnnotationHeap.lean',[(14,25),(70,88)],'heap and emitted-guard constructor laws'),
('lean/MicroCFTA/InternedConstructorTemplates.lean',[(228,255)],'literal raw edge and node constructors only'),
('lean/MicroCFTA/SourcePruningEnumerationSelectedValue.lean',[(18,36)],'whole; one Mu unfold, Union reconstruction, ordinary input identity'),
('lean/MicroCFTA/SourcePruningEnumerationSelectedValueInvariants.lean',[(22,48),(76,87)],'whole; arbitrary annotation preservation through actual selected normalization'),
('lean/MicroCFTA/SourcePruningEnumerationCheckedArity.lean',[(9,47),(79,114)],'whole; existing both-branch successful projection result'),
('lean/MicroCFTA/SourceCurrentAllocatedMkEdge.lean',[(35,46),(61,81)],'actual build/reject and retained construction receipt fields'),
('lean/MicroCFTA/SourceCurrentAllocatedParentEdge.lean',[(77,103)],'original Parent receipt construction disjunction and full retained fields'),
('lean/MicroCFTA/SourceEqualityMkEdgeAllocation.lean',[(29,59),(63,71)],'actual accepted and checked source constructor selection'),
('lean/MicroCFTA/SourceEqualityMkEdgeArity.lean',[(26,45)],'fits_exact derives Some source equality classes'),
('lean/MicroCFTA/MergedPhysicalGroupEdges.lean',[(25,40)],'literal makeEdge field equality proof used by raw counterexample'),
('lean/MicroCFTA/SourcePruningEnumerationCachedOwn.lean',[(23,42)],'actual arity/project guard; missing project gives unsupported None'),
('lean/MicroCFTA/SourcePruningEnumerationSelectedEdge.lean',[(70,86)],'actual SelectedEdge.run maps missing own prepare to unhandled'),
('lean/MicroCFTA/SourcePruningEnumerationNativeBranches.lean',[(21,43),(55,64)],'actual advance and prefix stop; later rows are not tried'),
('lean/MicroCFTA/SourcePruningEnumerationNativeParentCoverage.lean',[(158,205)],'existing accepted selector/index composition; no duplicate theorem'),
('cfta/src/Data/CFTA/Constraint.hs',[(117,136),(156,175)],'source contradiction/accessor/residual and positive guards only'),
('cfta/src/Data/CFTA/Equality/Constraint.hs',[(317,336)],'unsafe accessor and explicit contradictory arity rejection'),
('cfta/src/Data/CFTA/Interned/Type.hs',[(388,400),(545,587)],'checked mkEdge, sentinel filter, and equal-arity setChildren source paths'),
('cfta/src/Data/CFTA/Enumeration.hs',[(703,725),(756,788)],'canonical selector and actual enumeration accessor/child calls only'),
]
index=[]
for rel,cuts,scope in sources:
 source=root/rel;b=source.read_bytes();lines=b.splitlines(keepends=True)
 out=own/'sources'/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b)
 rec={'source':str(source),'whole':{'path':str(out.relative_to(own)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'cuts':[],'inspected_scope':scope}
 for first,last in cuts:
  assert 1<=first<=last<=len(lines),(rel,first,last,len(lines))
  cut=b''.join(lines[first-1:last]);p=own/'cuts'/(source.stem+f'.L{first}-{last}.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(cut)
  rec['cuts'].append({'path':str(p.relative_to(own)),'bytes':len(cut),'sha256':hashlib.sha256(cut).hexdigest(),'first_line':first,'last_line':last})
 index.append(rec)
(own/'source-index.json').write_text(json.dumps({'sources':index},indent=2)+'\n')
p=own/'drafts/v1/SourcePruningEnumerationCheckedProjection.lean';b=p.read_bytes()
(own/'draft-status-v1.json').write_text(json.dumps({'status':'UNTESTED by owner','path':str(p),'lines':len(b.splitlines()),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'compiler_owner':'Root','source_or_runtime_mutations_by_owner':False,'scope':'Actual checked-constructor projectability plus actual raw-native ready/annotation counterexample; no full Context/Packet counterexample and no Haskell defect.'},indent=2)+'\n')
print(len(index),sum(len(x['cuts']) for x in index))
