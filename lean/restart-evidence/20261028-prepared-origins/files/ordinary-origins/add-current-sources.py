from pathlib import Path
import json,hashlib
out=Path('/tmp/mcfta-prepared-origins-20261028/ordinary-origins'); root=Path('/home/tritlo/Code/mcfta')
idx=json.loads((out/'source-index.json').read_text()); existing={r['source'] for r in idx['sources']}
specs=[
('SourcePruningEnumerationTraversalCoverageOrigins.lean',[(1,129),(130,238),(290,415)],'Whole exact candidate source reviewed. Cuts expose retained and appended contracts, actual resource induction and both assignment observers.'),
('SourcePruningEnumerationSelectedEdgeOrigins.lean',[(1,149),(150,270),(271,380),(420,503)],'Whole exact candidate source reviewed. Cuts expose full retained result, origin witness allocation and actual residual finalization.'),
('SourcePruningEnumerationChildCoverageOrigins.lean',[(1,238)],'Whole exact source-reviewed child dependency; actual old observer witness is reused, then terminal counter or fresh +1 shape derives origins.'),
('SourcePruningEnumerationInitialOrigins.lean',[(1,80)],'Whole startup origin proof reviewed; actual counter is one, so accepted root uses empty path.'),
('SourcePruningEnumerationPolicyOrigins.lean',[(1,280)],'Whole policy/callback source reviewed; policies stay an original structural-subtree antecedent and counter framing preserves origins.'),
('SourcePruningProgramSemantics.lean',[(1,39)],'Exact ProgramAt and Avoids definitions reviewed. Other contents unreviewed in this origin assessment.'),
('SourcePruningStructuralTemplateMeaning.lean',[(1,25)],'Exact ProgramEncoding constructors reviewed. Remaining old proof is not a current review claim.')]
for name,spans,scope in specs:
 p=root/'lean/MicroCFTA'/name
 if not p.exists() or str(p) in existing: continue
 b=p.read_bytes(); lines=b.splitlines(keepends=True); dest=out/'sources'/name; dest.write_bytes(b); cuts=[]
 for a,z in spans:
  z=min(z,len(lines)); cb=b''.join(lines[a-1:z]); cp=out/'cuts'/f'{p.stem}-L{a}-L{z}.lean'; cp.write_bytes(cb)
  cuts.append({'path':str(cp.relative_to(out)),'bytes':len(cb),'sha256':hashlib.sha256(cb).hexdigest(),'first_line':a,'last_line':z})
 idx['sources'].append({'source':str(p),'whole':{'path':str(dest.relative_to(out)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'cuts':cuts,'scope':scope})
(out/'source-index.json').write_text(json.dumps(idx,indent=2)+'\n')
print(len(idx['sources']),sum(len(r['cuts']) for r in idx['sources']))
