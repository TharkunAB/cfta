from pathlib import Path
import hashlib,json,shutil,datetime
root=Path('/home/tritlo/Code/mcfta')
base=Path('/tmp/mcfta-incoming-coverage-20261027/incoming')
stage=base.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
records=[]
def capture(path,rel,kind='whole',first=None,last=None):
    data=path.read_bytes()
    if kind=='cut': data=b''.join(data.splitlines(keepends=True)[first-1:last])
    out=base/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
    record={'source':str(path),'snapshot':rel,'bytes':len(data),'sha256':sha(data),'kind':kind}
    if kind=='cut':record.update(first_line=first,last_line=last,source_bytes=path.stat().st_size,source_sha256=sha(path.read_bytes()))
    records.append(record)
    return record
sources={
'SourcePruningEnumerationIncomingBranchesLanguage.lean':[(32,118),(119,172)],
'SourcePruningEnumerationIncomingNodeResources.lean':[(34,71),(167,239)],
'SourcePruningEnumerationIncomingNodeLanguage.lean':[(35,105),(106,159)],
'SourcePruningEnumerationIncomingNode.lean':[(29,92),(145,203)]}
for name,cuts in sources.items():
    p=root/'lean/MicroCFTA'/name
    capture(p,'inputs/'+name)
    for a,b in cuts:capture(p,f'cuts/{p.stem}.{a}-{b}.lean.txt','cut',a,b)
p=stage/'strict-incoming-coverage-1'
for name in ['report.json','raw.log','MicroCFTA/SourcePruningEnumerationIncomingCoverage.lean']:
    capture(p/name,'evidence/strict-incoming-coverage-1/'+name)
capture(root/'lean/MicroCFTA/SourcePruningEnumerationIncomingCoverage.lean','installed/SourcePruningEnumerationIncomingCoverage.lean')
proposal=(base/'drafts/v1/SourcePruningEnumerationIncomingCoverage.lean').read_bytes()
assert proposal==(root/'lean/MicroCFTA/SourcePruningEnumerationIncomingCoverage.lean').read_bytes()
report=json.loads((p/'report.json').read_text())
assert report['exit_code']==0 and report['bytes']==0 and report['source_sha256']==sha(proposal)
assert report['cgroup_limits']['memory.max']=='4294967296' and report['cgroup_limits']['memory.swap.max']=='0'
old=(root/'lean/MicroCFTA/SourcePruningEnumerationIncomingBranchesLanguage.lean').read_text()
oldstmt=old[old.index('theorem run_complete_branches'):old.index(' := by',old.index('theorem run_complete_branches'))]
new=proposal.decode()
newstmt=new[new.index('theorem run_complete_accepting'):new.index(' := by',new.index('theorem run_complete_accepting'))]
newheader,newoutput=newstmt.split(' :\n    ∃',1)
oldheader,oldoutput=oldstmt.split(' :\n    ∃',1)
ranges=oldheader[oldheader.index('    (ranges :'):]
recoveredheader=newheader[:newheader.index('    (fits :')]+ranges
recoveredheader=recoveredheader.replace('theorem run_complete_accepting','theorem run_complete_branches',1)
recoveredheader=recoveredheader.replace('    (profile : Profile)\n','',1).replace('Caller (bits + 2)','Caller width')
recoveredoutput=newoutput[:newoutput.index(') ∧\n      replacement ≠ .empty')]
recoveredoutput=recoveredoutput.replace('      ((∀ extra,','      (∀ extra,',1)
recoveredoutput=recoveredoutput.replace('Caller (bits + 2)','Caller width').replace('Checked (bits + 2)','Checked width')
recovered=recoveredheader+' :\n    ∃'+recoveredoutput
assert recovered==oldstmt
for name,data in [('old-full-statement.lean.txt',oldstmt),('recovered-full-statement.lean.txt',recovered)]:
    (base/name).write_text(data)
comparison={'status':'PASS','old_source':str(root/'lean/MicroCFTA/SourcePruningEnumerationIncomingBranchesLanguage.lean'),
 'old_theorem':'MicroCFTA.SourcePruningEnumerationIncomingNode.run_complete_branches',
 'new_theorem':'MicroCFTA.SourcePruningEnumerationIncomingNode.run_complete_accepting',
 'old_statement':{'snapshot':'old-full-statement.lean.txt','bytes':len(oldstmt.encode()),'sha256':sha(oldstmt.encode())},
 'recovered_statement':{'snapshot':'recovered-full-statement.lean.txt','bytes':len(recovered.encode()),'sha256':sha(recovered.encode())},
 'mapping':['Remove ONLY appended replacement nonemptiness, concrete final Satisfies, and stable raw singleton family.',
 'Remove one grouping pair around the entire retained old conjunction; no forall changes scope.',
 'Replace width specialization bits+2 by width in Caller and Checked.',
 'Remove profile, Fits/Room and concrete model inputs; restore the literal original current WordRanges input.',
 'Restore only the original theorem name.'],
 'source_producer_calls':new.count('\n    run_complete_branches '),
 'current_ranges_derivations':new.count('have ranges := initial_ranges')}
assert comparison['source_producer_calls']==1 and comparison['current_ranges_derivations']==1
(base/'contract-comparison.json').write_text(json.dumps(comparison,indent=2)+'\n')
(base/'source-index.json').write_text(json.dumps({'status':'OPEN','line_convention':'one-based inclusive lines; preserve each original line LF when present','records':records},indent=2)+'\n')
print(json.dumps({'sources':len(sources),'literal_cuts':sum(map(len,sources.values())),'records':len(records),'draft_sha256':sha(proposal),'old_statement_bytes':len(oldstmt.encode()),'old_statement_sha256':sha(oldstmt.encode()),'strict':'PASS0/raw0;4GiB/swap0'},indent=2))
