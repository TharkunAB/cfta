from pathlib import Path
import datetime,hashlib,json,re
A=Path('/tmp/mcfta-worker-arity-20261027')
D=A/'public-metadata-plan'
R=Path('/home/tritlo/Code/mcfta/lean/MicroCFTA')
P=Path('/tmp/mcfta-native-prefix-arity-20261027')
now=datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M:%S %Z')

def digest(data):return hashlib.sha256(data).hexdigest()
def save(source,dest,scope):
 data=source.read_bytes();dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():assert dest.read_bytes()==data,(source,dest,'changed existing snapshot')
 else:dest.write_bytes(data)
 return {'source':str(source),'snapshot':str(dest),'bytes':len(data),'sha256':digest(data),'scope':scope}
def decls(source):
 # Preserve line numbers when removing multiline comments. All declarations in
 # these source files use an explicit declaration keyword on a separate line.
 text=re.sub(r'/\-.*?\-/',lambda m:'\n'*m.group(0).count('\n'),source.read_text(),flags=re.S)
 stack=[];found=[];exports=[]
 for i,line in enumerate(text.splitlines(),1):
  line=line.split('--')[0].strip()
  m=re.match(r'namespace\s+(\S+)',line)
  if m:stack.append(('namespace',m.group(1)));continue
  m=re.match(r'section(?:\s+(\S+))?$',line)
  if m:stack.append(('section',m.group(1) or ''));continue
  if re.match(r'end(?:\s+\S+)?$',line):
   assert stack,(source,i)
   stack.pop();continue
  m=re.match(r'(theorem|lemma|def|structure|inductive|abbrev)\s+([^\s({:\[]+)',line)
  if m:
   found.append({'kind':m.group(1),'name':'.'.join([x[1] for x in stack if x[0]=='namespace']+[m.group(2)]),'first_line':i})
  if line.startswith('export '):exports.append({'line':i,'source_command':line,'counted_as_new_declaration':False})
 assert not stack,(source,stack)
 return found,exports

items=[
 ('GateArity','gate',1),('ProbeExposureArity','probe-exposure',2),('RawRebuildArity','raw-rebuild',1),('CallerArity','caller',1),
 ('ProjectionArity','projection',3),('RequiredArity','required',2),('ConjunctionArity','conjunction',2),('SelectionArity','selection',2),
 ('MergeArity','merge',2),('SeededArity','seeded',3),('ScanArity','scan',1),('SharedTargetArity','shared-target',1),
 ('ClassEditArity','class-edit',2),('ClassPassArity','class-pass',1),('LocalReductionArity','local-reduction',2),('ParentArity','parent',1)
]
modules=[];allTheorems=[];data=[];definitions=[];sources=[]
for suffix,check,plannedAttempt in items:
 module='SourcePruningEnumeration'+suffix
 source=R/(module+'.lean')
 if not source.exists():
  source=A/'parent-arity/drafts/v1'/(module+'.lean') if suffix=='ParentArity' else A/(module+'.lean')
 assert source.exists(),source
 record=save(source,D/'sources'/(module+'.lean'),'whole canonical or installed source identity; declaration enumeration only')
 found,exports=decls(source)
 theorem=[x for x in found if x['kind'] in ('theorem','lemma')]
 for x in found:
  lines=source.read_bytes().splitlines(keepends=True);start=x['first_line']-1
  end=start
  while end<len(lines):
   # Public source header ends before its proof body or definition value.
   if b':=' in lines[end] or (x['kind']=='structure' and b'where' in lines[end]):break
   end+=1
  assert end<len(lines),(source,x)
  header=b''.join(lines[start:end+1])
  dest=D/'declarations'/(x['name']+'.txt');dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():assert dest.read_bytes()==header
  else:dest.write_bytes(header)
  x.update(last_line=end+1,snapshot=str(dest),bytes=len(header),sha256=digest(header))
  if x['kind'] in ('structure','inductive'):data.append(x['name'])
  elif x['kind'] in ('def','abbrev'):definitions.append(x['name'])
 allTheorems.extend(x['name'] for x in theorem)
 checks=[]
 for folder in sorted(A.glob('strict-'+check+'-arity-*')):
  reportPath=folder/'report.json'
  if not reportPath.exists():continue
  report=json.loads(reportPath.read_text());raw=(folder/'raw.log').read_bytes()
  assert len(raw)==report['bytes'] and digest(raw)==report['sha256'],folder
  snapshot=folder/'MicroCFTA'/(module+'.lean')
  checks.append({'folder':str(folder),'exit_code':report['exit_code'],'source_sha256':report.get('source_sha256'),
    'raw_bytes':len(raw),'raw_sha256':digest(raw),'matches_selected_source':snapshot.exists() and snapshot.read_bytes()==source.read_bytes(),
    'report':str(reportPath)})
 finalPass=[c for c in checks if c['exit_code']==0 and c['matches_selected_source']]
 proposed=A/('strict-'+check+'-arity-'+str(plannedAttempt))
 modules.append({'module':module,'fully_qualified_module':'MicroCFTA.'+module,'source':record,
   'line_count':len(source.read_bytes().splitlines()),'theorems':theorem,'other_public_declarations':[x for x in found if x not in theorem],
   'exported_aliases_not_counted':exports,'observed_strict_checks':checks,
   'strict_check_folder':finalPass[-1]['folder'] if finalPass else str(proposed),
   'strict_mapping_status':'ACTUAL PASS; source snapshot equal' if finalPass else 'ANTICIPATED final check; not asserted to have run or passed',
   'final_three_mapping':suffix in ['ClassPassArity','LocalReductionArity','ParentArity']})
 sources.append(record)

old=json.loads((P/'prior-public-declarations.json').read_text())
extra=['SourcePruningEnumerationNativePrefixArity.node_query_execute_heap','SourcePruningEnumerationNativePrefixArity.edge_query_execute_heap','SourcePruningEnumerationNativePrefixArity.node_execute_edge_memo_fits']
assert len(old)==9
retained=['MicroCFTA.'+n for n in old+extra]
raw=(P/'public-readback-final-1/raw.log').read_bytes()
report=json.loads((P/'public-readback-final-1/report.json').read_text())
assert report['exit_code']==0 and len(raw)==report['bytes'] and digest(raw)==report['sha256']
for name in ['raw.log','report.json','public.lean']:
 sources.append(save(P/'public-readback-final-1'/name,D/'prior-public'/name,'whole prior actual public readback evidence'))
sources.append(save(P/'prior-public-declarations.json',D/'prior-public/prior-public-declarations.json','whole prior exact retained-nine list'))
lines=raw.splitlines(keepends=True);retainedBlocks=[]
for name in retained:
 matches=[i for i,l in enumerate(lines) if l.startswith((name+' ').encode()) or l.rstrip(b'\r\n')==name.encode()]
 assert len(matches)==1,(name,matches)
 start=matches[0];end=next((j for j in range(start+1,len(lines)) if lines[j].startswith(b'MicroCFTA.')),len(lines))
 block=b''.join(lines[start:end]);assert ("'"+name+"' depends on axioms:").encode() in block
 dest=D/'prior-public/blocks'/(name+'.txt');dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():assert dest.read_bytes()==block
 else:dest.write_bytes(block)
 retainedBlocks.append({'name':name,'source':str(P/'public-readback-final-1/raw.log'),'first_line':start+1,'last_line':end,
    'snapshot':str(dest),'bytes':len(block),'sha256':digest(block),'scope':'literal complete theorem signature and axiom block'})
assert len(modules)==16 and len(allTheorems)==79 and len(set(allTheorems))==79
assert data==['MicroCFTA.SourcePruningEnumerationSelectionArity.Effect']
assert definitions==['MicroCFTA.SourcePruningEnumerationSelectionArity.Callback']
plan={'schema':'independent public metadata plan; does not replace running root metadata','measured_time':now,
 'scope':'Exact source declaration enumeration and strict mapping. This plan does not claim a new compiler/public run.',
 'counts':{'new_modules':16,'new_public_theorems':79,'retained_previous_theorems':12,'planned_total_theorem_signatures':91,
  'new_data_structures':1,'separate_public_predicate_definitions':1,'source_lines':sum(m['line_count'] for m in modules)},
 'modules':modules,'public_declarations':allTheorems+retained,
 'public_declarations_without_MicroCFTA':[n.removeprefix('MicroCFTA.') for n in allTheorems+retained],
 'new_data_declarations':data,'separate_public_predicate_definitions':definitions,
 'retained_previous_theorems':retained,'retained_previous_literal_blocks':retainedBlocks,
 'prior_public_identity':{'source':str(P/'public-readback-final-1/raw.log'),'bytes':len(raw),'sha256':digest(raw)},
 'cut_convention':'One-based inclusive lines; splitlines(keepends=True); preserve original LF. Public declaration headers include the final := line.',
 'input_sources':sources,
 'notes':['ClassPassArity declarations remain in the ClassEditArity namespace.',
  'SharedTargetArity adds declarations in three namespaces; none is inferred from its module filename.',
  'Gate Primary and Secondary names remain distinct.',
  'Selection Callback is a public predicate definition. It is not counted as a structure.',
  'Export aliases are excluded from new declaration and data counts.',
  'Anticipated final check folders require actual terminal receipt validation before publication.']}
path=A/'public-metadata-plan.json'
assert not path.exists(),'Do not overwrite an earlier independent plan; preserve a revision instead.'
path.write_text(json.dumps(plan,indent=2)+'\n')
print(json.dumps({'path':str(path),'sha256':digest(path.read_bytes()),'counts':plan['counts'],
 'final_three':[{k:m[k] for k in ['module','strict_check_folder','strict_mapping_status']} for m in modules if m['final_three_mapping']]},indent=2))
