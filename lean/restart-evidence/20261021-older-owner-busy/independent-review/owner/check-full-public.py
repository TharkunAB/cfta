from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent
prefix='older-owner-busy-'
source=(p/'SourceCurrentOlderOwnerBusy.lean').read_text()
printer=(p/(prefix+'public-1.source.lean')).read_text()
data=(p/(prefix+'public-1.log')).read_bytes();log=data.decode()
namespace='MicroCFTA.SourceCurrentOlderOwnerBusy.'
options=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
assert printer.startswith(source)
for option in options:assert printer.count('set_option '+option)==1
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
results=[]
heads=['no_node_busy']
allmarkers=[]
for head in heads:
 name=namespace+head
 for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+name)==1
 markers=list(re.finditer(r'^(?:@)?'+re.escape(name)+r' :',log,re.M))
 assert len(markers)==1,(head,len(markers))
 allmarkers.append(markers[0])
for index,head in enumerate(heads):
 name=namespace+head
 segment=log[allmarkers[index].end():allmarkers[index+1].start() if index+1<len(heads) else len(log)]
 kind='theorem'
 delimiter='\n'+kind+' '+name+' :'
 assert segment.count(delimiter)==1,(head,'declaration delimiter')
 checked,printed=segment.split(delimiter,1)
 axiom_marker=re.search("'"+re.escape(name)+"' (depends on axioms:|does not depend on any axioms)",printed)
 assert axiom_marker,(head,'axiom report')
 declaration=printed[:axiom_marker.start()]
 axiom_text=printed[axiom_marker.end():]
 separators=list(re.finditer(r' :=\n(?=fun\b)',declaration));assert len(separators)==1,(head,len(separators))
 declared,proof=declaration[:separators[0].start()],declaration[separators[0].end():]
 normalize=lambda s:''.join(s.split())
 assert normalize(checked)==normalize(declared),head
 assert '_private' not in checked+declared and len(proof)>50
 if axiom_marker.group(1)=='depends on axioms:':
  report=re.match(r'\s*\[([^\]]*)\]',axiom_text);assert report
  axioms={re.sub(r'\.\{[^}]*\}','',x.strip())for x in report.group(1).split(',')if x.strip()}
 else:axioms=set()
 assert axioms<={'propext','Classical.choice','Quot.sound'},(head,axioms)
 results.append({'head':name,'kind':kind,'check_print_type_identity':True,'normalized_type_characters':len(normalize(checked)),'unique_actual_lambda_body_delimiter':True,'body_characters':len(proof),'private_public_type_names':False,'actual_axioms':sorted(axioms),'actual_axioms_within_standard_allowed':True})
report={'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'source_lines':len(source.splitlines()),'printer_sha256':hashlib.sha256(printer.encode()).hexdigest(),'log_bytes':len(data),'log_sha256':hashlib.sha256(data).hexdigest(),'all_eight_printer_settings':True,'no_omissions':True,'heads':results,'owned_public_job_exit':json.loads((p/(prefix+'public-1.json')).read_text())['exit_code'],'new_metadata_proof_jobs':0}
print(json.dumps(report,indent=2))
