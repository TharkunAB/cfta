from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent
prefix='resource-owner-inherited-progress-'
source=(p/'SourceCurrentResourceOwnerInheritedProgress.lean').read_text()
printer=(p/(prefix+'public-1.source.lean')).read_text()
data=(p/(prefix+'public-1.log')).read_bytes();log=data.decode()
namespace='MicroCFTA.SourceCurrentResourceOwnerInheritedProgress.'
options=['linter.all true','pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254','pp.universes true','pp.deepTerms true','pp.maxSteps 10000000']
assert printer.startswith(source)
for option in options:assert printer.count('set_option '+option)==1
assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
results=[]
for head in ['key_ne_inherited']:
    name=namespace+head
    for directive in ['#check @','#print ','#print axioms ']:assert printer.count(directive+name)==1
    markers=list(re.finditer(r'^(?:@)?'+re.escape(name)+r' :',log,re.M))
    assert len(markers)==1,(head,len(markers))
    checked,printed=log[markers[0].end():].split('\ntheorem '+name+' :',1)
    printed,axiom_text=printed.split("'"+name+"' depends on axioms:",1)
    separators=list(re.finditer(r' :=\n(?=fun\b)',printed));assert len(separators)==1,(head,len(separators))
    declared,proof=printed[:separators[0].start()],printed[separators[0].end():]
    normalize=lambda s:''.join(s.split())
    assert normalize(checked)==normalize(declared),head
    assert '_private' not in checked+declared and len(proof)>1000
    report=re.match(r'\s*\[([^\]]*)\]',axiom_text);assert report
    axioms={re.sub(r'\.\{[^}]*\}','',x.strip())for x in report.group(1).split(',')}
    assert axioms=={'propext','Classical.choice','Quot.sound'},(head,axioms)
    results.append({'head':name,'check_print_type_identity':True,'normalized_type_characters':len(normalize(checked)),'unique_actual_lambda_proof_delimiter':True,'proof_characters':len(proof),'private_public_type_names':False,'actual_axioms':sorted(axioms)})
report={'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'source_lines':len(source.splitlines()),'printer_sha256':hashlib.sha256(printer.encode()).hexdigest(),'log_bytes':len(data),'log_sha256':hashlib.sha256(data).hexdigest(),'all_eight_printer_settings':True,'no_omissions':True,'heads':results,'owned_public_job_exit':json.loads((p/(prefix+'public-1.json')).read_text())['exit_code'],'new_metadata_proof_jobs':0}
print(json.dumps(report,indent=2))
