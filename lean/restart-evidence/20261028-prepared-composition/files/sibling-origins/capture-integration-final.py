from pathlib import Path
import hashlib,json
stage=Path('/tmp/mcfta-prepared-composition-20261028');own=stage/'sibling-origins'
def sha(b):return hashlib.sha256(b).hexdigest()
validation=json.loads((stage/'source-validation.json').read_text());records=[]
for rec in validation['commands']:
    name=rec['folder'];source=stage/name
    # Reuse complete owner check copies where present. Preserve other commands below integration.
    dest=(own/'checks'/name) if (own/'checks'/name).exists() else own/'integration'/name
    for src in sorted(source.rglob('*')):
        if src.is_file() and src.suffix not in ['.olean','.ilean']:
            dst=dest/src.relative_to(source);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
    b=(dest/'raw.log').read_bytes();report=json.loads((dest/'report.json').read_text())
    assert len(b)==rec['bytes'] and sha(b)==rec['sha256'] and report['exit_code']==rec['exit_code']
    records.append({**rec,'copy':str(dest.relative_to(own)),'inherited':name=='prior-public-readback'})
for src in sorted((stage/'parent-v1').rglob('*')):
    if src.is_file() and src.suffix not in ['.olean','.ilean']:
        dst=own/'checks/parent-v1'/src.relative_to(stage/'parent-v1');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
(own/'command-index-final.json').write_text(json.dumps({'commands':records,'current_commands':sum(not r['inherited'] for r in records),'inherited_commands':sum(r['inherited'] for r in records),'current_failed_compiler_commands':sum(not r['inherited'] and r['exit_code']!=0 for r in records),'precompiler_launch_failure':'checks/parent-v1/launch-failure.json','owner_actual_compiler_commands':0,'read_scope':'Owner source checks, both module builds, complete assigned public outputs and both Audit outputs reviewed. Other current compiler failures are preserved whole and classified from actual reports; Root reports full failure-log review. No owner claim to reread every unrelated failed log.'},indent=2)+'\n')
print(json.dumps({'copied_commands':len(records),'current':sum(not r['inherited'] for r in records),'inherited':sum(r['inherited'] for r in records),'current_failures':sum(not r['inherited'] and r['exit_code']!=0 for r in records)},indent=2))
