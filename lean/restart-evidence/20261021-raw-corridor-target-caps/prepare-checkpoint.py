import hashlib,json,shutil
from pathlib import Path
H=Path(__file__).resolve().parent
R=H.parents[2]
components=json.loads((H/'components.json').read_text())
assert {'raw-corridor','projection-cap','target-cap','class-plan'} <= {x['path'] for x in components} <= {'raw-corridor','projection-cap','target-cap','independent-review','class-plan'}
selected={}
strict={}
for module,directory,selection_name,check in [
    ('SourceCurrentRequiredRawCorridor','raw-corridor','raw-corridor-selection.json','raw-strict-1'),
    ('SourceCurrentRawCorridorProjectionCap','projection-cap','raw-projection-selection.json','projection-strict-1'),
    ('SourceCurrentRawCorridorSharedTargetCap','target-cap','target-selection.json','target-cap/target-direct-1')]:
    source='lean/MicroCFTA/'+module+'.lean'
    selection=json.loads((H/directory/selection_name).read_text())
    digest=hashlib.sha256((R/source).read_bytes()).hexdigest()
    assert digest==selection['source_sha256']
    selected[source]={'sha256':digest}
    strict[source]=check
for name,data in [('selected-sources.json',selected),('frozen-modules.json',{Path(n).stem:e['sha256'] for n,e in selected.items()}),('selected-checks.json',{'strict':strict,'audit':'audit-1'})]:
    (H/name).write_text(json.dumps(data,indent=2)+'\n')
(H/'root-support').mkdir(exist_ok=True)
previous=H/'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-required-shared-target-cap-publication.json','mcfta-required-shared-target-cap-final-publication*','mcfta-required-shared-target-cap-final-push.log','mcfta-required-shared-target-cap-final-remote.txt','mcfta-required-shared-target-cap-board-readback.json','mcfta-required-shared-target-cap-seal-1.*','mcfta-required-shared-target-cap-support-1.*']:
    found=[p for p in Path('/tmp').glob(pattern) if p.is_file()]
    assert found,pattern
    for p in found: shutil.copyfile(p,previous/p.name)
print(json.dumps({'status':'PASS','components':len(components),'new_modules':len(selected)}))
