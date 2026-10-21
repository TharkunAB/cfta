import hashlib
import json
import shutil
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
def write(name,value):
    (HERE/name).write_text(json.dumps(value,indent=2)+'\n')
components=json.loads((HERE/'components.json').read_text())
assert {item['path'] for item in components}=={'scan','independent-review','writer-plan','writer-readiness'}
selection=json.loads((HERE/'scan/scan-stores-selection.json').read_text())
module='SourceCurrentScanNativeStores'
name='lean/MicroCFTA/'+module+'.lean'
digest=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
assert digest==selection['source_sha256']=='1c92862363f0484d5cedb052e90c3b969eeb6d414bf7777ad2e516675625b77e'
write('selected-sources.json',{name:{'sha256':digest}})
write('frozen-modules.json',{module:digest})
write('selected-checks.json',{'scan':{'strict':'scan-strict-1','public':'scan/'+selection['selected_public']},'audit':'audit-1'})
previous=HERE/'previous-publication-support'
previous.mkdir()
for pattern in ['mcfta-scan-publication-intervals-publication.json','mcfta-scan-publication-intervals-final-publication*',
                'mcfta-scan-publication-intervals-final-push.log','mcfta-scan-publication-intervals-final-remote.txt',
                'mcfta-scan-publication-intervals-board-readback.json','mcfta-scan-publication-intervals-seal-1.*',
                'mcfta-scan-publication-intervals-support-1.*']:
    found=[p for p in Path('/tmp').glob(pattern) if p.is_file()]
    assert found,pattern
    for source in found:
        shutil.copyfile(source,previous/source.name)
print(json.dumps({'status':'PASS','components':len(components),'new_modules':1}))
