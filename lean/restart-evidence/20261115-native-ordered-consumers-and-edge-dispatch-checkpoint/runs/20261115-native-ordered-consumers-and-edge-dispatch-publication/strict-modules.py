from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta')
pins=json.loads((Path(__file__).parent/'source-pins.json').read_text())
def verify():
    for path,digest in pins.items():
        assert hashlib.sha256((root/path).read_bytes()).hexdigest()==digest,path
for name in ['SourceCurrentAllocatedNativeSourceOrderedMixedOrdinaryChildQualification', 'SourceCurrentAllocatedNativeOrderedFinitePrefixReferenceControl', 'SourceCurrentAllocatedNativeOrderedMixedReferenceNodeProfile', 'SourceCurrentAllocatedNativeMixedUnionProfile', 'SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin', 'SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions']:
    verify()
    subprocess.run(['lake','env','lean','-j1','-DwarningAsError=true','MicroCFTA/'+name+'.lean'],cwd=root/'lean',check=True)
    verify()
