from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta')
pins=json.loads((Path(__file__).parent/"source-pins.json").read_text())
def verify():
    for p,h in pins.items(): assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
for name in ['SourcePruningEnumerationIncomingCacheProtection', 'SourcePruningEnumerationSharedChildIsolation', 'SourcePruningEnumerationPreparedSharedChildIsolation', 'SourcePruningEnumerationSharedChildClassProtection', 'SourcePruningEnumerationSharedChildRetainedProtection', 'SourceCurrentAllocatedNativeContextCache', 'SourceCurrentAllocatedNativeReturnedProperties', 'SourceCurrentAllocatedNativeNodeShortcutFootprints', 'SourceCurrentAllocatedNativeEdgeBodyFootprints']:
    verify()
    subprocess.run(["lake","env","lean","-j1","-DwarningAsError=true",f"MicroCFTA/{name}.lean"],cwd=root/"lean",check=True)
    verify()
