from pathlib import Path
import hashlib,json,subprocess
r=Path('/home/tritlo/Code/mcfta')
pins=json.loads(Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261115-joint-arrow-bucket-native-universe-publication/source-pins.json').read_text())

for module in ['SourcePruningEnumerationSharedProperPathWitness', 'SourceSynthesisCurrentNativeUniverseMembership']:
    assert all(hashlib.sha256((r/n).read_bytes()).hexdigest()==v for n,v in pins.items())
    subprocess.run(["lake","env","lean","-j1","-DwarningAsError=true","MicroCFTA/"+module+".lean"],check=True)
    assert all(hashlib.sha256((r/n).read_bytes()).hexdigest()==v for n,v in pins.items())
