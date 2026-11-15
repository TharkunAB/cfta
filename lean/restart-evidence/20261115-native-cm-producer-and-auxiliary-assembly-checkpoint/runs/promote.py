from pathlib import Path
import hashlib,json,shutil
w=Path(__file__).parent
for item in json.loads((w/'promotion.json').read_text()):
 raw=Path(item['raw']);public=Path('lean/MicroCFTA')/(item['module']+'.lean')
 assert hashlib.sha256(raw.read_bytes()).hexdigest()==item['sha256']
 assert not public.exists()
 shutil.copyfile(raw,public)
