#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument('--root',default='/home/tritlo/Code/mcfta');a=p.parse_args()
here=Path(__file__).resolve().parent
manifest=json.loads((here/'mcfta-native-optional-owner-attachment-review-source-pins.json').read_text())
checked=0
for section in ('files','external_files'):
 for item in manifest[section]:
  path=(Path(a.root)/item['path']) if section=='files' else Path(item['path'])
  b=path.read_bytes()
  assert len(b)==item['bytes'],str(path)+' size mismatch'
  assert hashlib.sha256(b).hexdigest()==item['sha256'],str(path)+' hash mismatch'
  checked+=1
print(json.dumps({'status':'PASS','checked_files':checked,'new_lean_jobs':0,'new_proof_pairs':0,'scope':'design-only audit; proposed theorem unproved'},indent=2))
