from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
packet = root / 'lean/restart-evidence/20261116-real-callback-and-isolation-checkpoint'
assert not subprocess.check_output(['git','ls-files','--',str(packet.relative_to(root))],cwd=root).strip()
assert hashlib.sha256((packet / 'manifest.json').read_bytes()).hexdigest() == '0703885ae586504f964507e578f455721f91f03b0b182b9b54c2a5fde2a27d46'
checkpoint = json.loads((packet / 'checkpoint.json').read_text())
for item in checkpoint['documents']:
    path = root / item['path']
    prior = subprocess.check_output(['git','show',item['prior_commit']+':'+item['path']],cwd=root)
    prefix = gzip.decompress((packet / 'document-prefixes' / (item['path']+'.gz')).read_bytes())
    assert path.read_bytes() == prefix+prior
    path.write_bytes(prior)
for name in ['checkpoint.json','verification.json','manifest.json']:
    (work / ('unpublished-first-pass-'+name+'.gz')).write_bytes(gzip.compress((packet / name).read_bytes(),mtime=0))
(work / 'unpublished-first-pass-note.md.gz').write_bytes((packet / 'checkpoint-note.md.gz').read_bytes())
# This directory contains only rebuildable output from this work directory.
# All proof inputs and check logs remain in their original directories.
shutil.rmtree(packet)
print(json.dumps({'unpublished_derived_archive_reset':True,'original_document_bytes_restored':True,
    'proof_inputs_and_check_logs_retained':True,'reason':'Add the now-terminal full identity check before publication.'}))
