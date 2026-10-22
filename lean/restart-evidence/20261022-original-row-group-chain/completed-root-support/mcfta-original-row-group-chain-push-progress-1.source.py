import datetime
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

ROOT = Path('/home/tritlo/Code/mcfta')
HERE = ROOT / 'lean/restart-evidence/20261022-original-row-group-chain'
target = Path('/tmp/mcfta-original-row-group-chain-approved-publications')
assert not target.exists()
target.mkdir()
paths = [Path('/tmp/mcfta-original-row-deletion-soundness-approved-push-20261022-2115.json'),
         Path('/tmp/mcfta-original-row-cluster-approved-push.json'),
         Path('/tmp/mcfta-original-row-cluster-approved-push.network.log'),
         Path('/tmp/mcfta-prepend-grouping-authorized-push.json'),
         Path('/tmp/mcfta-prepend-grouping-authorized-push.network.log')]
for stem in ['mcfta-original-row-group-chain-approved-eight-push-1', 'mcfta-original-row-group-chain-standing-push-1']:
    for suffix in ['.json', '.log', '.limits.json', '.peaks.txt', '.source.py', '.usage.json']:
        paths.append(Path('/tmp/' + stem + suffix))
for path in paths:
    shutil.copyfile(path, target / path.name)
for name in ['mcfta-original-row-cluster-approved-push.json', 'mcfta-prepend-grouping-authorized-push.json']:
    assert json.loads((target / name).read_text())['status'] == 'PUSHED_AND_REMOTE_VERIFIED'
subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(target), 'approved-publications'], check=True)
full = Path('/tmp/mcfta-original-row-group-chain-full-preparation')
for pin in json.loads((full / 'pins.json').read_text()):
    data = (full / pin['path']).read_bytes()
    assert len(data) == pin['bytes'] and hashlib.sha256(data).hexdigest() == pin['sha256']
subprocess.run(['/usr/bin/python3', str(HERE / 'archive-extra.py'), str(full), 'full-preparation'], check=True)
now = datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')
with (HERE / 'current-progress.md').open('a') as out:
    out.write(f'\n## Reviewed declarations and completed publication\n\nUpdated: {now}.\n\n')
    out.write('The exact H22 declaration gate passes. One public groups_complete theorem,\n')
    out.write('one private bucket_readback helper and one generalized local complete statement\n')
    out.write('are authorized for a260–330-line proposal with a350-line hard stop.\n')
    out.write('Root and independent review retain all23 source identities and42 API cuts.\n')
    out.write('The fixed full iterator supplies remaining-entry membership; the tail is not\n')
    out.write('assumed to iterate the full map. Actual body construction is now authorized.\n')
    out.write('No H22 proof command or proof success is claimed yet.\n\n')
    out.write('The user approved the exact8 commits through d0cf685f46. Their push passes\n')
    out.write('and the remote tip was verified. The user then explicitly authorized\n')
    out.write('continued pushes to formalize. The two verified H21 commits also pass\n')
    out.write('push and remote verification at70787b95484cb69897bc4075858e07c7f9c22433.\n')
    out.write('All committed work is published at this cut. H22 remains uncommitted.\n')
    out.write('Root may publish future verified checkpoints under this authorization.\n')
    out.write('The checkpoint publisher itself remains a local-only, network-free tool.\n')
    out.write('No board post or Haskell change is made. The whole goal stays active.\n')
print(json.dumps({'status':'PASS', 'approved_published_tip':'70787b95484cb69897bc4075858e07c7f9c22433', 'H22_proof_jobs':0}))
