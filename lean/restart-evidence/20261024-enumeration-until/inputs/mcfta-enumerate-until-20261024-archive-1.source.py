import hashlib, json, shutil
from pathlib import Path

root = Path('/home/tritlo/Code/mcfta')
area = Path('/tmp/mcfta-enumerate-until-20261024')
here = root/'lean/restart-evidence/20261024-enumeration-until'
assert not here.exists()
assert json.loads((area/'preservation.json').read_text())['status'] == 'PASS'
here.mkdir()
shutil.copytree(area, here/'work', ignore=shutil.ignore_patterns('lib'))
for path in Path('/tmp').glob('mcfta-enumerate-until-20261024-*'):
    if path.is_file() and not path.name.startswith('mcfta-enumerate-until-20261024-archive-1.'):
        (here/'inputs').mkdir(exist_ok=True)
        shutil.copy2(path, here/'inputs'/path.name)
prior = here/'prior-refresh-post-seal'
prior.mkdir()
for stem in ['archive-1', 'provenance-1', 'local-publication-1', 'authorized-push-1']:
    for suffix in ['json','log','limits.json','usage.json','source.py','peaks.txt']:
        path = Path('/tmp')/('mcfta-main-refresh-20261024-'+stem+'.'+suffix)
        assert path.is_file(), path
        shutil.copy2(path, prior/path.name)
for name in ['local-publication','remote-publication']:
    path = Path('/tmp')/('mcfta-main-refresh-20261024-'+name+'.json')
    assert path.is_file(), path
    shutil.copy2(path, prior/path.name)
sources = here/'production-sources'
sources.mkdir()
for name in ['EnumerationUntil.lean','EnumerationUntilBridge.lean','Audit.lean']:
    shutil.copy2(root/'lean/MicroCFTA'/name, sources/name)
report = dict(status='PASS', baseline_files=126320,
              source_authorship=dict(operational_definitions='Guard', final_proofs_and_integration='Root',
                                     representative_read_helpers='Arity', independent_final_review='Required'),
              validation_owner='Root', final_source_review_owner='Required', goal='ACTIVE_INCOMPLETE')
(here/'provenance.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(dict(status='PASS', archive=str(here), files=sum(p.is_file() for p in here.rglob('*')))))
