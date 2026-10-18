import hashlib,json,re,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
check=runpy.run_path(str(HERE/'required-projection-verify.py'))
manifest=json.loads((HERE/'required-target-manifest.json').read_text())
for entry in manifest['files']:
 path=ROOT/entry['path']
 assert path.stat().st_size==entry['bytes'],entry['path']
 assert check['sha'](path)==entry['sha256'],entry['path']
selection=json.loads((HERE/'required-target-selection.json').read_text())
assert selection['finalized']
for stem in manifest['attempts']:check['meta'](stem)
assert len(manifest['attempts'])==selection['owned_lean_runs']
for stem,path,expected in [(selection['strict'],ROOT/selection['production'],selection['sha256']),
 (selection['fixture_strict'],ROOT/selection['fixture'],selection['fixture_sha256'])]:
 meta=check['meta'](stem)
 assert meta['exit_code']==0 and (HERE/meta['log']).read_bytes()==b'',stem
 assert check['sha'](path)==expected==check['sha'](HERE/meta['source']),stem
canonical=check['meta'](selection['canonical'])
log=(HERE/canonical['log']).read_text()
assert canonical['exit_code']==0 and 'Build completed successfully' in log
old=(ROOT/'lean/restart-evidence/20261019-mu-source-handoff/full-audit-1.log').read_text()
assert re.findall(r'^warning:.*$',log,re.M)==re.findall(r'^warning:.*$',old,re.M)
for group in selection['groups']:check['group'](group)
print(json.dumps({'status':'PASS','manifest_pins':len(manifest['files']),'public_pairs':1,
 'constructed_pairs':1,'strict_zero_logs':2,'owned_lean_runs':len(manifest['attempts']),
 'actual_required_to_immediate_target_origin':True,'fixture_has_changed_children':True,
 'raw_prefix_paths_not_a_normalized_class':True,'no_generated_child_mass_claim':True}))
