import datetime,hashlib,json,re
from pathlib import Path
H=Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261023-original-row-reconstruction')
r=json.loads((H/'original-row-reconstruction-strict-1.json').read_text());raw=(H/r['log']).read_bytes()
assert r['exit_code']==1 and r['sha256']=='31f617cdb892cf7eff50ea6f2aa671cb590b94211615e798bddad90538637276'
assert hashlib.sha256(raw).hexdigest()=='9e4eab7f245e7c14e149222ca0473e02a6faab6b2e73bb1a2797d3963189e0fa'
errors=len(re.findall(r'^.+?:[0-9]+:[0-9]+: error:',raw.decode(),re.M));assert errors==2
report=dict(status='ACTUAL_FAILED_FIRST_STRICT_RETAINED',observed_at=datetime.datetime.now().astimezone().isoformat(),actual_jobs=1,source_jobs=1,audit_jobs=0,failed_jobs=1,errors=2,warnings=0,raw_log_sha256=hashlib.sha256(raw).hexdigest(),source_sha256=r['sha256'],cause='Nested record-field multiline application parsing at lines26 and85. Syntax repair is pending new exact header/body review.',full_jobs=0,official_install=False)
(H/'strict-1-failure-summary.json').write_text(json.dumps(report,indent=2)+'\n')
with (H/'current-progress.md').open('a') as out:
 out.write('\n## First strict parsing failure retained\n\nStrict1 returns1 with two parsing errors at lines26 and85.\nThe nested record-field applications require a syntax repair. No FULL or Audit has run.\nThe exact failed source31f617cd, raw364-byte log9e4eab7f, receipt, limits and fresh usage remain.\nArity is preparing a minimal syntax repair and renewed private/public declaration fragments.\nOriginal frozen packages remain immutable. Root and independent review must precede strict2.\nThe materializer and saved verifier will point to the retained repaired signature before use.\nNo H23 success or official installation is claimed. The whole goal stays ACTIVE.\n')
print(json.dumps(report))
