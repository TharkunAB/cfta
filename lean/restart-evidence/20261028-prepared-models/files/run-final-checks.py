import subprocess,sys
runner='/tmp/mcfta-prepared-models-20261028/check-installed.py'
for args in [['lake','audit-build-final-v2','MicroCFTA.Audit'],['strict','audit-strict-final','Audit'],['public','public-readback-final']]:
 r=subprocess.run([sys.executable,runner,*args])
 if r.returncode:sys.exit(r.returncode)
