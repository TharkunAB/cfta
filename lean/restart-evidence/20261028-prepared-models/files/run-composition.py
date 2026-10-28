import subprocess,sys
runner='/tmp/mcfta-prepared-models-20261028/check-installed.py'
for args in [['strict','prefix-preparation-models-v3','SourcePruningEnumerationPreparedPrefixModels'],['strict','sibling-models-v1','SourcePruningEnumerationPreparedFiniteSiblingCoverage']]:
 result=subprocess.run([sys.executable,runner,*args])
 if result.returncode:sys.exit(result.returncode)
