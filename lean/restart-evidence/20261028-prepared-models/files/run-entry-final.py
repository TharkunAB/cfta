import subprocess,sys
runner='/tmp/mcfta-prepared-models-20261028/check-installed.py'
for args in [['strict','entry-models-v3','SourcePruningEnumerationPreparedEntryModels'],['lake','entry-model-update','MicroCFTA.SourcePruningEnumerationPreparedEntryModels'],['strict','prefix-preparation-models-v4','SourcePruningEnumerationPreparedPrefixModels'],['strict','sibling-models-v1','SourcePruningEnumerationPreparedFiniteSiblingCoverage']]:
 r=subprocess.run([sys.executable,runner,*args])
 if r.returncode:sys.exit(r.returncode)
