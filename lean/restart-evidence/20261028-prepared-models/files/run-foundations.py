import subprocess,sys
runner='/tmp/mcfta-prepared-models-20261028/check-installed.py'
commands=[['strict','callback-models-v2','SourcePruningEnumerationPreparedCallbackModels'],['strict','head-models-v3','SourcePruningEnumerationPreparedFiniteHeadCoverage'],['lake','model-foundations','MicroCFTA.SourcePruningEnumerationPreparedEntryModels','MicroCFTA.SourcePruningEnumerationPreparedFiniteHeadCoverage','MicroCFTA.SourcePruningEnumerationPreparedCallbackModels','MicroCFTA.SourcePruningEnumerationPreparedOpaqueModels'],['strict','prefix-preparation-models-v1','SourcePruningEnumerationPreparedPrefixModels']]
for c in commands:
 r=subprocess.run([sys.executable,runner,*c])
 if r.returncode:sys.exit(r.returncode)
