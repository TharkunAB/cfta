import json,subprocess
from pathlib import Path
root=Path('/home/tritlo/Code/mcfta')
commands=[['/home/tritlo/.cabal/bin/fourmolu','--mode','check','cfta-generator/src/Data/CFTA/Gen/Typing.hs'],['/home/tritlo/.cabal/bin/cabal-gild','--mode=check','cfta-generator/cfta-generator.cabal']]
reports=[]
for command in commands:
 result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 reports.append({'command':command,'exit_code':result.returncode,'output':result.stdout})
print(json.dumps({'checks':reports},indent=2))
