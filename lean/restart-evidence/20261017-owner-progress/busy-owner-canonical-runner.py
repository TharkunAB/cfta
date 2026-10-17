import json,os
from pathlib import Path
relative=Path('/proc/self/cgroup').read_text().split('0::',1)[1].splitlines()[0]
base=Path('/sys/fs/cgroup')/relative.lstrip('/')
limits={key:(base/key).read_text().strip() for key in ['memory.max','memory.high','memory.swap.max']}
print(json.dumps(limits),flush=True)
assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},limits
os.execv('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake',['lake','-d','/home/tritlo/Code/mcfta/lean','build','MicroCFTA.SourceCurrentOuterBusyOwners'])
