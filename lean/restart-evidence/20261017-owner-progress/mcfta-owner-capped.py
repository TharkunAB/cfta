import os,json
from pathlib import Path
relative=Path('/proc/self/cgroup').read_text().split('0::',1)[1].splitlines()[0]
base=Path('/sys/fs/cgroup')/relative.lstrip('/')
limits={key:(base/key).read_text().strip() for key in ['memory.max','memory.high','memory.swap.max']}
Path(os.environ['OWNER_LIMITS']).write_text(json.dumps(limits,indent=2)+'\n')
assert limits=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'},limits
os.execv('/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean',['lean','-Dlinter.all=true',os.environ['OWNER_SOURCE']])
