import os,subprocess
from pathlib import Path
area=Path('/tmp/mcfta-native-selected-step-20261026')
names=[line.removeprefix('#check MicroCFTA.') for line in (area/'public-final/public.lean').read_text().splitlines() if line.startswith('#check MicroCFTA.')]
env=dict(os.environ,XDG_RUNTIME_DIR='/run/user/1000',DBUS_SESSION_BUS_ADDRESS='unix:path=/run/user/1000/bus',HEAVY_PEAKS=str(area/'heavy-peaks'))
raise SystemExit(subprocess.run(['/home/tritlo/Code/heavy-management/bin/capped','--mem','4G','--time','5m','python3',str(area/'check.py'),'public','public-final-2',*names],env=env).returncode)
