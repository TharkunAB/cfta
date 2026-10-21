import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
result = subprocess.run(['/usr/bin/python3', str(HERE / 'warm-packet-check-full-public.py')],
    cwd='/', capture_output=True, text=True)
(HERE / 'full-reader-1.stdout').write_text(result.stdout)
(HERE / 'full-reader-1.stderr').write_text(result.stderr)
assert result.returncode == 0, result.stderr
report = json.loads(result.stdout)
assert report['source_sha256'] == '13e8373cff925aca8832a47e12514767dd94dbe3fdb8d68bd73b2cdf19246be8'
assert report['source_lines'] == 117 and len(report['heads']) == 1
log = (HERE / 'warm-packet-public-1.log').read_text()
name = 'MicroCFTA.SourceCurrentWarmNextPacket.node_call'
marker = re.search(r'^(?:@)?' + re.escape(name) + r' :', log, re.M)
assert marker
checked = log[marker.end():].split('\ntheorem ' + name + ' :', 1)[0]
assert len(checked) == report['heads'][0]['checked_type_characters']
(HERE / 'warm-node_call-public-type.txt').write_text(checked)
(HERE / 'warm-full-readback.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
