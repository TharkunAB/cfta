import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
result = subprocess.run(['/usr/bin/python3', str(HERE / 'cold-finite-calls-check-full-public.py')],
    cwd='/', capture_output=True, text=True)
(HERE / 'full-reader-1.stdout').write_text(result.stdout)
(HERE / 'full-reader-1.stderr').write_text(result.stderr)
assert result.returncode == 0, result.stderr
report = json.loads(result.stdout)
assert report['source_sha256'] == '__H6_SOURCE_SHA__'
assert report['source_lines'] == int('__H6_SOURCE_LINES__') and len(report['heads']) == 1
log = (HERE / 'cold-finite-calls-public-1.log').read_text()
name = 'MicroCFTA.SourceCurrentColdFiniteWarmCalls.constructed_node_calls'
marker = re.search(r'^(?:@)?' + re.escape(name) + r' :', log, re.M)
assert marker
checked, rest = log[marker.end():].split('\ntheorem ' + name + ' :', 1)
assert len(checked) == report['heads'][0]['checked_type_characters']
matches = [m for m in re.finditer(r' :=\n', rest)
    if ''.join(rest[:m.start()].split()) == ''.join(checked.split())]
assert len(matches) == 1
declared = rest[:matches[0].start()]
report['heads'][0]['check_print_type_byte_identity'] = checked == declared
(HERE / 'cold-finite-constructed_node_calls-public-type.txt').write_text(checked)
(HERE / 'cold-finite-constructed_node_calls-printed-public-type.txt').write_text(declared)
(HERE / 'cold-finite-full-readback.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
