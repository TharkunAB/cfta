"""Verify exact read-only review inputs and the frozen component evidence."""
from pathlib import Path
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
pins = json.loads((HERE / 'independent-mu-active-review-pins.json').read_text())
for entry in pins['files']:
    data = (ROOT / entry['path']).read_bytes()
    assert len(data) == entry['bytes'], entry['path']
    assert hashlib.sha256(data).hexdigest() == entry['sha256'], entry['path']
subprocess.run(['python3', str(HERE / 'mu-active-child-verify.py')], check=True)
print(f"PASS: {len(pins['files'])} independent review pins; production unchanged; no repeated Lean execution.")
