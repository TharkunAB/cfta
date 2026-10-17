#!/usr/bin/env python3
"""Check the final independent Required and class-pass evidence."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
SOURCES = [
    ('forest', 'SourceCurrentConstrainedCapForestSupport.lean', '8291316038d755194899bad2414e3b2ae954838213acdfb9e2b3bdedd84d026a'),
    ('completion', 'SourceCurrentConstrainedCapRichRequiredCompletion.lean', '204f6acd9f3839179123ff26788dc9957a2f4d5a8b2b1a203dc9cae0b567c347'),
    ('required-pass', 'SourceCurrentConstrainedCapRichRequiredClassPass.lean', '45f39b756b8e6d30e72a3ac0851f6aeaedf8f1a748b4885e067a2c452c0848d3'),
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def probes(kind: str, names: list[str]) -> None:
    source = (EVIDENCE / f'independent-final-{kind}.lean').read_text()
    log = (EVIDENCE / f'independent-final-{kind}-1.log').read_text()
    assert source == (EVIDENCE / f'independent-final-{kind}-1.source.lean').read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true',
                   'pp.deepTerms true', 'pp.maxSteps 1000000', 'pp.fullNames true']:
        assert f'set_option {option}' in source
    assert source.count('#print axioms ') == len(names)
    assert source.count('#check @') == len(names)
    assert not re.search(r'error:|error\(|warning:|sorryAx|declaration uses|truncated', log)
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    assert [name for name, _ in entries] == names
    for name, axioms in entries:
        used = {re.sub(r'\.\{[^}]*\}', '', atom.strip()) for atom in axioms.split(',') if atom.strip()}
        assert used <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert re.search(r'^@?' + re.escape(name) + r'\s*:', log, re.M)
        assert f'#check @{name}' in source


def main() -> None:
    for label, name, expected in SOURCES:
        path = ROOT / 'lean/MicroCFTA' / name
        assert digest(path) == expected
        assert path.read_bytes() == (EVIDENCE / f'independent-final-{label}.source.lean').read_bytes()
    probes('public', ['MicroCFTA.SourceCurrentConstrainedCapForestSupport.' + name
                      for name in ['trans', 'record_masks', 'closed_domains', 'closed_transport', 'propagate']]
           + ['MicroCFTA.SourceCurrentConstrainedCapRichRequiredCompletion.complete',
              'MicroCFTA.SourceCurrentConstrainedCapRichRequiredClassPass.verified'])
    probes('kernels', ['MicroCFTA.IndependentFinalRichKernels.required_then_pass'])
    for name, jobs in [('rich-final-build.log', 1427), ('rich-required-completion-build.log', 1344)]:
        assert f'Build completed successfully ({jobs} jobs).' in (EVIDENCE / name).read_text()
    manifest_path = EVIDENCE / 'independent-final-manifest.json'
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text())
        for entry in manifest['files']:
            path = ROOT / entry['path']
            assert path.is_file() and digest(path) == entry['sha256'], str(path)
    print('PASS: 3 exact final source hashes; 7 public + 1 constructive-prefix integration pairs; full signatures; standard axioms; canonical logs; manifest hashes.')


if __name__ == '__main__':
    main()
