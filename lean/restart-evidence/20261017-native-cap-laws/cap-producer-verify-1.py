#!/usr/bin/env python3
"""Validate the frozen local cap compiler source and proof evidence."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
MODULES = {
    'Scope': ('468d7dc464993e213a625a0e36a032ce44e798171235e86740ed5fdec1b65f1b', 4),
    'Code': ('9934fe5f8bb2e7c029c12086456217242a3b6cf87e30ee0240499ece0d0dad25', 3),
    'Compile': ('7018bb7b6ae03a7ee2a3d6eb7c757880d1d742a377c49a6f906063ef175fa0e3', 1),
    'Edge': ('cfc30060a26d06cee13ea386ef67757635388b1aa150eeac3e75288bf123f175', 1),
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def probes(kind: str, attempt: int, names: list[str]) -> None:
    source = (EVIDENCE / f'cap-producer-{kind}.lean').read_text()
    log = (EVIDENCE / f'cap-producer-{kind}-{attempt}.log').read_text()
    assert source == (EVIDENCE / f'cap-producer-{kind}-{attempt}.source.lean').read_text()
    for option in ['linter.all true', 'pp.explicit true', 'pp.proofs true', 'pp.universes true',
                   'pp.deepTerms true', 'pp.maxSteps 1000000', 'pp.fullNames true']:
        assert f'set_option {option}' in source
    assert source.count('#print axioms ') == len(names)
    assert source.count('#check @') == len(names)
    assert not re.search(r'error:|error\(|warning:|sorryAx|declaration uses|truncated', log)
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.S)
    assert [name for name, _ in entries] == names
    for name, axioms in entries:
        used = {re.sub(r'\.\{[^}]*\}', '', atom.strip()) for atom in axioms.split(',') if atom.strip()}
        assert used <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, used)
        assert re.search(r'^@?' + re.escape(name) + r'\s*:', log, re.M), name
        assert f'#check @{name}' in source


def main() -> None:
    for module, (expected, attempt) in MODULES.items():
        path = ROOT / f'lean/MicroCFTA/SourceCurrentConstrainedCapNative{module}.lean'
        assert digest(path) == expected
        assert path.read_bytes() == (EVIDENCE / f'cap-{module.lower()}-final.source.lean').read_bytes()
        assert path.read_bytes() == (EVIDENCE / f'cap-{module.lower()}-direct-{attempt}.source.lean').read_bytes()
        assert not (EVIDENCE / f'cap-{module.lower()}-direct-{attempt}.log').read_bytes()
    names = json.loads((EVIDENCE / 'cap-producer-public-names.json').read_text())
    assert len(names) == 22
    probes('public', 1, names)
    probes('kernels', 3, ['MicroCFTA.CapNativeProducerChecks.' + name for name in
                          ['empty_rows', 'arbitrary_guard_constructors', 'entered_source_reads']])
    for log, jobs in [('native-scope-build-2.log', 1004), ('native-cache-code-build.log', 1089),
                      ('native-compile-edge-build.log', 1098)]:
        assert f'Build completed successfully ({jobs} jobs).' in (EVIDENCE / log).read_text()
    failed_scope = EVIDENCE / 'cap-scope-direct-3.source.lean'
    assert digest(failed_scope) == '40e11640754459cd9cabe09b421c2c7a4cf90a72f068fb18258e81aa3e259128'
    assert 'error' in (EVIDENCE / 'cap-scope-direct-3.log').read_text()
    assert 'error' in (EVIDENCE / 'native-scope-build.log').read_text()
    manifest_path = EVIDENCE / 'cap-producer-manifest.json'
    if manifest_path.is_file():
        for entry in json.loads(manifest_path.read_text())['files']:
            path = ROOT / entry['path']
            assert path.is_file() and digest(path) == entry['sha256'], str(path)
    print('PASS: 4 exact frozen modules; clean strict direct/canonical checks; 22 public + 3 constructive integration pairs; complete signatures; standard axioms; preserved failures; manifest hashes.')


if __name__ == '__main__':
    main()
