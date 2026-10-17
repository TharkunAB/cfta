#!/usr/bin/env python3
"""Verify the frozen rich edit component and its standalone proof evidence."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent
EXPECTED = '7ec01755bdb82e1d38bb008d9a51213f855b130d01153b96a0b98c9108b11b13'
SOURCE = ROOT / 'lean/MicroCFTA/SourceCurrentConstrainedCapRichEditSupport.lean'


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def probe(source_name: str, log_name: str, names: list[str]) -> None:
    source = (EVIDENCE / source_name).read_text()
    log = (EVIDENCE / log_name).read_text()
    options = ['linter.all true', 'pp.explicit true', 'pp.proofs true',
               'pp.universes true', 'pp.deepTerms true',
               'pp.maxSteps 1000000', 'pp.fullNames true']
    for option in options:
        assert f'set_option {option}' in source, (source_name, option)
    assert source.count('#print axioms ') == len(names), source_name
    assert source.count('#check @') == len(names), source_name
    assert not re.search(r'error:|error\(|warning:|sorryAx|declaration uses|truncated', log), log_name
    axioms = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(axioms) == len(names), (log_name, len(axioms))
    assert [name for name, _ in axioms] == names, log_name
    for name, used in axioms:
        atoms = [re.sub(r'\.\{[^}]*\}', '', atom.strip()) for atom in used.split(',') if atom.strip()]
        assert set(atoms) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, atoms)
        assert re.search(r'^@?' + re.escape(name) + r'\s*:', log, re.M), (log_name, name)
        assert f'#check @{name}' in source, name


def main() -> None:
    assert digest(SOURCE) == EXPECTED
    assert SOURCE.read_bytes() == (EVIDENCE / 'rich-edit-final.source.lean').read_bytes()
    assert SOURCE.read_bytes() == (EVIDENCE / 'rich-edit-direct-3.source.lean').read_bytes()
    assert not (EVIDENCE / 'rich-edit-direct-3.log').read_bytes()
    assert 'Build completed successfully (1386 jobs).' in (EVIDENCE / 'rich-edit-build.log').read_text()
    probe('rich-edit-public.lean', 'rich-edit-public-1.log', [
        'MicroCFTA.SourceCurrentConstrainedCapRichEditSupport.' + name
        for name in ['node', 'children', 'rows', 'list']])
    probe('rich-edit-kernels.lean', 'rich-edit-kernels-4.log', [
        'MicroCFTA.RichEditChecks.actual_leaf', 'MicroCFTA.RichEditChecks.two_edits'])
    assert (EVIDENCE / 'rich-edit-public.lean').read_bytes() == (EVIDENCE / 'rich-edit-public-1.source.lean').read_bytes()
    assert (EVIDENCE / 'rich-edit-kernels.lean').read_bytes() == (EVIDENCE / 'rich-edit-kernels-4.source.lean').read_bytes()
    for kind, count in [('direct', 3), ('kernels', 4)]:
        for number in range(1, count + 1):
            assert (EVIDENCE / f'rich-edit-{kind}-{number}.log').is_file()
            assert (EVIDENCE / f'rich-edit-{kind}-{number}.source.lean').is_file()
    manifest_path = EVIDENCE / 'rich-edit-manifest.json'
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text())
        for entry in manifest['files']:
            path = ROOT / entry['path']
            assert path.is_file(), str(path)
            assert digest(path) == entry['sha256'], str(path)
    print('PASS: frozen source; direct and canonical builds; 4 public + 2 integration pairs; standard axioms; complete signatures; preserved attempts; manifest hashes.')


if __name__ == '__main__':
    main()
