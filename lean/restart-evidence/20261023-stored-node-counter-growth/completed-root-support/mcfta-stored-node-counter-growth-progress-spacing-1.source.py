exec(compile(open('/tmp/mcfta-stored-node-counter-growth-root-common.py').read(), '/tmp/mcfta-stored-node-counter-growth-root-common.py', 'exec'))
path = HERE / 'current-progress.md'
original = path.read_text()
changed = original
pairs = [('same82', 'same 82'), ('passed3653', 'passed 3653'), ('and75553', 'and 75553'),
    ('all37', 'all 37'), ('lines:13,12,12', 'lines: 13, 12, 12'), ('The12', 'The 12'),
    ('all63534', 'all 63534'), ('has3', 'has 3'), ('jobs,2', 'jobs, 2'), ('jobs,1', 'jobs, 1'),
    ('retains1 variant', 'retains 1 variant'), ('variant,0', 'variant, 0'), ('and856', 'and 856'),
    ('retains13', 'retains 13'), ('has404', 'has 404'), ('and212', 'and 212'), ('with483', 'with 483'),
    ('covers116844', 'covers 116844'), ('files/modes,3651', 'files/modes, 3651'),
    ('sources,298', 'sources, 298'), ('and207', 'and 207'), ('checks318', 'checks 318'),
    ('registries,1414', 'registries, 1414')]
for before, after in pairs:
    assert changed.count(before) == 1, before
    changed = changed.replace(before, after, 1)
assert changed.replace(' ', '') == original.replace(' ', '')
draft = HERE / 'history-drafts/progress-spacing-v1'
draft.mkdir()
(draft / 'current-progress.md.txt').write_text(original)
path.write_text(changed)
save('progress-spacing-history.json', dict(status='PROGRESS_SPACING_ONLY', changes=len(pairs),
    original='history-drafts/progress-spacing-v1/current-progress.md.txt',
    original_sha256=sha(draft / 'current-progress.md.txt'), final_sha256=sha(path),
    claims_unchanged=True, mathematical_source_or_jobs_changed=False))
print('Inserted spaces in the progress journal. Retained the exact original text and unchanged claims.')
