exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
old = HERE / 'variants/v1' / (NAME + '.lean')
assert sha(old) == 'c735af37e551e4a39fe9ee807fb8433a7709b2f88fc9f9ca0147457926259d76'
text = old.read_text()
before = '(fun value afterBody => work_mono (withoutSelfReference name value) afterBody)'
after = '(fun value after => work_mono (withoutSelfReference name value) after)'
assert text.count(before) == 1
text = text.replace(before, after)
directory = HERE / 'variants/v2'
directory.mkdir(exist_ok=False)
source = directory / (NAME + '.lean')
source.write_text(text)
save('body-v2-provenance.json', dict(status='SELECTED_NOT_COMPILED', source=str(source.relative_to(HERE)),
    source_sha256=sha(source), source_lines=len(text.splitlines()), previous_source_sha256=sha(old),
    patch='Rename the preserved Work continuation binder afterBody to the exact reviewed name after.',
    mathematical_change=False, declaration_change=False, compiler_runs=0,
    source_hard_stop=180, below_soft_target_without_padding=True, goal_status='ACTIVE_INCOMPLETE'))
for file in ['select-body-v2.py', 'body-materializer-review.txt']:
    original = Path('/tmp/mcfta-fresh-node-counter-growth-' + file)
    with (HERE / file).open('xb') as output:
        output.write(original.read_bytes())
print(json.dumps(dict(source=str(source),sha256=sha(source),lines=len(text.splitlines()),compiler_run=False)))
