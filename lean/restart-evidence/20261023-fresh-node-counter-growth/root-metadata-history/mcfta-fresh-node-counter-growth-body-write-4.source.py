exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import difflib
gate=load(HERE/'root-declaration-gate-v3.json')
assert gate['body_authoring_authorized'] and not gate['compiler_activation_authorized']
old=HERE/'variants/v3'/(NAME+'.lean')
assert sha(old)=='464dbcf3adbb832a6507510f2497c476b6f3f0b435358068e0e2621eb183f693'
source=old.read_text()
before_plan=HERE/'declaration-plan-v2'
after_plan=HERE/'declaration-plan-v3'
before_layout={r['file']:r for r in load(before_plan/'insertion-map.json')['compiled_fragments']}
after_layout={r['file']:r for r in load(after_plan/'insertion-map.json')['compiled_fragments']}
for file,digest in load(after_plan/'contracts.json').items():
    before=(before_plan/file).read_text()
    after=(after_plan/file).read_text()
    assert sha(after_plan/file)==digest
    if 'future_body_attachment' in before_layout[file]:
        before=before[:-1]+before_layout[file]['future_body_attachment']
        after=after[:-1]+after_layout[file]['future_body_attachment']
    assert source.count(before)==1,file
    source=source.replace(before,after,1)
assert 'omit ' not in source and 'variable [DecidableEq' not in source
assert len(source.splitlines())==117
directory=HERE/'variants/v4'
directory.mkdir(exist_ok=False)
target=directory/(NAME+'.lean')
target.write_text(source)
before='variants/v3/'+NAME+'.lean'
after='variants/v4/'+NAME+'.lean'
patch=''.join(difflib.unified_diff(old.read_text().splitlines(keepends=True),source.splitlines(keepends=True),fromfile=before,tofile=after))
(HERE/'patches/v3-to-v4.patch').write_text(patch)
save('body-v4-provenance.json',dict(status='SELECTED_NOT_COMPILED',source=str(target.relative_to(HERE)),
    source_sha256=sha(target),source_lines=117,previous_source_sha256=sha(old),
    declaration_gate='root-declaration-gate-v3.json',declaration_gate_sha256=sha(HERE/'root-declaration-gate-v3.json'),
    all_six_mathematical_bodies_unchanged=True,only_exact_context_and_header_substitution=True,
    earlier_failed_and_warned_jobs_retained=True,new_helpers_or_local_types=False,
    default_declaration_limits=True,all_linters=True,source_hard_stop=180,goal_status='ACTIVE_INCOMPLETE'))
with (HERE/'write-body-v4.py').open('xb') as output:
    output.write(Path('/tmp/mcfta-fresh-node-counter-growth-write-body-v4.py').read_bytes())
print(json.dumps(load(HERE/'body-v4-provenance.json')))
