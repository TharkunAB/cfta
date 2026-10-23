exec(compile(open('/tmp/mcfta-fresh-node-counter-growth-root-common.py').read(), '/tmp/mcfta-fresh-node-counter-growth-root-common.py', 'exec'))
import datetime
packages = [
    ('mcfta-next-node-counter-producer-assessment', 'counter-producer-assessment',
     'dbf84070734ae4b3b74e5eaf1f9af9506b0f3fe7c5c8a77b4c4d9d6cc02331ae',
     '838627035f544e6d6a521020ae7683e0cb3c149257fe3a835b204bd15774732f'),
    ('mcfta-next-constructor-counter-boundary-review', 'counter-boundary-review',
     '614b863250c019bc4bf8148facf8fc7956d7c149f3dabf2e05bff4db8b1acca7',
     '4fc6c88e077c1c82dde2d4ae4cae43da6486d322e2fde430d596286a9a691620')]
for source, target, pins, frozen in packages:
    owner = Path('/tmp') / source
    checked_package(owner, pins, frozen)
    archive(owner, target)
assert sha(HERE / 'counter-producer-assessment/note.md') == '4a337e023d48033d21d492ade7846b990c191f042da0c2e7a1a3e2206fff64ed'
assert sha(HERE / 'counter-boundary-review/review.json') == 'ebd3d1d81ff6233f89743712fc01cf9dde3be9e2411ca553dee59227182be9fc'
plan = Path('/tmp/mcfta-fresh-node-counter-growth-root-plan.md')
assert not (HERE / 'root-plan.md').exists()
(HERE / 'root-plan.md').write_bytes(plan.read_bytes())
save('root-initial-scope.json', dict(status='ACCEPTED_SOURCE_ONLY_SCOPE_BEFORE_EXACT_DECLARATION_DESIGN',
    observed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(), module=NAME,
    public_heads=['build_mono', 'buildMany_mono', 'buildEdges_mono'], private_helpers_max=3,
    target_source_lines=[120,155], whole_source_hard_stop=180, root_plan_sha256=sha(plan),
    repaired_executor_required=True, actual_done_and_pending_required=True,
    public_Dense_Valid_Facts_Good_success_or_counter_premises_authorized=False,
    exact_callback_and_mutual_IH_type_review_required_before_body=True,
    declaration_design_authorized=True, body_or_compiler_authorized=False,
    previous_checkpoint_pushed_and_remote_verified=START, goal_status='ACTIVE_INCOMPLETE'))
print('Accepted source-only node-counter scope and archived both assessments. Exact declaration review must precede a body.')
