import MicroCFTA.SourceEqualityNativeCheckedWidth

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

#print axioms MicroCFTA.SourceEqualityNativeCheckedWidth.children_at
#check @MicroCFTA.SourceEqualityNativeCheckedWidth.children_at
#print axioms MicroCFTA.SourceEqualityNativeCheckedWidth.sentinel_at
#check @MicroCFTA.SourceEqualityNativeCheckedWidth.sentinel_at
#print axioms MicroCFTA.SourceEqualityNativeCheckedWidth.body_at
#check @MicroCFTA.SourceEqualityNativeCheckedWidth.body_at
#print axioms MicroCFTA.SourceEqualityNativeCheckedWidth.body_bind_at
#check @MicroCFTA.SourceEqualityNativeCheckedWidth.body_bind_at
