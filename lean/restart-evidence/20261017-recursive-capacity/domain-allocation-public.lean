import MicroCFTA.CacheFiniteInterning
import MicroCFTA.SourceRecursiveIntersectionDomainAllocation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.CacheFiniteInterning.missing
#check @MicroCFTA.CacheFiniteInterning.missing

#print axioms MicroCFTA.CacheFiniteInterning.missing_le_length
#check @MicroCFTA.CacheFiniteInterning.missing_le_length

#print axioms MicroCFTA.CacheFiniteInterning.missing_mono
#check @MicroCFTA.CacheFiniteInterning.missing_mono

#print axioms MicroCFTA.CacheFiniteInterning.intern_extends
#check @MicroCFTA.CacheFiniteInterning.intern_extends

#print axioms MicroCFTA.CacheFiniteInterning.intern_present
#check @MicroCFTA.CacheFiniteInterning.intern_present

#print axioms MicroCFTA.CacheFiniteInterning.intern_next
#check @MicroCFTA.CacheFiniteInterning.intern_next

#print axioms MicroCFTA.CacheFiniteInterning.intern_hit
#check @MicroCFTA.CacheFiniteInterning.intern_hit

#print axioms MicroCFTA.CacheFiniteInterning.missing_drop
#check @MicroCFTA.CacheFiniteInterning.missing_drop

#print axioms MicroCFTA.CacheFiniteInterning.intern_potential
#check @MicroCFTA.CacheFiniteInterning.intern_potential

#print axioms MicroCFTA.CacheFiniteInterning.Trace
#check @MicroCFTA.CacheFiniteInterning.Trace

#print axioms MicroCFTA.CacheFiniteInterning.Trace.trans
#check @MicroCFTA.CacheFiniteInterning.Trace.trans

#print axioms MicroCFTA.CacheFiniteInterning.Trace.valid
#check @MicroCFTA.CacheFiniteInterning.Trace.valid

#print axioms MicroCFTA.CacheFiniteInterning.Trace.extends
#check @MicroCFTA.CacheFiniteInterning.Trace.extends

#print axioms MicroCFTA.CacheFiniteInterning.Trace.potential
#check @MicroCFTA.CacheFiniteInterning.Trace.potential

#print axioms MicroCFTA.CacheFiniteInterning.Trace.next_le_missing
#check @MicroCFTA.CacheFiniteInterning.Trace.next_le_missing

#print axioms MicroCFTA.CacheFiniteInterning.Trace.next_le
#check @MicroCFTA.CacheFiniteInterning.Trace.next_le

#print axioms MicroCFTA.CacheFiniteInterning.Trace.refl
#check @MicroCFTA.CacheFiniteInterning.Trace.refl

#print axioms MicroCFTA.CacheFiniteInterning.Trace.intern
#check @MicroCFTA.CacheFiniteInterning.Trace.intern

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.empty
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.empty

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.step
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.step

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.interns
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.interns

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.trans
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.trans

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.valid
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.valid

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.extends
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.extends

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.potential
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.potential

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.next_le_missing
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.next_le_missing

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.next_le
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.next_le

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.represents_mono
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.represents_mono

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.represented_identity_le
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.represented_identity_le

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.identity_le
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.identity_le

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.identity_lt
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.identity_lt

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.returned
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.returned

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.refl
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.refl

#print axioms MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.make
#check @MicroCFTA.SourceRecursiveIntersectionDomainAllocation.Trace.make
