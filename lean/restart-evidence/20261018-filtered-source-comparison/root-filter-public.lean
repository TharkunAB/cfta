import MicroCFTA.SourceCurrentStoredFilteredProfile
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentStoredFilteredProfile.filtered
#print MicroCFTA.SourceCurrentStoredFilteredProfile.filtered
#print axioms MicroCFTA.SourceCurrentStoredFilteredProfile.filtered

#check @MicroCFTA.SourceCurrentStoredFilteredProfile.reference
#print MicroCFTA.SourceCurrentStoredFilteredProfile.reference
#print axioms MicroCFTA.SourceCurrentStoredFilteredProfile.reference

#check @MicroCFTA.SourceCurrentStoredFilteredProfile.mu
#print MicroCFTA.SourceCurrentStoredFilteredProfile.mu
#print axioms MicroCFTA.SourceCurrentStoredFilteredProfile.mu

#check @MicroCFTA.SourceCurrentStoredFilteredProfile.congr
#print MicroCFTA.SourceCurrentStoredFilteredProfile.congr
#print axioms MicroCFTA.SourceCurrentStoredFilteredProfile.congr

#check @MicroCFTA.SourceCurrentStoredFilteredProfile.absent
#print MicroCFTA.SourceCurrentStoredFilteredProfile.absent
#print axioms MicroCFTA.SourceCurrentStoredFilteredProfile.absent

#check @MicroCFTA.SourceCurrentStoredFilteredProfile.filter_profile
#print MicroCFTA.SourceCurrentStoredFilteredProfile.filter_profile
#print axioms MicroCFTA.SourceCurrentStoredFilteredProfile.filter_profile
