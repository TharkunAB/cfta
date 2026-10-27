
/-- Equal stored slots retain the complete pending-bucket mass, including repeated entries. -/
theorem suspendedBound_values (before after : Core) (values : after.values = before.values) :
    suspendedBound after = suspendedBound before := by
  simp only [suspendedBound, values]

end MicroCFTA.SourcePruningEnumerationPrefixAdmission
