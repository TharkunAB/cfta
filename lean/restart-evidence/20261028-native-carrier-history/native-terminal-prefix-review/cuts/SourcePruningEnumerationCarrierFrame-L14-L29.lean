/-- A complete compression frame retains every graph-bearing class. -/
theorem Frame.carriers (frame : Frame before after) : PreservesCarriers before after := by
  apply carriers_classes before after frame.values
  rintro left right ⟨root, size, leftPath, rightPath⟩
  exact ⟨root, size, (frame.reaches left root size).mpr leftPath,
    (frame.reaches right root size).mpr rightPath⟩

/-- A complete compression frame retains all stored fragment and residual carriers. -/
theorem Frame.references (frame : Frame before after) (references : ReferencesCarry before) :
    ReferencesCarry after := by
  apply references_transport before after references frame.carriers
  · intro uv fragment stored
    simpa only [frame.values] using stored
  · exact frame.obligations

end MicroCFTA.EnumerationCompressionFrame
