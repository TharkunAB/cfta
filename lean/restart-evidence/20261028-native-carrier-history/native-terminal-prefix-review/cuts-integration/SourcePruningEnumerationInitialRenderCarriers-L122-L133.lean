    EnumerationRenderability.initial_references handle
  have rootCarrier : EnumerationCarriers.CarriesGraph (EnumerationState.initial handle : Core) 0 :=
    EnumerationCarriers.carries_self (EnumerationState.initial handle) (initial_storage handle).total
      0 (.unenumerated (some handle) []) rfl trivial
  intro output member
  have history := retained.1.2.2.1 0 output member
  have provenance := history.carriers_output initialReferences
  refine ⟨provenance.1 0 rootCarrier, provenance.2, ?_⟩
  intro marker discharged
  exact history.render_complete_models_from_origin marker 0 discharged initialReferences rootCarrier

end MicroCFTA.SourcePruningEnumerationRecursive
