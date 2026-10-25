/-- A worker cache supports complete closed recursive head exposure. -/
structure Ready (state : State Symbol Guard) : Prop where
  semantic : SemanticHeap state
  covered : Covered [] state
  depth : InternedOpenDepthReadback.Heap state
