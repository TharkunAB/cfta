theorem complete (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment) (canonical : Canonical before.core)
    (related : EnumerationFlatCached.Related flat before) :
    ∃ fuel result after,
      ((Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
