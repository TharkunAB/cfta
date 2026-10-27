inductive OrderedRelated {Left : Type u} {Right : Type v} (relation : Left → Right → Prop) :
    List Left → List Right → Prop where
  /-- Empty payload lists agree. -/
  | nil : OrderedRelated relation [] []
  /-- Related heads retain their position before related suffixes. -/
  | cons : relation first second → OrderedRelated relation rest tail →
      OrderedRelated relation (first :: rest) (second :: tail)
