inductive All₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ R [] []
  | cons : R a b → All₂ R as bs → All₂ R (a :: as) (b :: bs)
