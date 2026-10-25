theorem fst_mem_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ zipIdx l k) : x.1 ∈ l :=
  zipIdx_map_fst k l ▸ mem_map_of_mem h
