      FragmentCarries (finish residual fragment before).core fragment := by
  have actual : Success (recordResidual residual fragment) before.core ()
      (finish residual fragment before).core := by
    rw [Success, finish_raw]
    simp
  have preserved := recordResidual_carriers residual fragment before.core _ actual
  exact ⟨preserved, recordResidual_references residual fragment before.core _ references holes actual,
    holes.preserve fragment preserved⟩

end MicroCFTA.SourcePruningEnumerationSelectedEdge
