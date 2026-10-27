      obtain ⟨observed, middle, reading, finished⟩ := (success_bind _ _ _ _ _).mp success
      rw [bind_single _ _ _ _ _ (oracle_exact graph (first :: rest) fuel metadata.pending uv input
        before middle observed reading)]
      exact pure_exact _ result middle after finished

end MicroCFTA.SourcePruningCallbackExact
