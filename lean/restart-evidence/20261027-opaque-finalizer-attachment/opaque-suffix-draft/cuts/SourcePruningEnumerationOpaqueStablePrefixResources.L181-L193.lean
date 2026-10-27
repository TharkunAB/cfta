      exact (prefixProtected held storedFragment old).avoids bucket (pending held storedFragment old)
    · rw [prefixStopped] at matched
      cases matched

  · refine ⟨prefixResult, ?_⟩
    intro extra
    let work := bound + bound + bound + bound + bound + extra
    have RSame : R + (work - R) = work := by dsimp only [work]; omega
    have NSame : N + (work - N) = work := by dsimp only [work]; omega
    have KSame : K + (work - K) = work := by dsimp only [work]; omega
    have stable := prefixRunning (work - R) (work - N) work work (work - K)
      (by dsimp only [work]; omega) (by dsimp only [work]; omega)
    simpa only [RSame, NSame, KSame] using stable
