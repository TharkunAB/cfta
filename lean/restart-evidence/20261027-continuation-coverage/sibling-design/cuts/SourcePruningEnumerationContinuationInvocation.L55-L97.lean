              | stopped headOutputs reason endpoint => simp only [run, captured, hooked] at completed; cases completed
              | complete headOutputs middleCaller middleQueries =>
                  cases suffix : run hook checkEmpty r n p h k target scs before earlierEdges
                      middleCaller middleQueries with
                  | stopped tailProcessed tailOutputs current =>
                      simp only [run, captured, hooked, suffix] at completed; cases completed
                  | complete tailProcessed tailOutputs actualCaller actualQueries =>
                      simp only [run, captured, hooked, suffix, Result.complete.injEq] at completed
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := completed
                      exact .completed captured hooked
                        (ih (caller := middleCaller) (queries := middleQueries)
                          (processed := tailProcessed) (outputs := tailOutputs)
                          (afterCaller := actualCaller) (afterQueries := actualQueries) suffix observed)
          | rejected middleCaller middleQueries candidate =>
              cases suffix : run hook checkEmpty r n p h k target scs before earlierEdges
                  middleCaller middleQueries with
              | stopped tailProcessed tailOutputs current =>
                  simp only [run, captured, SourcePruningEnumerationNativeBranches.advance, suffix] at completed; cases completed
              | complete tailProcessed tailOutputs actualCaller actualQueries =>
                  simp only [run, captured, SourcePruningEnumerationNativeBranches.advance, suffix,
                    Result.complete.injEq] at completed
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := completed
                  exact .other captured trivial rfl
                    (ih (caller := middleCaller) (queries := middleQueries)
                      (processed := tailProcessed) (outputs := tailOutputs)
                      (afterCaller := actualCaller) (afterQueries := actualQueries) suffix observed)
          | stopped fragments observation candidate =>
              cases advanced : SourcePruningEnumerationNativeBranches.advance
                  (.stopped fragments observation candidate) with
              | none => simp only [run, captured, advanced] at completed; cases completed
              | some endpoint =>
                  obtain ⟨middleCaller, middleQueries⟩ := endpoint
                  cases suffix : run hook checkEmpty r n p h k target scs before earlierEdges
                      middleCaller middleQueries with
                  | stopped tailProcessed tailOutputs current =>
                      simp only [run, captured, advanced, suffix] at completed; cases completed
                  | complete tailProcessed tailOutputs actualCaller actualQueries =>
                      simp only [run, captured, advanced, suffix, Result.complete.injEq] at completed
                      obtain ⟨rfl, rfl, rfl, rfl⟩ := completed
                      exact .other captured trivial advanced
                        (ih (caller := middleCaller) (queries := middleQueries)
                          (processed := tailProcessed) (outputs := tailOutputs)
                          (afterCaller := actualCaller) (afterQueries := actualQueries) suffix observed)
