Root execution order:

1. Review the frozen staging controller and its actual staging result.
2. Copy this `prepare-publication.py` into Work57 and run it there.
3. Read the generated selection and source pins.
4. Run the generated publication `check.py` under the existing capped job runner.
5. Accept `checked.json` only after all five gates pass and all pins stay exact.

The publication runtime is `20261118-retained-source-gate-skip-publication`. The generated strict order is Gate, then Skip. Fresh queries run after both objects exist. A failure writes `results.json` and gives no new proof credit. The controller does not create a success receipt on failure.
