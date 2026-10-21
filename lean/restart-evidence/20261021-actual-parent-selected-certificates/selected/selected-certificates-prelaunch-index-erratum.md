# Prelaunch fourth-memo index correction

The initial source-only signature used a homogeneous equality between graph proofs with different fourth-memo indices. The saved Parent index was `savedFourth`. The supplied RecordScan index was `scanFourth`. These variables had no equality in the signature at that point. The proposed equality therefore did not have a well-formed type.

Independent source review found this issue before any Lean or Lake command. Root approved the correction on 2026-10-21 at 08:24 CEST. The corrected output retains the same `built` existential. It returns `savedFourth = scanFourth` and `HEq` between the same numeric graph and the same assembled live/classes/completed graph. The proof derives the equality from actual Scan return uniqueness. It adds no caller premise and selects no new graph.

The frozen plan and original signature remain unchanged. `selected-certificates-source-only.lean` preserves the complete initial 263-line source, SHA256 e1ea8ea5ce1e4839dd70da0527824e81c552385948a92a99ff99fc6ae976cbe6. `selected-certificates-corrected-signature.lean.txt` records the corrected public type. The remaining source and public type stay unchanged. This is a prelaunch type correction, not a Lean failure or an execution counterexample.
