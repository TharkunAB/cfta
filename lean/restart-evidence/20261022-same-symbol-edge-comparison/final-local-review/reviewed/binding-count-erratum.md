# Checkpoint binding count correction

The frozen checkpoint template note reports 19 distinct pending bindings.
The actual eight scripts contain 18 distinct bindings. The root binder copied the reported count.
The bind-1 command wrote eight candidate scripts, then rejected the count before activation.
Its whole partial directory remains as actual-tools-preparation-bind-1-partial.
The frozen templates remain unchanged. The exact binder before the repair and its patch remain.
The repaired binder requires all 18 actual keys. The verifier has 25 distinct keys.
The authored-cut helper pins remain. Current helper pins include the repaired binder.
This metadata failure does not add a Lean or Lake command or change the proof.
