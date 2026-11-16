UNCOMPILED. Original743/log12631 remain immutable.
All six complete headers and six complete proof blocks remain byte-exact.
This variant keeps actual runEager/runWith/narrow function heads opaque while the
scan proof compares literal closures. No executed operation is changed or hidden
behind a supplied receipt. These functions are parameters of the compared closures;
the scan does not execute or inspect the narrowing implementation.

APPEND-CORE-FIRST-FIVE plus APPEND-SCAN equal the combined declaration sequence.
The split permits an independent first-five check/checkpoint. Both pieces contain
normal namespace/section preambles only; probes contain no imports.
No heartbeat increase, target change, or new input premise is introduced.
