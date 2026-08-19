# Axiom audit

Run `./verify.sh` from the `Lean` directory. After compiling the library, the script elaborates `AxiomAudit.lean`, which:

- checks the two public $n=4$ theorems;
- checks the central geometric-certificate endpoints;
- prints the axioms used by each endpoint.

The imported proof closure contains no `sorry`, `admit`, custom `axiom`, or `unsafe` declarations at the recorded source commit. The printed list may still contain standard Lean/Mathlib logical principles such as quotient soundness, propositional extensionality, or classical choice.
