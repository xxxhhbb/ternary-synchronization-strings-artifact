# Current reproduction: D=216

This package verifies the finite ingredients used by the current manuscript:

- transparent ternary synchronization parameter `2001/2002`;
- non-strict normalized edit-distance gap `1/216`, hence every fixed
  `epsilon > 215/216` (for example `216/217`);
- the separately stated sufficiently large circle lengths with parameter
  `5201/5202`.

## Run

With Python 3 and Node.js on PATH, run from this package directory:

```text
python -B verify.py
```

From the repository root, the convenience entry is:

```text
python -B verify.py
```

Both run the same twelve current checks. `--full` is an alias for the
default complete finite replay. `--integrity-only` checks the manifest
without replaying the mathematical computations. Do not use Python `-O`.

The complete replay ends with `D216_ALL_CHECKS_PASS`; integrity-only mode
ends with `D216_INTEGRITY_ONLY_PASS`. No earlier-parameter replay is included
in this active package. Previous files were backed up outside it.

## Checks and inputs

`MANIFEST.json` pins every invoked verifier, input and certificate by SHA-256.
The canonical 54/952 codebook has SHA-256
`a1b4b912d956419ef59a15e5d0926ce337614a438da25923e19a65485da05e28`.

The replay includes transparent-source and entropy arithmetic checks,
complete-block recognition, the border spectrum, simultaneous flank
capacities for the same middle word, an independent direct-flank check,
phase-run bounds, both D216 exact arithmetic engines, circle phase and
boundary-template checks, circle rational arithmetic and its decimal
cross-check, and the cached pair-oracle comparison.

The D216 calculation uses denominator `216`, charge slope `37/100000`,
charge constant `21/100`, bilateral conditioning, odd exceptional totals
`229..463`, and exceptional even totals `456,462,464`.

`base/verifiers/exact_arithmetic.py` and
`base/verifiers/independent_exact_arithmetic.py` are shared arithmetic
implementation modules loaded by the two current calculators. They are
not separate reproduction entries. Their numerical algorithms are
unchanged; the current calculators supply all theorem parameters.

## Mathematical scope

The 54/952 occurrence-wise square-free guarantee is the published
Sollami--Douglas--Liebmann theorem cited in `base/SOURCE.md`. The programs
check the additional finite codeword properties and numerical bounds.
The clean-block counting, five-block geometry, capacity criterion and
all-length reductions remain mathematical arguments in the manuscript;
this replay is not a formalization of those arguments.

This version is distributed in the versioned companion repository. Use the
commit cited by the manuscript; this directory does not claim a DOI.
