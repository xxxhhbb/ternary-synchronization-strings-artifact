# Verification for the supported-alignment strengthening

This package accompanies *Synchronization Strings over the Optimal Alphabet*.
It verifies the finite inputs and numerical local-lemma bounds for normalized
edit-distance gap **1/216**, hence every synchronization parameter greater
than **215/216** (in particular, **216/217**).

## Running the checks

Install Python 3.11 or later and Node.js 20 or later, then run:

```
python verify.py
```

Only the standard libraries are used. Any failed check exits unsuccessfully.
The default run checks base certificate layout and coverage, runs its small
finite checks, and recomputes the phase comparisons and both numerical
bounds. It does not verify all deletion-certificate contents. To replay all
base deletion-shell cases as well, run `python verify.py --full`; the base
package reports a prior runtime of about 29 minutes. `--skip-base` runs the
new checks alone and does not check the inherited finite-shell dependencies.
Do not use Python's `-O` option,
which disables assertions.

## Contents and scope

- `base/` preserves the earlier verification package, including codeword
  provenance, finite-shell certificates, and its original 1/227 calculation.
  Its `PARAMETERS.json` describes that base calculation, not the new result.
- `verifiers/phase_runs.mjs` checks the finite nonzero-phase matching-run
  table by direct codeword-factor set comparisons.
- `verifiers/direct_bound.py` checks the common prefix and suffix, computes
  alignment capacities recursively, and evaluates the supported deletion
  volumes with exact rational upper bounds.
- `verifiers/independent_direct_bound.py` uses an iterative capacity table,
  deletion-deficit enumeration, and the independent base arithmetic engine.
- `verifiers/batched_oracle.py` is a small reference implementation of the
  cached event detector. Its tests compare every cache entry with exhaustive
  LCS detection after block updates. It is not a production string generator
  or an empirical benchmark of the asymptotic running time.

The new calculation uses denominator 216, charges
`p(a,b) exp(37(a+b)/100000 + 21/100)`, and the same excluded totals as the
base finite-shell lemmas: odd totals 229 through 463, and 456, 462, 464.
Totals 217, 227, and 452 are not separately excluded. The run-capacity
restriction handles them within the event-volume calculation.

There are 29,961 nonzero ordered length types through total 4,000. Including
the rational infinite tail, the bounds are `max x < 1/6000`,
`R0 < 364756/10^9`, and `109 R0 + R1 < 203468108/10^9`.
The matching-run recurrence and the reduction from all interval lengths to
the finite cutoff are mathematical arguments in the manuscript. The tests
check their finite ingredients and selected algorithmic cases; they do not
constitute a proof-assistant formalization of those arguments.

The long-distance result and expected `O(n^2 log^3(n+2))` construction are
proved in the manuscript from these bounds. In particular, the logarithmic
distant-interval cutoff is not presented as a practical finite-length
performance guarantee.
