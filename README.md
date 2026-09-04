# Verification artifact for *Synchronization Strings over the Optimal Alphabet*

This repository reproduces the finite computations used in the paper.  The
main alphabet theorem---the existence of ternary `2001/2002`-synchronization
strings of every length---has a separate human-readable proof and does not
depend on the large certificates here.

The artifact checks the computer-assisted quantitative refinement with weak
normalized edit-distance gap `1/227`, which yields ternary
epsilon-synchronization strings for every `epsilon > 226/227` (in particular,
`epsilon = 227/228`).  It also checks the finite ingredients in the theorem
giving ternary `5201/5202`-synchronization circles at every length at least
`10008`.

## Requirements

- Python 3.11 or later;
- Node.js 20 or later;
- no third-party Python or Node packages.

The commands below should be run from the repository root.  On Windows, use
`python`; on systems where Python is installed as `python3`, replace the
executable name accordingly.

## Verification modes

Check the release layout, runtimes, canonical codebook, and compact
certificate coverage:

```text
python verify.py --integrity-only
```

Run the standard semantic replay:

```text
python verify.py
```

This reruns two independently implemented exact local-lemma calculations,
the transparent six-codeword calculation, the 48 coordinate cores, phase
recognition, all 306 circle-boundary template cases, and both rational and
high-precision checks of the circle local-lemma arithmetic.  On a typical
desktop it takes a few minutes.  The final line is
`ARTIFACT_CORE_REPLAY_PASS`.

Run the exhaustive replay:

```text
python verify.py --full
```

In addition to the standard replay, this reconstructs all `56,264,264`
one-deletion cases and the exceptional two-deletion shells at totals `456`,
`462`, and `464`.  This mode is CPU intensive.  The final line is
`ARTIFACT_FULL_REPLAY_PASS`.

Add `--verbose` to either semantic mode to display the output of every
component verifier.

## Command-line contract

The public interface is

```text
python verify.py [-h] [--integrity-only | --full] [--verbose]
```

The two mode flags are mutually exclusive; omitting both selects the standard
semantic replay.  A successful run exits with status zero and ends with one of
the following lines:

```text
ARTIFACT_INTEGRITY_PASS
ARTIFACT_CORE_REPLAY_PASS
ARTIFACT_FULL_REPLAY_PASS
```

Any missing runtime, malformed input, incomplete certificate set, failed
inequality, or inconsistent enumeration produces a nonzero exit status.  The
verification is deterministic, CPU-only, read-only, and network-free.  It
does not use environment-specific paths, random seeds, downloaded packages,
or persistent caches.  Component verifiers run serially.

For reference, the standard replay took about 32 seconds and the exhaustive
replay about 29 minutes on the Windows 11 machine used to prepare this
release, with Python 3.11.7 and Node.js 22.23.2.  Running times will vary by
processor.

## What is checked

Before running the mathematics, `verify.py` checks the release layout and the
fixed proof parameters in `PARAMETERS.json`.  It then checks:

1. the 952 length-54 ternary codewords, including distinctness, syntax,
   ordering, and reversal closure;
2. the exact finite and rational-tail inequalities for the denominator-227
   local-lemma argument, using two independent Python implementations;
3. the 118 compact one-deletion certificates, their individual proof hashes,
   exact coverage of odd totals 229 through 463, and their aggregate count;
4. the three exceptional two-deletion totals used in the proof;
5. the phase-recognition calculation and all 17 periodic circle-boundary
   templates across all 18 square-free four-letter contexts; and
6. the rational inequalities underlying the all-length circle calculation.

## Trust boundary

The artifact verifies the finite codebook properties used by the argument,
but it does not re-prove the occurrence-wise square-free theorem for the
54-uniform 952-choice Brinkhuis family.  That theorem is the published
mathematical input cited in the paper:

> Michael Sollami, Craig C. Douglas, and Manfred Liebmann, "An Improved Lower
> Bound on the Number of Ternary Squarefree Words," *Journal of Integer
> Sequences* 19 (2016), Article 16.6.7, Theorem 4.

The canonical codebook and its provenance are described in `SOURCE.md`.

## Repository layout

```text
verify.py                 single entry point
PARAMETERS.json           proof parameters used by the verifiers
inputs/                   canonical published 54/952 codebook
certificates/             compact one-deletion and circle certificates
verifiers/                independent Python and JavaScript checkers
SOURCE.md                 provenance of the published codebook
CITATION.cff              citation metadata
```

Only the inputs, certificates, and verification programs needed for the
claims above are included.
