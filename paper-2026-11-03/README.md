# Codebooks and verification material for the 2026-11-03 paper

This directory is a versioned companion to *Synchronization Strings over a Ternary Alphabet*. It separates three kinds of evidence:

1. published arbitrary-length preservation results, cited in the paper;
2. executable finite checks and numerical inequalities used by the paper;
3. supplementary Lean statements, with their exact parameters and premises.

## Contents

| Material | Location | Scope |
| --- | --- | --- |
| Six length-18 codewords | `codebooks/brinkhuis_18_2.json` | Two alternatives for each of the three outer letters |
| Three 54/952 codebooks | `codebooks/brinkhuis_54_952_C0.txt`, `C1`, `C2` | Base list and its two cyclic alphabet shifts |
| Extremal 41/52 images and 49-letter caps | `codebooks/extremal_41_52_images.json` | Twelve permutation/reversal variants, including reversal-dependent cap assignment |
| Primary-source identity checks | `codebooks/verify_codebooks.py`, `published_identity.json` | Exact finite word-data comparisons; not preservation proofs |
| Current finite verification suite | `computational/` | All twelve checks for gap `1/216`, transparent constants and all-length circle inputs |
| Lean development | `lean/` | Source, pinned toolchain/dependencies, scope checks and precise limitations |
| Theorem/input map | `SOURCES.md` | Published version, required quantifiers and executable scope |

## Computational reproduction

Python 3 and Node.js on PATH, standard libraries only:

```sh
python -B computational/verify.py
python -B codebooks/verify_codebooks.py
```

The first command runs all twelve current checks by default and ends with
`D216_ALL_CHECKS_PASS`. `--full` is an alias for this complete run.
`--integrity-only` checks the computational manifest, not mathematical
content. Do not use Python `-O`.

For an independent comparison with the primary published word data, obtain
the two PDFs linked in `SOURCES.md`, install `pypdf`, and run:

```sh
python -B codebooks/verify_codebooks.py --sdl-pdf sollami3.pdf --mr-pdf mol-rampersad.pdf
```

These optional comparisons use local PDF files; they do not upload anything.
The original articles themselves are not redistributed here.

Lean reproduction and scope are documented in `lean/README.md`.

## What the executable checks do not establish

Finite recognition, overlap, capacity, template and arithmetic checks do not
replace the analytic reductions, arbitrary-length preservation theorems,
local lemma, or resampling output-distribution proofs. The supplement's
pair-oracle tests are a reference detector and small-instance update check,
not an end-to-end implementation or performance benchmark of the full
Las Vegas or Monte Carlo generators. The manuscript's algorithms are
asymptotic results with large inherited cutoffs.

Original constructions remain credited to their original authors. Citing
this repository identifies the actual data and verification version used;
it does not replace those mathematical citations.
