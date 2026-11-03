# Synchronization Strings over the Optimal Alphabet: D=216 artifact

Version 2.0.0 accompanies *Synchronization Strings over the Optimal Alphabet*,
by Huibo Xu, Shi Fu, Youming Qiao, and Dacheng Tao.

This version contains the current finite verification ingredients for:

- the transparent ternary parameter `2001/2002`;
- the non-strict normalized insertion/deletion-distance gap `1/216`, hence
  every fixed synchronization parameter `epsilon > 215/216`, including `216/217`;
- the separately stated ternary synchronization circles of every length
  `n >= 10008` with parameter `5201/5202`.

## Run the complete verification

Python 3.11 or later and Node.js 20 or later are required. Only their standard
libraries are used. From the repository root, run:

```sh
python -B verify.py
```

This runs all twelve current finite checks. Successful completion ends with
`D216_ALL_CHECKS_PASS`; a failed check returns a nonzero exit status.
`--full` is an alias for this same complete replay. There is no `--skip-base`
or earlier-parameter mode. Do not disable assertions with Python `-O`.

For file-integrity checking without mathematical replay:

```sh
python -B verify.py --integrity-only
```

This emits `D216_INTEGRITY_ONLY_PASS`, not the complete-verification marker.

## What is checked

1. The six-codeword square-free substitution.
2. The elementary entropy-transfer estimates.
3. Complete-block recognition, the border spectrum, and simultaneous flank
   capacities for one and the same middle word.
4. An independent direct verification of the flank and word-pair capacities.
5. The circle phase-recognition table.
6. The circle boundary templates.
7. The circle local-lemma bound using exact rational arithmetic.
8. An independent high-precision decimal check of that circle bound.
9. The finite bounds on nonzero-phase matching runs.
10. The D=216 direct unequal-interval bound using exact rational arithmetic.
11. A separate implementation of that D=216 bound.
12. The cached pair oracle, compared with exhaustive LCS detection after updates.

The D=216 calculation uses charge slope `37/100000`, charge constant `21/100`,
bilateral conditioning, odd exceptional totals `229..463`, and exceptional even
totals `456,462,464`. See `PARAMETERS.json` for the finite constants.

## Inputs and integrity

`MANIFEST.json` pins every other distributed file by SHA-256. The canonical
54/952 codebook is in `base/inputs/codewords_54_952.txt`, with SHA-256:

```text
a1b4b912d956419ef59a15e5d0926ce337614a438da25923e19a65485da05e28
```

`base/SOURCE.md` records the Sollami--Douglas--Liebmann source and extraction.
`base/` contains shared inputs, the necessary circle certificate, and common
verification modules. The two exact-arithmetic modules are implementations
used by the current calculators, not separate reproduction entry points.

## Scope

The occurrence-wise square-free guarantee of the 54/952 family is a published
theorem credited in `base/SOURCE.md`. These programs verify additional finite
codeword properties, finite relations, numerical bounds, and the oracle test.
The clean-block counting, alignment geometry, capacity criterion, and reductions
covering all interval lengths remain mathematical arguments in the manuscript.
This artifact is not a formal proof-assistant development or a production string
generator. The oracle comparison is a correctness check, not a performance benchmark.

This release replaces the earlier active verification layout. Historical files
remain available in Git history; they are not prerequisites for this version.
The reproducible version is:

https://github.com/xxxhhbb/ternary-synchronization-strings-artifact/tree/v2.0.0
