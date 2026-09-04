# Synchronization Strings over the Optimal Alphabet

Computational material accompanying *Synchronization Strings over the Optimal
Alphabet*, by Huibo Xu, Shi Fu, Youming Qiao, and Dacheng Tao.

The programs verify the finite-case lemmas and numerical inequalities used in
the paper's quantitative refinement: ternary strings with a non-strict
normalized edit-distance lower bound $1/227$, and hence synchronization parameter
$\varepsilon>226/227$. They also verify the finite cases and local-lemma
estimates for ternary $5201/5202$-synchronization circles of every length
$n\ge10008$.

## Mathematical computations

The denominator-227 local-lemma estimates are checked by two separate
implementations using exact rational bounds. The finite enumeration covers
$56{,}264{,}264$ one-deletion cases, represented by 118 certificates, and the
two-deletion cases at total lengths 456, 462, and 464. Each certificate is
checked against the codewords and the corresponding square-free contexts.

The remaining programs check the six-codeword Brinkhuis family, coordinate
cores for one-deletion constraints, phase recognition, and the circle-boundary
templates. The circle local-lemma estimates are checked both by rational
bounds and by high-precision arithmetic.

The 54-uniform, 952-choice Brinkhuis family is taken from Sollami, Douglas,
and Liebmann; its occurrence-wise square-free property is a published input
to the proof. The reference and codeword extraction are described in
[SOURCE.md](SOURCE.md). The paper's basic $2001/2002$ theorem does not depend
on the large deletion certificates.

## Reproducing the computations

Python 3.11 or later and Node.js 20 or later are required. The programs use
only the standard libraries. Run the commands below from the repository root;
replace `python` by `python3` where appropriate.

```sh
python verify.py
python verify.py --full
```

The first command runs the numerical estimates and small finite checks. The
second also verifies all deletion certificates and enumerates the exceptional
two-deletion cases. Successful completion of the full computation is reported
as `ARTIFACT_FULL_REPLAY_PASS`; a failed check returns a nonzero exit status.
The default and full runs took approximately 30 seconds and 29 minutes,
respectively, in tests with Python 3.11.7 and Node.js 22.23.2 on Windows.

The option `--verbose` displays the output of each verification program.
For a preliminary check of the required files, parameters, codeword format,
and certificate lengths and coverage, use `--integrity-only`. This option
does not verify the mathematical content of the certificates and cannot be
combined with `--full`. All options are listed by `--help`.

## Files

```text
verify.py          verification entry point
PARAMETERS.json    parameters for the denominator-227 estimates
inputs/           the 952 length-54 codewords
certificates/     deletion certificates and circle-boundary templates
verifiers/        verification programs
SOURCE.md         codebook reference and extraction
CITATION.cff      citation information
```
