# Synchronization Strings over a Ternary Alphabet: companion material

The current paper's codebooks, finite verifiers and supplementary Lean
development are in [`paper-2026-11-03/`](paper-2026-11-03/README.md).

* [Published-source and theorem correspondence](paper-2026-11-03/SOURCES.md)
* [Codebooks and exact primary-data comparison](paper-2026-11-03/codebooks/)
* [Current twelve-check computational suite](paper-2026-11-03/computational/README.md)
* [Lean source, reproduction and exact scope](paper-2026-11-03/lean/README.md)

## Run the current finite checks

With Python 3 and Node.js on PATH:

```sh
python -B verify.py
python -B paper-2026-11-03/codebooks/verify_codebooks.py
```

The default runs all twelve current finite checks and ends with
`D216_ALL_CHECKS_PASS`. `--full` is an alias for the same complete run;
`--integrity-only` checks the computational manifest without replaying the
mathematical calculations. Do not use Python `-O`.

The current computational bounds concern non-strict gap `1/216` and hence
every strict synchronization parameter greater than `215/216`, as well as
the transparent `2001/2002` parameter and the additional stated circle
checks. The Lean snapshot has a different, explicitly documented coverage;
it is not a formal verification of the complete paper.

Existing root `base/` and `verifiers/` files remain as historical material.
They are not the current reproduction entry. Older paper parameters and
certificate workflows are preserved in Git history. Use the version/commit
specified by the paper, rather than assuming every historical file supports
the current statements.

The mathematical constructions remain credited to their original authors.
This repository supplies concrete data and supplementary verification,
not a replacement for their cited preservation theorems. No full production
randomized string generator or practical performance benchmark is claimed.
