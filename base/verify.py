"""Reproduce the finite computations used in the paper.

The default mode checks every compact certificate and reruns the numerical,
phase-recognition, and boundary-template arguments.  ``--full`` additionally
reconstructs every one- and two-deletion case from the published codebook.
"""

from __future__ import annotations

import argparse
import base64
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parent
INPUT = ROOT / "inputs" / "codewords_54_952.txt"
CERTIFICATES = ROOT / "certificates"
ONE_DELETION = CERTIFICATES / "one_deletion"
CORES = CERTIFICATES / "one_deletion_coordinate_cores.json"
CIRCLE_TEMPLATES = CERTIFICATES / "circle_boundary_templates.json"
VERIFIERS = ROOT / "verifiers"
PARAMETERS = ROOT / "PARAMETERS.json"

ODD_TOTALS = tuple(range(229, 464, 2))
EXCLUDED_TOTALS = ODD_TOTALS + (456, 462, 464)
EXPECTED_ONE_DELETION_CASES = 56_264_264
FULL_RANGES = ((229, 287), (289, 347), (349, 407), (409, 463))


def check_release_layout() -> None:
    root_files = {path.name for path in ROOT.iterdir() if path.is_file()}
    expected_root = {
        ".gitignore",
        "CITATION.cff",
        "PARAMETERS.json",
        "README.md",
        "SOURCE.md",
        "verify.py",
    }
    if not expected_root.issubset(root_files):
        raise SystemExit(f"missing release files: {sorted(expected_root-root_files)}")
    expected_verifiers = {
        "independent_verify_d227_lll.py",
        "verify_circle_boundary_templates.mjs",
        "verify_circle_lll_decimal.py",
        "verify_circle_lll_rational.py",
        "verify_d227_lll.py",
        "verify_entropy_transfer.py",
        "verify_one_deletion_cores.mjs",
        "verify_one_deletion_range.mjs",
        "verify_phase_recognition.mjs",
        "verify_transparent_brinkhuis.py",
        "verify_two_deletion_shell.mjs",
    }
    actual_verifiers = {path.name for path in VERIFIERS.iterdir() if path.is_file()}
    if actual_verifiers != expected_verifiers:
        raise SystemExit("verifier file set mismatch")
    if {path.name for path in INPUT.parent.iterdir() if path.is_file()} != {INPUT.name}:
        raise SystemExit("input file set mismatch")
    certificate_root_files = {
        path.name for path in CERTIFICATES.iterdir() if path.is_file()
    }
    if certificate_root_files != {CORES.name, CIRCLE_TEMPLATES.name}:
        raise SystemExit("certificate root file set mismatch")

    data = json.loads(PARAMETERS.read_text(encoding="utf-8"))
    expected_parameters = {
        "weak_normalized_edit_distance_gap": "1/227",
        "open_epsilon_threshold": "226/227",
        "advertised_epsilon": "227/228",
        "alpha": "51/100000",
        "beta": "3/10",
        "excluded_totals": list(EXCLUDED_TOTALS),
    }
    if data != expected_parameters:
        raise SystemExit("proof-parameter file mismatch")
    print("PASS release layout and proof parameters")


def check_runtime() -> None:
    if sys.version_info < (3, 11):
        raise SystemExit("Python 3.11 or later is required")
    if not __debug__:
        raise SystemExit("optimized Python is unsupported; run without -O or PYTHONOPTIMIZE")
    node = shutil.which("node")
    if node is None:
        raise SystemExit("Node.js 20 or later is required")
    completed = subprocess.run(
        [node, "--version"], capture_output=True, text=True, check=True
    )
    match = re.fullmatch(r"v(\d+)\.\d+\.\d+\s*", completed.stdout)
    if match is None or int(match.group(1)) < 20:
        raise SystemExit(f"Node.js 20 or later is required; found {completed.stdout.strip()}")
    print(f"PASS runtime (Python {sys.version.split()[0]}, Node {completed.stdout.strip()})")


def check_codebook() -> None:
    raw = INPUT.read_bytes()
    words = raw.decode("ascii").splitlines()
    if len(words) != 952 or len(set(words)) != 952:
        raise SystemExit("expected 952 distinct codewords")
    if words != sorted(words):
        raise SystemExit("canonical codebook is not sorted")
    if any(len(word) != 54 or set(word) - set("012") for word in words):
        raise SystemExit("canonical codebook format mismatch")
    if {word[::-1] for word in words} != set(words):
        raise SystemExit("canonical codebook is not closed under reversal")
    print("PASS canonical 54/952 codebook")


def check_one_deletion_certificates() -> None:
    paths = sorted(ONE_DELETION.glob("ONE_DELETION_SHELL_*.json"))
    if len(paths) != len(ODD_TOTALS):
        raise SystemExit(f"expected 118 one-deletion certificates, found {len(paths)}")
    seen: dict[int, Path] = {}
    cases = 0
    for path in paths:
        payload = json.loads(path.read_text(encoding="utf-8"))
        total = int(payload["total"])
        if total in seen:
            raise SystemExit(f"duplicate one-deletion total {total}")
        proof = base64.b64decode(payload["edge_indices_base64"], validate=True)
        if len(proof) != int(payload["case_count"]):
            raise SystemExit(f"proof length mismatch in {path.name}")
        seen[total] = path
        cases += len(proof)
    if tuple(sorted(seen)) != ODD_TOTALS:
        raise SystemExit("one-deletion totals are not exactly the odd totals 229..463")
    if cases != EXPECTED_ONE_DELETION_CASES:
        raise SystemExit(f"one-deletion case-count mismatch: {cases}")
    print(f"PASS one-deletion certificates (118 shells, {cases:,} cases)")


def run(label: str, command: list[str], verbose: bool) -> None:
    print(f"RUN  {label}", flush=True)
    started = time.perf_counter()
    completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    elapsed = time.perf_counter() - started
    if completed.returncode:
        if completed.stdout:
            print(completed.stdout, file=sys.stderr, end="")
        if completed.stderr:
            print(completed.stderr, file=sys.stderr, end="")
        raise SystemExit(f"FAIL {label}: exit code {completed.returncode}")
    if verbose:
        if completed.stdout:
            print(completed.stdout, end="")
        if completed.stderr:
            print(completed.stderr, file=sys.stderr, end="")
    print(f"PASS {label} ({elapsed:.2f}s)")


def d227_command(script: Path) -> list[str]:
    return [
        sys.executable,
        str(script),
        "--source",
        str(INPUT),
        "--denominator",
        "227",
        "--exclude-totals",
        ",".join(map(str, EXCLUDED_TOTALS)),
        "--alpha",
        "51/100000",
        "--beta",
        "3/10",
        "--bilateral",
    ]


def core_replay(verbose: bool) -> None:
    node = shutil.which("node") or "node"
    run(
        "transparent six-codeword Brinkhuis source",
        [sys.executable, str(VERIFIERS / "verify_transparent_brinkhuis.py")],
        verbose,
    )
    run(
        "local-entropy transfer arithmetic",
        [sys.executable, str(VERIFIERS / "verify_entropy_transfer.py")],
        verbose,
    )
    run("D=227 primary exact LLL", d227_command(VERIFIERS / "verify_d227_lll.py"), verbose)
    run(
        "D=227 independent exact LLL",
        d227_command(VERIFIERS / "independent_verify_d227_lll.py"),
        verbose,
    )
    run(
        "one-deletion coordinate cores",
        [node, str(VERIFIERS / "verify_one_deletion_cores.mjs"), str(INPUT), str(CORES)],
        verbose,
    )
    run(
        "phase recognition",
        [node, str(VERIFIERS / "verify_phase_recognition.mjs")],
        verbose,
    )
    run(
        "circle boundary templates",
        [node, str(VERIFIERS / "verify_circle_boundary_templates.mjs"), str(CIRCLE_TEMPLATES)],
        verbose,
    )
    run(
        "circle LLL exact-rational bounds",
        [sys.executable, str(VERIFIERS / "verify_circle_lll_rational.py")],
        verbose,
    )
    run(
        "circle LLL high-precision cross-check",
        [sys.executable, str(VERIFIERS / "verify_circle_lll_decimal.py")],
        verbose,
    )


def full_replay(verbose: bool) -> None:
    node = shutil.which("node") or "node"
    for first, last in FULL_RANGES:
        run(
            f"one-deletion exhaustive replay {first}..{last}",
            [
                node,
                str(VERIFIERS / "verify_one_deletion_range.mjs"),
                str(INPUT),
                str(ONE_DELETION),
                str(first),
                str(last),
            ],
            verbose,
        )
    for total in (456, 462, 464):
        run(
            f"two-deletion exhaustive replay at total {total}",
            [node, str(VERIFIERS / "verify_two_deletion_shell.mjs"), str(INPUT), str(total)],
            verbose,
        )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument(
        "--integrity-only",
        action="store_true",
        help="check runtimes, layout, formats, and certificate coverage only",
    )
    modes.add_argument(
        "--full",
        action="store_true",
        help="also replay all 56,264,264 one-deletion cases and all exceptional two-deletion shells",
    )
    parser.add_argument("--verbose", action="store_true", help="show verifier output")
    args = parser.parse_args()

    check_runtime()
    check_release_layout()
    check_codebook()
    check_one_deletion_certificates()
    if args.integrity_only:
        print("ARTIFACT_INTEGRITY_PASS")
        return

    core_replay(args.verbose)
    if args.full:
        full_replay(args.verbose)
        print("ARTIFACT_FULL_REPLAY_PASS")
    else:
        print("ARTIFACT_CORE_REPLAY_PASS")


if __name__ == "__main__":
    main()
