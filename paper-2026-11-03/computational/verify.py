"""Replay every finite verification used by the current D=216 manuscript."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'base/inputs/codewords_54_952.txt'

def integrity():
    manifest=json.loads((ROOT/'MANIFEST.json').read_text(encoding='utf-8'))
    if manifest['denominator'] != 216:
        raise SystemExit('Manifest does not describe D=216.')
    for relative,expected in manifest['files'].items():
        p=(ROOT/relative).resolve()
        if not p.is_relative_to(ROOT) or not p.is_file():
            raise SystemExit('Missing or invalid current-package file: '+relative)
        if hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
            raise SystemExit('Current-package hash mismatch: '+relative)
    print('D216_INPUT_AND_VERIFIER_HASHES_PASS',flush=True)

def run(label,command):
    start=time.perf_counter()
    print('RUN',label,flush=True)
    subprocess.run(command,cwd=ROOT,check=True)
    print('PASS',label,f'({time.perf_counter()-start:.3f}s)',flush=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integrity-only',action='store_true',help='check the pinned files without semantic replay')
    parser.add_argument('--full',action='store_true',help='compatibility alias: default already runs every current D=216 finite check')
    args=parser.parse_args()
    if not __debug__:
        raise SystemExit('Do not disable assertions with Python -O.')
    print('CURRENT REPRODUCTION: D=216; weak gap 1/216; every fixed epsilon > 215/216.',flush=True)
    integrity()
    if args.integrity_only:
        print('D216_INTEGRITY_ONLY_PASS',flush=True)
        return
    node=shutil.which('node')
    if not node:
        raise SystemExit('Node.js is required.')
    py=lambda name:[sys.executable,'-B',str(ROOT/name)]
    js=lambda name:[node,str(ROOT/name)]
    for label,command in [
        ('transparent source',py('base/verifiers/verify_transparent_brinkhuis.py')),
        ('entropy transfer',py('base/verifiers/verify_entropy_transfer.py')),
        ('complete-block, border-spectrum and flank capacities',py('verifiers/verify_seam_capacities.py')+[str(SOURCE)]),
        ('independent direct flanks and word-pair capacities',js('verifiers/independent_four_seams.mjs')+[str(SOURCE)]),
        ('circle phase recognition',js('base/verifiers/verify_phase_recognition.mjs')),
        ('circle boundary templates',js('base/verifiers/verify_circle_boundary_templates.mjs')+[str(ROOT/'base/certificates/circle_boundary_templates.json')]),
        ('circle rational LLL',py('base/verifiers/verify_circle_lll_rational.py')),
        ('circle decimal cross-check',py('base/verifiers/verify_circle_lll_decimal.py')),
        ('nonzero-phase run bounds',js('verifiers/phase_runs.mjs')),
    ]:
        run(label,command)
    excluded=','.join(map(str,list(range(229,464,2))+[456,462,464]))
    options=['--source',str(SOURCE),'--denominator','216','--exclude-totals',excluded,
             '--alpha','37/100000','--beta','21/100','--bilateral']
    for name in ('direct_bound.py','independent_direct_bound.py'):
        run(name,py('verifiers/'+name)+options)
    run('cached pair oracle',py('verifiers/batched_oracle.py'))
    print('STRUCTURAL_ARTIFACT_ALL_CHECKS_PASS',flush=True)
    print('D216_ALL_CHECKS_PASS',flush=True)

if __name__=='__main__':
    main()
