"""Run the base finite checks and the supported-alignment strengthening."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--full', action='store_true',
                    help='regenerate the base deletion-shell checks instead of replaying them')
parser.add_argument('--skip-base', action='store_true',
                    help='run only the new checks; the base dependencies must be checked separately')
args = parser.parse_args()
node = shutil.which('node')
if node is None:
    raise SystemExit('Node.js is required for the finite phase checks.')
if not args.skip_base:
    subprocess.run([sys.executable, '-B', str(ROOT/'base/verify.py')]
                   + (['--full'] if args.full else []), cwd=ROOT/'base', check=True)
subprocess.run([node, str(ROOT/'verifiers/phase_runs.mjs')], check=True)
excluded = ','.join(map(str, list(range(229,464,2))+[456,462,464]))
options = ['--source', str(ROOT/'base/inputs/codewords_54_952.txt'),
           '--denominator', '216', '--exclude-totals', excluded,
           '--alpha', '37/100000', '--beta', '21/100', '--bilateral']
for name in ('direct_bound.py', 'independent_direct_bound.py'):
    subprocess.run([sys.executable, '-B', str(ROOT/'verifiers'/name), *options], check=True)
subprocess.run([sys.executable, '-B', str(ROOT/'verifiers/batched_oracle.py')], check=True)
print('SUPPORTED_ALIGNMENT_CHECKS_PASS' if args.skip_base else
      ('STRENGTHENING_AND_FULL_BASE_PASS' if args.full else 'STRENGTHENING_AND_BASE_CORE_PASS'))
