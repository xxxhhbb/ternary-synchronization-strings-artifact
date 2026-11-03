"""Run the current versioned finite verification suite."""
from pathlib import Path
import runpy

if __name__ == "__main__":
    runpy.run_path(str(Path(__file__).resolve().parent / "paper-2026-11-03/computational/verify.py"), run_name="__main__")
