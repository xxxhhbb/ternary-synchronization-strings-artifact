"""Check released codeword data; optionally compare with primary published PDFs.

Default: Python standard library only, no network access.
Optional --sdl-pdf / --mr-pdf comparisons require pypdf.
No finite check here is a proof of arbitrary-length preservation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent


def pdf_text(path):
    try:
        from pypdf import PdfReader
    except ImportError as error:
        raise SystemExit("Optional primary-PDF comparison requires pypdf.") from error
    return "\n".join(page.extract_text() for page in PdfReader(path).pages)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sdl-pdf", type=Path)
    parser.add_argument("--mr-pdf", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Do not run with Python -O.")
    small = json.loads((ROOT / "brinkhuis_18_2.json").read_text())
    images = small["images"]
    assert set(images) == {"0", "1", "2"}
    assert len({w for group in images.values() for w in group}) == 6
    for group in images.values():
        assert len(group) == 2 and all(len(w) == 18 for w in group)
    books = [(ROOT / f"brinkhuis_54_952_C{a}.txt").read_text().split() for a in range(3)]
    canonical = (ROOT.parent / "computational/base/inputs/codewords_54_952.txt").read_text().split()
    assert set(books[0]) == set(canonical)
    for a, book in enumerate(books):
        assert len(book) == len(set(book)) == 952
        assert all(len(w) == 54 and set(w) <= set("012") for w in book)
        tr = str.maketrans("012", "".join(str((i + a) % 3) for i in range(3)))
        assert set(book) == {w.translate(tr) for w in canonical}
    ext = json.loads((ROOT / "extremal_41_52_images.json").read_text())
    assert len(ext["images"]) == 12
    for vertex in ext["images"]:
        assert len(vertex["Q"]) == 41 and len(vertex["R"]) == 52
        assert len(vertex["left_cap"]) == len(vertex["right_cap"]) == 49
    print("RELEASED_CODEBOOK_CONSISTENCY_PASS")
    if args.sdl_pdf:
        text = pdf_text(args.sdl_pdf)
        base = re.findall(r"(?<![012])[012]{54}(?![012])", text)
        assert len(base) == len(set(base)) == 476
        assert set(base) | {w[::-1] for w in base} == set(canonical)
        assert all(w in text for group in images.values() for w in group)
        print("SDL_PUBLISHED_476_PLUS_REVERSALS_EXACT_MATCH")
        print("SDL_DISPLAYED_SIX_WORDS_EXACT_MATCH")
        print("SDL_PDF_SHA256", hashlib.sha256(args.sdl_pdf.read_bytes()).hexdigest())
    if args.mr_pdf:
        text = pdf_text(args.mr_pdf)
        for key, expected in ext["base_words"].items():
            assert re.search(r"\b" + key + r"\s*=\s*" + expected, text)
        print("MR_PUBLISHED_P_Q_R_S_EXACT_MATCH")
        print("MR_PDF_SHA256", hashlib.sha256(args.mr_pdf.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
