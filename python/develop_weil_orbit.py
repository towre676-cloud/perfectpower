"""Reproducible finite orbit/reflection evidence, separate from the paper proof."""
import json
from pathlib import Path
from perfectpower.weil_orbit import exact_orbit_certificate, exact_products_commute

ROOT = Path(__file__).resolve().parents[1]


def main():
    levels = sorted(set(range(1, 161)) | {243, 256, 343, 512, 625, 729})
    packets = [exact_orbit_certificate(n) for n in levels]
    dimensions = {p["level"]: p["dimension"] for p in packets}
    prior = json.loads((ROOT / "receipts/weil_commutant/summary.json").read_text())
    for row in prior["dimensions"]:
        assert dimensions[row["level"]] == row["dimension"]
    independent = (3, 4, 6, 8, 9, 12, 16, 18)
    assert all(exact_products_commute(n) for n in independent)
    result = {"schema": "pp-weil-orbit-census/1", "levels": len(levels),
              "packets": packets, "prior_exact_rows_matched": len(prior["dimensions"]),
              "independent_twisted_convolution_levels": list(independent),
              "paper_proof": "docs/WEIL_LOCAL_DIMENSION_MONOGRAPH.md",
              "execution_verified": False}
    out = ROOT / "receipts/weil_orbit/summary.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{len(levels)} exact phase/reflection levels; {len(prior['dimensions'])} prior rows; "
          f"{len(independent)} independent exact product levels")


if __name__ == "__main__":
    main()
