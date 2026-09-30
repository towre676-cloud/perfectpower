from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "DATA" / "RELATION" / "TASK_SELECTED_WORD_PROGRAMS_V23"

PROGRAM_FILES = (
    "sensor_d8_m12_padic.json",
    "sensor_d9_p1_padic.json",
    "paley_d8_m12_padic.json",
    "paley_d9_p1_padic.json",
)

MINUS = (
    np.arange(261, 336),
    np.arange(336, 411),
    np.arange(411, 486),
)
PLUS = (
    np.arange(251, 256),
    np.arange(256, 261),
)

GENERATOR_COST = {"G": 1732, "H": 1689}


def load_summary() -> dict[str, Any]:
    return json.loads((DATA / "summary.json").read_text(encoding="utf-8"))


def load_audit() -> dict[str, Any]:
    return json.loads((DATA / "multiprime_sparse_audit.json").read_text(encoding="utf-8"))


def load_program(name: str) -> dict[str, Any]:
    if name not in PROGRAM_FILES:
        raise KeyError(name)
    return json.loads((DATA / name).read_text(encoding="utf-8"))


def target_vector(task: str) -> np.ndarray:
    t = np.zeros(152, dtype=object)
    if task == "sensor":
        t[12] = 1
        t[48] = 1
    elif task == "paley":
        for j, s in ((12, -1), (125, 1), (48, -1), (116, 1), (59, -1), (95, 1)):
            t[j] = s
    else:
        raise KeyError(task)
    return t


def allowed_native_indices(program: dict[str, Any]) -> np.ndarray:
    degree = int(program["degree"])
    mask = program["mask"]
    if degree == 8 and mask == "m12":
        return np.r_[MINUS[0], MINUS[1]]
    if degree == 9 and mask == "p1":
        return PLUS[0]
    raise ValueError((degree, mask))


def exact_verify_program(name: str) -> dict[str, Any]:
    p = load_program(name)
    mats = np.load(DATA / "exact_prefix_1023.npz", allow_pickle=True)
    wn = mats["native"]
    wh = mats["hecke"]
    nums = np.asarray([int(x) for x in p["numerators"]], dtype=object)
    den = int(p["denominator"])
    n = len(nums)

    h = wh[:n].T @ nums
    hecke_ok = np.array_equal(h, target_vector(p["task"]) * den)

    allowed = allowed_native_indices(p)
    outside = np.ones(486, dtype=bool)
    outside[allowed] = False
    native = wn[:n].T @ nums
    native_ok = all(int(x) == 0 for x in native[outside])
    allowed_nonzero = sum(int(x) != 0 for x in native[~outside])

    return {
        "file": name,
        "task": p["task"],
        "degree": int(p["degree"]),
        "mask": p["mask"],
        "support_count": n,
        "nonzero_coefficients": sum(int(x) != 0 for x in nums),
        "denominator_bits": den.bit_length(),
        "max_numerator_bits": max(abs(int(x)).bit_length() for x in nums),
        "hecke_exact": bool(hecke_ok),
        "native_mask_exact": bool(native_ok),
        "allowed_native_nonzero_coordinates": int(allowed_nonzero),
    }


def prefix_cost(support_count: int) -> dict[str, int]:
    # Breadth-first binary words: after identity, extensions alternate G,H.
    edges = support_count - 1
    g_edges = (edges + 1) // 2
    h_edges = edges // 2
    cost = g_edges * GENERATOR_COST["G"] + h_edges * GENERATOR_COST["H"]
    return {"edges": edges, "G_edges": g_edges, "H_edges": h_edges, "primitive_cost": cost}
