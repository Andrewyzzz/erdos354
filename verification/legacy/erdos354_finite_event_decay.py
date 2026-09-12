#!/usr/bin/env python3
"""Exact finite checks for the two-column event-decay proof.

This program does not certify the infinite theorem by sampling.  The proof in
its companion Markdown file supplies all infinite quantifiers.  All assertions
below use integers or fractions, not floating-point pass/fail decisions.

Run: python erdos354_finite_event_decay.py
Only the Python standard library is required.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random
import time

BITS = ((0, 0), (1, 0), (0, 1), (1, 1))


def subset_bits(weights: list[int]) -> int:
    ans = 1
    for w in weights:
        if not isinstance(w, int) or w < 0:
            raise ValueError("Weights must be nonnegative integers")
        ans |= ans << w
    return ans


def rotate(word: int, step: int, period: int) -> int:
    if period <= 0 or word < 0 or word.bit_length() > period:
        raise ValueError("Invalid circular word")
    step %= period
    if step == 0:
        return word
    return ((word << step) | (word >> (period - step))) & ((1 << period) - 1)


def boundary(word: int, step: int, period: int) -> int:
    return (word ^ rotate(word, step, period)).bit_count()


def add_pair(p: int, a: int, b: int) -> int:
    out = p | (p << a)
    return out | (out << b)


def boundary_check(p: int, a: int, b: int, uv: tuple[int, int],
                   uv_next: tuple[int, int]) -> dict[str, int]:
    """Also valid for an arbitrary subset of [0,a+b), not just subset sums."""
    assert 0 < b < a < 2 * b
    L = a + b
    assert p >= 0 and p.bit_length() <= L
    u, v = uv
    w = u + v
    a1, b1 = 2 * a + u, 2 * b + v
    L1 = a1 + b1
    assert L1 == 2 * L + w
    p1 = add_pair(p, a, b)
    p2 = add_pair(p1, a1, b1)
    G = p1.bit_count() - 2 * p.bit_count()
    G1 = p2.bit_count() - 2 * p1.bit_count()
    assert G >= 0 and G1 >= 0
    h = ((1 << L) - 1) ^ p
    h1 = ((1 << L1) - 1) ^ p1
    duplicated = h | (h << L)
    if w:
        duplicated |= (h & ((1 << w) - 1)) << (2 * L)
    assert (h1 ^ duplicated).bit_count() <= G + w
    JA = boundary(h, a, L)
    J = boundary(h, 1, L)
    assert JA <= 2 * G
    assert boundary(h1, a1, L1) <= 2 * G1
    if w:
        assert J <= 16 * G + 4 * G1 + 4 * w
        if u == 0:  # The wrapped case actually has a sharper estimate.
            assert J <= 6 * G + 2 * G1 + 2
    a2, b2 = 2 * a1 + uv_next[0], 2 * b1 + uv_next[1]
    return {"G": G, "G1": G1, "J": J, "w": w,
            "q": L - p.bit_count(), "q1": L1 - p1.bit_count(),
            "q2": a2 + b2 - p2.bit_count()}


def global_bound_check(q: int, n: int, events: int, M: int, N: int) -> None:
    """Square the claimed rho^(events/2) bound; use integers throughout."""
    C = 2 * (M + N + 10)
    den, num = 32 * N, 32 * N - 1
    assert q * q * pow(den, events) <= C * C * (1 << (2 * n)) * pow(num, events)


def prefix_check(M: int, N: int, code: tuple[tuple[int, int], ...], n: int) -> bool:
    assert 0 < N < M < 2 * N and len(code) >= n + 2
    aa, bb = [M], [N]
    for u, v in code:
        aa.append(2 * aa[-1] + u)
        bb.append(2 * bb[-1] + v)
    p = subset_bits(aa[:n] + bb[:n])
    L = aa[n] + bb[n]
    S = sum(aa[:n] + bb[:n])
    D = L - S
    assert D == M + N + sum(u + v for u, v in code[:n])
    result = boundary_check(p, aa[n], bb[n], code[n], code[n + 1])
    q, G, G1, J, w = (result[k] for k in ("q", "G", "G1", "J", "w"))
    assert result["q1"] == 2 * q + w - G
    assert 2 * (q - D) <= N * J
    if w:
        assert q <= 8 * N * G + 2 * N * G1 + 2 * N * w + D
        assert 8 * N * result["q2"] <= (32 * N - 1) * q + D + 52 * N
    K = sum(u + v > 0 for u, v in code[:n])
    global_bound_check(q, n, K, M, N)
    global_bound_check(result["q1"], n + 1, K + (w > 0), M, N)
    global_bound_check(result["q2"], n + 2,
                       K + (w > 0) + (sum(code[n + 1]) > 0), M, N)
    return w > 0


def exhaustive_prefixes() -> dict[str, int]:
    tested = events = 0
    for M, N in ((3, 2), (5, 3), (9, 6), (33, 22)):
        for n in range(6):
            for code in product(BITS, repeat=n + 2):
                events += prefix_check(M, N, code, n)
                tested += 1
    return {"prefix_configurations": tested, "nonzero_event_configurations": events,
            "exact_global_bound_checks": 3 * tested}


def arbitrary_sets() -> dict[str, int]:
    tested = 0
    for b in range(2, 5):
        for a in range(b + 1, 2 * b):
            for p in range(1 << (a + b)):
                for uv in BITS[1:]:
                    # G1 is independent of the next bits; one choice suffices here.
                    boundary_check(p, a, b, uv, (0, 0))
                    tested += 1
    return {"arbitrary_periodic_set_event_checks": tested}


def scalar_iteration() -> dict[str, int]:
    tested = 0
    for M, N in ((3, 2), (33, 22)):
        rho = Fraction(32 * N - 1, 32 * N)
        for n in range(13):
            for event_word in product((0, 1), repeat=n):
                z = Fraction(M + N - 1)
                i = r = 0
                while i < n:
                    if event_word[i] == 0:
                        i += 1
                    elif i + 1 < n:
                        z = rho * z + Fraction(2 * (i + 1), 1 << i)
                        r += 1
                        i += 2
                    else:
                        z += Fraction(1, 1 << i)
                        i += 1
                assert 2 * r + 1 >= sum(event_word)
                assert z <= (M + N + 10) * rho ** r
                assert z * z <= (2 * (M + N + 10)) ** 2 * rho ** sum(event_word)
                tested += 1
    return {"worst_case_scalar_event_schedules": tested}


def longer_prefixes() -> dict[str, int]:
    rng = random.Random(35420260909)
    tested = 0
    for M, N in ((3, 2), (9, 6), (33, 22)):
        for n in (8, 12, 16):
            words = [tuple([uv] * (n + 2)) for uv in BITS]
            words.extend(tuple(rng.choice(BITS) for _ in range(n + 2)) for _ in range(6))
            for code in words:
                prefix_check(M, N, code, n)
                tested += 1
    return {"longer_exact_prefix_checks": tested}


def run_starts(p: int, length: int) -> int:
    """Bits marking starts of a run of at least length ones."""
    if length < 1:
        raise ValueError("length must be positive")
    out, size = p, 1
    while 2 * size <= length:
        out &= out >> size
        size *= 2
    if length > size:
        out &= out >> (length - size)
    return out


def algebraic_examples() -> list[dict[str, int | str]]:
    # These finite witnesses are separate from the algebraic all-parameter corollary.
    rows = []
    for beta in (3, 10, 100):
        p = 1
        for n in range(1, 18):
            b = beta * (1 << (n - 1))
            a = isqrt(2 * b * b)  # Exact floor(2^(n-1) beta sqrt(2)).
            p = add_pair(p, a, b)
            width = 2 * b + 1
            starts = run_starts(p, width + 1)
            if starts:
                lo = (starts & -starts).bit_length() - 1
                mask = (1 << (width + 1)) - 1
                assert (p >> lo) & mask == mask
                rows.append({"alpha": f"{beta}*sqrt(2)", "beta": beta,
                             "prefix_pairs": n, "interval_start": lo,
                             "interval_end": lo + width, "width": width,
                             "next_element": 2 * b})
                break
        else:
            raise AssertionError("Finite search budget exhausted; not a disproof")
    return rows


def main() -> None:
    started = time.monotonic()
    result: dict[str, object] = {
        "status": "Finite checks only; infinite statements require the companion proof.",
        "arithmetic": "integer and fractions.Fraction; no floating-point pass/fail checks",
        "exhaustive_prefixes": exhaustive_prefixes(),
        "arbitrary_sets": arbitrary_sets(),
        "scalar_iteration": scalar_iteration(),
        "longer_prefixes": longer_prefixes(),
        "finite_algebraic_examples": algebraic_examples(),
    }
    result["elapsed_seconds_diagnostic_only"] = round(time.monotonic() - started, 3)
    path = Path(__file__).with_name("erdos354_finite_event_decay_results.json")
    path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
