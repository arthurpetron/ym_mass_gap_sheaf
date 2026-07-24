"""DP.6 signed-sector survival: s-weighted channel sums over the triple corpus.

The question this module decides, exactly: do the heat-kernel-weighted
channel sums over the FULL triple-surface corpus of the 4-cube boundary
stay positive on all of s in (0, 1) — negative (spin >= 3) sector
included?

Derivation.  The 4-cube boundary carries 128 binary closed surfaces
(the F2 kernel of the face-edge incidence; computations/
hypercube4d_survey.py).  A k-fold surface combination assigns integer
spins n = 2j <= k per face via mod-free addition (combo_spins).  The
triple sweep (all C(128,3) = 341,376 combinations, spins <= 3) is the
first corpus where negative dual amplitudes occur: 32,384 negative-Z
triples, every one requiring a spin-3 face, with minimal exemplar
Z = -1/3981312 at spin profile {1:x9, 2:x6, 3:x3} (§15a; pinned by
tests/test_vertex_amplitude.py).

The DP.6 survival test weights each assignment by its exact heat-kernel
activity mass.  A face with spin n > 0 contributes d_n * s^{n(n+2)}
(d_n = n + 1, 4C_2 = n(n+2), s = e^{-t/4}), so

    Weight(assignment) = prod_{faces, n>0} (n+1) * s^{sum_f n_f(n_f+2)}
                       = c * s^E,   c in Z_{>0},  E = sum n(n+2),

and the channel sum attached to a configuration class (= sorted multiset
of nonzero face spins, the "spin profile") is

    F_class(s) = sum_{assignments in class} Z(assignment) * c * s^E.

Both c and E depend only on the profile, so F_class is a single exact
monomial c * (sum Z) * s^E: the class verdict on (0,1) is the sign of
the summed amplitude, and the genuine polynomial cancellation question
lives in the global sum F(s) = sum_classes F_class(s), where classes of
different exponent E compete.  Sign verdicts on (0,1) use the repo's
exact Sturm machinery (exact_haar_network.sign_on_unit_interval);
amplitudes come from the certified vertex product formula
(computations/vertex_amplitude.py, 949/949 vs the moment engine).

Truncation honesty: the triple corpus is exactly closed under fusion —
spins <= 3 by construction, no tail.  The pair (k = 2) and single
(k = 1) sectors are known all-positive (109/109 orbit survey) and can
only add positivity; --include-lower folds them (and the empty
assignment, Z = 1) into a second global sum for the full <=3 channel.

All arithmetic is Fraction-exact; no floating point anywhere.

Run:  python -m computations.dp6_signed_survival
      python -m computations.dp6_signed_survival --include-lower
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

from computations.exact_haar_network import (
    SPoly,
    sign_on_unit_interval,
    sp_str,
)
from computations.vertex_amplitude import (
    amplitude,
    combo_spins,
    surface_masks,
)

Frac = Fraction

# Expected corpus pins (§15a / tests/test_vertex_amplitude.py).
EXPECT_N_TRIPLES = 341_376
EXPECT_N_NEGATIVE = 32_384
EXPECT_MIN_Z = Frac(-1, 3981312)
EXPECT_MIN_Z_PROFILE = ((1, 9), (2, 6), (3, 3))

ENDPOINTS: List[Fraction] = [
    Frac(1, 2),
    Frac(3, 4),
    Frac(9, 10),
    Frac(99, 100),
    Frac(999, 1000),
]


# ---------------------------------------------------------------------------
# Profiles and weights.
# ---------------------------------------------------------------------------

Profile = Tuple[Tuple[int, int], ...]  # ((spin, multiplicity), ...) sorted


def profile_of(spins: Sequence[int]) -> Profile:
    """Sorted multiset of nonzero face spins, e.g. ((1, 9), (2, 6), (3, 3))."""
    counts: Dict[int, int] = {}
    for n in spins:
        if n:
            counts[n] = counts.get(n, 0) + 1
    return tuple(sorted(counts.items()))


def profile_weight(prof: Profile) -> Tuple[int, int]:
    """(c, E): heat-kernel weight c * s^E of any assignment in the class."""
    c = 1
    e = 0
    for n, mult in prof:
        c *= (n + 1) ** mult
        e += n * (n + 2) * mult
    return c, e


def profile_str(prof: Profile) -> str:
    return " ".join(f"{n}^{m}" for n, m in prof) if prof else "(empty)"


# ---------------------------------------------------------------------------
# Exact SPoly helpers (evaluation; the algebra lives in exact_haar_network).
# ---------------------------------------------------------------------------


def sp_eval(p: SPoly, s: Fraction) -> Fraction:
    return sum((c * s**k for k, c in p.items()), Frac(0))


def sp_split_eval(p: SPoly, s: Fraction) -> Tuple[Fraction, Fraction]:
    """(positive part, |negative part|) of p evaluated at s > 0."""
    pos = neg = Frac(0)
    for k, c in p.items():
        if c > 0:
            pos += c * s**k
        else:
            neg -= c * s**k
    return pos, neg


def sp_json(p: SPoly) -> Dict[str, str]:
    return {str(k): str(p[k]) for k in sorted(p)}


# ---------------------------------------------------------------------------
# Per-class accumulator.
# ---------------------------------------------------------------------------


class ClassRecord:
    __slots__ = ("prof", "coeff", "exp", "z_sum", "n_total", "n_nonzero",
                 "n_negative", "min_z", "neg_mass")

    def __init__(self, prof: Profile):
        self.prof = prof
        self.coeff, self.exp = profile_weight(prof)
        self.z_sum = Frac(0)          # sum of Z over members (weight = coeff)
        self.n_total = 0              # all triples with this profile
        self.n_nonzero = 0
        self.n_negative = 0
        self.min_z: Optional[Fraction] = None
        self.neg_mass = Frac(0)       # sum of |Z| * coeff over negative members

    def add(self, z: Fraction) -> None:
        self.n_total += 1
        if not z:
            return
        self.n_nonzero += 1
        self.z_sum += z
        if z < 0:
            self.n_negative += 1
            self.neg_mass += -z * self.coeff
        if self.min_z is None or z < self.min_z:
            self.min_z = z

    @property
    def poly(self) -> SPoly:
        c = self.z_sum * self.coeff
        return {self.exp: c} if c else {}


# ---------------------------------------------------------------------------
# Sweeps.
# ---------------------------------------------------------------------------


def sweep_triples(progress_every: int = 50_000):
    """All C(128,3) triples: per-profile class records + negative census.

    Returns (classes, n_eval, n_negative, min_z, min_z_profile,
    negatives_all_have_spin3).
    """
    surf = surface_masks()
    nf = 24
    bits = {m: [(m >> i) & 1 for i in range(nf)] for m in surf}
    classes: Dict[Profile, ClassRecord] = {}
    n_eval = 0
    n_negative = 0
    min_z: Optional[Fraction] = None
    min_z_profile: Optional[Profile] = None
    neg_all_spin3 = True
    t0 = time.time()
    for ma, mb, mc in itertools.combinations(surf, 3):
        ba, bb, bc = bits[ma], bits[mb], bits[mc]
        spins = [ba[i] + bb[i] + bc[i] for i in range(nf)]
        z = amplitude(spins)
        prof = profile_of(spins)
        rec = classes.get(prof)
        if rec is None:
            rec = classes[prof] = ClassRecord(prof)
        rec.add(z)
        if z < 0:
            n_negative += 1
            if max(spins) < 3:
                neg_all_spin3 = False
            if min_z is None or z < min_z:
                min_z, min_z_profile = z, prof
        n_eval += 1
        if progress_every and n_eval % progress_every == 0:
            print(f"    ...{n_eval} triples, {len(classes)} classes, "
                  f"{n_negative} negative  [{time.time() - t0:.0f}s]",
                  flush=True)
    return classes, n_eval, n_negative, min_z, min_z_profile, neg_all_spin3


def lower_sector_poly() -> SPoly:
    """Exact weighted sum over the empty + single + pair sectors.

    All amplitudes here are positive (109/109 pair-orbit survey), so this
    only adds positive monomials to the global sum.
    """
    surf = surface_masks()
    acc: SPoly = {}
    combos: List[Tuple[int, ...]] = [()]
    combos += [(m,) for m in surf]
    combos += list(itertools.combinations(surf, 2))
    for masks in combos:
        spins = combo_spins(masks)
        z = amplitude(spins)
        if not z:
            continue
        assert z > 0, f"lower sector produced negative Z at {masks}"
        c, e = profile_weight(profile_of(spins))
        acc[e] = acc.get(e, Frac(0)) + z * c
    return {k: v for k, v in acc.items() if v}


# ---------------------------------------------------------------------------
# Reporting.
# ---------------------------------------------------------------------------


def endpoint_table(p: SPoly) -> Dict[str, str]:
    return {str(s): str(sp_eval(p, s)) for s in ENDPOINTS}


def certification_method(p: SPoly) -> str:
    """How sign_on_unit_interval decided this polynomial's sign.

    'coefficient-signs' = the exact fast path (all coefficients share a
    sign; the verdict needs no root counting).  'sturm' = genuine
    square-free + Sturm root counting on (0,1).  Either way the verdict
    is exact; the label records which certificate carries it.
    """
    if not p:
        return "zero"
    signs = {v > 0 for v in p.values()}
    return "coefficient-signs" if len(signs) == 1 else "sturm"


def crossover_margin(rec: ClassRecord, s: Fraction) -> Fraction:
    """(negative part)/(positive part) of the class channel at s."""
    pos_mass = (rec.z_sum + rec.neg_mass / rec.coeff) * rec.coeff
    # pos_mass = coeff * sum of positive Z; both parts share s^E, so the
    # ratio is s-independent; evaluated at s for the ledger anyway.
    neg = rec.neg_mass * s**rec.exp
    pos = pos_mass * s**rec.exp
    return neg / pos if pos else Frac(-1)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--include-lower", action="store_true",
                    help="fold the (all-positive) empty/single/pair sectors "
                         "into a second global sum")
    ap.add_argument("--json", default="dp6_results.json")
    ap.add_argument("--report", default="dp6_report.md")
    args = ap.parse_args()

    t_start = time.time()
    print("DP.6 signed-sector survival: full C(128,3) triple corpus")
    print(f"triples sweep (all {EXPECT_N_TRIPLES} combinations, spins <= 3):")
    (classes, n_eval, n_negative, min_z, min_z_profile,
     neg_all_spin3) = sweep_triples()

    # --- sanity pins (§15a) -----------------------------------------------
    pins = {
        "n_triples": {"expected": EXPECT_N_TRIPLES, "got": n_eval,
                      "ok": n_eval == EXPECT_N_TRIPLES},
        "n_negative": {"expected": EXPECT_N_NEGATIVE, "got": n_negative,
                       "ok": n_negative == EXPECT_N_NEGATIVE},
        "negatives_require_spin3": {"expected": True, "got": neg_all_spin3,
                                    "ok": neg_all_spin3},
        "min_Z": {"expected": str(EXPECT_MIN_Z), "got": str(min_z),
                  "ok": min_z == EXPECT_MIN_Z},
        "min_Z_profile": {"expected": profile_str(EXPECT_MIN_Z_PROFILE),
                          "got": profile_str(min_z_profile or ()),
                          "ok": min_z_profile == EXPECT_MIN_Z_PROFILE},
    }
    pins_ok = all(p["ok"] for p in pins.values())
    print("sanity pins:", "ALL OK" if pins_ok else "FAILURES PRESENT")
    for name, p in pins.items():
        mark = "ok" if p["ok"] else "**MISMATCH**"
        print(f"    {name}: expected {p['expected']}, got {p['got']}  [{mark}]")
    if not pins_ok:
        print("!!! SANITY-PIN DISCREPANCY: corpus does not reproduce §15a; "
              "results below are suspect !!!")

    # --- per-class verdicts ----------------------------------------------
    mixed = {p: r for p, r in classes.items() if r.n_negative > 0}
    pure = {p: r for p, r in classes.items() if r.n_negative == 0}
    print(f"classes: {len(classes)} total; {len(mixed)} mixed "
          f"(contain negative-Z members); {len(pure)} pure-positive")

    class_records = []
    n_sturm = 0
    worst_class_verdict = "positive"
    for prof in sorted(classes):
        rec = classes[prof]
        entry = {
            "profile": profile_str(prof),
            "coeff": rec.coeff,
            "exp": rec.exp,
            "n_total": rec.n_total,
            "n_nonzero": rec.n_nonzero,
            "n_negative": rec.n_negative,
            "min_Z": str(rec.min_z) if rec.min_z is not None else None,
            "neg_mass": str(rec.neg_mass),
            "class_sum_Z": str(rec.z_sum),
        }
        if rec.n_negative == 0:
            entry["verdict"] = ("TRIVIAL-POSITIVE" if rec.z_sum > 0
                                else "TRIVIAL-ZERO" if rec.z_sum == 0
                                else "IMPOSSIBLE")
        else:
            verdict = sign_on_unit_interval(rec.poly)
            n_sturm += 1
            entry["verdict"] = verdict
            entry["certified_by"] = certification_method(rec.poly)
            entry["polynomial"] = sp_json(rec.poly)
            entry["endpoints"] = endpoint_table(rec.poly)
            entry["margin_at_999_1000"] = str(
                crossover_margin(rec, Frac(999, 1000)))
            if verdict != "positive" and worst_class_verdict == "positive":
                worst_class_verdict = verdict
        class_records.append(entry)

    # --- global sums ------------------------------------------------------
    global_poly: SPoly = {}
    for rec in classes.values():
        for k, v in rec.poly.items():
            nv = global_poly.get(k, Frac(0)) + v
            if nv:
                global_poly[k] = nv
            else:
                global_poly.pop(k, None)
    global_verdict = sign_on_unit_interval(global_poly)
    n_sturm += 1
    global_rec = {
        "sector": "triples only",
        "verdict": global_verdict,
        "certified_by": certification_method(global_poly),
        "polynomial": sp_json(global_poly),
        "endpoints": endpoint_table(global_poly),
        "n_terms": len(global_poly),
        "any_negative_coeff": any(v < 0 for v in global_poly.values()),
    }
    print(f"global sum (triples): {len(global_poly)} monomials, "
          f"verdict on (0,1): {global_verdict}")

    global_lower_rec = None
    if args.include_lower:
        print("folding in empty + single + pair sectors (all-positive)...")
        low = lower_sector_poly()
        full: SPoly = dict(global_poly)
        for k, v in low.items():
            nv = full.get(k, Frac(0)) + v
            if nv:
                full[k] = nv
            else:
                full.pop(k, None)
        v_full = sign_on_unit_interval(full)
        n_sturm += 1
        global_lower_rec = {
            "sector": "empty + singles + pairs + triples",
            "verdict": v_full,
            "certified_by": certification_method(full),
            "polynomial": sp_json(full),
            "endpoints": endpoint_table(full),
            "n_terms": len(full),
            "any_negative_coeff": any(v < 0 for v in full.values()),
        }
        print(f"global sum (with lower sectors): {len(full)} monomials, "
              f"verdict on (0,1): {v_full}")

    runtime = time.time() - t_start

    # --- headline ---------------------------------------------------------
    neg_classes = [p for p, r in mixed.items() if r.z_sum < 0]
    survived = (worst_class_verdict == "positive"
                and global_verdict == "positive")
    if survived:
        headline = ("DP.6 SURVIVED: every mixed-class channel sum and the "
                    "global sum are certified positive on all of s in (0,1)")
    elif global_verdict == "positive":
        headline = (
            f"DP.6 SPLIT VERDICT: per-class survival fails — "
            f"{len(neg_classes)} of {len(mixed)} mixed classes have "
            f"negative channel sums (each a single monomial, hence "
            f"negative on ALL of s in (0,1): "
            f"{', '.join(profile_str(p) for p in sorted(neg_classes))}) — "
            f"but the GLOBAL sum is certified positive on all of (0,1); "
            f"cross-class cancellation at each s-exponent restores "
            f"positivity")
    else:
        headline = (f"DP.6 SIGN CHANGE: worst class verdict "
                    f"'{worst_class_verdict}', global verdict "
                    f"'{global_verdict}' — see mixed-class table")
    print(headline)
    print(f"runtime: {runtime:.1f}s; Sturm calls: {n_sturm} "
          f"(pure-positive classes certified trivially)")

    # --- cancellation ledger at negative-class exponents ------------------
    ledger = []
    for prof in sorted(neg_classes):
        e = classes[prof].exp
        contributors = sorted(
            ((profile_str(p), r.z_sum * r.coeff)
             for p, r in classes.items() if r.exp == e and r.z_sum),
            key=lambda t: t[1])
        ledger.append({
            "negative_class": profile_str(prof),
            "exp": e,
            "global_coeff": str(global_poly.get(e, Frac(0))),
            "contributors": {p: str(v) for p, v in contributors},
        })

    # --- outputs ----------------------------------------------------------
    results = {
        "headline": headline,
        "survived": survived,
        "sanity_pins": pins,
        "sanity_pins_ok": pins_ok,
        "n_classes": len(classes),
        "n_mixed_classes": len(mixed),
        "n_sturm_calls": n_sturm,
        "classes": class_records,
        "global": global_rec,
        "global_with_lower": global_lower_rec,
        "cancellation_ledger": ledger,
        "runtime_seconds": round(runtime, 2),
    }
    with open(args.json, "w") as fh:
        json.dump(results, fh, indent=1)
    print(f"wrote {args.json}")

    write_report(args.report, results, classes, mixed, global_poly)
    print(f"wrote {args.report}")


def write_report(path: str, results, classes, mixed, global_poly: SPoly) -> None:
    lines = []
    a = lines.append
    a("# DP.6 signed-sector survival — full triple corpus")
    a("")
    a("Exact s-weighted channel sums over all C(128,3) = 341,376 "
      "triple-surface assignments of the 4-cube boundary, negative "
      "(spin-3) sector included.  Weight per face with spin n > 0: "
      "d_n s^{n(n+2)}; amplitudes from the certified vertex product "
      "formula; all arithmetic Fraction-exact.")
    a("")
    a(f"**Headline: {results['headline']}.**")
    a("")
    a("## Sanity pins (§15a)")
    a("")
    a("| pin | expected | got | ok |")
    a("|---|---|---|---|")
    for name, p in results["sanity_pins"].items():
        a(f"| {name} | {p['expected']} | {p['got']} | "
          f"{'yes' if p['ok'] else '**NO**'} |")
    a("")
    a(f"## Classes ({results['n_classes']} spin profiles, "
      f"{results['n_mixed_classes']} mixed)")
    a("")
    a("Every member of a class shares the weight monomial c s^E "
      "(c, E fixed by the profile), so each class channel is the exact "
      "monomial c (sum Z) s^E and its sign on (0,1) is the sign of the "
      "summed amplitude — s-INDEPENDENT, so no crossover in s can occur "
      "inside a class.  Pure-positive classes are trivially positive.  "
      "Mixed-class and global verdicts go through the repo's "
      "sign_on_unit_interval; the 'certified by' column records whether "
      "the exact coefficient-sign fast path sufficed or genuine Sturm "
      "root counting was needed.")
    a("")
    a("### Mixed classes (contain negative-Z members)")
    a("")
    a("| profile | E | members | nonzero | negative | min Z | sum Z | "
      "neg/pos margin | verdict | certified by |")
    a("|---|---|---|---|---|---|---|---|---|---|")
    for entry in results["classes"]:
        if "polynomial" not in entry:
            continue
        a(f"| {entry['profile']} | {entry['exp']} | {entry['n_total']} | "
          f"{entry['n_nonzero']} | {entry['n_negative']} | "
          f"{entry['min_Z']} | {entry['class_sum_Z']} | "
          f"{entry['margin_at_999_1000']} | {entry['verdict']} | "
          f"{entry['certified_by']} |")
    a("")
    a("The neg/pos margin is (negative mass)/(positive mass) at "
      "s = 999/1000; since both parts share s^E it is s-independent.  "
      "A margin > 1 means the class channel sum is negative.")
    a("")
    a("### Endpoint values (exact rationals, mixed classes + global)")
    a("")
    header = " | ".join(str(s) for s in ENDPOINTS)
    a(f"| channel | {header} |")
    a("|---" * (len(ENDPOINTS) + 1) + "|")
    for entry in results["classes"]:
        if "endpoints" not in entry:
            continue
        vals = " | ".join(entry["endpoints"][str(s)] for s in ENDPOINTS)
        a(f"| {entry['profile']} | {vals} |")
    gvals = " | ".join(results["global"]["endpoints"][str(s)]
                       for s in ENDPOINTS)
    a(f"| **global (triples)** | {gvals} |")
    if results["global_with_lower"]:
        gl = " | ".join(results["global_with_lower"]["endpoints"][str(s)]
                        for s in ENDPOINTS)
        a(f"| **global (+ lower sectors)** | {gl} |")
    a("")
    a("## Global sum")
    a("")
    a(f"- triples only: {results['global']['n_terms']} monomials; "
      f"negative coefficients present: "
      f"{results['global']['any_negative_coeff']}; verdict on (0,1): "
      f"**{results['global']['verdict']}** "
      f"(certified by {results['global']['certified_by']})")
    a(f"  - F(s) = {sp_str(global_poly)}")
    if results["global_with_lower"]:
        a(f"- with empty/single/pair sectors folded in: "
          f"{results['global_with_lower']['n_terms']} monomials; verdict: "
          f"**{results['global_with_lower']['verdict']}** "
          f"(certified by {results['global_with_lower']['certified_by']})")
    if results["cancellation_ledger"]:
        a("")
        a("## Cross-class cancellation at negative-class exponents")
        a("")
        a("For each class with a negative channel sum, the exact global "
          "s^E coefficient after summing every class sharing that "
          "exponent:")
        a("")
        for led in results["cancellation_ledger"]:
            a(f"- **{led['negative_class']}** (E = {led['exp']}): global "
              f"coefficient {led['global_coeff']}")
            for p, v in led["contributors"].items():
                a(f"    - {p}: {v}")
    a("")
    a(f"Runtime: {results['runtime_seconds']}s; Sturm calls: "
      f"{results['n_sturm_calls']}.")
    a("")
    with open(path, "w") as fh:
        fh.write("\n".join(lines))


if __name__ == "__main__":
    main()
