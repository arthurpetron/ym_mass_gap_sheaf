"""Generate DP6Ledger.lean from dp6_results.json — and verify the result.

Provenance chain: computations/dp6_signed_survival.py sweeps all
C(128,3) = 341,376 triple-surface assignments of the 4-cube boundary
and writes dp6_results.json; this script transcribes the DP.6 verdict
literals (global monomial ledgers, the four negative class sums, the
per-exponent cancellation ledger, the sanity pins) into a standalone
kernel-checkable Lean 4 file in the dual_kappa_spike style (no Mathlib,
axiom budget {propext, Quot.sound}, closed `decide` arithmetic only).

The generator is the anti-mistranscription device: literals never pass
through human hands, and after emitting the .lean file it RE-PARSES it
with a bracket-tuple parser and compares every parsed literal against a
fresh read of the JSON.  It also machine-checks delimiter balance.

Run:  python gen_dp6_lean.py            (from lean_out/)
      python gen_dp6_lean.py --json ../dp6_results.json --out DP6Ledger.lean
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent


# ---------------------------------------------------------------------------
# JSON -> canonical data.
# ---------------------------------------------------------------------------


def parse_profile(s: str):
    """'1^8 2^11 3^4' -> [(1, 8), (2, 11), (3, 4)]."""
    out = []
    for tok in s.split():
        n, m = tok.split("^")
        out.append((int(n), int(m)))
    return out


def profile_exp(prof) -> int:
    return sum(n * (n + 2) * m for n, m in prof)


def profile_coeff(prof) -> int:
    c = 1
    for n, m in prof:
        c *= (n + 1) ** m
    return c


def load(json_path: Path):
    d = json.loads(json_path.read_text())

    monos = [(int(k), Fraction(v))
             for k, v in sorted(d["global_with_lower"]["polynomial"].items(),
                                key=lambda kv: int(kv[0]))]
    monos_t = [(int(k), Fraction(v))
               for k, v in sorted(d["global"]["polynomial"].items(),
                                  key=lambda kv: int(kv[0]))]
    assert len(monos) == d["global_with_lower"]["n_terms"] == 80
    assert len(monos_t) == d["global"]["n_terms"] == 75
    assert all(v > 0 for _, v in monos) and all(v > 0 for _, v in monos_t)

    # Negative classes, in the (sorted-profile) order the ledger uses.
    neg = []
    for c in d["classes"]:
        zsum = Fraction(c["class_sum_Z"])
        if zsum < 0:
            prof = parse_profile(c["profile"])
            assert c["exp"] == profile_exp(prof)
            assert c["coeff"] == profile_coeff(prof)
            neg.append((prof, zsum, zsum * c["coeff"]))
    assert len(neg) == 4

    ledger = []
    for led, (prof, zsum, chan) in zip(d["cancellation_ledger"], neg):
        assert parse_profile(led["negative_class"]) == prof
        e = led["exp"]
        assert e == profile_exp(prof)
        vals = [Fraction(v) for v in led["contributors"].values()]
        p_sub = sum(v for v in vals if v > 0)
        n_sub = sum(v for v in vals if v < 0)
        g = Fraction(led["global_coeff"])
        assert p_sub + n_sub == g, (e, p_sub, n_sub, g)
        assert led["contributors"][led["negative_class"]] == str(chan)
        assert g == dict(monos_t)[e]
        ledger.append((e, p_sub, n_sub, g))
    assert [e for e, *_ in ledger] == [136, 138, 148, 172] or True  # order below
    assert sorted(e for e, *_ in ledger) == [136, 138, 148, 172]

    pins = d["sanity_pins"]
    assert pins["n_triples"]["got"] == 341376
    assert pins["n_negative"]["got"] == 32384
    assert pins["negatives_require_spin3"]["got"] is True
    min_z = Fraction(pins["min_Z"]["got"])
    assert min_z == Fraction(-1, 3981312)
    min_prof = parse_profile(pins["min_Z_profile"]["got"])
    assert min_prof == [(1, 9), (2, 6), (3, 3)]

    return {
        "monos": monos,
        "monos_t": monos_t,
        "neg": neg,
        "ledger": ledger,
        "min_z": min_z,
        "min_prof": min_prof,
        "min_exp": profile_exp(min_prof),
    }


# ---------------------------------------------------------------------------
# Rendering.
# ---------------------------------------------------------------------------


def q(fr: Fraction) -> str:
    return f"({fr.numerator}, {fr.denominator})"


def render_mono_list(name: str, doc: str, monos) -> str:
    body = ",\n".join(f"    ({e}, {q(v)})" for e, v in monos)
    return f"/-- {doc} -/\ndef {name} : List (Nat × Q) :=\n  [ {body.lstrip()} ]\n"


def render(data) -> str:
    monos, monos_t = data["monos"], data["monos_t"]
    neg, ledger = data["neg"], data["ledger"]

    neg_body = ",\n".join(
        "    ([" + ", ".join(f"({n}, {m})" for n, m in prof) + "], "
        + f"{q(zsum)}, {q(chan)})"
        for prof, zsum, chan in neg)
    ledger_body = ",\n".join(
        f"    ({e}, {q(p)}, {q(n)}, {q(g)})" for e, p, n, g in ledger)

    header = f'''/-
  DP6Ledger.lean — the DP.6 signed-sector survival verdict,
  kernel-checked at the coefficient-ledger level.

  GENERATED FILE: emitted by lean_out/gen_dp6_lean.py from
  dp6_results.json; upstream computation
  computations/dp6_signed_survival.py (the exact s-weighted channel
  sums over the full C(128,3) = 341,376 triple-surface corpus of the
  4-cube boundary, spin-3 sector included; amplitudes from the
  certified vertex product formula, all arithmetic Fraction-exact).
  Do not edit literals by hand — regenerate.

  The verdict this file banks (DP.6 SPLIT VERDICT):

  * PER-CLASS SURVIVAL FAILS.  Every configuration class (= spin
    profile) has channel sum c · (Σ Z) · s^E, a single monomial, so
    its sign on (0,1) is s-INDEPENDENT — and exactly four classes
    have negative channel sums (`negClasses`, kernel-checked
    negative).  This is the Lakatos fence: the counterexample side
    of the verdict, machine-banked.

  * THE GLOBAL SUM SURVIVES.  All 80 monomial coefficients of the
    global sum with lower sectors folded in (`globalMonomials`), and
    all 75 of the triples-only sum (`globalTriplesMonomials`), are
    strictly positive (kernel-checked), hence each global sum is a
    positive combination of s^E on (0,1) and strictly positive
    there.  Only the coefficient-sign ledger is formalized here;
    "positive polynomial on (0,1)" as a statement about real/rational
    evaluation is NOT formalized in this file (the FrozenHub-style
    evalNum bridge is the natural next step).

  * THE CANCELLATION IS LOCAL IN THE EXPONENT.  At each negative
    class's exponent E ∈ {{136, 138, 148, 172}}, the positive
    subtotal P_E and negative subtotal N_E of the classes sharing
    that exponent satisfy N_E < 0 < P_E + N_E, and P_E + N_E equals
    the recorded global s^E coefficient (`exponent_ledger_balances`,
    `ledger_matches_global`): positivity is restored class-by-class
    at exponent granularity, not by cross-exponent competition.

  Rationals are (numerator : Int, denominator : Nat) pairs with
  positive denominators; all comparisons cross-multiply into Int so
  kernel `decide` stays on closed integer arithmetic.

  Provenance caveat (spike-wide): the ledger literals are transported
  from the Python quaternion-Haar machinery; re-deriving them inside
  Lean from the main tree's finite product Haar evaluation is the
  wiring TODO shared with DualKappa.lean and FrozenHub.lean.

  Axiom budget: {{propext, Quot.sound}} at most.  No Mathlib.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace DP6Ledger

/-- An exact rational as (numerator, denominator) with the denominator
a positive `Nat`; comparisons cross-multiply into `Int` so every proof
below is closed integer arithmetic under kernel `decide`. -/
abbrev Q := Int × Nat

def qDen (a : Q) : Int := Int.ofNat a.2

def qPos (a : Q) : Bool := decide (0 < a.1) && decide (0 < a.2)

def qNeg (a : Q) : Bool := decide (a.1 < 0) && decide (0 < a.2)

/-- Cross-multiplied equality (valid whenever denominators are
positive, which `qPos`/`qNeg`/`ledgerBalanced` also check). -/
def qEq (a b : Q) : Bool := decide (a.1 * qDen b = b.1 * qDen a)

def qAdd (a b : Q) : Q := (a.1 * qDen b + b.1 * qDen a, a.2 * b.2)

def qMulNat (a : Q) (k : Nat) : Q := (a.1 * Int.ofNat k, a.2)

/-- Spin profile as (spin, multiplicity) pairs. -/
abbrev Profile := List (Nat × Nat)

/-- Heat-kernel exponent of a profile: E = Σ n(n+2)·mult
(4C₂(n/2) = n(n+2); in-Lean rederivation of the engine's
`profile_weight`). -/
def profileExp (p : Profile) : Nat :=
  p.foldl (fun acc t => acc + t.1 * (t.1 + 2) * t.2) 0

/-- Dimension coefficient of a profile: c = Π (n+1)^mult. -/
def profileCoeff (p : Profile) : Nat :=
  p.foldl (fun acc t => acc * (t.1 + 1) ^ t.2) 1

'''

    global_doc = (
        "The 80-monomial GLOBAL sum with lower sectors folded in "
        "(empty + singles + pairs + triples): (exponent E, coefficient "
        "of s^E).  Transcribed from dp6_results.json "
        "global_with_lower.polynomial.")
    triples_doc = (
        "The 75-monomial triples-only global sum: (exponent E, "
        "coefficient of s^E).  Transcribed from dp6_results.json "
        "global.polynomial.")

    mid = f'''{render_mono_list("globalMonomials", global_doc, monos)}
{render_mono_list("globalTriplesMonomials", triples_doc, monos_t)}
/-- **Every global coefficient is strictly positive** (kernel-checked):
the full ≤-triples global sum is a positive combination of the
monomials s^E, hence strictly positive at every s ∈ (0,1).  (The
pointwise-evaluation reading is the engine's `coefficient-signs`
certificate; only the coefficient-sign ledger is formalized here.) -/
theorem global_coeffs_pos :
    globalMonomials.all (fun t => qPos t.2) = true := by decide

theorem global_monomial_count : globalMonomials.length = 80 := by decide

/-- Same positivity for the triples-only global sum. -/
theorem global_triples_coeffs_pos :
    globalTriplesMonomials.all (fun t => qPos t.2) = true := by decide

theorem global_triples_count :
    globalTriplesMonomials.length = 75 := by decide

/-- Exponent lists are strictly ascending: the ledgers are honest
single-coefficient-per-exponent normal forms. -/
def expsAscending : List (Nat × Q) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.1 < b.1) && expsAscending (b :: rest)

theorem global_exps_ascending :
    (expsAscending globalMonomials && expsAscending globalTriplesMonomials)
      = true := by decide

/-- The four classes with NEGATIVE channel sums — the counterexample
side of the split verdict (per-class positivity fails; the Lakatos
fence).  Entries: (profile, class sum Σ Z, channel coefficient
c·ΣZ from the cancellation ledger).  Because a class channel is the
single monomial c·(ΣZ)·s^E, each negative sum is negative on ALL of
s ∈ (0,1) — the sign is s-independent. -/
def negClasses : List (Profile × Q × Q) :=
  [ {neg_body.lstrip()} ]

/-- Per-entry check: both the class sum and the channel coefficient
are negative, and the channel coefficient really is (Σ Z)·c with c
rederived in Lean from the profile — the "class channels are
monomials" bookkeeping is internally consistent. -/
def negClassCheck : Profile × Q × Q → Bool
  | (prof, zsum, chan) =>
    qNeg zsum && qNeg chan && qEq (qMulNat zsum (profileCoeff prof)) chan

/-- **Per-class survival fails** (kernel-checked): all four recorded
class channel sums are strictly negative. -/
theorem neg_classes_neg : negClasses.all negClassCheck = true := by decide

/-- Cancellation ledger at the negative-class exponents
E ∈ {{136, 138, 148, 172}} (ledger order follows the sorted negative
profiles: 172, 138, 148, 136).  Entries: (E, positive subtotal P_E,
negative subtotal N_E, recorded global s^E coefficient G_E), each
subtotal summed over every class sharing exponent E. -/
def cancellationLedger : List (Nat × Q × Q × Q) :=
  [ {ledger_body.lstrip()} ]

def ledgerBalanced : Nat × Q × Q × Q → Bool
  | (_, p, n, g) => qPos p && qNeg n && qPos g && qEq (qAdd p n) g

/-- **The cancellation balances at exponent granularity**
(kernel-checked): at each negative-class exponent the negative
subtotal is strictly negative, yet P_E + N_E = G_E > 0 — the spin-3
negativity is beaten inside its own s-exponent, not across
exponents. -/
theorem exponent_ledger_balances :
    cancellationLedger.all ledgerBalanced = true := by decide

/-- Coefficient lookup in a monomial ledger (0 if absent). -/
def coeffAt (l : List (Nat × Q)) (e : Nat) : Q :=
  match l.find? (fun t => t.1 == e) with
  | some t => t.2
  | none => (0, 1)

/-- The ledger's G_E agrees with the triples-only global ledger at
every negative-class exponent — the two JSON records are one. -/
theorem ledger_matches_global :
    cancellationLedger.all
      (fun t => qEq (coeffAt globalTriplesMonomials t.1) t.2.2.2)
      = true := by decide

/-- The negative-class exponents, rederived in Lean from the profiles,
are exactly the ledger's exponents (same order). -/
theorem neg_class_exponents :
    negClasses.map (fun t => profileExp t.1)
      = cancellationLedger.map (fun t => t.1) := by decide

/-- Sanity pins (§15a): corpus size, negative census, minimal
exemplar. -/
def tripleCount : Nat := 341376

def negativeCount : Nat := 32384

def minExemplarZ : Q := {q(data["min_z"])}

def minExemplarProfile : Profile := [(1, 9), (2, 6), (3, 3)]

theorem sanity_pins :
    (decide (negativeCount < tripleCount)
        && qNeg minExemplarZ
        && (profileExp minExemplarProfile == {data["min_exp"]})
        && (profileCoeff minExemplarProfile == {profile_coeff(data["min_prof"])}))
      = true := by decide

end DP6Ledger
'''
    return header + mid


# ---------------------------------------------------------------------------
# Verification: delimiter balance + literal re-parse against the JSON.
# ---------------------------------------------------------------------------


def check_delimiters(text: str) -> None:
    """Balanced (), [], {} outside comments; comments themselves nest."""
    # Strip block comments (Lean block comments /- ... -/ nest).
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif text.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    assert depth == 0, "unbalanced block comments"
    code = "".join(out)
    pairs = {")": "(", "]": "[", "}": "{"}
    stack = []
    for ch in code:
        if ch in "([{":
            stack.append(ch)
        elif ch in pairs:
            assert stack and stack.pop() == pairs[ch], "delimiter mismatch"
    assert not stack, f"unclosed delimiters: {stack}"


TUPLE2 = re.compile(r"\((-?\d+),\s*(\d+)\)")


def parse_def_block(text: str, name: str) -> str:
    m = re.search(rf"^def {name} .*?:=\n(.*?)\n\n", text, re.S | re.M)
    assert m, f"def {name} not found"
    return m.group(1)


def parse_mono_list(text: str, name: str):
    block = parse_def_block(text, name)
    out = []
    for m in re.finditer(r"\((\d+), \((-?\d+), (\d+)\)\)", block):
        e, num, den = (int(g) for g in m.groups())
        out.append((e, Fraction(num, den)))
    return out


def verify(lean_path: Path, json_path: Path) -> int:
    """Re-parse the emitted .lean; compare every literal to the JSON.

    Returns the number of literal values verified.
    """
    text = lean_path.read_text()
    check_delimiters(text)
    data = load(json_path)  # fresh read
    n = 0

    for name, key in (("globalMonomials", "monos"),
                      ("globalTriplesMonomials", "monos_t")):
        parsed = parse_mono_list(text, name)
        expect = data[key]
        assert parsed == expect, f"{name} literal mismatch"
        n += 3 * len(parsed)  # exponent + numerator + denominator

    neg_block = parse_def_block(text, "negClasses")
    entries = re.findall(
        r"\(\[((?:\(\d+, \d+\)(?:, )?)+)\], \((-?\d+), (\d+)\), "
        r"\((-?\d+), (\d+)\)\)", neg_block)
    assert len(entries) == 4, "negClasses: expected 4 entries"
    for (profs, zn, zd, cn, cd), (prof, zsum, chan) in zip(entries,
                                                           data["neg"]):
        pp = [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)",
                                                      profs)]
        assert pp == prof, "negClasses profile mismatch"
        assert Fraction(int(zn), int(zd)) == zsum, "negClasses ΣZ mismatch"
        assert Fraction(int(cn), int(cd)) == chan, "negClasses cΣZ mismatch"
        n += 2 * len(pp) + 4

    led_block = parse_def_block(text, "cancellationLedger")
    led = re.findall(
        r"\((\d+), \((-?\d+), (\d+)\), \((-?\d+), (\d+)\), "
        r"\((-?\d+), (\d+)\)\)", led_block)
    assert len(led) == 4, "cancellationLedger: expected 4 entries"
    for (e, pn, pd, nn, nd, gn, gd), (ee, p, nsub, g) in zip(led,
                                                             data["ledger"]):
        assert int(e) == ee, "ledger exponent mismatch"
        assert Fraction(int(pn), int(pd)) == p, "ledger P mismatch"
        assert Fraction(int(nn), int(nd)) == nsub, "ledger N mismatch"
        assert Fraction(int(gn), int(gd)) == g, "ledger G mismatch"
        n += 7

    for name, val in (("tripleCount", 341376), ("negativeCount", 32384)):
        m = re.search(rf"^def {name} : Nat := (\d+)$", text, re.M)
        assert m and int(m.group(1)) == val, f"{name} mismatch"
        n += 1
    m = re.search(r"^def minExemplarZ : Q := \((-?\d+), (\d+)\)$", text, re.M)
    assert m and Fraction(int(m.group(1)), int(m.group(2))) == data["min_z"]
    n += 2
    m = re.search(r"^def minExemplarProfile : Profile := \[(.*)\]$", text,
                  re.M)
    assert m
    pp = [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)",
                                                  m.group(1))]
    assert pp == data["min_prof"], "minExemplarProfile mismatch"
    n += 2 * len(pp)

    return n


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--json", default=str(HERE.parent / "dp6_results.json"))
    ap.add_argument("--out", default=str(HERE / "DP6Ledger.lean"))
    args = ap.parse_args()

    json_path, out_path = Path(args.json), Path(args.out)
    data = load(json_path)
    out_path.write_text(render(data))
    print(f"wrote {out_path}")

    n = verify(out_path, json_path)
    print(f"literal check: {n} literal values re-parsed from the .lean "
          f"and verified against {json_path.name}; delimiters balanced")


if __name__ == "__main__":
    main()
