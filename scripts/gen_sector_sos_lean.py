"""Emit dual_kappa_spike/SectorSOSLedger.lean from computations.sector_sos.

Convention: the DP6Ledger / DP3M2Ledger / WindowLedger spike convention —
rationals as (Int, Nat), cross-multiplied comparisons, closed-integer
`decide`, no Mathlib.  As in WindowLedger, the sector WEIGHTS and
EXPONENTS are REDERIVED in-kernel from the labelling; only the pure
Haar values (the sector kernels) are transcribed, with provenance.

Run:  python -m scripts.gen_sector_sos_lean
"""
from __future__ import annotations

import os
import sys
from fractions import Fraction as Frac

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.set_int_max_str_digits(0)

from computations.sector_sos import (  # noqa: E402
    ENTRIES,
    as_coeff_list,
    assemble,
    det_poly,
    gate_s1_multiplicity,
    moebius_reciprocal,
    positivity_certificate,
    sector_kernels,
    sector_weight,
)

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(HERE, "dual_kappa_spike", "SectorSOSLedger.lean")

CAP, TILE_M = 1, 2


def q(x: Frac) -> str:
    return f"({x.numerator}, {x.denominator})"


def poly_lean(p) -> str:
    items = ", ".join(f"({e}, {q(c)})" for e, c in sorted(p.items()))
    return "[" + items + "]"


def nat_list(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def main() -> None:
    secs = sector_kernels(CAP, TILE_M)
    T = assemble(secs)
    det = det_poly(T)
    cert = positivity_certificate(det)
    P, lo = as_coeff_list(det)
    R = moebius_reciprocal(P)
    tpow = cert["t_power"]
    Rhat = R[tpow:]
    mult, lead = gate_s1_multiplicity(CAP, TILE_M)
    assert cert["certified"] and cert["n_negative"] == 0
    assert all(c.denominator == 1 for c in Rhat)
    assert all(c.denominator == 1 for k in ENTRIES for c in T[k].values())

    keys = sorted(secs)
    sector_rows = []
    for (qq, ww) in keys:
        rows = secs[(qq, ww)]
        sector_rows.append(
            f"  ⟨{nat_list(qq)}, {nat_list(ww)}, "
            f"{poly_lean(rows[(0, 0)])}, {poly_lean(rows[(0, 1)])}, "
            f"{poly_lean(rows[(1, 1)])}⟩")

    tint = {k: "[" + ", ".join(f"({e}, {int(T[k][e])})" for e in sorted(T[k]))
            + "]" for k in ENTRIES}
    all_exps = sorted({we + e
                       for (qq, ww) in keys
                       for we in [sector_weight(qq, ww)[1]]
                       for k in ENTRIES
                       for e in secs[(qq, ww)][k]})

    SECTOR_BLOCK = ",\n".join(sector_rows)
    src = f'''/-
  SectorSOSLedger.lean — the SECTOR-SOS positivity certificate:
  X_11 > 0 on ALL of (0, 1), replayed by the Lean kernel.

  GENERATED FILE: emitted by scripts/gen_sector_sos_lean.py from
  computations/sector_sos.py.  Do not edit — regenerate.

  WHAT THE KERNEL CHECKS (work_plan §17g):

  * The 16 transverse sectors sigma = (q, w) with all labels <= 1 are
    carried with their EXACT sector kernels G_sigma[n,m] (finite
    polynomials in the coupling s: at fixed sector the triad
    constraint triad(n, q_i, a_i) TERMINATES the tile sums, so there
    is no truncation error inside a sector — the (F1) fact).
  * The sector WEIGHT W_sigma and its s-EXPONENT are REDERIVED here
    from the labelling (dims and Casimirs), WindowLedger precedent:
    W_sigma = prod dim(q_i)^2 s^(2 C(q_i)) * prod dim(w_i) s^(C(w_i)).
  * T_S[n,m] = sum_sigma W_sigma G_sigma is REASSEMBLED coefficient by
    coefficient against the declared integer polynomials, with an
    exponent-COMPLETENESS guard (no assembled term may fall outside
    the declared exponent set), so the integer forms are proved, not
    trusted.
  * det_S = T00 T11 - T01^2 is formed in-kernel and shifted by s^24.
  * The Moebius substitution s = 1/(1+t) — a bijection (0,1) ->
    (0, infinity) — is applied in-kernel by Horner in u = 1 + t, and
    the certificate is then a COEFFICIENT-SIGN statement:
        R(t) = t^4 * Rhat(t),  Rhat coefficientwise >= 0, Rhat(0) > 0
    hence det_S(s) > 0 for every s in (0,1), hence — by
    superadditivity of det on the PSD sector blocks (the (F2)/(F3)
    facts) — T00 T11 - T01^2 > 0 for the FULL M -> infinity kernel:
        X_11(s) = log(T00 T11 / T01^2) > 0  on ALL of (0, 1).
    This is the program's first kernel-checked INTERVAL statement; all
    previous certified statements were pointwise.
  * The per-sector 2x2 determinants det G_sigma >= 0 are checked at a
    rational probe grid (the (F2) consequence), and the U(1) MIRROR
    FENCE is banked as integer arithmetic on the abelian exponent
    form: unconjugated Cauchy-Schwarz FAILS for every off-diagonal
    charge pair (2 Qmin(n,m) - Qmin(n,n) - Qmin(m,m) = -2(n-m)^2 < 0)
    while the CONJUGATED form PASSES (+2(n-m)^2 >= 0).  SU(2) is
    self-conjugate, so for SU(2) the OS-PSD object and the X_11 object
    are the SAME matrix; for U(1) they are Hankel vs Toeplitz of the
    same Stieltjes moment sequence, with opposite determinant signs.
    That is where non-abelian-ness enters this step.

  TRANSCRIBED (provenance-caveated): the pure-character Haar values
  inside the sector kernels, from computations/dp3_fixed_tile.py
  (network_value_fixed / skeleton_value_fixed), the incumbent
  evaluator.  MATHEMATICAL INPUT (not re-proved here): sector-wise
  Osterwalder-Seiler link-reflection positivity of the half-config
  Gram — the SAME banked §16h lemma that §16h-§17e already consume,
  machine-gated in computations/sector_sos.py (gate_psd) on this
  16-sector family and independently on a 187-sector cap<=2 family.

  Axiom budget: {{propext, Quot.sound}} at most.  No Mathlib.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace SectorSOSLedger

abbrev Q := Int × Nat

def qDen (a : Q) : Int := Int.ofNat a.2

def qNonneg (a : Q) : Bool := decide (0 ≤ a.1) && decide (0 < a.2)

def qEq (a b : Q) : Bool := decide (a.1 * qDen b = b.1 * qDen a)

def qLe (a b : Q) : Bool := decide (a.1 * qDen b ≤ b.1 * qDen a)

def qAdd (a b : Q) : Q := (a.1 * qDen b + b.1 * qDen a, a.2 * b.2)

def qMul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)

def qSub (a b : Q) : Q := (a.1 * qDen b - b.1 * qDen a, a.2 * b.2)

def qZero : Q := (0, 1)

def qSum : List Q → Q
  | [] => qZero
  | a :: r => qAdd a (qSum r)

def intQ (n : Int) : Q := (n, 1)

/-- s^e for s = a/b. -/
def qPow (a b e : Nat) : Q := (Int.ofNat (a ^ e), b ^ e)

def casimir4 (n : Nat) : Nat := n * (n + 2)

def dimOf (n : Nat) : Nat := n + 1

/-- A sparse polynomial in the coupling: (exponent, coefficient). -/
abbrev QPoly := List (Nat × Q)

/-- One transverse sector: the labelling plus its three EXACT sector
kernels G[0,0], G[0,1], G[1,1]. -/
structure Sector where
  q : List Nat
  w : List Nat
  g00 : QPoly
  g01 : QPoly
  g11 : QPoly

/-- The 16 sectors with all labels <= 1 (the certificate family). -/
def sectors : List Sector :=
[
{SECTOR_BLOCK}
]

theorem sector_count : sectors.length = {len(keys)} := by decide

/-- The sector weight COEFFICIENT, rederived from the labelling:
prod dim(q_i)^2 * prod dim(w_i). -/
def secWeightCoeff (S : Sector) : Nat :=
  (S.q.foldl (fun acc n => acc * dimOf n * dimOf n) 1)
    * (S.w.foldl (fun acc n => acc * dimOf n) 1)

/-- The sector weight EXPONENT, rederived: 2 * sum C(q_i) + sum C(w_i).
The q classes carry two theta-paired faces each. -/
def secWeightExp (S : Sector) : Nat :=
  2 * (S.q.foldl (fun acc n => acc + casimir4 n) 0)
    + (S.w.foldl (fun acc n => acc + casimir4 n) 0)

def gOf (sel : Nat) (S : Sector) : QPoly :=
  if sel = 0 then S.g00 else if sel = 1 then S.g01 else S.g11

/-- The assembled coefficient of s^e in T_S[sel]: sum over sectors of
W_sigma times the matching sector-kernel term. -/
def tCoeff (sel e : Nat) : Q :=
  qSum (sectors.map (fun S =>
    let wc : Q := (Int.ofNat (secWeightCoeff S), 1)
    let we := secWeightExp S
    qSum ((gOf sel S).map (fun t =>
      if we + t.1 = e then qMul wc t.2 else qZero))))

/-- The declared integer forms of the assembled kernels. -/
def t00 : List (Nat × Int) := {tint[(0, 0)]}

def t01 : List (Nat × Int) := {tint[(0, 1)]}

def t11 : List (Nat × Int) := {tint[(1, 1)]}

/-- Every exponent produced by the assembly. -/
def declaredExps : List Nat := {nat_list(all_exps)}

/-- **Exponent completeness**: no assembled term falls outside
`declaredExps`, so checking the declared exponents checks everything. -/
theorem exps_complete :
    sectors.all (fun S =>
      [S.g00, S.g01, S.g11].all (fun g =>
        g.all (fun t => declaredExps.contains (secWeightExp S + t.1))))
      = true := by decide

/-- **The assembly is rederived**: at every declared exponent the
in-kernel sector sum equals the declared integer coefficient (and is
zero where no integer term is declared). -/
theorem t_rederived :
    declaredExps.all (fun e =>
      qEq (tCoeff 0 e) (intQ ((t00.lookup e).getD 0))
      && qEq (tCoeff 1 e) (intQ ((t01.lookup e).getD 0))
      && qEq (tCoeff 2 e) (intQ ((t11.lookup e).getD 0)))
      = true := by decide

theorem t_term_counts :
    t00.length = {len(T[(0, 0)])} ∧ t01.length = {len(T[(0, 1)])}
      ∧ t11.length = {len(T[(1, 1)])} := by decide

/-- Integer sparse-polynomial product. -/
def ipMul (a b : List (Nat × Int)) : List (Nat × Int) :=
  a.flatMap (fun p => b.map (fun r => (p.1 + r.1, p.2 * r.2)))

def ipCoeff (p : List (Nat × Int)) (e : Nat) : Int :=
  p.foldl (fun acc t => if t.1 = e then acc + t.2 else acc) 0

/-- det_S = T00 * T11 - T01^2, as a coefficient function. -/
def detCoeff (e : Nat) : Int :=
  ipCoeff (ipMul t00 t11) e - ipCoeff (ipMul t01 t01) e

/-- P(s) = det_S(s) / s^{lo}, dense ascending, degree {cert['deg_P']}. -/
def pDense : List Int :=
  (List.range {cert['deg_P'] + 1}).map (fun i => detCoeff (i + {lo}))

theorem p_length : pDense.length = {cert['deg_P'] + 1} := by decide

theorem p_head : pDense.headD 0 = {P[0]} := by decide

/-- The bottom of det_S is exactly s^{lo}: no lower term survives. -/
theorem det_bottom :
    (List.range {lo}).all (fun i => decide (detCoeff i = 0)) = true := by decide

def izip : List Int → List Int → List Int
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => (x + y) :: izip xs ys

/-- Multiply by u = 1 + t. -/
def mulU (a : List Int) : List Int := izip a (0 :: a)

/-- R(t) = (1+t)^deg * P(1/(1+t)), by Horner in u = 1 + t. -/
def rPoly : List Int := pDense.foldl (fun acc c => izip (mulU acc) [c]) []

/-- Rhat = R / t^{tpow}. -/
def rHat : List Int := rPoly.drop {tpow}

theorem r_length : rPoly.length = {len(R)} := by decide

/-- The Moebius image vanishes to order exactly {tpow} at t = 0: this is
the s -> 1 degeneracy of the observable, PROTECTED at order 4 (the
cap<=2 family of 187 sectors has the same order — banked refutation
that enlarging the transverse family sharpens the rate). -/
theorem r_low_order :
    (List.range {tpow}).all (fun i => decide (rPoly.getD i 0 = 0)) = true
      ∧ rHat.headD 0 = {Rhat[0]} := by decide

/-- **THE CERTIFICATE.**  Every coefficient of Rhat is non-negative.
Since s = 1/(1+t) maps (0,1) bijectively onto t in (0, infinity) and
Rhat(0) > 0, this gives Rhat(t) > 0 for all t >= 0, hence P(s) > 0 on
(0,1), hence det_S(s) = s^{lo} P(s) > 0 on (0,1) — and hence, by
superadditivity of det over the PSD sector blocks, the FULL kernel
satisfies T00 T11 > T01^2, i.e. X_11 > 0, on ALL of (0,1). -/
theorem sector_sos_certified :
    rHat.all (fun c => decide (0 ≤ c)) = true := by decide

/-- Non-vacuity: P itself is NOT coefficientwise non-negative, so the
Moebius step is doing real work. -/
theorem p_has_negative_coefficients :
    (pDense.filter (fun c => decide (c < 0))).length = {sum(1 for c in P if c < 0)}
      := by decide

/-- Per-sector 2x2 positivity (the (F2) consequence) at a rational probe
grid: det G_sigma >= 0 for every sector. -/
def evalQPoly (p : QPoly) (a b : Nat) : Q :=
  qSum (p.map (fun t => qMul t.2 (qPow a b t.1)))

def sectorDetNonneg (S : Sector) (a b : Nat) : Bool :=
  let A := evalQPoly S.g00 a b
  let C := evalQPoly S.g01 a b
  let B := evalQPoly S.g11 a b
  qNonneg A && qNonneg B && qLe (qMul C C) (qMul A B)

theorem sector_blocks_psd_on_grid :
    [(1, 2), (4, 5), (99, 100)].all (fun ab =>
      sectors.all (fun S => sectorDetNonneg S ab.1 ab.2)) = true := by decide

/-- The dominant (trivial) sector is EXACTLY rank one: its own
determinant vanishes identically, so the certificate is entirely
cross-sector INTERFERENCE — not a single-sector artifact. -/
theorem trivial_sector_rank_one :
    [(1, 2), (4, 5), (99, 100)].all (fun ab =>
      match sectors.head? with
      | none => false
      | some S =>
        qEq (qMul (evalQPoly S.g01 ab.1 ab.2) (evalQPoly S.g01 ab.1 ab.2))
            (qMul (evalQPoly S.g00 ab.1 ab.2) (evalQPoly S.g11 ab.1 ab.2)))
      = true := by decide

/- ------------------------------------------------------------------
   THE U(1) MIRROR FENCE (work_plan §17.4), as integer arithmetic.

   The abelian owned-boundary kernel has T[n,m] ~ s^{{Qmin(n,m)}} with
   Qmin(n,m) = 3 n^2 + 3 m^2 + 2 n m (banked, u1_theta_kernel).  The
   Cauchy-Schwarz / OS test compares 2 Qmin(n,m) against
   Qmin(n,n) + Qmin(m,m); the difference is exactly -2 (n-m)^2 in the
   UNCONJUGATED indexing and +2 (n-m)^2 in the CONJUGATED one
   (n -> nbar = -n).  So abelian-ly the observable's matrix is a
   Toeplitz form and the OS-positive matrix is the Hankel form: two
   different matrices with opposite determinant signs.  SU(2) is
   self-conjugate (nbar = n), so there they COINCIDE — that identity,
   and nothing else about the group at this step, licenses the sector
   PSD input used above.
   ------------------------------------------------------------------ -/

def qminU1 (n m : Int) : Int := 3 * n * n + 3 * m * m + 2 * n * m

/-- UNCONJUGATED abelian Cauchy-Schwarz FAILS at every off-diagonal
charge pair: the exponent budget has the wrong sign. -/
theorem u1_unconjugated_fails :
    ([0, 1, 2, 3] : List Int).all (fun n =>
      ([0, 1, 2, 3] : List Int).all (fun m =>
        decide (n = m)
        || decide (2 * qminU1 n m < qminU1 n n + qminU1 m m))) = true := by
  decide

/-- CONJUGATED abelian Cauchy-Schwarz PASSES.  The Gram object is
M[n,m] = T[nbar, m], so BOTH the cross entry AND the diagonal reference
are conjugated: M[n,n] = T[-n, n].  With that indexing the exponent
budget flips sign, reproducing the banked §17e statement. -/
theorem u1_conjugated_passes :
    ([0, 1, 2, 3] : List Int).all (fun n =>
      ([0, 1, 2, 3] : List Int).all (fun m =>
        decide (qminU1 (-n) n + qminU1 (-m) m ≤ 2 * qminU1 (-n) m))) = true := by
  decide

/-- The exact discriminant, both indexings in closed form: the abelian
CS budget is -2(n-m)^2 unconjugated (WRONG sign: Toeplitz) and
+2(n-m)^2 conjugated (RIGHT sign: Hankel).  The two differ by
4(n-m)^2 — the whole content of the fence. -/
theorem u1_conjugation_discriminant :
    ([0, 1, 2, 3] : List Int).all (fun n =>
      ([0, 1, 2, 3] : List Int).all (fun m =>
        decide (2 * qminU1 n m - qminU1 n n - qminU1 m m
                  = -2 * (n - m) * (n - m))
        && decide (2 * qminU1 (-n) m - qminU1 (-n) n - qminU1 (-m) m
                  = 2 * (n - m) * (n - m))))
      = true := by decide

end SectorSOSLedger
'''
    with open(OUT, "w") as fh:
        fh.write(src)
    print(f"wrote {OUT}")
    print(f"  sectors {len(keys)}, deg P {cert['deg_P']}, "
          f"Rhat {len(Rhat)} coeffs, s=1 order {mult}, leading {lead}")


if __name__ == "__main__":
    main()
