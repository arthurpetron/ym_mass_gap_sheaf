/-
# Algebraic commutator of pair exchange with one inner Omega lift

Peeling one `(b,c)` Cayley contraction intertwines first-pair exchange at
degree `(a,b)` with first-pair exchange at the reduced degree `(a,b-1)`, plus
an explicit four-term correction.  This file proves the denominator-free
polynomial certificate behind that commutator.  Boundary/degree substitution
is deliberately separate; the identity here is the exact algebraic engine
used by the inner-order induction.
-/

import YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahOmegaExchangeCommutator

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private def pv (n : Nat) : PolyExpr := .var n
private def pc (n : Int) : PolyExpr := .const n
private def pa (x y : PolyExpr) : PolyExpr := .add x y
private def pm (x y : PolyExpr) : PolyExpr := .mul x y
private def pn (x : PolyExpr) : PolyExpr := .neg x
private def ps (x y : PolyExpr) : PolyExpr := pa x (pn y)

private def omegaCommBase : PolyExpr :=
  ps (pm (pm (pv 2) (pv 4)) (pv 8))
    (pm (pm (pv 3) (pv 5)) (pv 9))

private def omegaCommLHS : PolyExpr :=
  pa
    (pm (pm (pv 0) (pv 2))
      (ps
        (ps
          (pm (pm (pa (pv 2) (pn (pc 1))) (pv 4)) (pv 6))
          (pm (pm (pa (pv 3) (pc 1)) (pv 5)) (pv 7)))
        omegaCommBase))
    (pm (pm (pv 1) (pv 3))
      (ps
        (ps
          (pm (pm (pa (pv 2) (pc 1)) (pv 4)) (pv 10))
          (pm (pm (pa (pv 3) (pn (pc 1))) (pv 5)) (pv 11)))
        omegaCommBase))

private def omegaCommReduced : PolyExpr :=
  ps
    (pm (pm (pv 2) (pv 4))
      (pa
        (pm (pm (pv 0) (pa (pv 2) (pn (pc 1))))
          (ps (pv 6) (pv 8)))
        (pm (pm (pv 1) (pv 3)) (ps (pv 10) (pv 8)))))
    (pm (pm (pv 3) (pv 5))
      (pa
        (pm (pm (pv 0) (pv 2)) (ps (pv 7) (pv 9)))
        (pm (pm (pv 1) (pa (pv 3) (pn (pc 1))))
          (ps (pv 11) (pv 9)))))

private def omegaCommCorrection : PolyExpr :=
  ps
    (pm (pm (pv 1) (pv 3))
      (pa (pm (pv 4) (pv 10)) (pm (pv 5) (pv 9))))
    (pm (pm (pv 0) (pv 2))
      (pa (pm (pv 4) (pv 8)) (pm (pv 5) (pv 7))))

private def omegaCommRHS : PolyExpr :=
  pa omegaCommReduced omegaCommCorrection

private theorem omegaComm_normal :
    normalize omegaCommLHS = normalize omegaCommRHS := by decide

/-- **One-Omega / pair-exchange commutator certificate.**

`A,I` are the two first-leg affine coefficients, `J,B` the current second-leg
coordinate/complement, and `C,L` the third-leg complement/coordinate.  The
six `x` values are precisely the shifted reduced-channel coefficients that
occur after one Omega lift.  The right side is the reduced-degree exchange
lift plus the four-term correction. -/
theorem omega_exchange_commutator_ring
    (A I J B C L x1 x2 x3 x4 x5 x6 : Q') :
    (A * J) *
          (((J + -1) * C * x1 + -((B + 1) * L * x2)) +
            -(J * C * x3 + -(B * L * x4))) +
        (I * B) *
          (((J + 1) * C * x5 + -((B + -1) * L * x6)) +
            -(J * C * x3 + -(B * L * x4))) ≈
      (J * C) *
          ((A * (J + -1)) * (x1 + -x3) +
            (I * B) * (x5 + -x3)) +
        -(B * L *
          ((A * J) * (x2 + -x4) +
            (I * (B + -1)) * (x6 + -x4))) +
        ((I * B) * (C * x5 + L * x4) +
          -((A * J) * (C * x3 + L * x2))) := by
  let ρ : Nat → Q' := fun r =>
    if r = 0 then A else if r = 1 then I else if r = 2 then J else
    if r = 3 then B else if r = 4 then C else if r = 5 then L else
    if r = 6 then x1 else if r = 7 then x2 else if r = 8 then x3 else
    if r = 9 then x4 else if r = 10 then x5 else x6
  have h := poly_identity_of_normal_eq omegaCommLHS omegaCommRHS
    omegaComm_normal ρ
  simpa [omegaCommLHS, omegaCommRHS, omegaCommBase, omegaCommReduced,
    omegaCommCorrection, pv, pc, pa, pm, pn, ps, eval, ρ] using h

end YMGap.Continuum.SU2OrderedRacahOmegaExchangeCommutator

#print axioms YMGap.Continuum.SU2OrderedRacahOmegaExchangeCommutator.omega_exchange_commutator_ring
