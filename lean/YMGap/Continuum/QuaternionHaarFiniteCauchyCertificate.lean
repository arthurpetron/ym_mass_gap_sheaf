/-
# Linear finite-family Cauchy certificate

For a finite list of supported polynomials, the exact gap

  |ps| * sum p^2 - (sum p)^2

is compiled into supported squares.  The induction uses the identity that
adjoining `x` adds the sum of `(x-p)^2` over the old list.  Consequently the
coefficient is the literal list length; no iterated binary triangle estimate
or exponential family cap is used.

This is finite algebra on the original polynomial Haar carrier.  It supplies
no path decomposition, active-link support theorem, or analytic comparison of
a Wilson observable with local kinetic increments.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul_left)

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def zeroCertificate (blocks : Nat) : Certificate blocks polyZero :=
  Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
    (.smul 0 (by decide) (Certificate.one blocks))

private def differenceSquares (x : RatPoly) (ps : List RatPoly) : RatPoly :=
  polySum (ps.map fun p =>
    polyMul (polyAdd x (polyNeg p)) (polyAdd x (polyNeg p)))

private def pairGap : List RatPoly → RatPoly
  | [] => polyZero
  | x :: ps => polyAdd (pairGap ps) (differenceSquares x ps)

private def capGap (ps : List RatPoly) : RatPoly :=
  polyAdd
    (polyMul (cap (Q'.ofNat ps.length))
      (polySum (ps.map fun p => polyMul p p)))
    (polyNeg (polyMul (polySum ps) (polySum ps)))

private theorem ofNat_succ_forward (n : Nat) :
    Q'.ofNat (n + 1) ≈ Q'.ofNat n + 1 := by
  exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1)
    (Q'.add_eqv_congr_left _ _ _ (by decide))

private theorem cap_succ (n : Nat) :
    RatPolyCoeffEqv (polyAdd (cap (Q'.ofNat n)) (cap 1))
      (cap (Q'.ofNat (n + 1))) :=
  (cap_add _ _).trans
    (RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_symm (ofNat_succ_forward n)) polyOne)

private theorem differenceSquares_formula (x : RatPoly) : ∀ ps : List RatPoly,
    RatPolyCoeffEqv (differenceSquares x ps)
      (polyAdd
        (polyMul (cap (Q'.ofNat ps.length)) (polyMul x x))
        (polyAdd (polySum (ps.map fun p => polyMul p p))
          (polyNeg (polyMul (cap 2) (polyMul x (polySum ps))))))
  | [] => by
      have hfirst : RatPolyCoeffEqv
          (polyMul (cap 0) (polyMul x x)) polyZero :=
        (cap_mul_left 0 _).trans (RatPolyCoeffEqv.zero_smul _)
      have hcross : RatPolyCoeffEqv
          (polyMul (cap 2) (polyMul x polyZero)) polyZero :=
        ((RatPolyCoeffEqv.refl (cap 2)).mul
          (RatPolyCoeffEqv.mul_zero_right x)).trans
          (RatPolyCoeffEqv.mul_zero_right (cap 2))
      have hsecond : RatPolyCoeffEqv
          (polyAdd polyZero (polyNeg (polyMul (cap 2) (polyMul x polyZero))))
          polyZero :=
        (((RatPolyCoeffEqv.refl polyZero).add (RatPolyCoeffEqv.neg hcross)).trans
          (RatPolyCoeffEqv.zero_add polyZero))
      exact ((hfirst.add hsecond).trans (RatPolyCoeffEqv.zero_add polyZero)).symm
  | p :: ps => by
      let S := polySum ps
      let D := polySum (ps.map fun q => polyMul q q)
      let n := Q'.ofNat ps.length
      let N := cap n
      have ih := differenceSquares_formula x ps
      have hfirst : RatPolyCoeffEqv (differenceSquares x (p :: ps))
          (polyAdd
            (polyMul (polyAdd x (polyNeg p)) (polyAdd x (polyNeg p)))
            (polyAdd (polyMul N (polyMul x x))
              (polyAdd D (polyNeg (polyMul (cap 2) (polyMul x S)))))) :=
        (RatPolyCoeffEqv.refl _).add ih
      have halgebra : RatPolyCoeffEqv
          (polyAdd
            (polyMul (polyAdd x (polyNeg p)) (polyAdd x (polyNeg p)))
            (polyAdd (polyMul N (polyMul x x))
              (polyAdd D (polyNeg (polyMul (cap 2) (polyMul x S))))))
          (polyAdd
            (polyMul (polyAdd N (cap 1)) (polyMul x x))
            (polyAdd (polyAdd (polyMul p p) D)
              (polyNeg (polyMul (cap 2) (polyMul x (polyAdd p S)))))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.add (.var 0) (.neg (.var 1)))
              (.add (.var 0) (.neg (.var 1))))
            (.add (.mul (.var 4) (.mul (.var 0) (.var 0)))
              (.add (.var 3) (.neg (.mul (.const 2) (.mul (.var 0) (.var 2)))))))
          (.add (.mul (.add (.var 4) (.const 1)) (.mul (.var 0) (.var 0)))
            (.add (.add (.mul (.var 1) (.var 1)) (.var 3))
              (.neg (.mul (.const 2) (.mul (.var 0) (.add (.var 1) (.var 2)))))))
          (by decide) (fun | 0 => x | 1 => p | 2 => S | 3 => D | _ => N)
      have hn := ((cap_succ ps.length).mul_right (polyMul x x)).add
          (RatPolyCoeffEqv.refl
            (polyAdd (polyAdd (polyMul p p) D)
              (polyNeg (polyMul (cap 2) (polyMul x (polyAdd p S))))))
      exact hfirst.trans (halgebra.trans hn)

private theorem gap_cons (x : RatPoly) (ps : List RatPoly) :
    RatPolyCoeffEqv (capGap (x :: ps))
      (polyAdd (capGap ps) (differenceSquares x ps)) := by
  let S := polySum ps
  let D := polySum (ps.map fun p => polyMul p p)
  let n := Q'.ofNat ps.length
  let N := cap n
  have hn : RatPolyCoeffEqv
      (polyMul (cap (Q'.ofNat (ps.length + 1)))
        (polyAdd (polyMul x x) D))
      (polyMul (polyAdd N (cap 1)) (polyAdd (polyMul x x) D)) :=
    (cap_succ ps.length).symm.mul_right _
  have hstart : RatPolyCoeffEqv (capGap (x :: ps))
      (polyAdd
        (polyMul (polyAdd N (cap 1)) (polyAdd (polyMul x x) D))
        (polyNeg (polyMul (polyAdd x S) (polyAdd x S)))) :=
    hn.add (RatPolyCoeffEqv.refl _)
  have halgebra : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyAdd N (cap 1)) (polyAdd (polyMul x x) D))
        (polyNeg (polyMul (polyAdd x S) (polyAdd x S))))
      (polyAdd (capGap ps)
        (polyAdd (polyMul N (polyMul x x))
          (polyAdd D (polyNeg (polyMul (cap 2) (polyMul x S)))))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 3) (.const 1))
          (.add (.mul (.var 0) (.var 0)) (.var 2)))
        (.neg (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))))
      (.add
        (.add (.mul (.var 3) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
        (.add (.mul (.var 3) (.mul (.var 0) (.var 0)))
          (.add (.var 2) (.neg (.mul (.const 2) (.mul (.var 0) (.var 1)))))))
      (by decide) (fun | 0 => x | 1 => S | 2 => D | _ => N)
  exact hstart.trans (halgebra.trans
    ((RatPolyCoeffEqv.refl (capGap ps)).add (differenceSquares_formula x ps).symm))

private theorem gap_pairGap : ∀ ps : List RatPoly,
    RatPolyCoeffEqv (capGap ps) (pairGap ps)
  | [] => by
      have hfirst := RatPolyCoeffEqv.mul_zero_right (cap 0)
      have hsecond : RatPolyCoeffEqv
          (polyNeg (polyMul polyZero polyZero)) polyZero :=
        RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left polyZero)
      exact (hfirst.add hsecond).trans (RatPolyCoeffEqv.zero_add polyZero)
  | x :: ps =>
      (gap_cons x ps).trans ((gap_pairGap ps).add (RatPolyCoeffEqv.refl _))

private def differenceSquares_certificate {blocks : Nat} (x : RatPoly)
    (hx : SupportedQuaternionBlocks blocks x) :
    (ps : List RatPoly) →
    (∀ p, p ∈ ps → SupportedQuaternionBlocks blocks p) →
    Certificate blocks (differenceSquares x ps)
  | [], _ => zeroCertificate blocks
  | p :: ps, hs =>
      .add
        (.square (polyAdd x (polyNeg p))
          (supported_add hx (support_neg (hs p List.mem_cons_self))))
        (differenceSquares_certificate x hx ps
          (fun q hq => hs q (List.mem_cons_of_mem p hq)))

private def pairGap_certificate {blocks : Nat} :
    (ps : List RatPoly) →
    (∀ p, p ∈ ps → SupportedQuaternionBlocks blocks p) →
    Certificate blocks (pairGap ps)
  | [], _ => zeroCertificate blocks
  | x :: ps, hs =>
      .add
        (pairGap_certificate ps (fun p hp => hs p (List.mem_cons_of_mem x hp)))
        (differenceSquares_certificate x (hs x List.mem_cons_self) ps
          (fun p hp => hs p (List.mem_cons_of_mem x hp)))

/-- Constructive finite Cauchy--Schwarz with the exact linear list-length
coefficient, represented as a certificate valid under every supported Haar
square insertion. -/
def sum_square_certificate {blocks : Nat} (ps : List RatPoly)
    (hsupport : ∀ p, p ∈ ps → SupportedQuaternionBlocks blocks p) :
    Certificate blocks
      (polyAdd
        (polySmul (Q'.ofNat ps.length)
          (polySum (ps.map fun p => polyMul p p)))
        (polyNeg (polyMul (polySum ps) (polySum ps)))) :=
  Certificate.ofCoeff
    (((cap_mul_left (Q'.ofNat ps.length)
      (polySum (ps.map fun p => polyMul p p))).symm.add
        (RatPolyCoeffEqv.refl _)).trans (gap_pairGap ps))
    (pairGap_certificate ps hsupport)

end YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate

#print axioms YMGap.Continuum.QuaternionHaarFiniteCauchyCertificate.sum_square_certificate
