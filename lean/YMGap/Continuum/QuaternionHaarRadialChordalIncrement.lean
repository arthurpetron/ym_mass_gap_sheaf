/-
# Radial trace increments with the necessary quartic correction

For Haar-unit polynomial quaternions p,q, put r=|p-q|^2 and f=2*p.scalar.
Seven explicit supported squares prove

  (2*p.scalar-2*q.scalar)^2 <= 2*r*(4-f^2)+2*r^2.

The inequality holds under any certified positive original Haar insertion.
The mixed radial/chordal moment and fourth-order displacement are retained;
neither is replaced by a product of expectations or a heat-rate assertion.
-/

import YMGap.Continuum.QuaternionHaarChordalDifference

namespace YMGap.Continuum.QuaternionHaarRadialChordalIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarWordDifference (difference weighted_order)

private def env (p q : PolyQuaternion) : Nat → RatPoly
  | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | 3 => p.kPart
  | 4 => q.scalar | 5 => q.iPart | 6 => q.jPart | _ => q.kPart

private def sq (e : PolyExpr) : PolyExpr := .mul e e
private def sub (e f : PolyExpr) : PolyExpr := .add e (.neg f)
private def times (c : Int) (e : PolyExpr) : PolyExpr := .mul (.const c) e
private def pe : PolyQuaternionExpr := .coordinate 0
private def qe : PolyQuaternionExpr := .coordinate 4
private def ze : PolyQuaternionExpr := PolyQuaternionExpr.mul qe (PolyQuaternionExpr.conj pe)
private def np : PolyExpr := PolyQuaternionExpr.norm pe
private def nq : PolyExpr := PolyQuaternionExpr.norm qe
private def de : PolyExpr := sub (.const 1) ze.scalar
private def se : PolyExpr := .add (.mul ze.iPart pe.iPart)
  (.add (.mul ze.jPart pe.jPart) (.mul ze.kPart pe.kPart))
private def re : PolyExpr := PolyQuaternionExpr.norm
  ⟨sub pe.scalar qe.scalar, sub pe.iPart qe.iPart,
    sub pe.jPart qe.jPart, sub pe.kPart qe.kPart⟩
private def te : PolyExpr := sub (times 2 pe.scalar) (times 2 qe.scalar)
private def budgetExpr : PolyExpr :=
  .add (times 2 (.mul re (sub (.const 4) (sq (times 2 pe.scalar))))) (times 2 (sq re))
private def t0 : PolyExpr := sub (.mul pe.scalar de) se
private def t1 : PolyExpr := sub (.mul ze.iPart pe.jPart) (.mul ze.jPart pe.iPart)
private def t2 : PolyExpr := sub (.mul ze.iPart pe.kPart) (.mul ze.kPart pe.iPart)
private def t3 : PolyExpr := sub (.mul ze.jPart pe.kPart) (.mul ze.kPart pe.jPart)
private def t4 : PolyExpr := .mul de pe.iPart
private def t5 : PolyExpr := .mul de pe.jPart
private def t6 : PolyExpr := .mul de pe.kPart
private def sosExpr : PolyExpr := .add (times 4 (sq t0))
  (.add (times 8 (sq t1)) (.add (times 8 (sq t2)) (.add (times 8 (sq t3))
    (.add (times 16 (sq t4)) (.add (times 16 (sq t5)) (times 16 (sq t6)))))))

/- The two explicit ideal multipliers certify the ring identity BEFORE
   using either Haar-unit equation. No external symbolic result is trusted. -/
private def mp : PolyExpr := times (-2)
  (.add (times 4 (.mul np nq))
  (.add (times (-2) (.mul np (sq qe.scalar)))
  (.add (.neg np) (.add (times (-4) (.mul nq (sq pe.scalar)))
  (.add (times 2 nq) (.add (times 4 (sq pe.scalar))
  (.add (times 4 (.mul pe.scalar qe.scalar))
  (.add (times (-2) (sq qe.scalar)) (.add (times 4 (sq ze.scalar))
  (.add (times (-12) ze.scalar) (.const 3)))))))))))
private def mq : PolyExpr := times (-2)
  (.add (.neg nq) (.add (times 4 ze.scalar) (.const (-3))))
private def rhsExpr : PolyExpr := .add sosExpr
  (.add (.mul mp (sub np (.const 1))) (.mul mq (sub nq (.const 1))))

/-- Literal fundamental-trace difference, not a surrogate coordinate. -/
def traceDifference (p q : PolyQuaternion) : RatPoly :=
  polyAdd (characterPolynomial p.scalar 1) (polyNeg (characterPolynomial q.scalar 1))

/-- Exactly `2*r*(4-f^2)+2*r^2`, expressed by the existing polynomial compiler. -/
def radialBudget (p q : PolyQuaternion) : RatPoly := coeffEvalExpr (env p q) budgetExpr

theorem radialBudget_pin (p q : PolyQuaternion) :
    RatPolyCoeffEqv (radialBudget p q)
      (polyAdd
        (polySmul 2 (polyMul (polyQuaternionNorm (difference p q))
          (polyAdd (cap 4) (polyNeg
            (polyMul (characterPolynomial p.scalar 1) (characterPolynomial p.scalar 1))))))
        (polySmul 2 (polyMul (polyQuaternionNorm (difference p q))
          (polyQuaternionNorm (difference p q))))) := by
  have hf := cap_mul_left 2 p.scalar
  exact ((cap_mul_left 2 _).trans
    (RatPolyCoeffEqv.smul 2 ((RatPolyCoeffEqv.refl _).mul
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (hf.mul hf)))))).add
    (cap_mul_left 2 _)

private theorem neg_support {n : Nat} {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem expr_support {n : Nat} (v : Nat → RatPoly)
    (hv : ∀ i, SupportedQuaternionBlocks n (v i)) :
    ∀ e, SupportedQuaternionBlocks n (coeffEvalExpr v e)
  | .const c => by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact supported_one n s hs
  | .var i => hv i
  | .add e f => supported_add (expr_support v hv e) (expr_support v hv f)
  | .mul e f => supported_polyMul (expr_support v hv e) (expr_support v hv f)
  | .neg e => neg_support (expr_support v hv e)
  | .pow e k => by
      induction k with
      | zero => exact supported_one n
      | succ k ih => exact supported_polyMul ih (expr_support v hv e)

private def sosCertificate {n : Nat} {p q : PolyQuaternion}
    (hp : Supported n p) (hq : Supported n q) :
    Certificate n (coeffEvalExpr (env p q) sosExpr) := by
  have hs : ∀ i, SupportedQuaternionBlocks n (env p q i) := by
    intro i
    match i with
    | 0 => exact hp.scalar | 1 => exact hp.iPart | 2 => exact hp.jPart | 3 => exact hp.kPart
    | 4 => exact hq.scalar | 5 => exact hq.iPart | 6 => exact hq.jPart | _+7 => exact hq.kPart
  let cert (c : Int) (hc : (0 : Q') ≤ Q'.ofInt c) (e : PolyExpr) :
      Certificate n (coeffEvalExpr (env p q) (times c (sq e))) :=
    (Certificate.constant n (Q'.ofInt c) hc).mul
      (.square _ (expr_support (env p q) hs e))
  exact (cert 4 (by decide) t0).add ((cert 8 (by decide) t1).add
    ((cert 8 (by decide) t2).add ((cert 8 (by decide) t3).add
      ((cert 16 (by decide) t4).add ((cert 16 (by decide) t5).add (cert 16 (by decide) t6))))))

set_option maxRecDepth 8192 in
private theorem gap_ring (p q : PolyQuaternion) :
    RatPolyCoeffEqv (coeffEvalExpr (env p q) (sub budgetExpr (sq te)))
      (coeffEvalExpr (env p q) rhsExpr) :=
  coeffEvalExpr_eqv_of_normalize_eq _ _ (by decide) (env p q)

private theorem unit_defect_zero {n : Nat} {p : PolyQuaternion}
    (hp : HaarCarrierEqv n (polyQuaternionNorm p) polyOne) :
    HaarCarrierEqv n (polyAdd (polyQuaternionNorm p) (polyNeg (cap 1))) polyZero := by
  have hz : RatPolyCoeffEqv (polyAdd polyOne (polyNeg polyOne)) polyZero :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (sub (.var 0) (.var 0)) (.const 0) (by decide) (fun _ => polyOne)).trans
      (RatPolyCoeffEqv.zero_smul polyOne)
  exact (HaarCarrierEqv.add hp (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.neg
    (RatPolyCoeffEqv.one_smul polyOne)))).trans (RatPolyCoeffEqv.haarCarrier hz)

/-- Explicit seven-square witness, with unit norms used only through equality
under arbitrary insertions. -/
def radialCertificate {n : Nat} {p q : PolyQuaternion}
    (hp : Supported n p) (hq : Supported n q)
    (hup : HaarCarrierEqv n (polyQuaternionNorm p) polyOne)
    (huq : HaarCarrierEqv n (polyQuaternionNorm q) polyOne) :
    Certificate n (polyAdd (radialBudget p q)
      (polyNeg (polyMul (traceDifference p q) (traceDifference p q)))) := by
  have ht : RatPolyCoeffEqv (coeffEvalExpr (env p q) te) (traceDifference p q) :=
    (cap_mul_left 2 p.scalar).add (RatPolyCoeffEqv.neg (cap_mul_left 2 q.scalar))
  have hzP := ((unit_defect_zero hup).mul_left (coeffEvalExpr (env p q) mp)).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _))
  have hzQ := ((unit_defect_zero huq).mul_left (coeffEvalExpr (env p q) mq)).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _))
  have hz : HaarCarrierEqv n (coeffEvalExpr (env p q) rhsExpr)
      (coeffEvalExpr (env p q) sosExpr) :=
    (HaarCarrierEqv.add (HaarCarrierEqv.refl n _) (HaarCarrierEqv.add hzP hzQ)).trans
      (RatPolyCoeffEqv.haarCarrier (by
        exact ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero polyZero)).trans
          (RatPolyCoeffEqv.add_zero _)))
  exact .transport
    ((RatPolyCoeffEqv.haarCarrier
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (ht.mul ht).symm))).trans
      ((RatPolyCoeffEqv.haarCarrier (gap_ring p q)).trans hz))
    (sosCertificate hp hq)

/-- Retain the complete positive weight in both the radial displacement and
the fourth-order correction. This is not a factorization of mixed moments. -/
theorem weighted_radial_bound {n : Nat} {W : RatPoly} (R : Certificate n W)
    {p q : PolyQuaternion} (hp : Supported n p) (hq : Supported n q)
    (hup : HaarCarrierEqv n (polyQuaternionNorm p) polyOne)
    (huq : HaarCarrierEqv n (polyQuaternionNorm q) polyOne) :
    quaternionHaar n (polyMul W (polyMul (traceDifference p q) (traceDifference p q))) ≤
      quaternionHaar n (polyMul W (radialBudget p q)) :=
  weighted_order R (radialCertificate hp hq hup huq)

#print axioms traceDifference
#print axioms radialBudget_pin
#print axioms radialCertificate
#print axioms weighted_radial_bound

end YMGap.Continuum.QuaternionHaarRadialChordalIncrement
