/-
# A finite local band around the same erased product-heat message

Each factor in a selected prefix is removed using the original one-factor
conditional certificate. The remaining factors and the entire certified
input stay inside the same Haar message. Repeated indices pay their literal
multiplicity; no independence or factorization of the input is assumed.
This is a finite conditional-message comparison, not a spatial or OS gap.
-/

import YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage

namespace YMGap.Continuum.SU2QuaternionProductHeatLocalBand

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
  (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatConditionalMessage
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left cap_mul)

local infix:50 " ≈ " => Q'.eqv

private def zeroCertificate (n : Nat) : Certificate n polyZero :=
  Certificate.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
    (Certificate.constant n 0 (Q'.le_refl' _))

private theorem lower_zero (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd p (polyNeg (polySmul 1 p))) polyZero :=
  (((RatPolyCoeffEqv.refl p).add
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.one_smul p))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => p))).trans
    (RatPolyCoeffEqv.zero_smul polyOne)

private theorem upper_zero (p : RatPoly) :
    RatPolyCoeffEqv (polyAdd (polySmul 1 p) (polyNeg p)) polyZero :=
  (((RatPolyCoeffEqv.one_smul p).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => p))).trans
    (RatPolyCoeffEqv.zero_smul polyOne)

private theorem lower_join (u s : Q') (a b c : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd a (polyNeg (polySmul u b)))
        (polySmul u (polyAdd b (polyNeg (polySmul s c)))))
      (polyAdd a (polyNeg (polySmul (u*s) c))) := by
  have hleft : RatPolyCoeffEqv
      (polyAdd (polyAdd a (polyNeg (polySmul u b)))
        (polySmul u (polyAdd b (polyNeg (polySmul s c)))))
      (polyAdd (polyAdd a (polyNeg (polyMul (cap u) b)))
        (polyMul (cap u) (polyAdd b (polyNeg (polyMul (cap s) c))))) :=
    ((RatPolyCoeffEqv.refl a).add
      (RatPolyCoeffEqv.neg (cap_mul_left u b).symm)).add
      ((cap_mul_left u _).symm.trans
        (((RatPolyCoeffEqv.refl b).add
          (RatPolyCoeffEqv.neg (cap_mul_left s c).symm)).mul_left (cap u)))
  have hring : RatPolyCoeffEqv
      (polyAdd (polyAdd a (polyNeg (polyMul (cap u) b)))
        (polyMul (cap u) (polyAdd b (polyNeg (polyMul (cap s) c)))))
      (polyAdd a (polyNeg (polyMul (polyMul (cap u) (cap s)) c))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
        (.mul (.var 3) (.add (.var 1) (.neg (.mul (.var 4) (.var 2))))))
      (.add (.var 0) (.neg (.mul (.mul (.var 3) (.var 4)) (.var 2))))
      (by decide)
      (fun | 0 => a | 1 => b | 2 => c | 3 => cap u | _ => cap s)
  exact hleft.trans (hring.trans
    ((RatPolyCoeffEqv.refl a).add
      (RatPolyCoeffEqv.neg ((cap_mul u s).mul_right c |>.trans
        (cap_mul_left (u*s) c)))))

private theorem upper_join (u s : Q') (a b c : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul u b) (polyNeg a))
        (polySmul u (polyAdd (polySmul s c) (polyNeg b))))
      (polyAdd (polySmul (u*s) c) (polyNeg a)) := by
  have hleft : RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul u b) (polyNeg a))
        (polySmul u (polyAdd (polySmul s c) (polyNeg b))))
      (polyAdd (polyAdd (polyMul (cap u) b) (polyNeg a))
        (polyMul (cap u) (polyAdd (polyMul (cap s) c) (polyNeg b)))) :=
    (((cap_mul_left u b).symm.add (RatPolyCoeffEqv.refl _)).add
      ((cap_mul_left u _).symm.trans
        (((cap_mul_left s c).symm.add (RatPolyCoeffEqv.refl _)).mul_left (cap u))))
  have hring : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul (cap u) b) (polyNeg a))
        (polyMul (cap u) (polyAdd (polyMul (cap s) c) (polyNeg b))))
      (polyAdd (polyMul (polyMul (cap u) (cap s)) c) (polyNeg a)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 3) (.var 1)) (.neg (.var 0)))
        (.mul (.var 3) (.add (.mul (.var 4) (.var 2)) (.neg (.var 1)))))
      (.add (.mul (.mul (.var 3) (.var 4)) (.var 2)) (.neg (.var 0)))
      (by decide)
      (fun | 0 => a | 1 => b | 2 => c | 3 => cap u | _ => cap s)
  exact hleft.trans (hring.trans
    (((cap_mul u s).mul_right c |>.trans (cap_mul_left (u*s) c)).add
      (RatPolyCoeffEqv.refl _)))

/-- The erased output is still a supported, certificate-positive message;
no exterior heat factor or input channel is dropped. -/
def erasedCertificate (n : Nat) {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (restIds : List Nat) (hrest : ∀ i, i ∈ restIds → i < n)
    {f : RatPoly} (hf : SupportedQuaternionBlocks n f) (F : Certificate n f) :
    Certificate n (productMap n w K restIds f) :=
  partialHaarHeads_certificate n n
    ((productHeatCertificate n hw0 hw1 K hK restIds hrest).mul
      (certificate_extend n hf F))

/-- Erasing a finite PREFIX costs exactly one head floor per literal factor.
The comparison is a witness-bearing positive polynomial certificate. -/
def productMap_localFloorCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (localIds restIds : List Nat)
    (hlocal : ∀ i, i ∈ localIds → i < n)
    (hrest : ∀ i, i ∈ restIds → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (F : Certificate n f) :
    Certificate n (polyAdd (productMap n w K (localIds ++ restIds) f)
      (polyNeg (polySmul ((headFloor w)^localIds.length)
        (productMap n w K restIds f)))) := by
  match localIds with
  | [] =>
      simpa only [List.nil_append, List.length_nil, Q'.pow_zero] using
        (Certificate.ofCoeff (lower_zero (productMap n w K restIds f))
          (zeroCertificate n))
  | i::is =>
      let h := headFloor w
      let a := productMap n w K ((i::is) ++ restIds) f
      let b := productMap n w K (is ++ restIds) f
      let c := productMap n w K restIds f
      have hi : i < n := hlocal i List.mem_cons_self
      have his : ∀ j, j ∈ is → j < n :=
        fun j hj => hlocal j (List.mem_cons_of_mem i hj)
      have hall : ∀ j, j ∈ is ++ restIds → j < n := by
        intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · exact his j hj
        · exact hrest j hj
      have hstep : Certificate n (polyAdd a (polyNeg (polySmul h b))) :=
        productMap_floorCertificate n hw0 hw1 K hK i (is ++ restIds)
          hi hall hf F
      have htail := productMap_localFloorCertificate n hw0 hw1 K hK
        is restIds his hrest hf F
      have hnonneg : (0 : Q') ≤ h :=
        Q'.le_of_lt (headFloor_positive hw0 hw1)
      have hjoin := hstep.add (.smul h hnonneg htail)
      have halg := lower_join h (h^is.length) a b c
      simpa only [List.cons_append, List.length_cons, Q'.pow_succ] using
        (Certificate.ofCoeff halg.symm hjoin)

/-- Matching finite PREFIX cap against precisely the same erased message. -/
def productMap_localCapCertificate (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (localIds restIds : List Nat)
    (hlocal : ∀ i, i ∈ localIds → i < n)
    (hrest : ∀ i, i ∈ restIds → i < n) {f : RatPoly}
    (hf : SupportedQuaternionBlocks n f) (F : Certificate n f) :
    Certificate n (polyAdd (polySmul ((prefixCap w)^localIds.length)
      (productMap n w K restIds f))
      (polyNeg (productMap n w K (localIds ++ restIds) f))) := by
  match localIds with
  | [] =>
      simpa only [List.nil_append, List.length_nil, Q'.pow_zero] using
        (Certificate.ofCoeff (upper_zero (productMap n w K restIds f))
          (zeroCertificate n))
  | i::is =>
      let u := prefixCap w
      let a := productMap n w K ((i::is) ++ restIds) f
      let b := productMap n w K (is ++ restIds) f
      let c := productMap n w K restIds f
      have hi : i < n := hlocal i List.mem_cons_self
      have his : ∀ j, j ∈ is → j < n :=
        fun j hj => hlocal j (List.mem_cons_of_mem i hj)
      have hall : ∀ j, j ∈ is ++ restIds → j < n := by
        intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · exact his j hj
        · exact hrest j hj
      have hstep : Certificate n (polyAdd (polySmul u b) (polyNeg a)) :=
        productMap_capCertificate n hw0 hw1 K hK i (is ++ restIds)
          hi hall hf F
      have htail := productMap_localCapCertificate n hw0 hw1 K hK
        is restIds his hrest hf F
      have hnonneg : (0 : Q') ≤ u := prefixCap_nonnegative hw0
      have hjoin := hstep.add (.smul u hnonneg htail)
      have halg := upper_join u (u^is.length) a b c
      simpa only [List.cons_append, List.length_cons, Q'.pow_succ] using
        (Certificate.ofCoeff halg.symm hjoin)

#print axioms erasedCertificate
#print axioms productMap_localFloorCertificate
#print axioms productMap_localCapCertificate

end YMGap.Continuum.SU2QuaternionProductHeatLocalBand
