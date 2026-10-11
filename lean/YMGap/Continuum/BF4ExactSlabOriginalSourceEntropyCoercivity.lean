/-
# Source-weighted ORIGINAL conditional defect payment with retained credit

Multiply the actual complete-action pointwise theorem by the SAME bounded
source g, keep the finite multiplication defect and negative source entropy,
then project by the literal Haar schedule. Its moment-based contraction uses
the computed biased moments from QuaternionHaarFamilySourceConcentration.

This supplies a finite source-weighted estimate, not an assumed analytic
payment. It does not produce a useful uniform kurtosis, identify a warmed
completed response with this insertion, remove either cutoff, or prove H1.
-/

import YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity
import YMGap.Continuum.QuaternionHaarFamilySourceConcentration
import YMGap.Continuum.RegularizedLogPolynomialProductDefect

namespace YMGap.Continuum.BF4ExactSlabOriginalSourceEntropyCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_smul evalRatPoly_one)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.QuaternionHaarFamilyPointwiseOrder (familyProject_pointwise_mono)
open YMGap.Continuum.QuaternionHaarFamilyFiniteEntropy
open YMGap.Continuum.QuaternionHaarFiniteEntropy (entropyStage entropyStage_eval)
open YMGap.Continuum.QuaternionHaarFamilySourceConcentration
open YMGap.Continuum.RegularizedLogPolynomial (partialSum)
open YMGap.Continuum.RegularizedLogPolynomialProductDefect (product_defect_bounds)
open YMGap.Continuum.RegularizedLogFiniteCoercivity (third)
open YMGap.Continuum.RegularizedLogPolynomialLowerTangent (ell)
open YMGap.Continuum.RegularizedLogFiniteProductCoercivity (selectedCount)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds
open YMGap.Continuum.BF4ExactSlabOriginalProductEntropyCoercivity
open YMGap.Continuum.BF4ExactSlabOriginalSelectedHaarEntropyCoercivity
open YMGap.Continuum.SU2HeatJacobiOriginalCoercivity (coercivityCutoff)
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount (activeFactorCount)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem qr (p q : PE) (h : RingNormaliser.normalize p = RingNormaliser.normalize q)
    (rho : Nat → Q') : RingNormaliser.eval rho p ≈ RingNormaliser.eval rho q :=
  poly_identity_of_normal_eq p q h rho

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  tc (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem partial_congr {a b : Q'} (h : a ≈ b) :
    ∀ N, partialSum a N ≈ partialSum b N
  | 0 => Q'.eqv_refl _
  | N+1 => Q'.add_eqv_congr' (partial_congr h N)
      (mc (Q'.eqv_refl _) (mc h
        (BernsteinSequenceWrap.pow_eqv_congr
          (Q'.add_eqv_congr' (Q'.eqv_refl 1) (Q'.neg_eqv_congr _ _ h)) (N+1))))

private theorem source_scalar_payment (W g D c b B : Q') (N : Nat)
    (hW : (0 : Q') ≤ W ∧ W ≤ 1) (hg : (0 : Q') ≤ g ∧ g ≤ 1)
    (hc : (0 : Q') ≤ c) (hB : (0 : Q') ≤ B)
    (hpayment : W*D ≤ c*(partialSum W N+b*W+B*Q'.invSucc N)) :
    (W*g)*D ≤ c*(partialSum (W*g) N-W*partialSum g N+b*(W*g)+(B+1)*Q'.invSucc N) := by
  let r := Q'.invSucc N
  have hpd := (product_defect_bounds W g hW.1 hW.2 hg.1 hg.2 N).2
  have hs := Q'.add_le_add_right _ _ (partialSum (W*g) N-W*partialSum g N) hpd
  have hleft : g*partialSum W N ≤ partialSum (W*g) N-W*partialSum g N+r :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (qr ((.var 0+ .var 1+ -(.var 2))+(.var 2+ -(.var 1)))
        (.var 0) (by decide) (fun
          | 0 => g*partialSum W N
          | 1 => W*partialSum g N
          | _ => partialSum (W*g) N)))
      (Q'.le_trans' _ _ _ hs
        (Q'.le_of_eqv (Q'.add_comm_eqv r (partialSum (W*g) N-W*partialSum g N))))
  have he : (B*r)*g ≤ B*r := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hg.2 (Q'.mul_nonneg _ _ hB (Q'.invSucc_nonneg N)))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hsum := Q'.add_le_add (Q'.add_le_add_right _ _ (b*(W*g)) hleft) he
  have hinside : g*(partialSum W N+b*W+B*r) ≤
      partialSum (W*g) N-W*partialSum g N+b*(W*g)+(B+1)*r := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_))
    · exact qr (.var 0*(.var 1+ .var 2* .var 3+ .var 4* .var 5))
        ((.var 0* .var 1+ .var 2*(.var 3* .var 0))+(.var 4* .var 5)* .var 0)
        (by decide) (fun
          | 0 => g | 1 => partialSum W N | 2 => b | 3 => W | 4 => B | _ => r)
    · exact qr (((.var 0+ -(.var 1)+ .var 2)+ .var 3)+ .var 4* .var 2)
        ((.var 0+ -(.var 1)+ .var 3)+(.var 4+1)* .var 2)
        (by decide) (fun
          | 0 => partialSum (W*g) N | 1 => W*partialSum g N
          | 2 => r | 3 => b*(W*g) | _ => B)
  have hp := Q'.mul_le_mul_of_nonneg_left _ _ g hpayment hg.1
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qr ((.var 0* .var 1)* .var 2) (.var 1*(.var 0* .var 2))
      (by decide) (fun | 0 => W | 1 => g | _ => D)))
    (Q'.le_trans' _ _ _ hp
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (qr (.var 0*(.var 1* .var 2)) (.var 1*(.var 0* .var 2))
          (by decide) (fun | 0 => g | 1 => c | _ => partialSum W N+b*W+B*r)))
        (Q'.mul_le_mul_of_nonneg_left _ _ c hinside hc)))

private def rhsPolynomial (W g : RatPoly) (N : Nat) (c b e : Q') : RatPoly :=
  polySmul c (polyAdd
    (polyAdd (entropyStage N (polyMul W g)) (polySmul (-1) (polyMul W (entropyStage N g))))
    (polyAdd (polySmul b (polyMul W g)) (polySmul e polyOne)))

private theorem constant_eval (rho : Nat → Q') (c : Q') :
    evalRatPoly rho (polySmul c polyOne) ≈ c :=
  tc (evalRatPoly_smul rho c polyOne) (tc (mc (Q'.eqv_refl _) (evalRatPoly_one rho)) (Q'.mul_one_eqv c))

private theorem minus_one_mul (a : Q') : (-1)*a ≈ -a :=
  tc (Q'.neg_mul_eqv 1 a) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))

private theorem rhs_eval (W g : RatPoly) (N : Nat) (c b e : Q') (rho : Nat → Q') :
    evalRatPoly rho (rhsPolynomial W g N c b e) ≈
      c*(partialSum (evalRatPoly rho (polyMul W g)) N-
        evalRatPoly rho W*partialSum (evalRatPoly rho g) N+
        (b*evalRatPoly rho (polyMul W g)+e)) :=
  tc (evalRatPoly_smul rho c _) (mc (Q'.eqv_refl _)
    (tc (evalRatPoly_add rho _ _) (Q'.add_eqv_congr'
      (tc (evalRatPoly_add rho _ _) (Q'.add_eqv_congr'
        (entropyStage_eval N (polyMul W g) rho)
        (tc (evalRatPoly_smul rho (-1) _) (tc (minus_one_mul _)
          (Q'.neg_eqv_congr _ _ (tc (evalRatPoly_mul rho _ _)
            (mc (Q'.eqv_refl _) (entropyStage_eval N g rho))))))))
      (tc (evalRatPoly_add rho _ _)
        (Q'.add_eqv_congr' (evalRatPoly_smul rho b _) (constant_eval rho e))))))

private theorem rhs_project (slots : List Nat) (W g : RatPoly)
    (N : Nat) (c b e : Q') (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs) (familyProject slots (rhsPolynomial W g N c b e)) ≈
      c*(evalRatPoly (environment qs) (familyProject slots (entropyStage N (polyMul W g)))-
        sourceEntropy slots W g qs N+(b*sourceMass slots W g qs+e)) := by
  refine tc (familyProject_smul_eval slots c _ _) (mc (Q'.eqv_refl _) ?_)
  rw [familyProject_add, familyProject_add, familyProject_add]
  exact tc (evalRatPoly_add _ _ _) (Q'.add_eqv_congr'
    (tc (evalRatPoly_add _ _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (tc (familyProject_smul_eval slots (-1) _ _) (minus_one_mul _))))
    (tc (evalRatPoly_add _ _ _) (Q'.add_eqv_congr'
      (familyProject_smul_eval slots b _ _) (familyProject_constant_eval slots e _))))

/-- Actual source insertion in the complete original conditional action. -/
def originalSourceDefect (q : Q') (hq0 : (0 : Q') < q) (K extent : Nat)
    (ids slots : List Nat) (selected : Nat → Bool) (g : RatPoly) (qs : Nat → UnitNorm) : Q' :=
  evalRatPoly (environment qs) (familyProject slots
    (polyMul (polyMul (normalizedHeatProduct q hq0 K extent ids) g)
      (selectedFaceDefectPolynomial extent selected ids)))

/-- Finite ORIGINAL source-tilt payment. Both biased partition and negative
source-entropy credit are retained at the SAME assignment and schedule. -/
theorem original_source_entropy_payment {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (ids slots : List Nat) (selected : Nat → Bool) (g : RatPoly)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1) (N : Nat) (hN : 1 ≤ N) :
    originalSourceDefect q hq0 K extent ids slots selected g qs ≤
      (256*(1-q))*(partialSum (sourceMass slots (normalizedHeatProduct q hq0 K extent ids) g qs) N-
        sourceEntropy slots (normalizedHeatProduct q hq0 K extent ids) g qs N+
        ((3*partialSum third N)*Q'.ofNat (selectedCount selected ids)*
          sourceMass slots (normalizedHeatProduct q hq0 K extent ids) g qs+
        (Q'.ofNat ids.length+3*Q'.ofNat (activeFactorCount q-1)*
          Q'.ofNat (selectedCount selected ids)+1)*Q'.invSucc N)) := by
  let W := normalizedHeatProduct q hq0 K extent ids
  let c := (256 : Q')*(1-q)
  let b := (3*partialSum third N)*Q'.ofNat (selectedCount selected ids)
  let B := Q'.ofNat ids.length+3*Q'.ofNat (activeFactorCount q-1)*Q'.ofNat (selectedCount selected ids)
  let e := (B+1)*Q'.invSucc N
  have hKf : SU2PointwiseHeatStrictFloor.finiteCutoff q ≤ K+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
  have hW (heads : Nat → UnitNorm) :
      (0 : Q') ≤ evalRatPoly (environment heads) W ∧ evalRatPoly (environment heads) W ≤ 1 :=
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_lt (normalizedFloor_positive hq0 hq1 K ids))
      (normalizedHeatProduct_bounds hq0 hq1 K extent ids hKf heads).1,
      (normalizedHeatProduct_bounds hq0 hq1 K extent ids hKf heads).2⟩
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt (HKPos.one_sub_pos hq1))
  have hB : (0 : Q') ≤ B := Q'.zero_le_add _ _ (ClusterCount.ofNat_nonneg _)
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) (ClusterCount.ofNat_nonneg _))
      (ClusterCount.ofNat_nonneg _))
  have hpoint (heads : Nat → UnitNorm) :
      evalRatPoly (environment heads)
        (polyMul (polyMul W g) (selectedFaceDefectPolynomial extent selected ids)) ≤
      evalRatPoly (environment heads) (rhsPolynomial W g N c b e) := by
    let rho := environment heads
    have hraw := source_scalar_payment (evalRatPoly rho W) (evalRatPoly rho g)
      (RegularizedLogFiniteProductCoercivity.selectedDefectSum (faceDefect extent heads) selected ids)
      c b B N (hW heads) (hg heads) hc hB
      (original_selected_product_coercivity_finite hq0 hq hq1 K extent ids selected heads hK N hN)
    have hL := tc (evalRatPoly_mul rho _ _)
      (mc (evalRatPoly_mul rho W g) (selectedFaceDefectPolynomial_eval extent selected heads ids))
    have hR := tc (rhs_eval W g N c b e rho)
      (qr (.var 0*(.var 1+ -(.var 2)+(.var 3+ .var 4)))
        (.var 0*(.var 1+ -(.var 2)+ .var 3+ .var 4)) (by decide) (fun
          | 0 => c | 1 => partialSum (evalRatPoly rho (polyMul W g)) N
          | 2 => evalRatPoly rho W*partialSum (evalRatPoly rho g) N
          | 3 => b*evalRatPoly rho (polyMul W g) | _ => e))
    have hp : partialSum (evalRatPoly rho (polyMul W g)) N ≈
        partialSum (evalRatPoly rho W*evalRatPoly rho g) N := by
      exact partial_congr (evalRatPoly_mul rho W g) N
    have hright : evalRatPoly rho (rhsPolynomial W g N c b e) ≈
        c*(partialSum (evalRatPoly rho W*evalRatPoly rho g) N-
          evalRatPoly rho W*partialSum (evalRatPoly rho g) N+
          b*(evalRatPoly rho W*evalRatPoly rho g)+e) :=
      tc hR (mc (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.add_eqv_congr' hp (Q'.eqv_refl _))
          (mc (Q'.eqv_refl _) (evalRatPoly_mul rho W g))) (Q'.eqv_refl _)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ hraw (Q'.ge_of_eqv hright))
  have hupper (heads : Nat → UnitNorm) : evalRatPoly (environment heads) (polyMul W g) ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (evalRatPoly_mul _ W g))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (hg heads).2 (hW heads).1)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) (hW heads).2))
  have hj := family_partial_jensen slots (polyMul W g) hupper qs N
  have hp := familyProject_pointwise_mono slots _ _ hpoint qs
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (rhs_project slots W g N c b e qs))
      (Q'.mul_le_mul_of_nonneg_left _ _ c
        (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ hj)) hc))

/-- The source-entropy credit is paid by its COMPUTED biased moments, not
discarded or replaced by a supplied kurtosis bound. The positive source mass
is explicit; no normalized conclusion is asserted for a zero source. -/
theorem original_source_moment_payment {q : Q'}
    (hq0 : (0 : Q') < q) (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K extent : Nat) (ids slots : List Nat) (selected : Nat → Bool) (g : RatPoly)
    (hg : ∀ heads : Nat → UnitNorm,
      (0 : Q') ≤ evalRatPoly (environment heads) g ∧ evalRatPoly (environment heads) g ≤ 1)
    (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1)
    (ha : (0 : Q') < sourceMass slots (normalizedHeatProduct q hq0 K extent ids) g qs)
    (N : Nat) (hN : 1 ≤ N) :
    originalSourceDefect q hq0 K extent ids slots selected g qs ≤
      (256*(1-q))*(partialSum (sourceMass slots (normalizedHeatProduct q hq0 K extent ids) g qs) N-
        sourceMass slots (normalizedHeatProduct q hq0 K extent ids) g qs*
          ell (sourceMean slots (normalizedHeatProduct q hq0 K extent ids) g qs ha) N+
        ((3*partialSum third N)*Q'.ofNat (selectedCount selected ids)*
          sourceMass slots (normalizedHeatProduct q hq0 K extent ids) g qs+
        (Q'.ofNat ids.length+3*Q'.ofNat (activeFactorCount q-1)*
          Q'.ofNat (selectedCount selected ids)+1)*Q'.invSucc N)) := by
  have hKf : SU2PointwiseHeatStrictFloor.finiteCutoff q ≤ K+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
  have hW (heads : Nat → UnitNorm) :
      (0 : Q') ≤ evalRatPoly (environment heads) (normalizedHeatProduct q hq0 K extent ids) :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt (normalizedFloor_positive hq0 hq1 K ids))
      (normalizedHeatProduct_bounds hq0 hq1 K extent ids hKf heads).1
  have hcredit := retained_credit_upper slots (normalizedHeatProduct q hq0 K extent ids) g hW hg qs ha N
  exact Q'.le_trans' _ _ _
    (original_source_entropy_payment hq0 hq hq1 K extent ids slots selected g hg qs hK N hN)
    (Q'.mul_le_mul_of_nonneg_left _ _ (256*(1-q))
      (Q'.add_le_add_right _ _ _ hcredit)
      (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt (HKPos.one_sub_pos hq1))))

end YMGap.Continuum.BF4ExactSlabOriginalSourceEntropyCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabOriginalSourceEntropyCoercivity.originalSourceDefect
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSourceEntropyCoercivity.original_source_entropy_payment
#print axioms YMGap.Continuum.BF4ExactSlabOriginalSourceEntropyCoercivity.original_source_moment_payment
