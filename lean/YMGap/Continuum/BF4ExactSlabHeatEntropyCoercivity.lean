/-
# Original face-defect payment by the actual finite entropy series

Use the EXISTING identity-normalized original face value, with its original
heat coefficients and inclusive cutoff K. The actual Jacobi active count
k=M(q)-1 supplies 256*(1-q)*k*(1-decay(x)) >= 1-x.
The finite weighted entropy inequality therefore pays the original face
defect. No logarithm or entropy-coercivity premise is supplied.

The finite remainder is 256*(1-q)*3*k/(N+1), where N is the independent
entropy cutoff. A computed q/epsilon cutoff removes it, uniformly in the
face, assignment, extent and heat cutoff beyond coercivityCutoff(q).
This is pointwise one-face payment. The complete collar product, conditional
integration, OLD-centered signed response, physical scaling and gap remain
separate obligations. Identity normalization is not division by a partition.
-/

import YMGap.Continuum.RegularizedLogFiniteCoercivity
import YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization
import YMGap.Continuum.SU2HeatJacobiOriginalCoercivity
import YMGap.Continuum.ClusterCount

namespace YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (evalRatPoly)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail (faceScalar)
open YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor (eval_faceHeatPolynomial_eqv)
open YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder (faceScalar_box)
open YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds (identityHeat)
open YMGap.Continuum.BF4ExactSlabPolynomialHeatLocalization
open YMGap.Continuum.SU2HeatJacobiOriginalCoercivity
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount
open YMGap.Continuum.RegularizedLogPolynomial (partialSum modulus)
open YMGap.Continuum.RegularizedLogFiniteCoercivity (third)
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
private abbrev PE := PolyExpr
local instance : Add PE := ⟨.add⟩
local instance : Mul PE := ⟨.mul⟩
local instance : Neg PE := ⟨.neg⟩
local instance (n : Nat) : OfNat PE n := ⟨.const (Int.ofNat n)⟩

private theorem qr (a b : PE) (h : RingNormaliser.normalize a = RingNormaliser.normalize b)
    (rho : Nat → Q') : RingNormaliser.eval rho a ≈ RingNormaliser.eval rho b :=
  poly_identity_of_normal_eq a b h rho

private theorem tc {a b c : Q'} (h : a ≈ b) (k : b ≈ c) : a ≈ c :=
  Q'.eqv_trans _ _ _ h k

private theorem count_le_twice {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q')) :
    Q'.ofNat (activeFactorCount q) ≤ 2*Q'.ofNat (activeFactorCount q-1) := by
  have ht := activeFactorCount_two hq hq1
  have hn : activeFactorCount q ≤ 2*(activeFactorCount q-1) := by omega
  exact Q'.le_trans' _ _ _ (ClusterCount.ofNat_le_ofNat hn)
    (Q'.le_of_eqv (ClusterCount.ofNat_mul_eqv 2 (activeFactorCount q-1)))

/-- Cleared coefficient; no inverse or hidden physical calibration is used. -/
theorem active_gap_coercivity {q x : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (_hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    1-x ≤ (256*(1-q))*(Q'.ofNat (activeFactorCount q-1)*(1-decay x)) := by
  let g := (1 : Q')-q
  let k := Q'.ofNat (activeFactorCount q-1)
  have hg0 := Q'.le_of_lt (HKPos.one_sub_pos hq1)
  have hm := Q'.le_trans' _ _ _ (activeFactorCount_mass hq hq1)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (count_le_twice hq hq1) hg0)
  have hm16 := Q'.mul_le_mul_of_nonneg_left _ _ (16 : Q') hm (by decide)
  have hmass : (1 : Q') ≤ (32*g)*k := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (by decide : (16 : Q')*Q'.mkPos 1 16 (by decide) ≈ 1))
    (Q'.le_trans' _ _ _ hm16 (Q'.le_of_eqv
      (qr (16*((2*.var 0)*.var 1)) ((32*.var 1)*.var 0) (by decide)
        (fun | 0 => k | _ => g))))
  have hd0 := Q'.sub_nonneg_of_le hxhi
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ (1-x) hmass hd0
  have hp : (256*g)*(k*(1-decay x)) ≈ ((32*g)*k)*(1-x) := by
    unfold decay
    exact tc (qr ((256*.var 0)*(.var 1*(1 + -(1 + -(.var 2*.var 3)))))
      ((256*.var 2)*((.var 0*.var 1)*.var 3)) (by decide)
      (fun | 0 => g | 1 => k | 2 => Q'.mkPos 1 8 (by decide) | _ => 1-x))
      (tc (Q'.mul_eqv_congr_right _ _ _
        (by decide : (256 : Q')*Q'.mkPos 1 8 (by decide) ≈ 32))
        (qr (32*((.var 0*.var 1)*.var 2)) (((32*.var 0)*.var 1)*.var 2)
          (by decide) (fun | 0 => g | 1 => k | _ => 1-x)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
    (Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv hp))

/-- The existing normalized original face satisfies the actual heat envelope. -/
theorem normalizedFace_envelope {q : Q'} (hq0 : (0 : Q') < q)
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K extent id : Nat) (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1) :
    normalizedFace q hq0 K extent id qs ≤
      3*(decay (evalRatPoly (environment qs) (faceScalar extent id)))^(activeFactorCount q-1) := by
  let x := evalRatPoly (environment qs) (faceScalar extent id)
  let r := reciprocal q hq0 K
  let b := (decay x)^(activeFactorCount q-1)
  have hr0 : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos _ _)
  have hh := Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_faceHeatPolynomial_eqv q K extent id (environment qs)))
    (original_heat_envelope hq hq1 (faceScalar_box extent id qs).1
      (faceScalar_box extent id qs).2 K hK)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ r hh hr0
  have hrpin : r*identityHeat q K ≈ (1 : Q') :=
    tc (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv (identityHeat q K)
        (BF4ExactSlabNormalizedHeatBounds.identityHeat_positive (Q'.le_of_lt hq0) K))
  have hp : r*(3*b*identityHeat q K) ≈ 3*b :=
    tc (qr (.var 0*((3*.var 1)*.var 2)) ((3*.var 1)*(.var 0*.var 2))
      (by decide) (fun | 0 => r | 1 => b | _ => identityHeat q K))
      (tc (Q'.mul_eqv_congr_left _ _ _ hrpin)
        (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hp)

/-- Finite original face-defect payment. N is the independent entropy cutoff. -/
theorem original_face_coercivity_finite {q : Q'} (hq0 : (0 : Q') < q)
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K extent id : Nat) (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1)
    (N : Nat) (hN : 1 ≤ N) :
    normalizedFace q hq0 K extent id qs*(1-evalRatPoly (environment qs) (faceScalar extent id)) ≤
      (256*(1-q))*(partialSum (normalizedFace q hq0 K extent id qs) N+
        3*normalizedFace q hq0 K extent id qs*partialSum third N+
        (3*Q'.ofNat (activeFactorCount q-1))*Q'.invSucc N) := by
  let h := normalizedFace q hq0 K extent id qs
  let x := evalRatPoly (environment qs) (faceScalar extent id)
  have hKf : SU2PointwiseHeatStrictFloor.finiteCutoff q ≤ K+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK
  have hh0 : (0 : Q') ≤ h := Q'.le_trans' _ _ _ (Q'.le_of_lt (eta_positive hq0 hq1 K))
    (normalizedFace_floor hq0 hq1 K extent id qs hKf)
  have hb := decay_bounds (faceScalar_box extent id qs).1 (faceScalar_box extent id qs).2
  have hc0 : (0 : Q') ≤ 256*(1-q) := Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (HKPos.one_sub_pos hq1))
  have hc := Q'.mul_le_mul_of_nonneg_left _ _ h
    (active_gap_coercivity hq hq1 (faceScalar_box extent id qs).1 (faceScalar_box extent id qs).2) hh0
  have he := RegularizedLogFiniteCoercivity.envelope_coercivity h hh0
    (normalizedFace_upper hq0 K extent id qs) (decay x)
    (Q'.pos_of_lt_of_le (by decide : (0 : Q') < Q'.mkPos 3 4 (by decide)) hb.1) hb.2
    (activeFactorCount q-1) N hN (normalizedFace_envelope hq0 hq hq1 K extent id qs hK)
  exact Q'.le_trans' _ _ _ hc (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qr (.var 0*(.var 1*.var 2)) (.var 1*(.var 0*.var 2))
      (by decide) (fun | 0 => h | 1 => 256*(1-q) | _ => Q'.ofNat (activeFactorCount q-1)*(1-decay x))))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ he hc0))

/-- The entropy approximation threshold is data, with the nome dependence explicit. -/
def entropyCoercivityRate (q epsilon : Q') : Nat :=
  max 1 (modulus (epsilon*Q'.invSucc (768*(activeFactorCount q-1))))

private theorem error_coefficient_le {q : Q'} (hq0 : (0 : Q') < q) (_hq1 : q < (1 : Q')) :
    (256*(1-q))*(3*Q'.ofNat (activeFactorCount q-1)) ≤
      Q'.ofNat (768*(activeFactorCount q-1)) := by
  let k := Q'.ofNat (activeFactorCount q-1)
  have hg1 : 1-q ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hq0)))
    (Q'.le_of_eqv (by decide : (1 : Q')+ -(0 : Q') ≈ 1))
  have hk0 := ClusterCount.ofNat_nonneg (activeFactorCount q-1)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (256 : Q')
    (Q'.mul_le_mul_of_nonneg_right _ _ (3*k) hg1 (Q'.mul_nonneg _ _ (by decide) hk0)) (by decide)
  have hp : 256*(1*(3*k)) ≈ Q'.ofNat (768*(activeFactorCount q-1)) :=
    tc (qr (256*(1*(3*.var 0))) (768*.var 0) (by decide) (fun _ => k))
      (Q'.eqv_symm (ClusterCount.ofNat_mul_eqv 768 (activeFactorCount q-1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hp))

/-- Actual pointwise entropy payment with a recoverable q/epsilon rate,
uniform in the assignment, face, extent and admissible original heat cutoff. -/
theorem original_face_coercivity_approx {q : Q'} (hq0 : (0 : Q') < q)
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (K extent id : Nat) (qs : Nat → UnitNorm) (hK : coercivityCutoff q ≤ K+1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (N : Nat)
    (hN : entropyCoercivityRate q epsilon ≤ N) :
    normalizedFace q hq0 K extent id qs*(1-evalRatPoly (environment qs) (faceScalar extent id)) ≤
      (256*(1-q))*(partialSum (normalizedFace q hq0 K extent id qs) N+
        3*normalizedFace q hq0 K extent id qs*partialSum third N)+epsilon := by
  let k := activeFactorCount q-1
  let A := 768*k
  let delta := epsilon*Q'.invSucc A
  have hd : (0 : Q') < delta := Q'.mul_pos he (Q'.invSucc_pos A)
  have hN1 : 1 ≤ N := Nat.le_trans (Nat.le_max_left _ _) hN
  have hNm : modulus delta ≤ N := Nat.le_trans (Nat.le_max_right _ _) hN
  have hinv := Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hNm) (HalfPow.invSucc_den_le delta hd)
  have hA0 := ClusterCount.ofNat_nonneg A
  have hA1 : Q'.ofNat A*Q'.invSucc A ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (ClusterCount.ofNat_le_ofNat (Nat.le_succ A)) (Q'.invSucc_nonneg A))
    (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc A))
  have heps : Q'.ofNat A*delta ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qr (.var 0*(.var 1*.var 2)) (.var 1*(.var 0*.var 2))
      (by decide) (fun | 0 => Q'.ofNat A | 1 => epsilon | _ => Q'.invSucc A)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hA1 (Q'.le_of_lt he))
      (Q'.le_of_eqv (Q'.mul_one_eqv epsilon)))
  have herr : ((256*(1-q))*(3*Q'.ofNat k))*Q'.invSucc N ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _
      (error_coefficient_le hq0 hq1) (Q'.invSucc_nonneg N))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hinv hA0) heps)
  have hf := original_face_coercivity_finite hq0 hq hq1 K extent id qs hK N hN1
  let B := partialSum (normalizedFace q hq0 K extent id qs) N+
    3*normalizedFace q hq0 K extent id qs*partialSum third N
  have hp : (256*(1-q))*(B+(3*Q'.ofNat k)*Q'.invSucc N) ≈
      (256*(1-q))*B+((256*(1-q))*(3*Q'.ofNat k))*Q'.invSucc N :=
    tc (Q'.mul_add_eqv _ _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
  exact Q'.le_trans' _ _ _ hf (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (Q'.add_le_add_left _ _ _ herr))

end YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity

#print axioms YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity.active_gap_coercivity
#print axioms YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity.normalizedFace_envelope
#print axioms YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity.original_face_coercivity_finite
#print axioms YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity.entropyCoercivityRate
#print axioms YMGap.Continuum.BF4ExactSlabHeatEntropyCoercivity.original_face_coercivity_approx
