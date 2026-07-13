/-
# Harmonic spacing absorption for the dimensionless margin

The additive harmonic mass drift is not separately bounded by the
multiplicative defect after division by the next spacing.  The contraction of
the spacing supplies the missing payment.  This module keeps those two terms
together and proves the exact scalar absorption needed to turn the additive
mass-drop estimate into the multiplicative dimensionless-margin step.
-/

import YMGap.Continuum.HarmonicThetaPascalClosure
import YMGap.Continuum.HarmonicWeightedAbelReserve
import YMGap.Continuum.SpectralMarginBridge
import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.HarmonicTrueMarginAbsorption

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralMarginBridge
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

private theorem absorption_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem absorption_one_num : (1 : Q').num = 1 := rfl
private theorem absorption_one_den_cast : (((1 : Q').den : Int)) = 1 := rfl

local macro "absorption_ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, absorption_neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem harmonicSpacing_eqv_harmU_sq (k : Nat) :
    harmonicSpacing k ≈ harmU k * harmU k := by
  unfold harmonicSpacing Ncut harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num,
    Q'.mkPos_den, Int.one_mul, Int.mul_one]
  push_cast
  rfl

private theorem harmU_succ_mul_one_add (k : Nat) :
    harmU (k + 1) * ((1 : Q') + harmU k) ≈ harmU k := by
  change Q'.invSucc (k + 2) * ((1 : Q') + Q'.invSucc (k + 1)) ≈
    Q'.invSucc (k + 1)
  have h := YMGap.Constructive.ExpNeg.invSucc_cancel (k + 1)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.add_comm_eqv (1 : Q') (Q'.invSucc (k + 1)))) h

/-- The finite-character dimensionless harmonic margin. -/
def harmonicTrueMargin (k : Nat) : Q' :=
  Q'.divPos (harmonicMass k) (harmonicSpacing k) (harmonicSpacing_pos k)

/-- The reciprocal-quadratic schedule has enough spacing gain to absorb the
coefficient-two lattice drift once a `4u²` transverse payment is retained. -/
private theorem four_unit_schedule (k : Nat) :
    (Q'.ofNat 2 * invSqTerm 2 (by decide) k) * harmonicSpacing k ≤
      harmU k *
        (harmonicSpacing k +
          -(((1 : Q') + -(Q'.ofNat 4 * (harmU k * harmU k))) *
            harmonicSpacing (k + 1))) := by
  unfold invSqTerm harmonicSpacing harmU Ncut unit
  show _ * (_ : Int) ≤ _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, absorption_neg_num_cast,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    absorption_one_num, absorption_one_den_cast,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
    Int.neg_neg, Int.one_mul, Int.mul_one]
  push_cast
  let n : Int := (k : Int) + 1 + 1
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hsimple :
      2 * ((n + 1) * (n + 1)) ≤
        n * ((n + 1) * (n + 1)) + -(n * n * n) + 4 * n := by
    simp only [Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one, Int.mul_assoc]
    omega
  let t : Int := n * (n * n * (n * n))
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    exact Int.mul_nonneg (by omega)
      (Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega))
        (Int.mul_nonneg (by omega) (by omega)))
  have hscaled : t * (2 * ((n + 1) * (n + 1))) ≤
      t * (n * ((n + 1) * (n + 1)) + -(n * n * n) + 4 * n) :=
    Int.mul_le_mul_of_nonneg_left hsimple ht0
  have hleft :
      2 * (n * (n * n * (n * n * ((n + 1) * (n + 1))))) =
        t * (2 * ((n + 1) * (n + 1))) := by
    dsimp only [t]
    ac_rfl
  have hright :
      n * n * ((n + 1) * (n + 1)) * (n * n * (n * n)) +
          (-(n * n * (n * n) * (n * n * (n * n))) +
            4 * (n * n) * (n * n * (n * n))) =
        t * (n * ((n + 1) * (n + 1)) + -(n * n * n) + 4 * n) := by
    let a := n * ((n + 1) * (n + 1))
    let b := -(n * n * n)
    let c := 4 * n
    have hdist : t * (a + b + c) = t * a + (t * b + t * c) := by
      exact Eq.trans
        (Eq.trans (Int.mul_add t (a + b) c)
          (congrArg (fun z => z + t * c) (Int.mul_add t a b)))
        (Int.add_assoc (t * a) (t * b) (t * c))
    rw [hdist]
    dsimp only [t, a, b, c]
    rw [Int.mul_neg]
    congr 1
    · ac_rfl
    congr 1
    · apply congrArg Neg.neg
      ac_rfl
    · ac_rfl
  change 2 * (n * (n * n * (n * n * ((n + 1) * (n + 1))))) ≤
      n * n * ((n + 1) * (n + 1)) * (n * n * (n * n)) +
        (-(n * n * (n * n) * (n * n * (n * n))) +
          4 * (n * n) * (n * n * (n * n)))
  rw [hleft, hright]
  exact hscaled

/-- The exact renormalized transverse defect retains at least the `4u²`
payment used by `four_unit_schedule`. -/
private theorem four_unit_sq_le_defect (k : Nat) :
    Q'.ofNat 4 * (harmU k * harmU k) ≤
      bondMovingDeltaRen 1 pMult (harmW k) := by
  let u := harmU k
  let w := harmW k
  have huw : (1 : Q') - w ≈ u := by
    dsimp only [w]
    unfold harmW oneSub
    refine Q'.eqv_trans _ ((1 : Q') + (-(1 : Q') + harmU k)) _ ?_ ?_
    · refine Q'.add_eqv_congr_left 1 _ _ ?_
      refine Q'.eqv_trans _ (-(1 : Q') + -(-harmU k)) _
        (Q'.neg_add_eqv 1 (-harmU k)) ?_
      exact Q'.add_eqv_congr_left (-(1 : Q')) _ _
        (Q'.neg_neg_eqv (harmU k))
    · refine Q'.eqv_trans _ (((1 : Q') + -(1 : Q')) + harmU k) _
        (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1) (harmU k))) ?_
      refine Q'.eqv_trans _ ((0 : Q') + harmU k) _
        (Q'.add_eqv_congr_right _ _ (harmU k) (Q'.add_neg_self_eqv 1)) ?_
      exact YMGap.Constructive.QPoly.q_zero_add_eqv (harmU k)
  have hdef : bondMovingDeltaRen 1 pMult w ≈
      Q'.ofNat 2 * ((u * u) * (Q'.ofNat 2 + w)) := by
    unfold bondMovingDeltaRen pMult dimQ c4
    refine Q'.eqv_trans _
      (Q'.ofNat 2 *
        ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3))) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.eqv_refl _)
    · refine Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ ?_
      refine Q'.eqv_trans _
        ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w)) _
        (renDefect_factor w) ?_
      exact Q'.mul_eqv_congr_right _ _ (Q'.ofNat 2 + w)
        (Q'.eqv_trans _ (u * ((1 : Q') - w)) _
          (Q'.mul_eqv_congr_right _ _ ((1 : Q') - w) huw)
          (Q'.mul_eqv_congr_left u _ _ huw))
  have hsq0 : (0 : Q') ≤ u * u :=
    Q'.mul_nonneg _ _ (harmU_nonneg k) (harmU_nonneg k)
  have h22 : (Q'.ofNat 2 : Q') ≤ Q'.ofNat 2 + w := by
    have h := Q'.add_le_add_left (Q'.ofNat 2) 0 w (harmW_nonneg k)
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (YMGap.Constructive.QPoly.q_add_zero_eqv (Q'.ofNat 2))) h
  have hinner : (u * u) * Q'.ofNat 2 ≤ (u * u) * (Q'.ofNat 2 + w) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h22 hsq0
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hinner (by decide)
  have hleft : Q'.ofNat 4 * (u * u) ≈
      Q'.ofNat 2 * ((u * u) * Q'.ofNat 2) := by
    refine Q'.eqv_trans _
      ((Q'.ofNat 2 * Q'.ofNat 2) * (u * u)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ (u * u) (by decide)
    · refine Q'.eqv_trans _
        (Q'.ofNat 2 * (Q'.ofNat 2 * (u * u))) _
        (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
        (Q'.mul_comm_eqv (Q'.ofNat 2) (u * u))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hdef))

/-- Pure schedule arithmetic behind the absorption theorem. -/
theorem twoInvSq_spacing_le_harmU_spacing_defect (k : Nat) :
    (Q'.ofNat 2 * invSqTerm 2 (by decide) k) * harmonicSpacing k ≤
      harmU k *
        (harmonicSpacing k -
          ((1 : Q') - bondMovingDeltaRen 1 pMult (harmW k)) *
            harmonicSpacing (k + 1)) := by
  let four := Q'.ofNat 4 * (harmU k * harmU k)
  let delta := bondMovingDeltaRen 1 pMult (harmW k)
  let next := harmonicSpacing (k + 1)
  have hfour : four ≤ delta := four_unit_sq_le_defect k
  have hneg : -delta ≤ -four := Q'.neg_le_neg hfour
  have hcoef : (1 : Q') + -delta ≤ (1 : Q') + -four :=
    Q'.add_le_add_left 1 _ _ hneg
  have hnext0 : (0 : Q') ≤ next :=
    Q'.le_of_lt (harmonicSpacing_pos (k + 1))
  have hmul : ((1 : Q') + -delta) * next ≤
      ((1 : Q') + -four) * next :=
    Q'.mul_le_mul_of_nonneg_right _ _ next hcoef hnext0
  have hnegmul : -(((1 : Q') + -four) * next) ≤
      -(((1 : Q') + -delta) * next) := Q'.neg_le_neg hmul
  have hbracket :
      harmonicSpacing k + -(((1 : Q') + -four) * next) ≤
        harmonicSpacing k + -(((1 : Q') + -delta) * next) :=
    Q'.add_le_add_left (harmonicSpacing k) _ _ hnegmul
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (harmU k) hbracket
    (harmU_nonneg k)
  exact Q'.le_trans' _ _ _ (four_unit_schedule k) (by
    dsimp only [four, delta, next] at hscaled
    exact hscaled)

/-- Exact scalar payment: the spacing contraction together with the transverse
defect absorbs the full coefficient-two inverse-square lattice-mass drift,
using only the already-proved harmonic-unit mass floor. -/
theorem harmonic_spacing_defect_absorbs_twoInvSq (k : Nat) :
    (Q'.ofNat 2 * invSqTerm 2 (by decide) k) * harmonicSpacing k ≤
      harmonicMass k *
        (harmonicSpacing k -
          ((1 : Q') - bondMovingDeltaRen 1 pMult (harmW k)) *
            harmonicSpacing (k + 1)) := by
  let x := harmonicSpacing k -
    ((1 : Q') - bondMovingDeltaRen 1 pMult (harmW k)) * harmonicSpacing (k + 1)
  have hbase := twoInvSq_spacing_le_harmU_spacing_defect k
  have hleft0 : (0 : Q') ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) * harmonicSpacing k :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) k))
      (Q'.le_of_lt (harmonicSpacing_pos k))
  have hux0 : (0 : Q') ≤ harmU k * x := by
    exact Q'.le_trans' _ _ _ hleft0 (by simpa [x] using hbase)
  have hx0 : (0 : Q') ≤ x := by
    have hz : harmU k * (0 : Q') ≤ harmU k * x :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (harmU k))) hux0
    exact Q'.le_of_mul_le_mul_left hz (harmU_pos k)
  have hfloor : harmU k ≤ harmonicMass k := by
    by_cases hk0 : k = 0
    · subst k
      decide
    · exact harmonic_unit_le_mass (Nat.one_le_iff_ne_zero.mpr hk0)
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ x hfloor hx0
  exact Q'.le_trans' _ _ _ hbase (by simpa [x] using hmul)

/-- Cross-multiplied quotient algebra used by the physical margin step. -/
private theorem margin_step_of_absorption
    (M0 M1 s0 s1 r e : Q') (hs0 : (0 : Q') < s0) (hs1 : (0 : Q') < s1)
    (hdrop : M0 - M1 ≤ e)
    (habs : e * s0 ≤ M0 * (s0 - r * s1)) :
    r * Q'.divPos M0 s0 hs0 ≤ Q'.divPos M1 s1 hs1 := by
  let A := M0 * s0
  let B := M1 * s0
  let C := (r * M0) * s1
  have hscaled : (M0 - M1) * s0 ≤ e * s0 :=
    Q'.mul_le_mul_of_nonneg_right _ _ s0 hdrop (Q'.le_of_lt hs0)
  have hraw : (M0 - M1) * s0 ≤ M0 * (s0 - r * s1) :=
    Q'.le_trans' _ _ _ hscaled habs
  have hleft : (M0 - M1) * s0 ≈ A + -B := by
    dsimp only [A, B]
    change (M0 + -M1) * s0 ≈ M0 * s0 + -(M1 * s0)
    absorption_ring_qeqv
  have hright : M0 * (s0 - r * s1) ≈ A + -C := by
    dsimp only [A, C]
    change M0 * (s0 + -(r * s1)) ≈ M0 * s0 + -((r * M0) * s1)
    absorption_ring_qeqv
  have hAC : A + -B ≤ A + -C :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hright))
  have hadd := Q'.add_le_add_left (-A) _ _ hAC
  have hcancel (X : Q') : -A + (A + -X) ≈ -X := by
    refine Q'.eqv_trans _ ((-A + A) + -X) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-A) A (-X))) ?_
    have hzero : -A + A ≈ (0 : Q') := by
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (-A) A)
        (Q'.add_neg_self_eqv A)
    exact Q'.eqv_trans _ ((0 : Q') + -X) _
      (Q'.add_eqv_congr_right _ _ (-X) hzero)
      (YMGap.Constructive.QPoly.q_zero_add_eqv (-X))
  have hcancelB : -A + (A + -B) ≈ -B := hcancel B
  have hcancelC : -A + (A + -C) ≈ -C := hcancel C
  have hneg : -B ≤ -C :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancelB)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hcancelC))
  have hn := Q'.neg_le_neg hneg
  have hcross : C ≤ B :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv C))
      (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.neg_neg_eqv B)))
  have hquot := FusionMarginMono.divPos_le_divPos_of_cross
    (r * M0) s0 M1 s1 hs0 hs1 (by simpa [B, C] using hcross)
  have hmul : r * Q'.divPos M0 s0 hs0 ≈
      Q'.divPos (r * M0) s0 hs0 := by
    unfold Q'.divPos
    exact Q'.eqv_symm (Q'.mul_assoc_eqv r M0 (Q'.recipPos s0 hs0))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hmul) hquot

/-- A coefficient-two additive lattice-mass drift therefore implies the exact
multiplicative step for the dimensionless harmonic margin. -/
theorem harmonicTrueMargin_singleStep_of_mass_drop (k : Nat)
    (hdrop : harmonicMass k - harmonicMass (k + 1) ≤
      Q'.ofNat 2 * invSqTerm 2 (by decide) k) :
    ((1 : Q') - bondMovingDeltaRen 1 pMult (harmW k)) *
        harmonicTrueMargin k ≤ harmonicTrueMargin (k + 1) := by
  unfold harmonicTrueMargin
  exact margin_step_of_absorption
    (harmonicMass k) (harmonicMass (k + 1))
    (harmonicSpacing k) (harmonicSpacing (k + 1))
    ((1 : Q') - bondMovingDeltaRen 1 pMult (harmW k))
    (Q'.ofNat 2 * invSqTerm 2 (by decide) k)
    (harmonicSpacing_pos k) (harmonicSpacing_pos (k + 1)) hdrop
    (harmonic_spacing_defect_absorbs_twoInvSq k)

#print axioms twoInvSq_spacing_le_harmU_spacing_defect
#print axioms harmonic_spacing_defect_absorbs_twoInvSq
#print axioms harmonicTrueMargin_singleStep_of_mass_drop

end YMGap.Continuum.HarmonicTrueMarginAbsorption
