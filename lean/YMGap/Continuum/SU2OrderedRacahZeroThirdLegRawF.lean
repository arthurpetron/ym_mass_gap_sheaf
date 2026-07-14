/-
# Unsquared ordered F coefficient on the zero-third-leg family

When the third tensor factor has degree zero, the right inner contraction is
the identity and both bracketings reduce to the same projected transvectant of
the first two factors.  This supplies a second arbitrary-label boundary family
for the raw ordered associator, independent of the zero-first-leg family.
-/

import YMGap.Continuum.SU2OrderedRacahZeroLegRawF
import YMGap.Continuum.SU2FixedLeftRightZeroLegInverseBridge
import YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

namespace YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.TreeGraphBoundProgress
open YMGap.Continuum.SixJKernel
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection
open YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates
open YMGap.Continuum.SU2GeneralHahnGlobalCoordinateBases
open YMGap.Continuum.SU2GeneralHahnLeftNestedCoordinateBases
open YMGap.Continuum.SU2GeneralHahnDirectRightNestedCoordinateBases
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SU2OrderedRacahZeroLegKernel
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence
open YMGap.Continuum.SU2FixedLeftRightAssociatorSchur
open YMGap.Continuum.SU2FixedLeftRightOrderedAssociatorBridge
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantAllLabelGNSIsometryCompleted

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.add_zero, Int.zero_add]; ac_rfl))

def zeroThirdD (a b p : Nat) : Nat := a + b - 2 * p

def zeroThirdLeftFamily (a b p : Nat) (hp : p ≤ min a b) :
    FixedLeftCGChannel a b 0 (zeroThirdD a b p) where
  k := p
  k_le := hp
  r := 0
  r_le := by simp
  degree_eq := by simp [zeroThirdD]

def zeroThirdRightFamily (a b p : Nat) (hp : p ≤ min a b) :
    FixedRightCGChannel a b 0 (zeroThirdD a b p) where
  p := 0
  p_le := by simp
  r := p
  r_le := by
    apply Nat.le_min.mpr
    exact ⟨(Nat.le_min.mp hp).1, (Nat.le_min.mp hp).2⟩
  degree_eq := by simp [zeroThirdD]

/-! ## Degree-zero identities on the right -/

theorem transvect_zero_right_project (n : Nat) (x : BForm2)
    (s : Nat) (hs : s ≤ n) :
    transvect n 0 0 (rectProject n 0 x) s ≈ x s 0 := by
  unfold transvect OmegaK diag
  have hsum :
      finSum (fun i => rectProject n 0 x i (s - i)) (s + 1) ≈
        finSum (fun i => if i = s then x s 0 else 0) (s + 1) := by
    apply finSum_eqv_congr_lt
    intro i hiRange
    by_cases hi : i = s
    · subst i
      simp only [if_pos, Nat.sub_self]
      exact rectProject_apply_physical n 0 x s 0 hs (Nat.zero_le 0)
    · rw [if_neg hi]
      have his : i < s := by omega
      have hpos : 0 < s - i := Nat.sub_pos_of_lt his
      exact rectProject_zero_outside n 0 x i (s - i) (Or.inr hpos)
  exact Q'.eqv_trans _ _ _ hsum
    (finSum_onehot_value (x s 0) (s + 1) s (by omega))

theorem lastPairOutput_zero_right (b : Nat) (x : TriForm)
    (i s : Nat) (hs : s ≤ b) :
    lastPairOutput b 0 x 0 i s ≈ x i s 0 := by
  simpa only [lastPairOutput, rightTriSlice] using
    transvect_zero_right_project b (rightTriSlice x i) s hs

/-! ## Equality of the two nested coordinate functionals -/

theorem zero_third_coordinate_functionals_at (a b p : Nat)
    (hp : p ≤ min a b) (x : TriForm) (s : Nat)
    (hs : s ≤ zeroThirdD a b p) :
    leftNestedCoordinates a b 0 x
        (fixedLeftNestedChannel (zeroThirdLeftFamily a b p hp) s hs) ≈
      directRightNestedCoordinates a b 0 x
        (fixedRightNestedChannel (zeroThirdRightFamily a b p hp) s hs) := by
  let q : PhysicalCGChannel a b :=
    { k := p
      k_le := hp
      s := s
      s_le := by
        have h := Nat.le_min.mp hp
        unfold zeroThirdD at hs
        exact hs }
  have hleftOuter := transvect_zero_right_project (a + b - 2 * p)
    (firstPairOutput a b x p) s (by simpa [zeroThirdD] using hs)
  have hrightTensor : PhysicalRectangleEqv a b
      (lastPairOutput b 0 x 0) (fun i s => x i s 0) := by
    intro i s hi hs
    exact lastPairOutput_zero_right b x i s hs
  have hright := globalTransvectCoordinates_congr a b
    (lastPairOutput b 0 x 0) (fun i s => x i s 0)
    hrightTensor q
  change globalTransvectCoordinates (a + b - 2 * p) 0
      (firstPairOutput a b x p) _ ≈
    globalTransvectCoordinates a b (lastPairOutput b 0 x 0) _
  refine Q'.eqv_trans _ (firstPairOutput a b x p s 0) _ ?_ ?_
  · simpa [globalTransvectCoordinates, fixedLeftNestedChannel,
      zeroThirdLeftFamily] using hleftOuter
  · simpa [globalTransvectCoordinates, q, firstPairOutput, triSlice,
      fixedRightNestedChannel, zeroThirdRightFamily] using
      (Q'.eqv_symm hright)

theorem zero_third_coordinate_functionals (a b p : Nat)
    (hp : p ≤ min a b) (x : TriForm) :
    leftNestedCoordinates a b 0 x
        (fixedLeftNestedChannel (zeroThirdLeftFamily a b p hp) 0 (by omega)) ≈
      directRightNestedCoordinates a b 0 x
        (fixedRightNestedChannel (zeroThirdRightFamily a b p hp) 0 (by omega)) :=
  zero_third_coordinate_functionals_at a b p hp x 0 (Nat.zero_le _)

/-! ## The unsquared all-label unit entry -/

theorem zero_third_fixedOrderedFCoefficient_eq_one (a b p : Nat)
    (hp : p ≤ min a b) :
    fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp) ≈ 1 := by
  let qL := zeroThirdLeftFamily a b p hp
  let qR := zeroThirdRightFamily a b p hp
  let x := leftNestedReconstruct a b 0 (fixedLeftCoordinateDelta qL)
  have hF := fixedOrderedFCoefficient_eq_directCoordinate qL qR
  have hfun := zero_third_coordinate_functionals a b p hp x
  have hleft := leftNestedCoordinates_reconstruct a b 0
    (fixedLeftCoordinateDelta qL)
    (fixedLeftNestedChannel qL 0 (by omega))
  refine Q'.eqv_trans _ _ _ hF ?_
  refine Q'.eqv_trans _
    (leftNestedCoordinates a b 0 x
      (fixedLeftNestedChannel qL 0 (by omega))) _
      (Q'.eqv_symm hfun) ?_
  exact Q'.eqv_trans _ _ _ hleft (by
    unfold fixedLeftCoordinateDelta fixedLeftNestedChannel qL
    rw [if_pos]
    · exact Q'.eqv_refl 1
    · exact ⟨rfl, rfl, rfl⟩)

/-! ## The faithful factorial kernel on the same family -/

def zeroThirdT (a b p : Nat) : Nat := a + b - p

theorem zero_third_valid6 (a b p : Nat) (hp : p ≤ min a b) :
    valid6 a b 0 (zeroThirdD a b p) (zeroThirdD a b p) b = true := by
  have hp' := Nat.le_min.mp hp
  have habd : fusionOK a b (zeroThirdD a b p) = true :=
    (fusionOK_iff_ladder a b (zeroThirdD a b p)).2
      ⟨p, hp'.1, hp'.2, by unfold zeroThirdD; omega⟩
  have hadb : fusionOK a (zeroThirdD a b p) b = true :=
    (fusionOK_iff_ladder a (zeroThirdD a b p) b).2
      ⟨a - p, by omega, by unfold zeroThirdD; omega,
        by unfold zeroThirdD; omega⟩
  have h0bb : fusionOK 0 b b = true :=
    (fusionOK_iff_ladder 0 b b).2 ⟨0, by omega, by omega, by omega⟩
  have h0dd : fusionOK 0 (zeroThirdD a b p) (zeroThirdD a b p) = true :=
    (fusionOK_iff_ladder 0 (zeroThirdD a b p) (zeroThirdD a b p)).2
      ⟨0, by omega, by omega, by omega⟩
  unfold valid6
  simp only [habd, hadb, h0bb, h0dd, Bool.true_and]

private theorem zero_third_racah_parameters (a b p : Nat)
    (hp : p ≤ min a b) :
    (a + b + zeroThirdD a b p) / 2 = zeroThirdT a b p ∧
    (a + zeroThirdD a b p + b) / 2 = zeroThirdT a b p ∧
    (0 + b + b) / 2 = b ∧
    (0 + zeroThirdD a b p + zeroThirdD a b p) / 2 =
      zeroThirdD a b p ∧
    (a + b + 0 + zeroThirdD a b p) / 2 = zeroThirdT a b p ∧
    (b + zeroThirdD a b p + zeroThirdD a b p + b) / 2 =
      b + zeroThirdD a b p ∧
    (a + zeroThirdD a b p + 0 + b) / 2 = zeroThirdT a b p := by
  have hp' := Nat.le_min.mp hp
  unfold zeroThirdD zeroThirdT
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

private theorem zero_third_tGuard_at_T (a b p : Nat)
    (hp : p ≤ min a b) :
    tGuard (zeroThirdT a b p) (zeroThirdT a b p) b
      (zeroThirdD a b p) (zeroThirdT a b p)
      (b + zeroThirdD a b p) (zeroThirdT a b p)
      (zeroThirdT a b p) = true := by
  have hp' := Nat.le_min.mp hp
  unfold tGuard zeroThirdD zeroThirdT
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  refine ⟨?_, by omega⟩
  exact ⟨by omega, by omega⟩

theorem zero_third_racahSummand_onehot (a b p t : Nat)
    (hp : p ≤ min a b) :
    racahSummand
      ((a + b + zeroThirdD a b p) / 2)
      ((a + zeroThirdD a b p + b) / 2)
      ((0 + b + b) / 2)
      ((0 + zeroThirdD a b p + zeroThirdD a b p) / 2)
      ((a + b + 0 + zeroThirdD a b p) / 2)
      ((b + zeroThirdD a b p + zeroThirdD a b p + b) / 2)
      ((a + zeroThirdD a b p + 0 + b) / 2) t ≈
      (if t = zeroThirdT a b p then
        zeroLegRacahAmplitude b a p else 0) := by
  have hpar := zero_third_racah_parameters a b p hp
  rw [hpar.1, hpar.2.1, hpar.2.2.1, hpar.2.2.2.1,
    hpar.2.2.2.2.1, hpar.2.2.2.2.2.1, hpar.2.2.2.2.2.2]
  by_cases ht : t = zeroThirdT a b p
  · subst t
    rw [if_pos rfl]
    unfold racahSummand
    rw [if_pos (zero_third_tGuard_at_T a b p hp)]
    have h1 : zeroThirdT a b p - b = a - p := by
      unfold zeroThirdT
      omega
    have h2 : zeroThirdT a b p - zeroThirdD a b p = p := by
      unfold zeroThirdT zeroThirdD
      omega
    have h3 : b + zeroThirdD a b p - zeroThirdT a b p = b - p := by
      unfold zeroThirdT zeroThirdD
      omega
    have hT : zeroThirdT a b p = zeroLegT b a p := by
      unfold zeroThirdT zeroLegT
      omega
    unfold zeroLegRacahAmplitude zeroLegDen sevenFacts
    simp only [Nat.sub_self, fact, Nat.mul_one, Nat.one_mul]
    rw [h1, h2, h3, hT]
    exact Q'.eqv_refl _
  · rw [if_neg ht]
    unfold racahSummand
    rw [if_neg]
    · exact Q'.eqv_refl 0
    · intro hg
      unfold tGuard at hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      exact ht (by omega)

theorem zero_third_racahSum_eq_amplitude (a b p : Nat)
    (hp : p ≤ min a b) :
    racahSum a b (zeroThirdD a b p) 0 (zeroThirdD a b p) b ≈
      zeroLegRacahAmplitude b a p := by
  unfold racahSum
  have hcongr := finSum_eqv_congr _ _
    (fun t => zero_third_racahSummand_onehot a b p t hp)
    ((a + b + zeroThirdD a b p + 0 + zeroThirdD a b p + b) / 2 + 1)
  have hinside : zeroThirdT a b p <
      (a + b + zeroThirdD a b p + 0 + zeroThirdD a b p + b) / 2 + 1 := by
    have hp' := Nat.le_min.mp hp
    unfold zeroThirdT zeroThirdD
    omega
  exact Q'.eqv_trans _ _ _ hcongr
    (finSum_onehot_value (zeroLegRacahAmplitude b a p)
      ((a + b + zeroThirdD a b p + 0 + zeroThirdD a b p + b) / 2 + 1)
      (zeroThirdT a b p) hinside)

/-- **Symbolic zero-third-leg unit kernel.**  It is transported to the already
closed zero-first-leg cancellation only after deriving the correctly permuted
signed Racah sum, so no tetrahedral symmetry is assumed. -/
theorem zero_third_racahKernel_eq_one (a b p : Nat)
    (hp : p ≤ min a b) :
    racahKernel6 a b 0 (zeroThirdD a b p)
      (zeroThirdD a b p) b ≈ 1 := by
  have hsum := zero_third_racahSum_eq_amplitude a b p hp
  have hp' := Nat.le_min.mp hp
  have hpSwap : p ≤ min b a := Nat.le_min.mpr ⟨hp'.2, hp'.1⟩
  have hsum0 := zero_leg_racahSum_eq_amplitude b a p hpSwap
  have hD : zeroThirdD a b p = zeroLegD b a p := by
    unfold zeroThirdD zeroLegD
    omega
  have hS : racahSum a b (zeroThirdD a b p) 0
        (zeroThirdD a b p) b ≈
      racahSum 0 b b a (zeroLegD b a p) (zeroLegD b a p) := by
    exact Q'.eqv_trans _ _ _ hsum (Q'.eqv_symm hsum0)
  have hprod :
      racahSum a b (zeroThirdD a b p) 0 (zeroThirdD a b p) b *
          racahSum a b (zeroThirdD a b p) 0 (zeroThirdD a b p) b ≈
        racahSum 0 b b a (zeroLegD b a p) (zeroLegD b a p) *
          racahSum 0 b b a (zeroLegD b a p) (zeroLegD b a p) := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hS)
      (Q'.mul_eqv_congr_left _ _ _ hS)
  rw [hD] at hprod
  have hkernel : racahKernel6 a b 0 (zeroThirdD a b p)
        (zeroThirdD a b p) b ≈
      racahKernel6 0 b a (zeroLegD b a p) b (zeroLegD b a p) := by
    unfold racahKernel6
    rw [if_pos (zero_third_valid6 a b p hp),
      if_pos (zero_leg_valid6 b a p hpSwap)]
    rw [hD]
    refine Q'.eqv_trans _
      (Q'.ofNat (dimRep (zeroLegD b a p)) * Q'.ofNat (dimRep b) *
        (triSq a b (zeroLegD b a p) * triSq a (zeroLegD b a p) b *
          triSq 0 b b * triSq 0 (zeroLegD b a p) (zeroLegD b a p)) *
        (racahSum 0 b b a (zeroLegD b a p) (zeroLegD b a p) *
          racahSum 0 b b a (zeroLegD b a p) (zeroLegD b a p))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hprod
    · ring_qeqv
  exact Q'.eqv_trans _ _ _ hkernel
    (zero_leg_racahKernel_eq_one b a p hpSwap)

/-! ## Physical map, Gram, and corrected normalization bridges -/

theorem zero_third_triMaps_eqv (a b p : Nat)
    (hp : p ≤ min a b) :
    TriMapEqv a b 0 (zeroThirdD a b p)
      (triLeft a b 0 (zeroThirdD a b p) (zeroThirdD a b p))
      (triRight a b 0 (zeroThirdD a b p) b) := by
  intro i hi j hj l hl s hs
  have hsd : s ≤ zeroThirdD a b p := by omega
  let qL := zeroThirdLeftFamily a b p hp
  let qR := zeroThirdRightFamily a b p hp
  let x := pureTri (mono i) (mono j) (mono l)
  have hcoord := zero_third_coordinate_functionals_at a b p hp x s hsd
  have hcoord' : fixedLeftAnalysis qL x s ≈ fixedRightAnalysis qR x s := by
    simpa only [fixedLeftAnalysis, fixedRightAnalysis, dif_pos hsd,
      qL, qR] using hcoord
  have hleft := fixedLeftAnalysis_pure_monomial_eq_triLeft qL
    i j l (by omega) (by omega) (by omega) s hs
  have hright := fixedRightAnalysis_pure_monomial_eq_triRight qR
    i j l (by omega) (by omega) (by omega) s hs
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hcoord' hright)

theorem zero_third_channel_weights_eqv (a b p : Nat)
    (hp : p ≤ min a b) :
    triLeftChannelWeight a b 0 (zeroThirdD a b p) (zeroThirdD a b p) ≈
      triRightChannelWeight a b 0 (zeroThirdD a b p) b := by
  unfold triLeftChannelWeight triRightChannelWeight
  exact triMapInner_diagonal_congr_all_labels a b 0 (zeroThirdD a b p)
    (triLeft a b 0 (zeroThirdD a b p) (zeroThirdD a b p))
    (triRight a b 0 (zeroThirdD a b p) b)
    (zero_third_triMaps_eqv a b p hp)

theorem zero_third_gramWeightedRacahBridge (a b p : Nat)
    (hp : p ≤ min a b) :
    GramWeightedRacahBridgeAt (zeroThirdLeftFamily a b p hp)
      (zeroThirdRightFamily a b p hp) := by
  unfold GramWeightedRacahBridgeAt
  change triRightChannelWeight a b 0 (zeroThirdD a b p) b *
      racahKernel6 a b 0 (zeroThirdD a b p) (zeroThirdD a b p) b ≈
    triLeftChannelWeight a b 0 (zeroThirdD a b p) (zeroThirdD a b p) *
      (fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp) *
       fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp))
  have hW := zero_third_channel_weights_eqv a b p hp
  have hP := zero_third_racahKernel_eq_one a b p hp
  have hF := zero_third_fixedOrderedFCoefficient_eq_one a b p hp
  have hleft : triRightChannelWeight a b 0 (zeroThirdD a b p) b *
      racahKernel6 a b 0 (zeroThirdD a b p) (zeroThirdD a b p) b ≈
      triRightChannelWeight a b 0 (zeroThirdD a b p) b :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hP)
      (Q'.mul_one_eqv _)
  have hFsq :
      fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
          (zeroThirdRightFamily a b p hp) *
        fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
          (zeroThirdRightFamily a b p hp) ≈ 1 := by
    exact Q'.eqv_trans _ (1 *
      fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp)) _
      (Q'.mul_eqv_congr_right _ _ _ hF)
      (Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _ hF) (Q'.one_mul_eqv 1))
  have hright :
      triLeftChannelWeight a b 0 (zeroThirdD a b p) (zeroThirdD a b p) *
        (fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
            (zeroThirdRightFamily a b p hp) *
          fixedOrderedFCoefficient (zeroThirdLeftFamily a b p hp)
            (zeroThirdRightFamily a b p hp)) ≈
      triLeftChannelWeight a b 0 (zeroThirdD a b p) (zeroThirdD a b p) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hFsq)
      (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hW) (Q'.eqv_symm hright))

theorem zero_third_fixedLeftRightDiagonalCoeff_eq_one (a b p : Nat)
    (hp : p ≤ min a b) :
    fixedLeftRightDiagonalCoeff (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp) 0 ≈ 1 := by
  let qL := zeroThirdLeftFamily a b p hp
  let qR := zeroThirdRightFamily a b p hp
  let x := fixedRightSection qR (mono 0)
  have hfun := zero_third_coordinate_functionals a b p hp x
  have hright := directRightNestedCoordinates_reconstruct a b 0
    (fixedRightSectionData qR (mono 0))
    (fixedRightNestedChannel qR 0 (by omega))
  have hone : fixedRightSectionData qR (mono 0)
      (fixedRightNestedChannel qR 0 (by omega)) ≈ 1 := by
    unfold fixedRightSectionData fixedRightNestedChannel qR
    rw [dif_pos]
    · unfold mono
      rw [if_pos rfl]
      exact Q'.eqv_refl 1
    · exact ⟨rfl, rfl⟩
  unfold fixedLeftRightDiagonalCoeff fixedLeftAnalysis
  rw [dif_pos (by omega : 0 ≤ zeroThirdD a b p)]
  refine Q'.eqv_trans _ _ _ hfun ?_
  exact Q'.eqv_trans _ _ _
    (by simpa only [x, fixedRightSection] using hright) hone

theorem zero_third_fixedLeftRightRawKernel_eq_one (a b p : Nat)
    (hp : p ≤ min a b) :
    fixedLeftRightRawKernel (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp) ≈ 1 := by
  have h := zero_third_fixedLeftRightDiagonalCoeff_eq_one a b p hp
  unfold fixedLeftRightRawKernel
  exact Q'.eqv_trans _
    (1 * fixedLeftRightDiagonalCoeff (zeroThirdLeftFamily a b p hp)
      (zeroThirdRightFamily a b p hp) 0) _
    (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.eqv_trans _ (1 * 1) _
      (Q'.mul_eqv_congr_left 1 _ _ h) (Q'.one_mul_eqv 1))

theorem zero_third_inverseSchurGramRacahBridge (a b p : Nat)
    (hp : p ≤ min a b) :
    InverseSchurGramRacahBridgeAt (zeroThirdLeftFamily a b p hp)
      (zeroThirdRightFamily a b p hp) := by
  unfold InverseSchurGramRacahBridgeAt
  change triLeftChannelWeight a b 0 (zeroThirdD a b p) (zeroThirdD a b p) *
      racahKernel6 a b 0 (zeroThirdD a b p) (zeroThirdD a b p) b ≈
    triRightChannelWeight a b 0 (zeroThirdD a b p) b *
      fixedLeftRightRawKernel (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp)
  have hW := zero_third_channel_weights_eqv a b p hp
  have hP := zero_third_racahKernel_eq_one a b p hp
  have hK := zero_third_fixedLeftRightRawKernel_eq_one a b p hp
  have hleft : triLeftChannelWeight a b 0 (zeroThirdD a b p)
        (zeroThirdD a b p) *
      racahKernel6 a b 0 (zeroThirdD a b p) (zeroThirdD a b p) b ≈
      triLeftChannelWeight a b 0 (zeroThirdD a b p) (zeroThirdD a b p) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hP)
      (Q'.mul_one_eqv _)
  have hright : triRightChannelWeight a b 0 (zeroThirdD a b p) b *
      fixedLeftRightRawKernel (zeroThirdLeftFamily a b p hp)
        (zeroThirdRightFamily a b p hp) ≈
      triRightChannelWeight a b 0 (zeroThirdD a b p) b :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hK)
      (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hW (Q'.eqv_symm hright))

end YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF

#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.transvect_zero_right_project
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.lastPairOutput_zero_right
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_coordinate_functionals_at
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_coordinate_functionals
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_fixedOrderedFCoefficient_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_valid6
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_racahSummand_onehot
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_racahSum_eq_amplitude
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_racahKernel_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_triMaps_eqv
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_channel_weights_eqv
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_gramWeightedRacahBridge
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_fixedLeftRightDiagonalCoeff_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_fixedLeftRightRawKernel_eq_one
#print axioms YMGap.Continuum.SU2OrderedRacahZeroThirdLegRawF.zero_third_inverseSchurGramRacahBridge
