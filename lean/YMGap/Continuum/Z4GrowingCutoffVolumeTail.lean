/-
# An explicit growing-cutoff tail that beats four-dimensional box volume

At fixed character cutoff the first omitted positive heat-kernel coefficient,
paid independently on every plaquette, diverges with volume.  Here the cutoff
is allowed to grow with both the box and the cofinal stage.  The exact schedule

`K(stage) = plaquetteEdgeCount(stage + 2) + stage + 2`

absorbs the plaquette multiplicity and the representation dimension into two
disjoint blocks of the quadratic Casimir exponent.  The remaining block is at
least `stage`, giving the explicit constructive bound

`volume * coeffW coupling (K(stage)+1) ≤ (1/2)^stage`.

The argument then resums every finite omitted window uniformly in its depth.
It also pays the extra representation dimension from the elementary character
supremum bound, obtaining the same explicit modulus for the actual local
character-series envelope.  This remains an additive, unnormalised estimate;
transport through the full Haar expansion and partition-function ratios is the
next step.
-/

import YMGap.Continuum.Z4UnitCubeGrowingCutoffCofinal
import YMGap.Continuum.Z4FixedCutoffNaiveTailFence
import YMGap.Continuum.PinnedCluster
import YMGap.Constructive.HalfPow
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.Z4GrowingCutoffVolumeTail

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedCutoffNaiveTailFence
open YMGap.Continuum.SU2PeterWeylWilsonBlock

local infix:50 " ≈ " => Q'.eqv

private theorem mul_rearrange (a b c d e : Q') :
    (a * b) * (c * (d * e)) ≈ c * ((a * d) * (b * e)) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem mul_three_rearrange (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem mul_four_cross (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * d) * (b * c) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem add_self_eqv_two_mul (a : Q') :
    a + a ≈ Q'.ofNat 2 * a :=
  Q'.eqv_symm (ExpNeg.two_mul_eqv a)

private theorem mul_character_rearrange (v d s a b c : Q') :
    v * ((d * d) * (s * (a * (b * c)))) ≈
      s * ((v * a) * ((d * b) * (d * c))) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

theorem qpow_coupling_eqv_halfPow : ∀ n : Nat,
    qpow coupling n ≈ HalfPow.half ^ n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      change qpow coupling n * coupling ≈
        HalfPow.half * (HalfPow.half ^ n)
      refine Q'.eqv_trans _ ((HalfPow.half ^ n) * HalfPow.half) _ ?_ ?_
      · refine Q'.eqv_trans _ (HalfPow.half ^ n * coupling) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ (qpow_coupling_eqv_halfPow n)
        · exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl _)
      · exact Q'.mul_comm_eqv _ _

theorem qpow_coupling_le_invSucc (n : Nat) :
    qpow coupling n ≤ Q'.invSucc n :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qpow_coupling_eqv_halfPow n))
    (HalfPow.pow_half_le_invSucc n)

/-- Dyadic powers decrease with their exponent, routed through the existing
heat-kernel power monotonicity. -/
theorem halfPow_antitone {m n : Nat} (hmn : m ≤ n) :
    HalfPow.half ^ n ≤ HalfPow.half ^ m := by
  refine Q'.le_trans' _ (qpow coupling n) _ ?_ ?_
  · exact Q'.le_of_eqv (Q'.eqv_symm (qpow_coupling_eqv_halfPow n))
  refine Q'.le_trans' _ (qpow coupling m) _ ?_ ?_
  · exact HeatKernelRGStep.qpow_antitone (by decide) (by decide) m n hmn
  · exact Q'.le_of_eqv (qpow_coupling_eqv_halfPow m)

/-- The leading factor two consumes one dyadic power exactly. -/
theorem two_halfPow_succ_eqv (n : Nat) :
    Q'.ofNat 2 * (HalfPow.half ^ (n + 1)) ≈ HalfPow.half ^ n := by
  change Q'.ofNat 2 * (HalfPow.half * (HalfPow.half ^ n)) ≈
    HalfPow.half ^ n
  refine Q'.eqv_trans _ ((Q'.ofNat 2 * HalfPow.half) *
    (HalfPow.half ^ n)) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  refine Q'.eqv_trans _ ((1 : Q') * (HalfPow.half ^ n)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  · exact Q'.one_mul_eqv _

private theorem twoPow_halfPow_eqv_one : ∀ n : Nat,
    Q'.ofNat (2 ^ n) * (HalfPow.half ^ n) ≈ (1 : Q')
  | 0 => by
      rw [Q'.pow_zero]
      exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) (by decide)
  | n + 1 => by
      have ih := twoPow_halfPow_eqv_one n
      rw [Nat.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _
        ((Q'.ofNat (2 ^ n) * HalfPow.half ^ n) *
          (Q'.ofNat 2 * HalfPow.half)) _ ?_ ?_
      · refine Q'.eqv_trans _
          ((Q'.ofNat (2 ^ n) * Q'.ofNat 2) *
            (HalfPow.half * HalfPow.half ^ n)) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv (2 ^ n) 2))
        · exact mul_four_cross _ _ _ _
      · refine Q'.eqv_trans _ ((1 : Q') * (1 : Q')) _
          (Q'.eqv_trans _ ((1 : Q') * (Q'.ofNat 2 * HalfPow.half)) _
            (Q'.mul_eqv_congr_right _ _ _ ih)
            (Q'.mul_eqv_congr_left 1 _ _ (by decide))) ?_
        exact Q'.one_mul_eqv 1

/-- A dyadic product-growth factor is cancelled exactly by the matching block
of the retained character-tail reserve. -/
theorem twoPow_halfPow_add_eqv (n r : Nat) :
    Q'.ofNat (2 ^ n) * (HalfPow.half ^ (n + r)) ≈
      HalfPow.half ^ r := by
  have hsplit : HalfPow.half ^ (n + r) ≈
      HalfPow.half ^ n * HalfPow.half ^ r :=
    Q'.pow_add_eqv HalfPow.half n r
  refine Q'.eqv_trans _
    (Q'.ofNat (2 ^ n) *
      ((HalfPow.half ^ n) * (HalfPow.half ^ r))) _
    (Q'.mul_eqv_congr_left _ _ _ hsplit) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (2 ^ n) * (HalfPow.half ^ n)) *
      (HalfPow.half ^ r)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((1 : Q') * (HalfPow.half ^ r)) _
    (Q'.mul_eqv_congr_right _ _ _ (twoPow_halfPow_eqv_one n)) ?_
  exact Q'.one_mul_eqv _

def volumeAbsorbingCutoff (stage : Nat) : Nat :=
  plaquetteEdgeCount (stage + 2) + stage + 2

def growingNaiveVolumeTail (stage : Nat) : Q' :=
  naiveFixedCutoffVolumeTail (volumeAbsorbingCutoff stage) (stage + 2)

theorem volumeAbsorbingCutoff_ge_two (stage : Nat) :
    2 ≤ volumeAbsorbingCutoff stage := by
  unfold volumeAbsorbingCutoff
  omega

theorem volumeAbsorbingCutoff_unbounded (bound : Nat) :
    ∃ stage, bound ≤ volumeAbsorbingCutoff stage := by
  refine ⟨bound, ?_⟩
  unfold volumeAbsorbingCutoff
  omega

private theorem volume_qpow_le_one (stage : Nat) :
    Q'.ofNat (plaquetteEdgeCount (stage + 2)) *
        qpow coupling (volumeAbsorbingCutoff stage) ≤ (1 : Q') := by
  let V := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  have hVK : V ≤ K + 1 := by
    dsimp only [V, K, volumeAbsorbingCutoff]
    omega
  have hnat : Q'.ofNat V ≤ Q'.ofNat (K + 1) := Q'.ofNat_le_ofNat hVK
  have hpow := qpow_coupling_le_invSucc K
  have hpow0 : (0 : Q') ≤ qpow coupling K :=
    qpow_nonneg coupling (by decide) K
  have hinv0 : (0 : Q') ≤ Q'.invSucc K := Q'.invSucc_nonneg K
  have hV0 : (0 : Q') ≤ Q'.ofNat V := ExpNeg.ofNat_nonneg' V
  have h1 : Q'.ofNat V * qpow coupling K ≤
    Q'.ofNat V * Q'.invSucc K :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow hV0
  have h2 : Q'.ofNat V * Q'.invSucc K ≤
      Q'.ofNat (K + 1) * Q'.invSucc K :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hnat hinv0
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h1 h2)
    (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc K))

private theorem dimension_qpow_le_one (K : Nat) :
    Q'.ofNat (K + 2) * qpow coupling (K + 1) ≤ (1 : Q') := by
  have hpow := qpow_coupling_le_invSucc (K + 1)
  have hnat0 : (0 : Q') ≤ Q'.ofNat (K + 2) := ExpNeg.ofNat_nonneg' _
  have h1 : Q'.ofNat (K + 2) * qpow coupling (K + 1) ≤
      Q'.ofNat (K + 2) * Q'.invSucc (K + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow hnat0
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_of_eqv (Q'.ofNat_succ_mul_invSucc (K + 1)))

theorem growingNaiveVolumeTail_le_halfPow (stage : Nat) :
    growingNaiveVolumeTail stage ≤ HalfPow.half ^ stage := by
  let V := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  have hstageK : stage ≤ K := by
    dsimp only [K, volumeAbsorbingCutoff]
    omega
  have hlin : stage + K + (K + 1) ≤ 3 * (K + 1) := by omega
  have hthree : 3 * (K + 1) ≤ (K + 1) * (K + 3) := by
    rw [Nat.mul_comm 3 (K + 1)]
    exact Nat.mul_le_mul_left (K + 1) (by omega)
  have hexp : stage + K + (K + 1) ≤ (K + 1) * (K + 3) :=
    Nat.le_trans hlin hthree
  have hanti : qpow coupling ((K + 1) * (K + 3)) ≤
      qpow coupling (stage + K + (K + 1)) :=
    HeatKernelRGStep.qpow_antitone (by decide) (by decide) _ _ hexp
  have hsplit : qpow coupling (stage + K + (K + 1)) ≈
      qpow coupling stage *
        (qpow coupling K * qpow coupling (K + 1)) := by
    refine Q'.eqv_trans _
      (qpow coupling (stage + K) *
        qpow coupling (K + 1)) _ ?_ ?_
    · exact HeatKernelRGStep.qpow_add coupling (stage + K) (K + 1)
    · refine Q'.eqv_trans _
        ((qpow coupling stage * qpow coupling K) *
          qpow coupling (K + 1)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (HeatKernelRGStep.qpow_add coupling stage K)
      · exact Q'.mul_assoc_eqv _ _ _
  have hV : Q'.ofNat V * qpow coupling K ≤ (1 : Q') := by
    dsimp only [V, K]
    exact volume_qpow_le_one stage
  have hD : Q'.ofNat (K + 2) * qpow coupling (K + 1) ≤ (1 : Q') :=
    dimension_qpow_le_one K
  have hstage0 : (0 : Q') ≤ qpow coupling stage :=
    qpow_nonneg coupling (by decide) _
  have hV0 : (0 : Q') ≤ Q'.ofNat V * qpow coupling K :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (qpow_nonneg coupling (by decide) _)
  have hD0 : (0 : Q') ≤ Q'.ofNat (K + 2) * qpow coupling (K + 1) :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (qpow_nonneg coupling (by decide) _)
  have hpair : (Q'.ofNat V * qpow coupling K) *
      (Q'.ofNat (K + 2) * qpow coupling (K + 1)) ≤ (1 : Q') := by
    have h1 := Q'.mul_le_mul_of_nonneg_left _ _ _ hD hV0
    have h2 : (Q'.ofNat V * qpow coupling K) * (1 : Q') ≤
        (1 : Q') * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hV (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h1 h2) (Q'.le_of_eqv (by decide))
  have hmain :
      (Q'.ofNat V * Q'.ofNat (K + 2)) *
        (qpow coupling stage *
          (qpow coupling K * qpow coupling (K + 1))) ≤
        qpow coupling stage := by
    have hrearr := mul_rearrange (Q'.ofNat V) (Q'.ofNat (K + 2))
      (qpow coupling stage) (qpow coupling K)
      (qpow coupling (K + 1))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr) ?_
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ hpair hstage0
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_one_eqv _))
  unfold growingNaiveVolumeTail naiveFixedCutoffVolumeTail firstOmittedCoefficient
  change Q'.ofNat V * (Q'.ofNat (K + 2) *
      qpow coupling ((K + 1) * (K + 3))) ≤ HalfPow.half ^ stage
  have houter : Q'.ofNat V * (Q'.ofNat (K + 2) *
      qpow coupling ((K + 1) * (K + 3))) ≤
      Q'.ofNat V * (Q'.ofNat (K + 2) *
        qpow coupling (stage + K + (K + 1))) := by
    have hdim0 : (0 : Q') ≤ Q'.ofNat (K + 2) := ExpNeg.ofNat_nonneg' _
    have hinner := Q'.mul_le_mul_of_nonneg_left _ _ _ hanti hdim0
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hinner (ExpNeg.ofNat_nonneg' _)
  have hassoc : Q'.ofNat V * (Q'.ofNat (K + 2) *
      qpow coupling (stage + K + (K + 1))) ≈
      (Q'.ofNat V * Q'.ofNat (K + 2)) *
        qpow coupling (stage + K + (K + 1)) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  refine Q'.le_trans' _ _ _ houter ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (ExpNeg.ofNat_nonneg' _))) ?_
  exact Q'.le_trans' _ _ _ hmain
    (Q'.le_of_eqv (qpow_coupling_eqv_halfPow stage))

/-! ## The complete finite omitted-character window -/

/-- A finite window of all heat-kernel character coefficients above `K`. -/
def omittedCoefficientWindow (K depth : Nat) : Q' :=
  finSum (fun offset => coeffW coupling (K + 1 + offset)) depth

/-- Every finite omitted-character window is at most twice its first term.
The bound is uniform in the window depth. -/
theorem omittedCoefficientWindow_le_two_head (K depth : Nat) :
    omittedCoefficientWindow K depth ≤
      Q'.ofNat 2 * firstOmittedCoefficient K := by
  let f : Nat → Q' := fun offset => coeffW coupling (K + 1 + offset)
  let head := coeffW coupling (K + 1)
  have hratio : Q'.ofNat 2 * qpow coupling 5 ≤ HalfPow.half :=
    PlaquetteActivity.ratio_le_half (w := coupling) (by decide) (by decide)
  have hratio0 : (0 : Q') ≤ Q'.ofNat 2 * qpow coupling 5 :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
      (qpow_nonneg coupling (by decide) _)
  have hf0 : f 0 ≤ head := by
    dsimp only [f, head]
    simpa only [Nat.add_zero] using (Q'.le_refl' (coeffW coupling (K + 1)))
  have hdom : ∀ offset, f (offset + 1) ≤ HalfPow.half * f offset := by
    intro offset
    have hidx : K + 1 + (offset + 1) = (K + 1 + offset) + 1 := by omega
    have hstep := PlaquetteActivity.coeffW_succ_ratio
      (w := coupling) (by decide) (by decide)
      (K + 1 + offset) (by omega)
    dsimp only [f]
    rw [hidx]
    refine Q'.le_trans' _ _ _ hstep ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hratio
      (coeffW_nonneg (by decide) _)
  have hhead0 : (0 : Q') ≤ head := coeffW_nonneg (by decide) _
  have hH0 : (0 : Q') ≤ Q'.ofNat 2 * head :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) hhead0
  have hhalfHead : HalfPow.half * (Q'.ofNat 2 * head) ≈ head := by
    refine Q'.eqv_trans _ ((HalfPow.half * Q'.ofNat 2) * head) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    · refine Q'.eqv_trans _ ((1 : Q') * head) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
      · exact Q'.one_mul_eqv _
  have hrec : head + HalfPow.half * (Q'.ofNat 2 * head) ≤
      Q'.ofNat 2 * head := by
    refine Q'.le_trans' _ (head + head) _ ?_ ?_
    · exact Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ hhalfHead)
    · exact Q'.le_of_eqv (add_self_eqv_two_mul head)
  have hsum := CharacterTail.geom_series_le f head HalfPow.half
    (Q'.ofNat 2 * head) HalfPow.half_nonneg hH0 hf0 hdom hrec depth
  unfold omittedCoefficientWindow firstOmittedCoefficient
  dsimp only [f, head] at hsum
  exact hsum

/-- The complete finite omitted-character window, paid independently on every
plaquette of the cofinal box. -/
def growingOmittedVolumeTail (stage depth : Nat) : Q' :=
  Q'.ofNat (plaquetteEdgeCount (stage + 2)) *
    omittedCoefficientWindow (volumeAbsorbingCutoff stage) depth

/-- The full omitted-character window has a depth-uniform dyadic volume bound.
Thus every finite truncation above the growing cutoff is controlled by the same
explicit quantity `2*(1/2)^stage`. -/
theorem growingOmittedVolumeTail_le_two_halfPow (stage depth : Nat) :
    growingOmittedVolumeTail stage depth ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  let V := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  have hwindow := omittedCoefficientWindow_le_two_head K depth
  have hV0 : (0 : Q') ≤ Q'.ofNat V := ExpNeg.ofNat_nonneg' _
  have hmul : Q'.ofNat V * omittedCoefficientWindow K depth ≤
      Q'.ofNat V * (Q'.ofNat 2 * firstOmittedCoefficient K) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hwindow hV0
  have hrearr : Q'.ofNat V * (Q'.ofNat 2 * firstOmittedCoefficient K) ≈
      Q'.ofNat 2 * (Q'.ofNat V * firstOmittedCoefficient K) :=
    mul_three_rearrange _ _ _
  have hfirst : Q'.ofNat V * firstOmittedCoefficient K ≤
      HalfPow.half ^ stage := by
    dsimp only [V, K]
    exact growingNaiveVolumeTail_le_halfPow stage
  unfold growingOmittedVolumeTail
  dsimp only [V, K] at hmul hrearr ⊢
  refine Q'.le_trans' _ _ _ hmul ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hfirst
    (ExpNeg.ofNat_nonneg' _)

/-- Explicit, depth-uniform modulus for the complete finite omitted-character
window.  For target `ε>0`, stage `ε.den+1` already suffices, independently of
how far the omitted window is extended. -/
theorem growingOmittedVolumeTail_modulus (ε : Q') (hε : (0 : Q') < ε) :
    ∀ stage, ε.den + 1 ≤ stage → ∀ depth,
      growingOmittedVolumeTail stage depth ≤ ε := by
  intro stage hstage depth
  have htail := growingOmittedVolumeTail_le_two_halfPow stage depth
  have hpow : HalfPow.half ^ stage ≤ HalfPow.half ^ (ε.den + 1) :=
    halfPow_antitone hstage
  have htwo : Q'.ofNat 2 * (HalfPow.half ^ stage) ≤
      Q'.ofNat 2 * (HalfPow.half ^ (ε.den + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (ExpNeg.ofNat_nonneg' _)
  refine Q'.le_trans' _ _ _ htail ?_
  refine Q'.le_trans' _ _ _ htwo ?_
  refine Q'.le_trans' _ (HalfPow.half ^ ε.den) _ ?_ ?_
  · exact Q'.le_of_eqv (two_halfPow_succ_eqv ε.den)
  · exact HalfPow.pow_half_le ε hε

/-! ## Dimension-weighted character-supremum tail -/

/-- The coefficient contribution after paying the elementary SU(2) character
bound `|χ_s| ≤ dim(s)`. -/
def characterSupTerm (s : Nat) : Q' :=
  dimQ s * coeffW coupling s

/-- Paying the character supremum turns the coefficient into the degree-two
Casimir tail term exactly. -/
theorem characterSupTerm_eqv_tailTerm (s : Nat) :
    characterSupTerm s ≈ tailTerm coupling 2 s := by
  unfold characterSupTerm coeffW tailTerm dimQ
  rw [Nat.pow_two]
  refine Q'.eqv_trans _
    ((Q'.ofNat (s + 1) * Q'.ofNat (s + 1)) * qpow coupling (c4 s)) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv (s + 1) (s + 1)))

/-- Complete finite character-supremum window above the external face cutoff. -/
def omittedCharacterSupWindow (K depth : Nat) : Q' :=
  tailWindow coupling 2 (K + 1) depth

private theorem degreeTwo_ratio_le_half (S : Nat) (hS : 1 ≤ S) :
    Q'.ofNat (2 ^ 2) * qpow coupling (2 * S + 3) ≤ HalfPow.half := by
  have hexp : 5 ≤ 2 * S + 3 := by omega
  have hp : qpow coupling (2 * S + 3) ≤ qpow coupling 5 :=
    HeatKernelRGStep.qpow_antitone (by decide) (by decide) 5 (2 * S + 3) hexp
  have hm : Q'.ofNat (2 ^ 2) * qpow coupling (2 * S + 3) ≤
      Q'.ofNat (2 ^ 2) * qpow coupling 5 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hp (ExpNeg.ofNat_nonneg' _)
  exact Q'.le_trans' _ _ _ hm (by decide)

/-- The full dimension-weighted omitted window is at most twice its first
term, uniformly in the window depth. -/
theorem omittedCharacterSupWindow_le_two_head (K depth : Nat) :
    omittedCharacterSupWindow K depth ≤
      Q'.ofNat 2 * tailTerm coupling 2 (K + 1) := by
  let f : Nat → Q' := fun offset => tailTerm coupling 2 (K + 1 + offset)
  let head := tailTerm coupling 2 (K + 1)
  have hratio := degreeTwo_ratio_le_half (K + 1) (by omega)
  have hf0 : f 0 ≤ head := by
    dsimp only [f, head]
    simpa only [Nat.add_zero] using (Q'.le_refl' (tailTerm coupling 2 (K + 1)))
  have hdom : ∀ offset, f (offset + 1) ≤ HalfPow.half * f offset := by
    intro offset
    have hr := tailTerm_ratio (w := coupling) (by decide) (by decide)
      2 (K + 1) offset
    have hterm0 : (0 : Q') ≤ tailTerm coupling 2 (K + 1 + offset) :=
      tailTerm_nonneg (by decide) _ _
    exact Q'.le_trans' _ _ _ hr
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hratio hterm0)
  have hhead0 : (0 : Q') ≤ head := tailTerm_nonneg (by decide) _ _
  have hH0 : (0 : Q') ≤ Q'.ofNat 2 * head :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) hhead0
  have hhalfHead : HalfPow.half * (Q'.ofNat 2 * head) ≈ head := by
    refine Q'.eqv_trans _ ((HalfPow.half * Q'.ofNat 2) * head) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    refine Q'.eqv_trans _ ((1 : Q') * head) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    · exact Q'.one_mul_eqv _
  have hrec : head + HalfPow.half * (Q'.ofNat 2 * head) ≤
      Q'.ofNat 2 * head := by
    refine Q'.le_trans' _ (head + head) _ ?_ ?_
    · exact Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ hhalfHead)
    · exact Q'.le_of_eqv (add_self_eqv_two_mul head)
  have hsum := CharacterTail.geom_series_le f head HalfPow.half
    (Q'.ofNat 2 * head) HalfPow.half_nonneg hH0 hf0 hdom hrec depth
  unfold omittedCharacterSupWindow tailWindow
  dsimp only [f, head] at hsum
  exact hsum

private theorem growingCharacterSupHead_le_halfPow (stage : Nat) :
    Q'.ofNat (plaquetteEdgeCount (stage + 2)) *
        tailTerm coupling 2 (volumeAbsorbingCutoff stage + 1) ≤
      HalfPow.half ^ (stage + plaquetteEdgeCount (stage + 2)) := by
  let V := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  let D := Q'.ofNat (K + 2)
  let R := stage + V
  have hK1 : 1 ≤ K := by
    dsimp only [K, volumeAbsorbingCutoff]
    omega
  have hstageK : stage ≤ K := by
    dsimp only [K, volumeAbsorbingCutoff]
    omega
  have hlin : R + K + (K + 1) + (K + 1) ≤ 4 * (K + 1) := by
    dsimp only [R, K, V, volumeAbsorbingCutoff]
    omega
  have hfour : 4 * (K + 1) ≤ (K + 1) * (K + 3) := by
    rw [Nat.mul_comm 4 (K + 1)]
    exact Nat.mul_le_mul_left (K + 1) (by omega)
  have hexp : R + K + (K + 1) + (K + 1) ≤ (K + 1) * (K + 3) :=
    Nat.le_trans hlin hfour
  have hanti : qpow coupling ((K + 1) * (K + 3)) ≤
      qpow coupling (R + K + (K + 1) + (K + 1)) :=
    HeatKernelRGStep.qpow_antitone (by decide) (by decide) _ _ hexp
  have hassocExp : R + K + (K + 1) + (K + 1) =
      R + (K + ((K + 1) + (K + 1))) := by omega
  have hsplit : qpow coupling (R + K + (K + 1) + (K + 1)) ≈
      qpow coupling R *
        (qpow coupling K * (qpow coupling (K + 1) * qpow coupling (K + 1))) := by
    rw [hassocExp]
    refine Q'.eqv_trans _
      (qpow coupling R * qpow coupling (K + ((K + 1) + (K + 1)))) _ ?_ ?_
    · exact HeatKernelRGStep.qpow_add coupling R _
    · refine Q'.mul_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _
        (qpow coupling K * qpow coupling ((K + 1) + (K + 1))) _ ?_ ?_
      · exact HeatKernelRGStep.qpow_add coupling K _
      · exact Q'.mul_eqv_congr_left _ _ _
          (HeatKernelRGStep.qpow_add coupling (K + 1) (K + 1))
  have hV : Q'.ofNat V * qpow coupling K ≤ (1 : Q') := by
    dsimp only [V, K]
    exact volume_qpow_le_one stage
  have hD : D * qpow coupling (K + 1) ≤ (1 : Q') := by
    dsimp only [D]
    exact dimension_qpow_le_one K
  have hV0 : (0 : Q') ≤ Q'.ofNat V * qpow coupling K :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (qpow_nonneg coupling (by decide) _)
  have hD0 : (0 : Q') ≤ D * qpow coupling (K + 1) :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (qpow_nonneg coupling (by decide) _)
  have hDD : (D * qpow coupling (K + 1)) *
      (D * qpow coupling (K + 1)) ≤ (1 : Q') := by
    have h1 := Q'.mul_le_mul_of_nonneg_left _ _ _ hD hD0
    have h2 := Q'.mul_le_mul_of_nonneg_right _ _ _ hD (by decide : (0 : Q') ≤ 1)
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h1 h2)
      (Q'.le_of_eqv (by decide))
  have htriple : (Q'.ofNat V * qpow coupling K) *
      ((D * qpow coupling (K + 1)) * (D * qpow coupling (K + 1))) ≤ (1 : Q') := by
    have h1 := Q'.mul_le_mul_of_nonneg_left _ _ _ hDD hV0
    have h2 := Q'.mul_le_mul_of_nonneg_right _ _ _ hV (by decide : (0 : Q') ≤ 1)
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h1 h2)
      (Q'.le_of_eqv (by decide))
  have hstage0 : (0 : Q') ≤ qpow coupling R := qpow_nonneg coupling (by decide) _
  have hmain : Q'.ofNat V * ((D * D) *
      (qpow coupling R *
        (qpow coupling K * (qpow coupling (K + 1) * qpow coupling (K + 1))))) ≤
      qpow coupling R := by
    refine Q'.le_trans' _
      (qpow coupling R *
        ((Q'.ofNat V * qpow coupling K) *
          ((D * qpow coupling (K + 1)) * (D * qpow coupling (K + 1))))) _ ?_ ?_
    · exact Q'.le_of_eqv (mul_character_rearrange _ _ _ _ _ _)
    · have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ htriple hstage0
      exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_one_eqv _))
  unfold tailTerm
  change Q'.ofNat V *
      (Q'.ofNat ((K + 1 + 1) ^ 2) * qpow coupling ((K + 1) * (K + 1 + 2))) ≤
    HalfPow.half ^ R
  have hidx : K + 1 + 1 = K + 2 := by omega
  have hc4inner : K + 1 + 2 = K + 3 := by omega
  have hc4 : (K + 1) * (K + 1 + 2) = (K + 1) * (K + 3) := by
    rw [hc4inner]
  rw [hidx, hc4]
  have hsquare : Q'.ofNat ((K + 2) ^ 2) ≈ D * D := by
    dsimp only [D]
    rw [Nat.pow_two]
    exact HeatKernelRGStep.ofNat_mul_eqv (K + 2) (K + 2)
  have houter : Q'.ofNat V *
      (Q'.ofNat ((K + 2) ^ 2) * qpow coupling ((K + 1) * (K + 3))) ≤
      Q'.ofNat V * ((D * D) *
        qpow coupling (R + K + (K + 1) + (K + 1))) := by
    have hq0 : (0 : Q') ≤ qpow coupling ((K + 1) * (K + 3)) :=
      qpow_nonneg coupling (by decide) _
    have hDD0 : (0 : Q') ≤ D * D :=
      Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _) (ExpNeg.ofNat_nonneg' _)
    have hs1 : Q'.ofNat ((K + 2) ^ 2) * qpow coupling ((K + 1) * (K + 3)) ≤
        (D * D) * qpow coupling ((K + 1) * (K + 3)) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_eqv hsquare) hq0
    have hs2 : (D * D) * qpow coupling ((K + 1) * (K + 3)) ≤
        (D * D) * qpow coupling (R + K + (K + 1) + (K + 1)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hanti hDD0
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ hs1 hs2) (ExpNeg.ofNat_nonneg' _)
  refine Q'.le_trans' _ _ _ houter ?_
  have hsplitD : (D * D) * qpow coupling (R + K + (K + 1) + (K + 1)) ≈
      (D * D) * (qpow coupling R *
        (qpow coupling K * (qpow coupling (K + 1) * qpow coupling (K + 1)))) :=
    Q'.mul_eqv_congr_left _ _ _ hsplit
  have hsplitV : Q'.ofNat V *
      ((D * D) * qpow coupling (R + K + (K + 1) + (K + 1))) ≈
      Q'.ofNat V * ((D * D) * (qpow coupling R *
        (qpow coupling K * (qpow coupling (K + 1) * qpow coupling (K + 1))))) :=
    Q'.mul_eqv_congr_left _ _ _ hsplitD
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplitV) ?_
  exact Q'.le_trans' _ _ _ hmain
    (Q'.le_of_eqv (qpow_coupling_eqv_halfPow R))

/-- Dimension-weighted omitted-character charge paid over the full cofinal box. -/
def growingCharacterSupVolumeTail (stage depth : Nat) : Q' :=
  Q'.ofNat (plaquetteEdgeCount (stage + 2)) *
    omittedCharacterSupWindow (volumeAbsorbingCutoff stage) depth

/-- The actual character-supremum tail, including the representation-dimension
factor, retains an additional dyadic power for every plaquette.  This reserve
is what can absorb a later product-telescoping factor. -/
theorem growingCharacterSupVolumeTail_le_two_halfPow_with_volume (stage depth : Nat) :
    growingCharacterSupVolumeTail stage depth ≤
      Q'.ofNat 2 *
        (HalfPow.half ^ (stage + plaquetteEdgeCount (stage + 2))) := by
  let V := plaquetteEdgeCount (stage + 2)
  let K := volumeAbsorbingCutoff stage
  have hwindow := omittedCharacterSupWindow_le_two_head K depth
  have hmul : Q'.ofNat V * omittedCharacterSupWindow K depth ≤
      Q'.ofNat V * (Q'.ofNat 2 * tailTerm coupling 2 (K + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hwindow (ExpNeg.ofNat_nonneg' _)
  have hrearr : Q'.ofNat V * (Q'.ofNat 2 * tailTerm coupling 2 (K + 1)) ≈
      Q'.ofNat 2 * (Q'.ofNat V * tailTerm coupling 2 (K + 1)) :=
    mul_three_rearrange _ _ _
  have hhead : Q'.ofNat V * tailTerm coupling 2 (K + 1) ≤
      HalfPow.half ^ (stage + V) := by
    dsimp only [V, K]
    exact growingCharacterSupHead_le_halfPow stage
  unfold growingCharacterSupVolumeTail
  dsimp only [V, K] at hmul hrearr ⊢
  refine Q'.le_trans' _ _ _ hmul ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hhead (ExpNeg.ofNat_nonneg' _)

/-- Even after multiplying the whole-box tail by one factor two per
plaquette, the retained volume reserve cancels that product growth exactly.
This is the quantitative interface needed by finite-product telescoping. -/
theorem dyadicAmplifiedGrowingCharacterSupVolumeTail_le_two_halfPow
    (stage depth : Nat) :
    Q'.ofNat (2 ^ plaquetteEdgeCount (stage + 2)) *
        growingCharacterSupVolumeTail stage depth ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  let V := plaquetteEdgeCount (stage + 2)
  have hstrong :=
    growingCharacterSupVolumeTail_le_two_halfPow_with_volume stage depth
  have hmul : Q'.ofNat (2 ^ V) * growingCharacterSupVolumeTail stage depth ≤
      Q'.ofNat (2 ^ V) *
        (Q'.ofNat 2 * (HalfPow.half ^ (stage + V))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hstrong (ExpNeg.ofNat_nonneg' _)
  have hrearr : Q'.ofNat (2 ^ V) *
      (Q'.ofNat 2 * (HalfPow.half ^ (stage + V))) ≈
      Q'.ofNat 2 *
        (Q'.ofNat (2 ^ V) * (HalfPow.half ^ (stage + V))) :=
    mul_three_rearrange _ _ _
  have hcancel : Q'.ofNat (2 ^ V) *
      (HalfPow.half ^ (stage + V)) ≈ HalfPow.half ^ stage := by
    rw [Nat.add_comm stage V]
    exact twoPow_halfPow_add_eqv V stage
  dsimp only [V] at hmul hrearr hcancel ⊢
  refine Q'.le_trans' _ _ _ hmul ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrearr) ?_
  exact Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hcancel)

/-- The weaker stage-only envelope, retained as a convenient corollary. -/
theorem growingCharacterSupVolumeTail_le_two_halfPow (stage depth : Nat) :
    growingCharacterSupVolumeTail stage depth ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  have hstrong := growingCharacterSupVolumeTail_le_two_halfPow_with_volume stage depth
  have hpow : HalfPow.half ^ (stage + plaquetteEdgeCount (stage + 2)) ≤
      HalfPow.half ^ stage := halfPow_antitone (by omega)
  exact Q'.le_trans' _ _ _ hstrong
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (ExpNeg.ofNat_nonneg' _))

/-- Explicit depth-uniform modulus for the dimension-weighted character tail. -/
theorem growingCharacterSupVolumeTail_modulus (ε : Q') (hε : (0 : Q') < ε) :
    ∀ stage, ε.den + 1 ≤ stage → ∀ depth,
      growingCharacterSupVolumeTail stage depth ≤ ε := by
  intro stage hstage depth
  have htail := growingCharacterSupVolumeTail_le_two_halfPow stage depth
  have hpow : HalfPow.half ^ stage ≤ HalfPow.half ^ (ε.den + 1) :=
    halfPow_antitone hstage
  have htwo : Q'.ofNat 2 * (HalfPow.half ^ stage) ≤
      Q'.ofNat 2 * (HalfPow.half ^ (ε.den + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (ExpNeg.ofNat_nonneg' _)
  refine Q'.le_trans' _ _ _ htail ?_
  refine Q'.le_trans' _ _ _ htwo ?_
  refine Q'.le_trans' _ (HalfPow.half ^ ε.den) _ ?_ ?_
  · exact Q'.le_of_eqv (two_halfPow_succ_eqv ε.den)
  · exact HalfPow.pow_half_le ε hε

#print axioms qpow_coupling_eqv_halfPow
#print axioms qpow_coupling_le_invSucc
#print axioms halfPow_antitone
#print axioms two_halfPow_succ_eqv
#print axioms twoPow_halfPow_add_eqv
#print axioms volumeAbsorbingCutoff_ge_two
#print axioms volumeAbsorbingCutoff_unbounded
#print axioms growingNaiveVolumeTail_le_halfPow
#print axioms omittedCoefficientWindow_le_two_head
#print axioms growingOmittedVolumeTail_le_two_halfPow
#print axioms growingOmittedVolumeTail_modulus
#print axioms characterSupTerm_eqv_tailTerm
#print axioms omittedCharacterSupWindow_le_two_head
#print axioms growingCharacterSupVolumeTail_le_two_halfPow_with_volume
#print axioms dyadicAmplifiedGrowingCharacterSupVolumeTail_le_two_halfPow
#print axioms growingCharacterSupVolumeTail_le_two_halfPow
#print axioms growingCharacterSupVolumeTail_modulus

end YMGap.Continuum.Z4GrowingCutoffVolumeTail
