import YMGap.Continuum.SevenAnchorWindowRetune
import YMGap.Continuum.CutoffCorrelationMonotone

namespace YMGap.Continuum.HarmonicDABoundTransport

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

theorem harmonicMass_le_of_DA (k : Nat) (U : Q')
    (h : harmonicD k - harmonicA k ≤ U * harmonicD k) :
    harmonicMass k ≤ U := by
  have hdiv := Q'.divPos_le_of_le_mul
    (harmonicD k - harmonicA k) (harmonicD k) (harmonicD_pos k) h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (harmonicMass_eq_DA k)) hdiv

theorem harmonicMass_ge_of_DA (k : Nat) (L : Q')
    (h : L * harmonicD k ≤ harmonicD k - harmonicA k) :
    L ≤ harmonicMass k := by
  have hdiv := Q'.le_divPos_of_mul_le
    (harmonicD k - harmonicA k) (harmonicD k) (harmonicD_pos k) h
  exact Q'.le_trans' _ _ _ hdiv (Q'.ge_of_eqv (harmonicMass_eq_DA k))

/-- Cutoff quotient monotonicity turns any fixed-prefix deficit estimate into
an upper bound for the full harmonic mass.  This avoids reducing the large
quadratic cutoff in kernel computation. -/
theorem harmonicMass_le_of_prefix (k N tail : Nat) (U : Q')
    (hcut : N + tail = Ncut k)
    (hprefix : coordNormSq (harmW k) N - adjCorr (harmW k) N ≤
      U * coordNormSq (harmW k) N) :
    harmonicMass k ≤ U := by
  let w := harmW k
  let A0 := adjCorr w N
  let D0 := coordNormSq w N
  let A := adjCorr w (Ncut k)
  let D := coordNormSq w (Ncut k)
  have hD0 : (0 : Q') < D0 :=
    CutoffCorrelationMonotone.coordNormSq_pos (harmW_nonneg k) N
  have hD : (0 : Q') < D :=
    CutoffCorrelationMonotone.coordNormSq_pos (harmW_nonneg k) (Ncut k)
  have hcross0 := CutoffCorrelationMonotone.finite_cutoff_tail_compare
    (harmW_nonneg k) (harmW_le_one k) (harmW_pos k) N tail
  have hcross : A0 * D ≤ A * D0 := by
    unfold A0 D A
    rw [← hcut]
    exact hcross0
  have hquot := FusionMarginMono.divPos_le_divPos_of_cross
    A0 D0 A D hD0 hD hcross
  have hone :
      (1 : Q') - Q'.divPos A D hD ≤
        (1 : Q') - Q'.divPos A0 D0 hD0 :=
    Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hquot)
  have hdef : Q'.divPos (D - A) D hD ≤
      Q'.divPos (D0 - A0) D0 hD0 := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (HeatKernelRGStep.one_sub_divPos_eqv A D hD))
      (Q'.le_trans' _ _ _ hone
        (Q'.le_of_eqv (HeatKernelRGStep.one_sub_divPos_eqv A0 D0 hD0)))
  have hp : Q'.divPos (D0 - A0) D0 hD0 ≤ U := by
    apply Q'.divPos_le_of_le_mul
    unfold D0 A0 w
    exact hprefix
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (harmonicMass_eq_DA k))
    (Q'.le_trans' _ _ _ hdef hp)

private theorem harmonicMass_mul_D (k : Nat) :
    harmonicMass k * harmonicD k ≈ harmonicD k - harmonicA k := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (harmonicD k) (harmonicMass_eq_DA k))
    (Q'.divPos_mul_eqv _ _ _)

theorem DA_cross_of_mass_ratio (k : Nat) (p q : Q')
    (hratio : p * harmonicMass k ≤ q * harmonicMass (k + 1)) :
    (p * (harmonicD k - harmonicA k)) * harmonicD (k + 1) ≤
      (q * (harmonicD (k + 1) - harmonicA (k + 1))) * harmonicD k := by
  let den := harmonicD k * harmonicD (k + 1)
  have hden0 : (0 : Q') ≤ den := Q'.mul_nonneg _ _
    (Q'.le_of_lt (harmonicD_pos k)) (Q'.le_of_lt (harmonicD_pos (k + 1)))
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ _ hratio hden0
  have hleft : (p * harmonicMass k) * den ≈
      (p * (harmonicD k - harmonicA k)) * harmonicD (k + 1) := by
    unfold den
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv p (harmonicMass k) _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (harmonicMass k)
          (harmonicD k) (harmonicD (k + 1))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv p
        (harmonicMass k * harmonicD k) (harmonicD (k + 1)))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left p _ _ (harmonicMass_mul_D k))
  have hright : (q * harmonicMass (k + 1)) * den ≈
      (q * (harmonicD (k + 1) - harmonicA (k + 1))) * harmonicD k := by
    unfold den
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (q * harmonicMass (k + 1)) _ _
        (Q'.mul_comm_eqv (harmonicD k) (harmonicD (k + 1)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv q (harmonicMass (k + 1)) _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (harmonicMass (k + 1))
          (harmonicD (k + 1)) (harmonicD k)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv q
        (harmonicMass (k + 1) * harmonicD (k + 1)) (harmonicD k))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left q _ _ (harmonicMass_mul_D (k + 1)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hright))

end YMGap.Continuum.HarmonicDABoundTransport

#print axioms YMGap.Continuum.HarmonicDABoundTransport.harmonicMass_le_of_DA
#print axioms YMGap.Continuum.HarmonicDABoundTransport.harmonicMass_ge_of_DA
#print axioms YMGap.Continuum.HarmonicDABoundTransport.harmonicMass_le_of_prefix
#print axioms YMGap.Continuum.HarmonicDABoundTransport.DA_cross_of_mass_ratio
