/-
# Original replica-cut cost joined to the existing conditional energy

The positive cut and star floors are retained explicitly. This is a
finite-volume, nome-dependent comparison on original weighted L2, not a
physical-time or scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabOrderedPathCut
import YMGap.Continuum.BF4ExactSlabReplacementEnergyBound
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4ExactSlabOrderedPathEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison
open YMGap.Continuum.BF4ExactSlabReplicaPathVariance
open YMGap.Continuum.BF4ExactSlabCrossExteriorReplacement
open YMGap.Continuum.BF4ExactSlabReplacementEnergyBound
open YMGap.Continuum.BF4ExactSlabOrderedPathCut
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

private theorem mul_rat (c : Q') (x : RC) :
    RCmul (Quotient.mk crealSetoid (ofQ' c)) x = RCscale c x := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

/-- The denominator consists of the actual cut floor and actual incident-star
floor; it has no cutoff or observable dependence. -/
def stepFloor (w : Q') (extent : Nat) (A : List Nat) (link : Z4Link) : Q' :=
  (headFloor w * headFloor w)^crossingCount extent (selectedLinks extent A) *
    (starLower w extent link * starLower w extent link)

theorem stepFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (A : List Nat) (link : Z4Link) :
    (0 : Q') < stepFloor w extent A link :=
  Q'.mul_pos
    (HKPos.pow_pos (Q'.mul_pos (headFloor_positive hw0 hw1)
      (headFloor_positive hw0 hw1)) _)
    (Q'.mul_pos (starLower_positive hw0 hw1 extent link)
      (starLower_positive hw0 hw1 extent link))

/-- Explicit per-step comparison cost, uniform only over late heat cutoffs
at fixed nome, extent, cut and link. The partition is NOT absorbed here. -/
def stepCost {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (A : List Nat) (link : Z4Link) : Q' :=
  Q'.recipPos (stepFloor w extent A link) (stepFloor_positive hw0 hw1 extent A link) *
    ((prefixCap w * prefixCap w)^crossingCount extent (selectedLinks extent A) *
      (starUpper w extent link * starUpper w extent link))

private theorem positive_factor_remove (c : Q') (hc : (0 : Q') < c) (x y : RC)
    (h : RCle (RCscale c x) y) : RCle x (RCscale (Q'.recipPos c hc) y) := by
  have hs := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos c hc)) h
  rw [RCscale_RCscale] at hs
  have he : Q'.eqv (Q'.recipPos c hc * c) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  rw [RCSignedPairBudget.scale_congr he x, RCscale_one] at hs
  exact hs

private theorem cut_energy_join (c e u v z J I : Q') (E : RC)
    (hc : (0 : Q') < c) (he : (0 : Q') < e) (hu : (0 : Q') ≤ u)
    (hcut : c*J ≤ u*I) (henergy : RCle (rat (e*I)) (RCscale (v*z) E)) :
    RCle (rat J)
      (RCscale ((Q'.recipPos (c*e) (Q'.mul_pos hc he) * (u*v))*z) E) := by
  have h1 : RCle (rat (e*(c*J))) (rat (e*(u*I))) :=
    leEv_ofQ'_of_approx_ge (fun _ =>
      Q'.mul_le_mul_of_nonneg_left _ _ _ hcut (Q'.le_of_lt he))
  have h2 := RCscale_mono hu henergy
  rw [scale_rat, RCscale_RCscale] at h2
  have hleft : rat (e*(c*J)) = RCscale (c*e) (rat J) := by
    rw [scale_rat]
    exact Quotient.sound (ofQ'_equiv_of_eqv
      (RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (by decide)
        (fun | 0 => c | 1 => e | _ => J)))
  have hmiddle : rat (e*(u*I)) = rat (u*(e*I)) := by
    exact Quotient.sound (ofQ'_equiv_of_eqv
      (RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => e | 1 => u | _ => I)))
  rw [hleft, hmiddle] at h1
  have h := positive_factor_remove (c*e) (Q'.mul_pos hc he) (rat J)
    (RCscale (u*(v*z)) E) (RCle_trans h1 h2)
  rw [RCscale_RCscale] at h
  have hassoc : Q'.eqv
      (Q'.recipPos (c*e) (Q'.mul_pos hc he) * (u*(v*z)))
      ((Q'.recipPos (c*e) (Q'.mul_pos hc he) * (u*v))*z) := by
    exact RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (by decide)
      (fun | 0 => Q'.recipPos (c*e) (Q'.mul_pos hc he) | 1 => u | 2 => v | _ => z)
  rw [RCSignedPairBudget.scale_congr hassoc E] at h
  exact h

/-- Each next-link path increment is controlled by the EXISTING conditional
residual of that SAME physical link in the full ORIGINAL action completion.
The original partition occurs once, outside the explicit comparison cost. -/
theorem original_selected_increment_energy_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (A : List Nat)
    (hA : ∀ i, i ∈ A → i < blocks extent) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (hnot : slot extent link ∉ A) (p : (fullData hw0 hw1 K extent hK).V) :
    RCle
      (Quotient.mk crealSetoid (ofQ'
        (incrementIntegral w K extent A (slot extent link) p.val)))
      (RCscale (stepCost hw0 hw1 extent A link *
          quaternionHaar (blocks extent) (fullWeight w K extent))
        (RCadd
          (normSq ((projections hw0 hw1 K extent hK).residual ⟨link,hl⟩
            (embedV (fullData hw0 hw1 K extent hK) p)))
          (normSq ((projections hw0 hw1 K extent hK).residual ⟨link,hl⟩
            (embedV (fullData hw0 hw1 K extent hK) p))))) := by
  have hc := original_selected_increment_bound hw0 hw1 K extent hK A hA
    (slot extent link) hnot p.val p.property
  have he := original_replacement_energy_bound hw0 hw1 K extent hK link hl p
  rw [mul_rat] at he
  exact cut_energy_join
    ((headFloor w * headFloor w)^crossingCount extent (selectedLinks extent A))
    (starLower w extent link * starLower w extent link)
    ((prefixCap w * prefixCap w)^crossingCount extent (selectedLinks extent A))
    (starUpper w extent link * starUpper w extent link)
    (quaternionHaar (blocks extent) (fullWeight w K extent))
    (incrementIntegral w K extent A (slot extent link) p.val)
    (replacementIntegral w K extent link p.val) _
    (HKPos.pow_pos (Q'.mul_pos (headFloor_positive hw0 hw1)
      (headFloor_positive hw0 hw1)) _)
    (Q'.mul_pos (starLower_positive hw0 hw1 extent link)
      (starLower_positive hw0 hw1 extent link))
    (Q'.pow_nonneg _ (Q'.mul_nonneg _ _
      (prefixCap_nonnegative hw0) (prefixCap_nonnegative hw0)) _) hc he

#print axioms stepFloor_positive
#print axioms stepCost
#print axioms original_selected_increment_energy_bound

end YMGap.Continuum.BF4ExactSlabOrderedPathEnergy
