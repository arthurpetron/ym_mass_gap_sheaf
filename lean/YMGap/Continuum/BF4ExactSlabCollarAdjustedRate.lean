/-
# Absorb the ORIGINAL collar cost into a volume-independent core rate

With delta(w)=128*w^3 and r(w)=1/(1-delta(w)), the literal collar count
gives each normalized core weight the bound

  r(w)^(12*|probe links|) * (kappa(w)*r(w)^48)^|core|.

The prefactor retains the probe support size. The per-face rate names the
coupling w but not the slab volume or cutoff. This is still a per-core
estimate: a bound on the number of rooted cores is a separate obligation.
-/

import YMGap.Continuum.BF4ExactSlabCollarDegreeBound
import YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget
import YMGap.Continuum.TotalMajorantClose

namespace YMGap.Continuum.BF4ExactSlabCollarAdjustedRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabMixedAction
open YMGap.Continuum.BF4ExactSlabMixedRelativePartition
open YMGap.Continuum.BF4ExactSlabMixedCoefficientBound
open YMGap.Continuum.BF4ExactSlabMixedFiniteBoundaryBudget
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.BF4ExactSlabConnectedCoefficientBound
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

def inverseFaceFloor (w : Q') (hd : heatRemainderBound w < 1) : Q' :=
  Q'.recipPos (1 + -heatRemainderBound w) (HKPos.one_sub_pos hd)

def probePrefactor (w : Q') (hd : heatRemainderBound w < 1) (linkCount : Nat) : Q' :=
  (inverseFaceFloor w hd)^(12*linkCount)

def adjustedCoreRate (w : Q') (hd : heatRemainderBound w < 1) : Q' :=
  pairedHeatRate w * (inverseFaceFloor w hd)^48

theorem inverseFaceFloor_pos (w : Q') (hd : heatRemainderBound w < 1) :
    (0 : Q') < inverseFaceFloor w hd := Q'.recipPos_pos _ _

theorem one_le_inverseFaceFloor {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1) :
    (1 : Q') ≤ inverseFaceFloor w hd := by
  have ha : 1 + -heatRemainderBound w ≤ (1 : Q') := by
    apply Q'.le_of_sub_nonneg
    exact Q'.le_trans' _ _ _ (heatRemainderBound_nonnegative hw)
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.var 0)
        (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0))))) (by decide) (fun _ => heatRemainderBound w)))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
      (Q'.le_trans' _ _ _ ha (Q'.ge_of_eqv (Q'.mul_recipPos_eqv _ (HKPos.one_sub_pos hd)))))
    (HKPos.one_sub_pos hd)

theorem probePrefactor_nonnegative (w : Q') (hd : heatRemainderBound w < 1) (linkCount : Nat) :
    (0 : Q') ≤ probePrefactor w hd linkCount :=
  Q'.pow_nonneg _ (Q'.le_of_lt (inverseFaceFloor_pos w hd)) _

theorem adjustedCoreRate_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1) :
    (0 : Q') ≤ adjustedCoreRate w hd :=
  Q'.mul_nonneg _ _ (pairedHeatRate_nonnegative hw) (Q'.pow_nonneg _ (Q'.le_of_lt (inverseFaceFloor_pos w hd)) _)

private theorem inverse_powers {a r : Q'} (har : a*r ≈ 1) : ∀ n : Nat, a^n*r^n ≈ 1
  | 0 => Q'.mul_one_eqv 1
  | n+1 => Q'.eqv_trans _ _ _ (TotalMajorantClose.mul4_swap a (a^n) r (r^n))
      (Q'.eqv_trans _ _ _ (qmul har (inverse_powers har n)) (Q'.mul_one_eqv 1))

theorem mixedReciprocal_le_power (w : Q') (hd : heatRemainderBound w < 1)
    (keep : Nat → Bool) (removed : List Nat) :
    Q'.recipPos (mixedRemovalFloor w keep removed) (mixedRemovalFloor_pos hd keep removed) ≤
      (inverseFaceFloor w hd)^(removed.length+(inside keep removed).length) := by
  let a := 1 + -heatRemainderBound w
  let r := inverseFaceFloor w hd
  have har : a*r ≈ 1 := Q'.mul_recipPos_eqv _ (HKPos.one_sub_pos hd)
  have he : mixedRemovalFloor w keep removed * (r^removed.length*r^(inside keep removed).length) ≈ 1 :=
    Q'.eqv_trans _ _ _ (TotalMajorantClose.mul4_swap (a^removed.length) (a^(inside keep removed).length)
      (r^removed.length) (r^(inside keep removed).length))
      (Q'.eqv_trans _ _ _ (qmul (inverse_powers har _) (inverse_powers har _)) (Q'.mul_one_eqv 1))
  have h := Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv _ (mixedRemovalFloor_pos hd keep removed)))
      (Q'.ge_of_eqv he)) (mixedRemovalFloor_pos hd keep removed)
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (YMGap.Continuum.Q'.pow_add_eqv r _ _))

theorem collarReciprocal_bound {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1)
    (extent : Nat) (links : List Z4Link) (keep : Nat → Bool) (ambient anchor : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    Q'.recipPos (mixedRemovalFloor w keep (collarIds extent links anchor ambient))
        (mixedRemovalFloor_pos hd keep _) ≤
      (inverseFaceFloor w hd)^(12*links.length+48*anchor.length) := by
  have hc := collarIds_length_le extent links anchor ambient hn hphys
  have hi : (inside keep (collarIds extent links anchor ambient)).length ≤
      (collarIds extent links anchor ambient).length := List.length_filter_le _ _
  exact Q'.le_trans' _ _ _ (mixedReciprocal_le_power w hd keep _)
    (TotalMajorantClose.q_pow_mono (one_le_inverseFaceFloor hw hd) (by omega))

private theorem split_rate (r k : Q') (linkCount count : Nat) :
    k^count * r^(12*linkCount+48*count) ≈ r^(12*linkCount)*(k*r^48)^count := by
  have he := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (k^count) _ _ (YMGap.Continuum.Q'.pow_add_eqv r _ _))
    (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun i => if i = 0 then k^count else if i = 1 then r^(12*linkCount) else r^(48*count)))
  exact Q'.eqv_trans _ _ _ he (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (k^count) _ _ (Q'.eqv_symm (TotalMajorantClose.pow_mul r 48 count)))
    (Q'.eqv_symm (TotalMajorantClose.mul_pow k (r^48) count))))

/-- The existing normalized weight, with both collar copies absorbed into a
coupling-dependent rate and a probe-only prefactor. -/
theorem normalizedCoreWeight_geometric_bound {w : Q'} (hw : (0 : Q') ≤ w) (hd : heatRemainderBound w < 1)
    (extent : Nat) (links : List Z4Link) (keep : Nat → Bool) (ambient anchor : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    normalizedCoreWeight w hd extent links keep ambient anchor ≤
      probePrefactor w hd links.length * (adjustedCoreRate w hd)^anchor.length :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (mixedHeatWeight_le_pairedPow hw keep anchor)
      (Q'.le_of_lt (Q'.recipPos_pos _ _)))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (collarReciprocal_bound hw hd extent links keep ambient anchor hn hphys)
        (Q'.pow_nonneg _ (pairedHeatRate_nonnegative hw) _))
      (Q'.le_of_eqv (split_rate (inverseFaceFloor w hd) (pairedHeatRate w) links.length anchor.length)))

end YMGap.Continuum.BF4ExactSlabCollarAdjustedRate

#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.inverseFaceFloor
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.probePrefactor
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.adjustedCoreRate
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.inverseFaceFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.one_le_inverseFaceFloor
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.probePrefactor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.adjustedCoreRate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.mixedReciprocal_le_power
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.collarReciprocal_bound
#print axioms YMGap.Continuum.BF4ExactSlabCollarAdjustedRate.normalizedCoreWeight_geometric_bound
