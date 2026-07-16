/-
# Spin-dependent local fusion multiplicity bound

The cutoff-cardinality majorant maximizes every internal fusion channel over
the global auxiliary window and is therefore unusable for a uniform polymer
estimate.  Admissible channels are actually bounded by prefix sums of the
incident physical spins.  This module retains that information and proves that
every valence-zero-through-six local fusion multiplicity is at most

  `(1 + sum of incident physical spins)^3`.

The bound is independent of the representation cutoff.  Its cubic degree is
the exact maximum number of internal channels in the chosen valence-six
resolution.
-/

import YMGap.Continuum.Z4ExplicitSpinFoamBounds
import YMGap.Continuum.Z4ExplicitExcitationLocalization
import YMGap.Continuum.Z4ValenceFusionCutoffIndependence

namespace YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

def spinSumCube (sum : Nat) : Nat :=
  (sum + 1) * ((sum + 1) * (sum + 1))

def externalPrefixSpinSum : Nat → EdgeLabelling → Nat
  | 0, _ => 0
  | degree + 1, external =>
      externalPrefixSpinSum degree external + external degree

def externalPrefixSpinProduct : Nat → EdgeLabelling → Nat
  | 0, _ => 1
  | degree + 1, external =>
      externalPrefixSpinProduct degree external * (external degree + 1)

def spinProductCube (product : Nat) : Nat :=
  product * (product * product)

private theorem base_le_spinSumCube (sum : Nat) :
    sum + 1 ≤ spinSumCube sum := by
  let base := sum + 1
  have hpos : 0 < base := by unfold base; omega
  have hlinear : base ≤ base * base :=
    Nat.le_mul_of_pos_right base hpos
  have hsquare : base * base ≤ base * (base * base) :=
    Nat.mul_le_mul_left base hlinear
  exact Nat.le_trans hlinear hsquare

private theorem square_le_spinSumCube_of_le
    {value sum : Nat} (hvalue : value ≤ sum + 1) :
    value * value ≤ spinSumCube sum := by
  have hsq : value * value ≤ (sum + 1) * (sum + 1) :=
    Nat.mul_le_mul hvalue hvalue
  have hbase : sum + 1 ≤ (sum + 1) * (sum + 1) :=
    Nat.le_mul_of_pos_right (sum + 1) (by omega)
  have hcube : (sum + 1) * (sum + 1) ≤
      (sum + 1) * ((sum + 1) * (sum + 1)) :=
    Nat.mul_le_mul_left (sum + 1) hbase
  exact Nat.le_trans hsq hcube

private theorem cube_le_spinSumCube_of_le
    {value sum : Nat} (hvalue : value ≤ sum + 1) :
    value * (value * value) ≤ spinSumCube sum := by
  unfold spinSumCube
  exact Nat.mul_le_mul hvalue (Nat.mul_le_mul hvalue hvalue)

private theorem oneValentMultiplicity_le_one
    (cutoff a : Nat) : oneValentMultiplicity cutoff a ≤ 1 := by
  rw [oneValentMultiplicity_cutoff_independent
    (bound := 0) (cutoff := cutoff) (a := a) (by omega)]
  cases h : fusionOK a 0 0 <;>
    simp [oneValentMultiplicity, h]

private theorem twoValentMultiplicity_le_one
    (cutoff a b : Nat) : twoValentMultiplicity cutoff a b ≤ 1 := by
  rw [twoValentMultiplicity_cutoff_independent
    (bound := 0) (cutoff := cutoff) (a := a) (b := b) (by omega)]
  cases h : fusionOK a b 0 <;>
    simp [twoValentMultiplicity, h]

private theorem boolMultiplicity_le_one (allowed : Bool) :
    boolMultiplicity allowed ≤ 1 := by
  cases allowed <;> decide

/-! ## 1. Channel-count bounds by the external spin sum -/

theorem oneChannelMultiplicity_le_spinSumCube
    (cutoff a b c d : Nat) :
    oneChannelMultiplicity cutoff a b c d ≤
      spinSumCube (a + b + c + d) := by
  let sum := a + b + c + d
  by_cases hcutoff : cutoff ≤ sum
  · exact Nat.le_trans (oneChannelMultiplicity_le cutoff a b c d)
      (base_le_spinSumCube sum |> fun h => by
        apply Nat.le_trans (show cutoff + 1 ≤ sum + 1 by omega)
        exact h)
  · have hsum : sum ≤ cutoff := by omega
    let allowed : Nat → Bool := fun x =>
      fusionOK a b x && fusionOK x c d
    have hsupport : ∀ x, allowed x = true → x ≤ sum := by
      intro x hx
      have hfirst := ((Bool.and_eq_true _ _).mp hx).1
      have hout := fusionOK_output_le_add hfirst
      unfold sum
      omega
    have hstable := filterRangeCount_stable_of_le
      (bound := sum) (cutoff := cutoff) allowed hsum hsupport
    change filterRangeCount cutoff allowed ≤ spinSumCube sum
    rw [hstable]
    exact Nat.le_trans (by
        unfold filterRangeCount
        simpa using List.length_filter_le allowed (List.range (sum + 1)))
      (base_le_spinSumCube sum)

theorem twoChannelMultiplicity_le_spinSumCube
    (cutoff a b c d e : Nat) :
    twoChannelMultiplicity cutoff a b c d e ≤
      spinSumCube (a + b + c + d + e) := by
  let sum := a + b + c + d + e
  by_cases hcutoff : cutoff ≤ sum
  · exact Nat.le_trans (twoChannelMultiplicity_le cutoff a b c d e)
      (square_le_spinSumCube_of_le
        (show cutoff + 1 ≤ sum + 1 by omega))
  · have hsum : sum ≤ cutoff := by omega
    let allowed : Nat × Nat → Bool := fun xy =>
      fusionOK a b xy.1 &&
        (fusionOK xy.1 c xy.2 && fusionOK xy.2 d e)
    have hxSupport : ∀ x y, allowed (x, y) = true → x ≤ sum := by
      intro x y hxy
      have hparts := (Bool.and_eq_true _ _).mp hxy
      have hx := fusionOK_output_le_add hparts.1
      unfold sum
      omega
    have hySupport : ∀ x y, allowed (x, y) = true → y ≤ sum := by
      intro x y hxy
      have hparts := (Bool.and_eq_true _ _).mp hxy
      have htail := (Bool.and_eq_true _ _).mp hparts.2
      have hx := fusionOK_output_le_add hparts.1
      have hy := fusionOK_output_le_add htail.1
      unfold sum
      omega
    have hinner := pairPathCount_inner_stable cutoff allowed hsum hySupport
    have houter := pairPathCount_outer_stable
      (innerCutoff := sum) allowed hsum hxSupport
    have heq : twoChannelMultiplicity cutoff a b c d e =
        twoChannelMultiplicity sum a b c d e := by
      calc
        twoChannelMultiplicity cutoff a b c d e =
            pairPathCount cutoff cutoff allowed :=
          twoChannelMultiplicity_eq_pairPathCount _ _ _ _ _ _
        _ = pairPathCount cutoff sum allowed := hinner
        _ = pairPathCount sum sum allowed := houter
        _ = twoChannelMultiplicity sum a b c d e :=
          (twoChannelMultiplicity_eq_pairPathCount _ _ _ _ _ _).symm
    rw [heq]
    exact Nat.le_trans (twoChannelMultiplicity_le sum a b c d e)
      (square_le_spinSumCube_of_le (Nat.le_refl _))

theorem threeChannelMultiplicity_le_spinSumCube
    (cutoff a b c d e f : Nat) :
    threeChannelMultiplicity cutoff a b c d e f ≤
      spinSumCube (a + b + c + d + e + f) := by
  let sum := a + b + c + d + e + f
  by_cases hcutoff : cutoff ≤ sum
  · exact Nat.le_trans
      (threeChannelMultiplicity_le cutoff a b c d e f)
      (cube_le_spinSumCube_of_le
        (show cutoff + 1 ≤ sum + 1 by omega))
  · have hsum : sum ≤ cutoff := by omega
    let allowed : Nat × Nat × Nat → Bool := fun xyz =>
      fusionOK a b xyz.1 &&
        (fusionOK xyz.1 c xyz.2.1 &&
          (fusionOK xyz.2.1 d xyz.2.2 &&
            fusionOK xyz.2.2 e f))
    have hxSupport : ∀ x y z,
        allowed (x, y, z) = true → x ≤ sum := by
      intro x y z hxyz
      dsimp only [allowed] at hxyz
      have hparts := (Bool.and_eq_true _ _).mp hxyz
      have hx := fusionOK_output_le_add hparts.1
      unfold sum
      omega
    have hySupport : ∀ x y z,
        allowed (x, y, z) = true → y ≤ sum := by
      intro x y z hxyz
      dsimp only [allowed] at hxyz
      have hparts := (Bool.and_eq_true _ _).mp hxyz
      have htail := (Bool.and_eq_true _ _).mp hparts.2
      have hx := fusionOK_output_le_add hparts.1
      have hy := fusionOK_output_le_add htail.1
      unfold sum
      omega
    have hzSupport : ∀ x y z,
        allowed (x, y, z) = true → z ≤ sum := by
      intro x y z hxyz
      dsimp only [allowed] at hxyz
      have hparts := (Bool.and_eq_true _ _).mp hxyz
      have htail := (Bool.and_eq_true _ _).mp hparts.2
      have hlast := (Bool.and_eq_true _ _).mp htail.2
      have hx := fusionOK_output_le_add hparts.1
      have hy := fusionOK_output_le_add htail.1
      have hz := fusionOK_output_le_add hlast.1
      unfold sum
      omega
    have hinner := triplePathCount_inner_stable
      cutoff cutoff allowed hsum hzSupport
    have hmiddle := triplePathCount_middle_stable
      (outerCutoff := cutoff) (innerCutoff := sum)
      allowed hsum hySupport
    have houter := triplePathCount_outer_stable
      (middleCutoff := sum) (innerCutoff := sum)
      allowed hsum hxSupport
    have heq : threeChannelMultiplicity cutoff a b c d e f =
        threeChannelMultiplicity sum a b c d e f := by
      calc
        threeChannelMultiplicity cutoff a b c d e f =
            triplePathCount cutoff cutoff cutoff allowed :=
          threeChannelMultiplicity_eq_triplePathCount _ _ _ _ _ _ _
        _ = triplePathCount cutoff cutoff sum allowed := hinner
        _ = triplePathCount cutoff sum sum allowed := hmiddle
        _ = triplePathCount sum sum sum allowed := houter
        _ = threeChannelMultiplicity sum a b c d e f :=
          (threeChannelMultiplicity_eq_triplePathCount
            _ _ _ _ _ _ _).symm
    rw [heq]
    exact Nat.le_trans (threeChannelMultiplicity_le sum a b c d e f)
      (cube_le_spinSumCube_of_le (Nat.le_refl _))

/-! ## 2. Uniform valence and actual-link forms -/

theorem explicitValenceMultiplicity_le_spinSumCube
    {cutoff degree : Nat} (external : EdgeLabelling)
    (hdegree : degree ≤ linkIncidenceBound) :
    explicitValenceMultiplicity cutoff degree external ≤
      spinSumCube (externalPrefixSpinSum degree external) := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 1 ≤ 1
    exact Nat.le_refl 1
  · exact Nat.le_trans (oneValentMultiplicity_le_one cutoff (external 0))
      (Nat.le_trans (by omega)
        (base_le_spinSumCube (externalPrefixSpinSum 1 external)))
  · exact Nat.le_trans
      (twoValentMultiplicity_le_one cutoff (external 0) (external 1))
      (Nat.le_trans (by omega)
        (base_le_spinSumCube (externalPrefixSpinSum 2 external)))
  · exact Nat.le_trans
      (boolMultiplicity_le_one
        (fusionOK (external 0) (external 1) (external 2)))
      (Nat.le_trans (by omega)
        (base_le_spinSumCube (externalPrefixSpinSum 3 external)))
  · simpa [externalPrefixSpinSum] using
      oneChannelMultiplicity_le_spinSumCube cutoff
        (external 0) (external 1) (external 2) (external 3)
  · simpa [externalPrefixSpinSum] using
      twoChannelMultiplicity_le_spinSumCube cutoff
        (external 0) (external 1) (external 2) (external 3) (external 4)
  · simpa [externalPrefixSpinSum] using
      threeChannelMultiplicity_le_spinSumCube cutoff
        (external 0) (external 1) (external 2) (external 3) (external 4)
          (external 5)

theorem externalPrefixSpinSum_add_one_le_product
    (degree : Nat) (external : EdgeLabelling) :
    externalPrefixSpinSum degree external + 1 ≤
      externalPrefixSpinProduct degree external := by
  induction degree with
  | zero =>
      change 1 ≤ 1
      exact Nat.le_refl 1
  | succ degree ih =>
      change externalPrefixSpinSum degree external +
          external degree + 1 ≤
        externalPrefixSpinProduct degree external *
          (external degree + 1)
      have honeProduct : 1 ≤ externalPrefixSpinProduct degree external :=
        Nat.le_trans (by omega) ih
      have hscale : external degree ≤
          externalPrefixSpinProduct degree external * external degree := by
        have := Nat.mul_le_mul_right (external degree) honeProduct
        simpa [Nat.mul_comm] using this
      have hadd := Nat.add_le_add ih hscale
      rw [Nat.mul_add, Nat.mul_one]
      omega

theorem spinSumCube_le_prefixProductCube
    (degree : Nat) (external : EdgeLabelling) :
    spinSumCube (externalPrefixSpinSum degree external) ≤
      spinProductCube (externalPrefixSpinProduct degree external) := by
  unfold spinSumCube spinProductCube
  have h := externalPrefixSpinSum_add_one_le_product degree external
  exact Nat.mul_le_mul h (Nat.mul_le_mul h h)

theorem explicitValenceMultiplicity_le_prefixProductCube
    {cutoff degree : Nat} (external : EdgeLabelling)
    (hdegree : degree ≤ linkIncidenceBound) :
    explicitValenceMultiplicity cutoff degree external ≤
      spinProductCube (externalPrefixSpinProduct degree external) := by
  exact Nat.le_trans
    (explicitValenceMultiplicity_le_spinSumCube external hdegree)
    (spinSumCube_le_prefixProductCube degree external)

def actualIncidentSpinSum (n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × Z4Link) : Nat :=
  externalPrefixSpinSum (incidentPlaqIds n indexed.2).length
    (fun position => physical
      (localIdentifierRename (incidentPlaqIds n indexed.2)
        (linkBlockBase n indexed.1) position))

def actualIncidentSpinProduct (n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × Z4Link) : Nat :=
  externalPrefixSpinProduct (incidentPlaqIds n indexed.2).length
    (fun position => physical
      (localIdentifierRename (incidentPlaqIds n indexed.2)
        (linkBlockBase n indexed.1) position))

theorem explicitLinkMultiplicityFactor_le_spinSumCube
    (K n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × Z4Link) :
    explicitLinkMultiplicityFactor K n physical indexed ≤
      Q'.ofNat (spinSumCube
        (actualIncidentSpinSum n physical indexed)) := by
  unfold explicitLinkMultiplicityFactor actualIncidentSpinSum
  apply Q'.ofNat_le_ofNat
  exact explicitValenceMultiplicity_le_spinSumCube _
    (incidentPlaqIds_length_le_six n indexed.2)

theorem explicitLinkMultiplicityFactor_le_spinProductCube
    (K n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × Z4Link) :
    explicitLinkMultiplicityFactor K n physical indexed ≤
      Q'.ofNat (spinProductCube
        (actualIncidentSpinProduct n physical indexed)) := by
  unfold explicitLinkMultiplicityFactor actualIncidentSpinProduct
  apply Q'.ofNat_le_ofNat
  exact explicitValenceMultiplicity_le_prefixProductCube _
    (incidentPlaqIds_length_le_six n indexed.2)

end YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.oneChannelMultiplicity_le_spinSumCube
#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.twoChannelMultiplicity_le_spinSumCube
#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.threeChannelMultiplicity_le_spinSumCube
#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.explicitValenceMultiplicity_le_spinSumCube
#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.externalPrefixSpinSum_add_one_le_product
#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.explicitValenceMultiplicity_le_prefixProductCube
#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.explicitLinkMultiplicityFactor_le_spinSumCube
#print axioms YMGap.Continuum.Z4SpinDependentLocalMultiplicityBound.explicitLinkMultiplicityFactor_le_spinProductCube
