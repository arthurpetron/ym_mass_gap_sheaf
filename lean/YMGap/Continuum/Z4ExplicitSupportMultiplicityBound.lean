/-
# Support-sized majorant for localized fusion multiplicities

The exact localized link product has at most four factors per excited
plaquette.  This file combines that incidence theorem with the literal
one-, two-, and three-channel cardinality bounds.  The resulting majorant is
volume independent, but deliberately crude: it retains a cutoff-dependent
cubic worst-case factor at each touched link.  Its failure or success as a
cluster-expansion constant can therefore be checked explicitly rather than
hidden in bookkeeping.
-/

import YMGap.Continuum.Z4ExplicitSupportFaceBound

namespace YMGap.Continuum.Z4ExplicitSupportMultiplicityBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

/-! ## 1. A uniform cubic cardinality envelope for every local valence -/

def localMultiplicityNatBound (cutoff : Nat) : Nat :=
  (cutoff + 1) * ((cutoff + 1) * (cutoff + 1))

private theorem one_le_localMultiplicityNatBound (cutoff : Nat) :
    1 ≤ localMultiplicityNatBound cutoff := by
  unfold localMultiplicityNatBound
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos cutoff)
      (Nat.mul_pos (Nat.succ_pos cutoff) (Nat.succ_pos cutoff))))

private theorem linear_le_localMultiplicityNatBound (cutoff : Nat) :
    cutoff + 1 ≤ localMultiplicityNatBound cutoff := by
  unfold localMultiplicityNatBound
  exact Nat.le_mul_of_pos_right (cutoff + 1)
    (Nat.mul_pos (Nat.succ_pos cutoff) (Nat.succ_pos cutoff))

private theorem quadratic_le_localMultiplicityNatBound (cutoff : Nat) :
    (cutoff + 1) * (cutoff + 1) ≤ localMultiplicityNatBound cutoff := by
  unfold localMultiplicityNatBound
  have hlinear : cutoff + 1 ≤ (cutoff + 1) * (cutoff + 1) :=
    Nat.le_mul_of_pos_right (cutoff + 1) (Nat.succ_pos cutoff)
  exact Nat.mul_le_mul_left (cutoff + 1) hlinear

private theorem boolMultiplicity_le_one (allowed : Bool) :
    boolMultiplicity allowed ≤ 1 := by
  cases allowed <;> decide

theorem explicitValenceMultiplicity_le_cubic
    {cutoff degree : Nat} (external : EdgeLabelling)
    (hdegree : degree ≤ linkIncidenceBound) :
    explicitValenceMultiplicity cutoff degree external ≤
      localMultiplicityNatBound cutoff := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_le_localMultiplicityNatBound cutoff
  · exact Nat.le_trans
      (oneValentMultiplicity_le cutoff (external 0))
      (linear_le_localMultiplicityNatBound cutoff)
  · exact Nat.le_trans
      (twoValentMultiplicity_le cutoff (external 0) (external 1))
      (linear_le_localMultiplicityNatBound cutoff)
  · exact Nat.le_trans
      (boolMultiplicity_le_one _)
      (one_le_localMultiplicityNatBound cutoff)
  · exact Nat.le_trans
      (oneChannelMultiplicity_le cutoff
        (external 0) (external 1) (external 2) (external 3))
      (linear_le_localMultiplicityNatBound cutoff)
  · exact Nat.le_trans
      (twoChannelMultiplicity_le cutoff
        (external 0) (external 1) (external 2) (external 3) (external 4))
      (quadratic_le_localMultiplicityNatBound cutoff)
  · exact threeChannelMultiplicity_le cutoff
      (external 0) (external 1) (external 2) (external 3) (external 4)
        (external 5)

def linkMultiplicityBound (K : Nat) : Q' :=
  Q'.ofNat (localMultiplicityNatBound (linkAuxiliaryCutoff K))

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

theorem one_le_linkMultiplicityBound (K : Nat) :
    (1 : Q') ≤ linkMultiplicityBound K := by
  change Q'.ofNat 1 ≤
    Q'.ofNat (localMultiplicityNatBound (linkAuxiliaryCutoff K))
  exact Q'.ofNat_le_ofNat
    (one_le_localMultiplicityNatBound (linkAuxiliaryCutoff K))

theorem explicitLinkMultiplicityFactor_le_bound
    (K n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × YMGap.Continuum.ClusterCount4DProgress.Z4Link) :
    explicitLinkMultiplicityFactor K n physical indexed ≤
      linkMultiplicityBound K := by
  unfold explicitLinkMultiplicityFactor linkMultiplicityBound
  apply Q'.ofNat_le_ofNat
  exact explicitValenceMultiplicity_le_cubic _
    (incidentPlaqIds_length_le_six n indexed.2)

/-! ## 2. Product and exponent bounds -/

theorem explicitLinkMultiplicityProduct_le_pow
    (K n : Nat) (physical : EdgeLabelling) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link),
      explicitLinkMultiplicityProduct K n physical links ≤
        linkMultiplicityBound K ^ links.length
  | [] => Q'.le_refl' 1
  | indexed :: rest => by
      change explicitLinkMultiplicityFactor K n physical indexed *
          explicitLinkMultiplicityProduct K n physical rest ≤
        linkMultiplicityBound K ^ (rest.length + 1)
      rw [Q'.pow_succ]
      have hrest0 : (0 : Q') ≤
          explicitLinkMultiplicityProduct K n physical rest :=
        explicitLinkMultiplicityProduct_nonnegative K n physical rest
      have hbound0 : (0 : Q') ≤ linkMultiplicityBound K :=
        Q'.le_trans' _ _ _ Q'.zero_le_one
          (one_le_linkMultiplicityBound K)
      have hfirst : explicitLinkMultiplicityFactor K n physical indexed *
          explicitLinkMultiplicityProduct K n physical rest ≤
        linkMultiplicityBound K *
          explicitLinkMultiplicityProduct K n physical rest :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (explicitLinkMultiplicityFactor_le_bound K n physical indexed)
          hrest0
      have hsecond : linkMultiplicityBound K *
          explicitLinkMultiplicityProduct K n physical rest ≤
        linkMultiplicityBound K * linkMultiplicityBound K ^ rest.length :=
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (explicitLinkMultiplicityProduct_le_pow K n physical rest)
          hbound0
      exact Q'.le_trans' _ _ _ hfirst hsecond

private theorem qpow_le_succ {B : Q'} (hB : (1 : Q') ≤ B)
    (s : Nat) : B ^ s ≤ B ^ (s + 1) := by
  have hB0 : (0 : Q') ≤ B := Q'.le_trans' _ _ _ Q'.zero_le_one hB
  show B ^ s ≤ B * B ^ s
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (B ^ s))) ?_
  exact Q'.mul_le_mul_of_nonneg_right 1 B (B ^ s) hB
    (Q'.pow_nonneg B hB0 s)

private theorem qpow_add_le {B : Q'} (hB : (1 : Q') ≤ B)
    (s : Nat) : ∀ d, B ^ s ≤ B ^ (s + d)
  | 0 => Q'.le_refl' _
  | d + 1 => by
      have hindex : s + (d + 1) = (s + d) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _ (qpow_add_le hB s d)
        (qpow_le_succ hB (s + d))

private theorem qpow_mono_exp {B : Q'} (hB : (1 : Q') ≤ B)
    {s t : Nat} (hst : s ≤ t) : B ^ s ≤ B ^ t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact qpow_add_le hB s d

theorem localizedLinkMultiplicityProduct_le_supportPow
    (K n : Nat) (physical : EdgeLabelling) :
    explicitLinkMultiplicityProduct K n physical
        ((enumerate (distinctBoxLinks n)).filter
          (linkTouchesExcitationB n physical)) ≤
      linkMultiplicityBound K ^
        ((excitedPlaquetteEntries n physical).length * 4) := by
  have hproduct := explicitLinkMultiplicityProduct_le_pow K n physical
    ((enumerate (distinctBoxLinks n)).filter
      (linkTouchesExcitationB n physical))
  have hcount := touchedIndexedLinks_length_le n physical
  unfold touchedIndexedLinks at hcount
  exact Q'.le_trans' _ _ _ hproduct
    (qpow_mono_exp (one_le_linkMultiplicityBound K) hcount)

/-! ## 3. A complete support-sized weight majorant -/

theorem localizedSpinFoamWeight_le_supportMajorant
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings K n) :
    localizedSpinFoamWeight K n physical ≤
      quarter ^ (excitedPlaquetteEntries n physical).length *
        linkMultiplicityBound K ^
          ((excitedPlaquetteEntries n physical).length * 4) := by
  unfold localizedSpinFoamWeight
  have hface := explicitPhysicalFaceFactor_le_entryPow hphysical
  have hlink := localizedLinkMultiplicityProduct_le_supportPow K n physical
  have hface0 : (0 : Q') ≤ explicitPhysicalFaceFactor K n physical :=
    explicitPhysicalFaceFactor_nonnegative K n physical
  have hlink0 : (0 : Q') ≤ explicitLinkMultiplicityProduct K n physical
      ((enumerate (distinctBoxLinks n)).filter
        (linkTouchesExcitationB n physical)) :=
    explicitLinkMultiplicityProduct_nonnegative K n physical _
  have hquarterPow0 : (0 : Q') ≤
      quarter ^ (excitedPlaquetteEntries n physical).length :=
    Q'.pow_nonneg quarter (by decide) _
  have hfirst : explicitPhysicalFaceFactor K n physical *
      explicitLinkMultiplicityProduct K n physical
        ((enumerate (distinctBoxLinks n)).filter
          (linkTouchesExcitationB n physical)) ≤
    quarter ^ (excitedPlaquetteEntries n physical).length *
      explicitLinkMultiplicityProduct K n physical
        ((enumerate (distinctBoxLinks n)).filter
          (linkTouchesExcitationB n physical)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hface hlink0
  have hsecond : quarter ^ (excitedPlaquetteEntries n physical).length *
      explicitLinkMultiplicityProduct K n physical
        ((enumerate (distinctBoxLinks n)).filter
          (linkTouchesExcitationB n physical)) ≤
    quarter ^ (excitedPlaquetteEntries n physical).length *
      linkMultiplicityBound K ^
        ((excitedPlaquetteEntries n physical).length * 4) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hlink hquarterPow0
  exact Q'.le_trans' _ _ _ hfirst hsecond

end YMGap.Continuum.Z4ExplicitSupportMultiplicityBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitSupportMultiplicityBound.explicitValenceMultiplicity_le_cubic
#print axioms YMGap.Continuum.Z4ExplicitSupportMultiplicityBound.explicitLinkMultiplicityFactor_le_bound
#print axioms YMGap.Continuum.Z4ExplicitSupportMultiplicityBound.explicitLinkMultiplicityProduct_le_pow
#print axioms YMGap.Continuum.Z4ExplicitSupportMultiplicityBound.localizedLinkMultiplicityProduct_le_supportPow
#print axioms YMGap.Continuum.Z4ExplicitSupportMultiplicityBound.localizedSpinFoamWeight_le_supportMajorant
