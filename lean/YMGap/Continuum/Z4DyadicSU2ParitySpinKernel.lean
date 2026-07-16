/-
# SU(2) parity shadow of the cellular dyadic pushforward

Twice-spin SU(2) labels have a canonical mod-two shadow.  This module proves
that the geometric support of odd labels has link-incidence parity equal to
the production `incidentSpinSum`, so nonzero local fusion multiplicity (and,
more strongly, nonzero finite spin-foam weight) forces that support to be
closed.  The cellular dyadic map therefore transports this exact F2 shadow.

The resulting coarse labels are honest bounded cutoff-one face labellings and
define a positive normalized deterministic coefficient kernel.  They are not asserted
to be the physical blocked Yang--Mills law: an explicit cutoff-two fence shows
that distinct bounded fine-spin states have the same parity image.  Recovering
the full spin distribution requires a separate summed-amplitude pushforward
identity, which is not claimed here.
-/

import YMGap.Continuum.Z4DyadicModTwoCellularKernel
import YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection

namespace YMGap.Continuum.Z4DyadicSU2ParitySpinKernel

open scoped List

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4ExplicitExcitationLocalization
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-- The geometric finite-box support of faces carrying an odd SU(2)
twice-spin label.  The numerical face identifier and geometric plaquette
come from the same canonical enumeration entry. -/
def oddPhysicalPlaquettes (n : Nat) (physical : EdgeLabelling) :
    List Z4Plaq :=
  ((enumerate (boxPlaquettes n)).filter fun indexed =>
    decide (physical indexed.1 % 2 = 1)).map Prod.snd

theorem oddPhysicalPlaquettes_nodup (n : Nat) (physical : EdgeLabelling) :
    (oddPhysicalPlaquettes n physical).Nodup := by
  unfold oddPhysicalPlaquettes
  have hfilter :
      (enumerate (boxPlaquettes n)).filter
          (fun indexed => decide (physical indexed.1 % 2 = 1)) <+
        enumerate (boxPlaquettes n) :=
    List.filter_sublist
  have hsub := hfilter.map Prod.snd
  rw [enumerate_map_snd] at hsub
  exact hsub.nodup (boxPlaquettes_nodup n)

theorem faceIncidenceCount_eq_filter_length (ell : Z4Link) :
    ∀ faces : List Z4Plaq,
      YMGap.Continuum.Z4UnitCubeIncidenceParity.faceIncidenceCount ell faces =
        (faces.filter fun p => decide (ell ∈ edgesOf p)).length
  | [] => rfl
  | p :: rest => by
      rw [YMGap.Continuum.Z4UnitCubeIncidenceParity.faceIncidenceCount]
      rw [faceIncidenceCount_eq_filter_length ell rest]
      by_cases hinc : ell ∈ edgesOf p
      · simp [hinc, Nat.add_comm]
      · simp [hinc]

theorem natListSum_mod_two_eq_odd_length : ∀ values : List Nat,
    natListSum values % 2 =
      (values.filter fun value => decide (value % 2 = 1)).length % 2
  | [] => rfl
  | head :: tail => by
      rw [natListSum]
      have ih := natListSum_mod_two_eq_odd_length tail
      have hlt : head % 2 < 2 := Nat.mod_lt head (by omega)
      by_cases hodd : head % 2 = 1
      · simp [hodd]
        omega
      · have heven : head % 2 = 0 := by omega
        simp [hodd]
        omega

private theorem oddPhysicalPlaquettes_incident_length
    (n : Nat) (physical : EdgeLabelling)
    (ell : Z4Link) :
    ((oddPhysicalPlaquettes n physical).filter fun p =>
      decide (ell ∈ edgesOf p)).length =
    (((incidentPlaqIds n ell).map physical).filter fun value =>
      decide (value % 2 = 1)).length := by
  unfold oddPhysicalPlaquettes incidentPlaqIds
  rw [List.filter_map]
  simp only [List.map_map]
  rw [List.filter_map]
  simp only [List.length_map]
  rw [List.filter_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro indexed hindexed
  simpa only [Function.comp_apply] using
    Bool.and_comm (decide (ell ∈ edgesOf indexed.2))
      (decide (physical indexed.1 % 2 = 1))

theorem oddPhysicalPlaquettes_incidenceParity_eq_incidentSpinSum
    (n : Nat) (physical : EdgeLabelling) (ell : Z4Link) :
    YMGap.Continuum.Z4UnitCubeIncidenceParity.faceIncidenceCount ell
        (oddPhysicalPlaquettes n physical) % 2 =
      incidentSpinSum n physical ell % 2 := by
  rw [faceIncidenceCount_eq_filter_length]
  rw [incidentSpinSum]
  rw [natListSum_mod_two_eq_odd_length]
  rw [oddPhysicalPlaquettes_incident_length]

theorem oddPhysicalPlaquettes_subset_box
    {n : Nat} {physical : EdgeLabelling} {p : Z4Plaq}
    (hmem : p ∈ oddPhysicalPlaquettes n physical) :
    p ∈ boxPlaquettes n := by
  unfold oddPhysicalPlaquettes at hmem
  obtain ⟨indexed, hindexed, heq⟩ := List.mem_map.mp hmem
  have hentry := (List.mem_filter.mp hindexed).1
  have hsnd : indexed.2 ∈
      (enumerate (boxPlaquettes n)).map Prod.snd :=
    List.mem_map.mpr ⟨indexed, hentry, rfl⟩
  rw [enumerate_map_snd] at hsnd
  simpa [heq] using hsnd

theorem incidentSpinSum_even_of_nonzero_linkMultiplicity
    {K n i : Nat} {physical : EdgeLabelling} {ell : Z4Link}
    (hnonzero : explicitLinkMultiplicityFactor K n physical (i, ell) ≠ 0) :
    incidentSpinSum n physical ell % 2 = 0 := by
  have hnotodd : incidentSpinSum n physical ell % 2 ≠ 1 := by
    intro hodd
    exact hnonzero
      (explicitLinkMultiplicityFactor_eq_zero_of_odd_incidentSpinSum hodd)
  have hlt : incidentSpinSum n physical ell % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  omega

/-- The production local fusion factor can be nonzero only if the geometric
odd-spin support has even incidence at that link. -/
theorem oddPhysicalPlaquettes_even_at_link_of_nonzero
    {K n i : Nat} {physical : EdgeLabelling} {ell : Z4Link}
    (hnonzero : explicitLinkMultiplicityFactor K n physical (i, ell) ≠ 0) :
    YMGap.Continuum.Z4UnitCubeIncidenceParity.faceIncidenceCount ell
        (oddPhysicalPlaquettes n physical) % 2 = 0 := by
  rw [oddPhysicalPlaquettes_incidenceParity_eq_incidentSpinSum]
  exact incidentSpinSum_even_of_nonzero_linkMultiplicity hnonzero

theorem oddPhysicalPlaquettes_evenFaceIncidence_of_nonzero_fusion
    {K n : Nat} {physical : EdgeLabelling}
    (hnonzero : ∀ ell : Z4Link, ∃ i : Nat,
      explicitLinkMultiplicityFactor K n physical (i, ell) ≠ 0) :
    YMGap.Continuum.Z4DyadicDeterministicSupportKernel.EvenFaceIncidence
      (oddPhysicalPlaquettes n physical) := by
  intro ell
  obtain ⟨i, hi⟩ := hnonzero ell
  exact oddPhysicalPlaquettes_even_at_link_of_nonzero hi

private theorem faceIncidenceCount_eq_zero_of_no_incidence
    (ell : Z4Link) : ∀ faces : List Z4Plaq,
    (∀ p, p ∈ faces → ell ∉ edgesOf p) →
      YMGap.Continuum.Z4UnitCubeIncidenceParity.faceIncidenceCount ell faces = 0
  | [], _ => rfl
  | p :: rest, hnone => by
      have hp : ell ∉ edgesOf p := hnone p List.mem_cons_self
      have hrest : ∀ q, q ∈ rest → ell ∉ edgesOf q := by
        intro q hq
        exact hnone q (List.mem_cons_of_mem p hq)
      simp [YMGap.Continuum.Z4UnitCubeIncidenceParity.faceIncidenceCount,
        hp, faceIncidenceCount_eq_zero_of_no_incidence ell rest hrest]

theorem oddPhysicalPlaquettes_evenFaceIncidence_of_nonzero_weight
    {K n : Nat} {physical : EdgeLabelling}
    (hnonzero : ¬ explicitSpinFoamWeight K n physical ≈ 0) :
    YMGap.Continuum.Z4DyadicDeterministicSupportKernel.EvenFaceIncidence
      (oddPhysicalPlaquettes n physical) := by
  intro ell
  by_cases hlink : ell ∈ distinctBoxLinks n
  · obtain ⟨i, hindexed⟩ := exists_mem_enumerate hlink
    have hnotodd : incidentSpinSum n physical ell % 2 ≠ 1 := by
      intro hodd
      exact hnonzero
        (explicitSpinFoamWeight_eqv_zero_of_odd_incidentSpinSum
          hindexed hodd)
    have hlt : incidentSpinSum n physical ell % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    have hsumzero : incidentSpinSum n physical ell % 2 = 0 := by
      omega
    exact (oddPhysicalPlaquettes_incidenceParity_eq_incidentSpinSum
      n physical ell).trans hsumzero
  · rw [faceIncidenceCount_eq_zero_of_no_incidence]
    intro p hp hinc
    have hpbox := oddPhysicalPlaquettes_subset_box hp
    have hboxLink := boundary_mem_boxLinks hpbox hinc
    have hdistinct : ell ∈ distinctBoxLinks n := by
      simpa [distinctBoxLinks] using hboxLink
    exact hlink hdistinct

/-- The smallest spin-valued coefficient carried by the cellular map: XOR
of fine odd-spin indicators in the exact four-face fibre, represented as the
natural-number label zero or one. -/
def dyadicParitySpinCoefficient (n : Nat) (finePhysical : EdgeLabelling)
    (coarsePlaquette : Z4Plaq) : Nat :=
  (dyadicFacePushforward
    (supportCoefficient (oddPhysicalPlaquettes (2 * n) finePhysical))
    coarsePlaquette).toNat

theorem dyadicParitySpinCoefficient_le_one
    (n : Nat) (finePhysical : EdgeLabelling) (coarsePlaquette : Z4Plaq) :
    dyadicParitySpinCoefficient n finePhysical coarsePlaquette ≤ 1 := by
  unfold dyadicParitySpinCoefficient
  cases dyadicFacePushforward
      (supportCoefficient (oddPhysicalPlaquettes (2 * n) finePhysical))
      coarsePlaquette <;> decide

theorem dyadicParitySpinCoefficient_parity
    (n : Nat) (finePhysical : EdgeLabelling) (coarsePlaquette : Z4Plaq) :
    decide (dyadicParitySpinCoefficient n finePhysical coarsePlaquette % 2 = 1) =
      dyadicFacePushforward
        (supportCoefficient (oddPhysicalPlaquettes (2 * n) finePhysical))
        coarsePlaquette := by
  unfold dyadicParitySpinCoefficient
  cases dyadicFacePushforward
      (supportCoefficient (oddPhysicalPlaquettes (2 * n) finePhysical))
      coarsePlaquette <;> rfl

def coarseOddSpinSupport (n : Nat) (finePhysical : EdgeLabelling) :
    List Z4Plaq :=
  dyadicModTwoPushforwardSupport n
    (oddPhysicalPlaquettes (2 * n) finePhysical)

theorem supportCoefficient_coarseOddSpinSupport
    (n : Nat) (finePhysical : EdgeLabelling) (coarsePlaquette : Z4Plaq) :
    supportCoefficient (coarseOddSpinSupport n finePhysical) coarsePlaquette =
      decide (dyadicParitySpinCoefficient n finePhysical coarsePlaquette % 2 = 1) := by
  rw [dyadicParitySpinCoefficient_parity]
  unfold coarseOddSpinSupport
  exact supportCoefficient_dyadicModTwoPushforwardSupport
    (fun finePlaquette hfine => oddPhysicalPlaquettes_subset_box hfine)
    coarsePlaquette

/-- Canonical numerical coarse-face labelling induced by the parity
coefficient.  It vanishes outside the physical coarse-face identifiers. -/
def coarseParityPhysicalLabelling (n : Nat)
    (finePhysical : EdgeLabelling) : EdgeLabelling :=
  fun coarseId =>
    if coarseId < plaquetteEdgeCount n then
      dyadicParitySpinCoefficient n finePhysical
        (boxPlaquetteAt n coarseId)
    else 0

theorem coarseParityPhysicalLabelling_at_enumerate
    {n coarseId : Nat} {finePhysical : EdgeLabelling}
    {coarsePlaquette : Z4Plaq}
    (hindexed : (coarseId, coarsePlaquette) ∈
      enumerate (boxPlaquettes n)) :
    coarseParityPhysicalLabelling n finePhysical coarseId =
      dyadicParitySpinCoefficient n finePhysical coarsePlaquette := by
  have hlt : coarseId < plaquetteEdgeCount n := by
    unfold plaquetteEdgeCount
    exact YMGap.Continuum.Z4LinkIdentifierFreshness.enumerate_index_lt hindexed
  unfold coarseParityPhysicalLabelling
  rw [if_pos hlt]
  rw [boxPlaquetteAt_eq_of_enumerate hindexed]

theorem coarseParityPhysicalLabelling_mem_cutoff_one
    (n : Nat) (finePhysical : EdgeLabelling) :
    coarseParityPhysicalLabelling n finePhysical ∈
      explicitPhysicalLabellings 1 n := by
  unfold explicitPhysicalLabellings
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    have hlt : edge < plaquetteEdgeCount n := by
      exact List.mem_range.mp hedge
    unfold coarseParityPhysicalLabelling
    rw [if_pos hlt]
    have hle := dyadicParitySpinCoefficient_le_one n finePhysical
      (boxPlaquetteAt n edge)
    omega
  · intro edge hnot
    have hnlt : ¬ edge < plaquetteEdgeCount n := by
      intro hlt
      exact hnot (List.mem_range.mpr hlt)
    simp [coarseParityPhysicalLabelling, hnlt]

theorem coarseOddSpinSupport_evenFaceIncidence_of_nonzero_fusion
    {K n : Nat} {finePhysical : EdgeLabelling}
    (hnonzero : ∀ ell : Z4Link, ∃ i : Nat,
      explicitLinkMultiplicityFactor K (2 * n) finePhysical (i, ell) ≠ 0) :
    YMGap.Continuum.Z4DyadicDeterministicSupportKernel.EvenFaceIncidence
      (coarseOddSpinSupport n finePhysical) := by
  apply dyadicModTwoPushforwardSupport_preserves_evenFaceIncidence
  · intro finePlaquette hfine
    exact oddPhysicalPlaquettes_subset_box hfine
  · exact oddPhysicalPlaquettes_nodup _ _
  · exact oddPhysicalPlaquettes_evenFaceIncidence_of_nonzero_fusion
      hnonzero

theorem coarseOddSpinSupport_evenFaceIncidence_of_nonzero_weight
    {K n : Nat} {finePhysical : EdgeLabelling}
    (hnonzero : ¬ explicitSpinFoamWeight K (2 * n) finePhysical ≈ 0) :
    YMGap.Continuum.Z4DyadicDeterministicSupportKernel.EvenFaceIncidence
      (coarseOddSpinSupport n finePhysical) := by
  apply dyadicModTwoPushforwardSupport_preserves_evenFaceIncidence
  · intro finePlaquette hfine
    exact oddPhysicalPlaquettes_subset_box hfine
  · exact oddPhysicalPlaquettes_nodup _ _
  · exact oddPhysicalPlaquettes_evenFaceIncidence_of_nonzero_weight
      hnonzero

open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-- Deterministic coefficient kernel onto the parity label.  This is a
kernel for the two-label F2 shadow only, not a Yang--Mills measure
pushforward. -/
def dyadicParitySpinKernel (n : Nat) (finePhysical : EdgeLabelling)
    (coarsePlaquette : Z4Plaq) (coarseSpin : Nat) : Q' :=
  if coarseSpin =
      dyadicParitySpinCoefficient n finePhysical coarsePlaquette then 1 else 0

theorem dyadicParitySpinKernel_nonnegative
    (n : Nat) (finePhysical : EdgeLabelling)
    (coarsePlaquette : Z4Plaq) (coarseSpin : Nat) :
    (0 : Q') ≤ dyadicParitySpinKernel n finePhysical coarsePlaquette coarseSpin := by
  unfold dyadicParitySpinKernel
  by_cases h : coarseSpin =
      dyadicParitySpinCoefficient n finePhysical coarsePlaquette
  · rw [if_pos h]
    exact Q'.zero_le_one
  · rw [if_neg h]
    exact Q'.le_refl' 0

theorem dyadicParitySpinKernel_on_image
    (n : Nat) (finePhysical : EdgeLabelling)
    (coarsePlaquette : Z4Plaq) :
    dyadicParitySpinKernel n finePhysical coarsePlaquette
      (dyadicParitySpinCoefficient n finePhysical coarsePlaquette) = 1 := by
  simp [dyadicParitySpinKernel]

theorem dyadicParitySpinKernel_off_image
    {n coarseSpin : Nat} {finePhysical : EdgeLabelling}
    {coarsePlaquette : Z4Plaq}
    (hne : coarseSpin ≠
      dyadicParitySpinCoefficient n finePhysical coarsePlaquette) :
    dyadicParitySpinKernel n finePhysical coarsePlaquette coarseSpin = 0 := by
  simp [dyadicParitySpinKernel, hne]

theorem dyadicParitySpinKernel_row_normalized
    (n : Nat) (finePhysical : EdgeLabelling)
    (coarsePlaquette : Z4Plaq) :
    listQSum (dyadicParitySpinKernel n finePhysical coarsePlaquette) [0, 1]
      ≈ 1 := by
  have hle := dyadicParitySpinCoefficient_le_one
    n finePhysical coarsePlaquette
  have hcases : dyadicParitySpinCoefficient n finePhysical coarsePlaquette = 0 ∨
      dyadicParitySpinCoefficient n finePhysical coarsePlaquette = 1 := by
    omega
  rcases hcases with hzero | hone
  · simp [dyadicParitySpinKernel, hzero, listQSum]
    exact Q'.eqv_of_eq (by decide)
  · simp [dyadicParitySpinKernel, hone, listQSum]
    exact Q'.eqv_of_eq (by decide)

def evenTwoPhysical : EdgeLabelling :=
  setEdgeLabel zeroEdgeLabelling 0 2

theorem zeroEdgeLabelling_ne_evenTwoPhysical :
    zeroEdgeLabelling ≠ evenTwoPhysical := by
  intro hequal
  have hzero := congrArg (fun label : EdgeLabelling => label 0) hequal
  simp [zeroEdgeLabelling, evenTwoPhysical, setEdgeLabel] at hzero

/-- Equal parity does not retain the SU(2) fusion range: labels zero and two
have the same parity, but replacing the vacuum output of `0 ⊗ 0` by label
two changes the exact fusion guard from true to false. -/
theorem parity_does_not_determine_fusion_guard :
    decide (0 % 2 = 1) = decide (2 % 2 = 1) ∧
      YMGap.Continuum.BondMovingStep.fusionOK 0 0 0 = true ∧
      YMGap.Continuum.BondMovingStep.fusionOK 0 0 2 = false := by
  decide

theorem zero_mem_physicalFaceEdges_succ (n : Nat) :
    0 ∈ physicalFaceEdges (n + 1) := by
  unfold physicalFaceEdges plaquetteEdgeCount
  apply List.mem_range.mpr
  rw [boxPlaquettes_length]
  exact Nat.mul_pos
    (Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (by omega) (by omega))
        (by omega))
      (by omega))
    (by decide)

theorem zeroEdgeLabelling_mem_cutoff_two_succ (n : Nat) :
    zeroEdgeLabelling ∈ explicitPhysicalLabellings 2 (n + 1) := by
  unfold explicitPhysicalLabellings
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    simp [zeroEdgeLabelling]
  · intro edge hnot
    rfl

theorem evenTwoPhysical_mem_cutoff_two_succ (n : Nat) :
    evenTwoPhysical ∈ explicitPhysicalLabellings 2 (n + 1) := by
  unfold explicitPhysicalLabellings
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    by_cases hzero : edge = 0
    · simp [evenTwoPhysical, setEdgeLabel, hzero]
    · simp [evenTwoPhysical, setEdgeLabel, zeroEdgeLabelling, hzero]
  · intro edge hnot
    have hne : edge ≠ 0 := by
      intro hequal
      subst edge
      exact hnot (zero_mem_physicalFaceEdges_succ n)
    simp [evenTwoPhysical, setEdgeLabel, zeroEdgeLabelling, hne]

theorem oddPhysicalPlaquettes_evenTwo_eq_zero (n : Nat) :
    oddPhysicalPlaquettes n evenTwoPhysical =
      oddPhysicalPlaquettes n zeroEdgeLabelling := by
  unfold oddPhysicalPlaquettes
  congr 1
  apply List.filter_congr
  intro indexed hindexed
  by_cases hzero : indexed.1 = 0
  · simp [evenTwoPhysical, setEdgeLabel, zeroEdgeLabelling, hzero]
  · simp [evenTwoPhysical, setEdgeLabel, zeroEdgeLabelling, hzero]

theorem dyadicParitySpinCoefficient_information_loss
    (n : Nat) (coarsePlaquette : Z4Plaq) :
    dyadicParitySpinCoefficient n evenTwoPhysical coarsePlaquette =
      dyadicParitySpinCoefficient n zeroEdgeLabelling coarsePlaquette := by
  unfold dyadicParitySpinCoefficient
  rw [oddPhysicalPlaquettes_evenTwo_eq_zero]

theorem coarseParityPhysicalLabelling_information_loss (n : Nat) :
    coarseParityPhysicalLabelling n evenTwoPhysical =
      coarseParityPhysicalLabelling n zeroEdgeLabelling := by
  funext coarseId
  unfold coarseParityPhysicalLabelling
  by_cases hlt : coarseId < plaquetteEdgeCount n
  · rw [if_pos hlt, if_pos hlt]
    exact dyadicParitySpinCoefficient_information_loss n
      (boxPlaquetteAt n coarseId)
  · rw [if_neg hlt, if_neg hlt]

theorem coarseParityPhysicalLabelling_not_injective (n : Nat) :
    ¬ Function.Injective (coarseParityPhysicalLabelling n) := by
  intro hinjective
  exact zeroEdgeLabelling_ne_evenTwoPhysical
    (hinjective (coarseParityPhysicalLabelling_information_loss n).symm)

theorem boundedSpin_information_loss_fence (n : Nat) :
    zeroEdgeLabelling ∈
        explicitPhysicalLabellings 2 (2 * (n + 1)) ∧
      evenTwoPhysical ∈
        explicitPhysicalLabellings 2 (2 * (n + 1)) ∧
      zeroEdgeLabelling ≠ evenTwoPhysical ∧
      coarseParityPhysicalLabelling (n + 1) zeroEdgeLabelling =
        coarseParityPhysicalLabelling (n + 1) evenTwoPhysical := by
  have hzero := zeroEdgeLabelling_mem_cutoff_two_succ (2 * n + 1)
  have htwo := evenTwoPhysical_mem_cutoff_two_succ (2 * n + 1)
  have hvolume : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  rw [hvolume] at hzero htwo
  exact ⟨hzero, htwo, zeroEdgeLabelling_ne_evenTwoPhysical,
    (coarseParityPhysicalLabelling_information_loss (n + 1)).symm⟩

theorem dyadicParitySpinKernel_information_loss
    (n : Nat) (coarsePlaquette : Z4Plaq) (coarseSpin : Nat) :
    dyadicParitySpinKernel n evenTwoPhysical coarsePlaquette coarseSpin =
      dyadicParitySpinKernel n zeroEdgeLabelling
        coarsePlaquette coarseSpin := by
  unfold dyadicParitySpinKernel
  rw [dyadicParitySpinCoefficient_information_loss]

#print axioms incidentSpinSum_even_of_nonzero_linkMultiplicity
#print axioms oddPhysicalPlaquettes_incidenceParity_eq_incidentSpinSum
#print axioms oddPhysicalPlaquettes_even_at_link_of_nonzero
#print axioms oddPhysicalPlaquettes_evenFaceIncidence_of_nonzero_weight
#print axioms dyadicParitySpinCoefficient_parity
#print axioms supportCoefficient_coarseOddSpinSupport
#print axioms coarseParityPhysicalLabelling_at_enumerate
#print axioms coarseParityPhysicalLabelling_mem_cutoff_one
#print axioms coarseOddSpinSupport_evenFaceIncidence_of_nonzero_fusion
#print axioms coarseOddSpinSupport_evenFaceIncidence_of_nonzero_weight
#print axioms dyadicParitySpinKernel_nonnegative
#print axioms dyadicParitySpinKernel_on_image
#print axioms dyadicParitySpinKernel_off_image
#print axioms dyadicParitySpinKernel_row_normalized
#print axioms zeroEdgeLabelling_ne_evenTwoPhysical
#print axioms parity_does_not_determine_fusion_guard
#print axioms zeroEdgeLabelling_mem_cutoff_two_succ
#print axioms evenTwoPhysical_mem_cutoff_two_succ
#print axioms dyadicParitySpinCoefficient_information_loss
#print axioms coarseParityPhysicalLabelling_not_injective
#print axioms boundedSpin_information_loss_fence
#print axioms dyadicParitySpinKernel_information_loss

end YMGap.Continuum.Z4DyadicSU2ParitySpinKernel
