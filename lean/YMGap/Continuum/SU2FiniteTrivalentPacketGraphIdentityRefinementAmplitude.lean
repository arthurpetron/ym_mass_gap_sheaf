/-
# Packet amplitudes under trivalent identity refinement

The identity refinement projector forces the new segment label to copy the
old segment and fixes the third leg to the vacuum.  Here the new segment is
given the bounded all-ones packet and the third leg the normalized vacuum
packet.  The refined bare and projected amplitudes then equal the original
amplitudes exactly.  Combined with the previously computed graph eigenvalue,
this isolates the sole spectral effect of the subdivision.

Honest scope: this is the pointwise integrand identity.  The two new finite
label sums are not yet collapsed in this module.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude

set_option maxHeartbeats 800000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem q_pow_congr {a b : Q'} (h : a ≈ b) : ∀ n : Nat,
    a ^ n ≈ b ^ n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      rw [Q'.pow_succ, Q'.pow_succ]
      exact q_mul_congr h (q_pow_congr h n)

/-- The finite identity packet: coefficient one on every represented spin. -/
def allOnesPacket (K : Nat) : CharacterPacket K where
  coeff _ := 1

theorem coeffAt_allOnesPacket {K spin : Nat} (hspin : spin < K + 1) :
    coeffAt (allOnesPacket K) spin = 1 := by
  rw [coeffAt_of_lt (allOnesPacket K) hspin]
  rfl

/-- Packet family for the refined graph: normalized vacuum on the third leg,
all-ones identity carrier on the copied segment, and the original family on
all old edges. -/
def identityRefinedPacket {K : Nat} (newEdge vacuumEdge : Nat)
    (P : Nat → CharacterPacket K) : Nat → CharacterPacket K :=
  fun edge => if edge = vacuumEdge then vacuumPacket K
    else if edge = newEdge then allOnesPacket K else P edge

private theorem eliminateLinks_eq_on
    (f g : Nat → Q') : ∀ edges,
    (∀ edge, edge ∈ edges → f edge = g edge) →
      eliminateLinks f edges = eliminateLinks g edges
  | [], _ => rfl
  | edge :: rest, h => by
      have hedge := h edge List.mem_cons_self
      have hrest : ∀ e, e ∈ rest → f e = g e :=
        fun e he => h e (List.mem_cons_of_mem edge he)
      simp only [eliminateLinks]
      rw [hedge, eliminateLinks_eq_on f g rest hrest]

private theorem refinedPacket_eq_on_old_edges {K : Nat}
    (newEdge vacuumEdge : Nat) (P : Nat → CharacterPacket K)
    {edges : List Nat} (hnew : newEdge ∉ edges)
    (hvac : vacuumEdge ∉ edges) :
    ∀ edge, edge ∈ edges →
      identityRefinedPacket newEdge vacuumEdge P edge = P edge := by
  intro edge hmem
  have hneNew : edge ≠ newEdge := by
    intro h
    subst edge
    exact hnew hmem
  have hneVac : edge ≠ vacuumEdge := by
    intro h
    subst edge
    exact hvac hmem
  simp [identityRefinedPacket, hneNew, hneVac]

/-- On the fusion-selected refined labelling, the extra vacuum and identity
coefficients are both one, so the bare amplitude is unchanged. -/
theorem packetGraphBareAmplitude_identity_refinement {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (P : Nat → CharacterPacket K) (label : EdgeLabelling)
    (holdBound : label oldEdge < K + 1)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hnv : newEdge ≠ vacuumEdge) :
    packetGraphBareAmplitude
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedPacket newEdge vacuumEdge P)
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      packetGraphBareAmplitude edges P label := by
  let refined := identityRefinedLabel oldEdge newEdge vacuumEdge label
  have hvacCoord : refined vacuumEdge = 0 :=
    identityRefinedLabel_vacuum oldEdge newEdge vacuumEdge label
  have hnewCoord : refined newEdge = label oldEdge :=
    identityRefinedLabel_new oldEdge newEdge vacuumEdge label hnv
  have hrest : eliminateLinks
      (fun edge => coeffAt
        (identityRefinedPacket newEdge vacuumEdge P edge) (refined edge))
      edges =
      eliminateLinks (fun edge => coeffAt (P edge) (label edge)) edges := by
    apply eliminateLinks_eq_on
    intro edge hmem
    rw [refinedPacket_eq_on_old_edges newEdge vacuumEdge P hnew hvac
      edge hmem]
    change coeffAt (P edge)
        (identityRefinedLabel oldEdge newEdge vacuumEdge label edge) =
      coeffAt (P edge) (label edge)
    rw [SU2FiniteTrivalentPacketGraphIdentityRefinement.identityRefinedLabel_eq_on_old_edges
      oldEdge newEdge vacuumEdge label hnew hvac edge hmem]
  unfold packetGraphBareAmplitude identityRefinedEdges
  change coeffAt (identityRefinedPacket newEdge vacuumEdge P vacuumEdge)
      (refined vacuumEdge) *
    (coeffAt (identityRefinedPacket newEdge vacuumEdge P newEdge)
        (refined newEdge) *
      eliminateLinks
        (fun edge => coeffAt
          (identityRefinedPacket newEdge vacuumEdge P edge) (refined edge))
        edges) ≈
    eliminateLinks (fun edge => coeffAt (P edge) (label edge)) edges
  rw [identityRefinedPacket, if_pos rfl, hvacCoord,
    coeffAt_vacuumPacket, if_pos rfl]
  have hnewNotVac : newEdge ≠ vacuumEdge := hnv
  rw [identityRefinedPacket, if_neg hnewNotVac, if_pos rfl,
    hnewCoord, coeffAt_allOnesPacket holdBound, hrest]
  exact Q'.eqv_trans _
    (1 * eliminateLinks (fun edge => coeffAt (P edge) (label edge)) edges) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))
    (Q'.one_mul_eqv _)

/-- The full gauge/vacuum projected amplitude is unchanged by the interacting
identity refinement. -/
theorem packetGraphProjectedAmplitude_identity_refinement {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (label : EdgeLabelling) (hold : oldEdge ∈ edges)
    (holdBound : label oldEdge < K + 1)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    packetGraphProjectedAmplitude
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P)
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      packetGraphProjectedAmplitude edges vertices P label := by
  let refined := identityRefinedLabel oldEdge newEdge vacuumEdge label
  have hphys := graphPhysicalB_identity_refinement
    oldEdge newEdge vacuumEdge edges vertices label hold hnew hvac
      hno hvo hnv hnewV hvacV
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical edges vertices label
  · have hpRefined : GraphPhysical
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        refined := by
      change graphPhysicalB
          (identityRefinedEdges newEdge vacuumEdge edges)
          (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
          refined = true
      rw [hphys]
      exact hp
    rw [if_pos hpRefined, if_pos hp]
    exact packetGraphBareAmplitude_identity_refinement
      oldEdge newEdge vacuumEdge edges P label holdBound
        hnew hvac hnv
  · have hpRefined : ¬ GraphPhysical
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        refined := by
      intro h
      apply hp
      change graphPhysicalB edges vertices label = true
      rw [← hphys]
      exact h
    rw [if_neg hpRefined, if_neg hp]
    exact Q'.eqv_refl 0

/-- At time zero, the complete projected correlator integrand is pointwise
unchanged under the identity refinement. -/
theorem projectedCorrTerm_identity_refinement_zero {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (label : EdgeLabelling) (hold : oldEdge ∈ edges)
    (holdBound : label oldEdge < K + 1)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    projectedCorrTerm
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) 0
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      projectedCorrTerm edges vertices P 0 label := by
  unfold projectedCorrTerm projectedSquare
  simp only [Q'.pow_zero]
  exact q_mul_congr
    (q_mul_congr
      (packetGraphProjectedAmplitude_identity_refinement
        oldEdge newEdge vacuumEdge edges vertices P label hold holdBound
          hnew hvac hno hvo hnv hnewV hvacV)
      (packetGraphProjectedAmplitude_identity_refinement
        oldEdge newEdge vacuumEdge edges vertices P label hold holdBound
          hnew hvac hno hvo hnv hnewV hvacV))
    (Q'.eqv_refl 1)

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude.coeffAt_allOnesPacket
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude.packetGraphBareAmplitude_identity_refinement
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude.packetGraphProjectedAmplitude_identity_refinement
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude.projectedCorrTerm_identity_refinement_zero
