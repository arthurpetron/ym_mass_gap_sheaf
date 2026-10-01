/-
# Actual passive-channel first order against the SAME original variance

The original positive-depth terminal source is projected over the fringe,
then dressed by the unchanged passive heat channels. A local source band
and exact spectator factorization prove

  l^2*A_ch <= 12*u^2*Z*Var_original.

The coefficient depends on nome and the complete family's link-list size,
not on full width, late cutoff or positive terminal depth. All signed and
repeated faces stay in one square. This is a CHANNEL first-order estimate,
not a volume-free bound on the old bare-source first order.

The original energy consumer retains the complete signed channel Taylor
remainder, including actual finite-cutoff omitted modes. No scaling-small
rate, continuum survival, physical mass, full QFT or every-group result is
asserted. No new analytic hypothesis is supplied to obtain the finite bound.
-/

import YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalBand
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyPassiveCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition (faceSlots)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyLocalBand
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
  (spatialSpan_fringe_independent_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalSourceBounds
  (projectedSource_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported oddCentered_independent centered_source_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBareHaar
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyPassiveCancellation
  (padded_family_energy_eq_channels)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem project_smul (ids : List Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (familyProject ids (polySmul c p))
      (polySmul c (familyProject ids p)) :=
  (familyProject_congr ids (cap_mul_left c p).symm).trans
    ((familyProject_mul_of_independent ids (cap c) p
      (fun i _ => quaternionBlockIndependent_polySmul c
        (quaternionBlockIndependent_polyOne i))).trans (cap_mul_left c _))

private theorem familySlots_to_link (width : Nat) :
    ∀ (qs : List Z4Plaq) (i : Nat), i ∈ familySlots width qs →
      ∃ l, l ∈ familyLinks qs ∧ i = (baseLinks width).idxOf l
  | [], _, hi => False.elim (List.not_mem_nil hi)
  | face::qs, i, hi => by
      rcases List.mem_append.mp hi with hface | hrest
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hface
        exact ⟨l, List.mem_append.mpr (Or.inl hl), rfl⟩
      · obtain ⟨l, hl, he⟩ := familySlots_to_link width qs i hrest
        exact ⟨l, List.mem_append.mpr (Or.inr hl), he⟩

/-- The original common spectator, projected by the SAME fringe schedule. -/
def projectedFamilySpectator (w : Q') (K width n : Nat) (qs : List Z4Plaq) : RatPoly :=
  familyProject (fringeBlocks width) (familySpectator w K width n qs)

theorem projectedFamilySpectator_outside_passive {base width : Nat}
    (hwidth : base < width) (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) (w : Q') (K n : Nat) :
    ∀ i, i < N width → i ∉ familySpectatorBlocks width qs →
      QuaternionBlockIndependent i (projectedFamilySpectator w K width n qs) := by
  intro i hi hn
  have hmem : i ∈ familySpectatorBlocks width qs ++ familyObservableBlocks width qs :=
    (familySpectator_observable_cover width qs).mem_iff.mpr (List.mem_range.mpr hi)
  have hob : i ∈ familyObservableBlocks width qs :=
    (List.mem_append.mp hmem).resolve_left hn
  have hslot : i ∈ familySlots width qs := of_decide_eq_true (List.mem_filter.mp hob).2
  obtain ⟨l, hl, he⟩ := familySlots_to_link width qs i hslot
  subst i
  exact familyProject_preserves_independent (fringeBlocks width)
    (familySpectator_independent hwidth qs hqs w K n l hl)

/-- The supplied size-only lower band survives actual fringe integration. -/
def projectedFamily_lowerCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (qs : List Z4Plaq) :
    Certificate (N width) (polyAdd
      (projectedEndpointSource w K width (terminalMessage w K width (n+1)))
      (polyNeg (polySmul (localLower w (4*qs.length))
        (projectedFamilySpectator w K width n qs)))) := by
  let a := familyEndpoint w K width n
  let R := familySpectator w K width n qs
  let l := localLower w (4*qs.length)
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1))
  have hR := familySpectator_supported w K width n qs
  have C := endpoint_localLowerCertificate hw0 hw1 K width hK n (familyLinks qs)
    (4*qs.length) (Nat.le_of_eq (familyLinks_length qs))
  have CP := familyProject_certificate (N width) (fringeBlocks width) (fringeBlocks_lt width)
    (supported_add ha (support_neg (polySmul_supported hR l))) C
  have he : RatPolyCoeffEqv
      (familyProject (fringeBlocks width) (polyAdd a (polyNeg (polySmul l R))))
      (polyAdd (familyProject (fringeBlocks width) a)
        (polyNeg (polySmul l (familyProject (fringeBlocks width) R)))) := by
    rw [familyProject_add]
    exact (RatPolyCoeffEqv.refl _).add ((familyProject_neg _ _).trans
      (RatPolyCoeffEqv.neg (project_smul _ l R)))
  exact .ofCoeff he.symm CP

/-- The upper band retains the identical spectator and original heat nome. -/
def projectedFamily_upperCertificate {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n : Nat) (qs : List Z4Plaq) :
    Certificate (N width) (polyAdd
      (polySmul (localUpper w (4*qs.length)) (projectedFamilySpectator w K width n qs))
      (polyNeg (projectedEndpointSource w K width (terminalMessage w K width (n+1))))) := by
  let a := familyEndpoint w K width n
  let R := familySpectator w K width n qs
  let u := localUpper w (4*qs.length)
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width (n+1))
  have hR := familySpectator_supported w K width n qs
  have C := endpoint_localUpperCertificate hw0 hw1 K width hK n (familyLinks qs)
    (4*qs.length) (Nat.le_of_eq (familyLinks_length qs))
  have CP := familyProject_certificate (N width) (fringeBlocks width) (fringeBlocks_lt width)
    (supported_add (polySmul_supported hR u) (support_neg ha)) C
  have he : RatPolyCoeffEqv
      (familyProject (fringeBlocks width) (polyAdd (polySmul u R) (polyNeg a)))
      (polyAdd (polySmul u (familyProject (fringeBlocks width) R))
        (polyNeg (familyProject (fringeBlocks width) a))) := by
    rw [familyProject_add]
    exact (project_smul _ u R).add (familyProject_neg _ a)
  exact .ofCoeff he.symm CP

/-- The first order of the actual channel Taylor expansion, on the COMPLETE
signed family. This is not the old raw first order of the unchannelized source. -/
def familyChannelFirstOrder (w : Q') (K width depth : Nat)
    (c : Z4Plaq → Q') (qs : List Z4Plaq) : Q' :=
  let f := spatialSpan width c qs
  channelSquare (N width) w K (familySpectatorBlocks width qs)
    (projectedEndpointSource w K width (terminalMessage w K width depth))
    (activeGamma (List.range (N width)) f f)

/-- No source, variance, or channel mass is inverted. The SAME original
mean and partition appear in the final moment. Scalar constants charge only
nome and the complete family footprint, not full volume or positive depth. -/
theorem family_channel_firstOrder_variance_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    let f := spatialSpan width c qs
    let l := localLower w (4*qs.length)
    let u := localUpper w (4*qs.length)
    (l*l)*familyChannelFirstOrder w K width (n+1) c qs ≤
      (12*(u*u))*(oddMass w K width (n+1) *
        oddVariance hw0 hw1 K width hK (n+1) f) := by
  dsimp only
  let f := spatialSpan width c qs
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  let R := projectedFamilySpectator w K width n qs
  let ids := familySpectatorBlocks width qs
  let active := familyObservableBlocks width qs
  let psi := oddCentered hw0 hw1 K width hK (n+1) f
  let G := activeGamma (List.range (N width)) f f
  let e := familyProject ids G
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  let M := channelMass (N width) w K ids R
  let V := oddMass w K width (n+1) * oddVariance hw0 hw1 K width hK (n+1) f
  let B := sourceMoment (N width) w K (List.range (N width)) R (polyMul psi psi)
  let A := familyChannelFirstOrder w K width (n+1) c qs
  have hids := familySpectatorBlocks_lt width qs
  have hnd := familySpectatorBlocks_nodup width qs
  have hf := spatialSpan_supported width c qs
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width)
        (terminalMessage_supported w K width (n+1)))
  have hR : SupportedQuaternionBlocks (N width) R :=
    familyProject_supported _ (familySpectator_supported w K width n qs)
  have Q := projectedSource_certificate hw0 hw1 K width hK n
  have CR := familyProject_certificate (N width) (fringeBlocks width) (fringeBlocks_lt width)
    (familySpectator_supported w K width n qs)
    (familySpectator_certificate hw0 hw1 K width hK n qs)
  have hRi := projectedFamilySpectator_outside_passive hwidth qs hqs w K n
  have hl : (0 : Q') ≤ l := Q'.le_of_lt (localLower_positive hw0 hw1 _)
  have hu : (0 : Q') ≤ u := Q'.le_of_lt (localUpper_positive hw0 hw1 _)
  have hG := activeGamma_supported (List.range (N width))
    (fun i hi => List.mem_range.mp hi) hf hf
  have CG := activeGamma_squareCertificate (List.range (N width))
    (fun i hi => List.mem_range.mp hi) hf
  have he : SupportedQuaternionBlocks (N width) e := familyProject_supported ids hG
  have CE := familyProject_certificate (N width) ids hids hG CG
  have hei : ∀ i, i ∈ ids → QuaternionBlockIndependent i e :=
    familyProject_independent ids G
  have hpsi := oddCentered_supported hw0 hw1 K width hK (n+1) hf
  have hpsii : ∀ i, i ∈ ids → QuaternionBlockIndependent i psi := fun i hi =>
    oddCentered_independent hw0 hw1 K width hK (n+1) i
      (spatialSpan_familySpectator_independent width c qs i hi)
  have hM : (0 : Q') ≤ M :=
    channelMass_nonnegative (N width) (Q'.le_of_lt hw0) K ids hids R hR
  have hupper := productChannels_familyProject_positiveWeighted_square_mono
    (N width) hw0 hw1 K hK ids hnd hids q (polySmul u R) e hq
    (polySmul_supported hR u) he Q (CR.smul u hu) CE
    (projectedFamily_upperCertificate hw0 hw1 K width hK n qs) hei
  have hscale := productChannels_familyProject_weighted_square_smul
    (N width) w K ids hnd hids R e hR he hei u
  have hA : A ≤ (u*u)*channelSquare (N width) w K ids R e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (channelSquare_project_weight (N width) w K ids hids q G))
      (Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv hscale))
  have hfactor := channelSquare_factor (N width) w K ids hids R e hR he hRi
  have hbare : H (N width) e ≤ 12*H (N width) (polyMul psi psi) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (familyProject_mean (N width) ids hids G))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv
        (family_gamma_square width c qs
          (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp))))
        (Q'.mul_le_mul_of_nonneg_left _ _ 12
          (family_shifted_square_ge width c qs
            (fun p hp => spatialFaces_mono (Nat.le_of_lt hwidth) (hqs p hp)) _)
          (by decide)))
  have hB := spectator_sourceMoment_factor (N width) w K active ids
    (familyObservableBlocks_lt width qs) hids (familySpectator_not_observable width qs)
    (familySpectator_observable_cover width qs) R (polyMul psi psi) hR
    (supported_polyMul hpsi hpsi) hRi
    (fun i hi => quaternionBlockIndependent_polyMul (hpsii i hi) (hpsii i hi))
  have hcompare : channelSquare (N width) w K ids R e ≤ 12*B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ M hbare hM)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.const 12) (.var 1)))
            (.mul (.const 12) (.mul (.var 0) (.var 1))) (by decide)
            (fun | 0 => M | _ => H (N width) (polyMul psi psi)))
          (Q'.mul_eqv_congr_left 12 _ _ hB.symm))))
  have hA' : A ≤ (u*u)*(12*B) :=
    Q'.le_trans' _ _ _ hA (Q'.mul_le_mul_of_nonneg_left _ _ (u*u) hcompare
      (SumOfSquares.q_mul_self_nonneg u))
  have hlower0 := sourceMoment_square_mono hw0 hw1 K hK (List.range (N width))
    (fun i hi => List.mem_range.mp hi) (polySmul l R) q psi
    (polySmul_supported hR l) hq hpsi (CR.smul l hl) Q
    (projectedFamily_lowerCertificate hw0 hw1 K width hK n qs)
  have hV := centered_source_square hw0 hw1 K width hK (n+1) hf
    (spatialSpan_fringe_independent_after_padding hwidth c qs hqs)
  have hlower : (l*l)*B ≤ V :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv
      (sourceMoment_smul (N width) w K (List.range (N width)) R (polyMul psi psi) l))
      (Q'.le_trans' _ _ _ hlower0 (Q'.le_of_eqv hV))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (l*l) hA'
    (SumOfSquares.q_mul_self_nonneg l)
  have hreshape : (l*l)*((u*u)*(12*B)) ≈ (12*(u*u))*((l*l)*B) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.const 12) (.var 2))))
      (.mul (.mul (.const 12) (.var 1)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => l*l | 1 => u*u | _ => B)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreshape)
      (Q'.mul_le_mul_of_nonneg_left _ _ (12*(u*u)) hlower
        (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg u))))

/-- Computed coefficient: nome and family size only. It is not asserted
bounded as coupling changes or as the observable footprint grows. -/
def channelFirstOrderVarianceConstant {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) : Q' :=
  (12*(localUpper w (4*size)*localUpper w (4*size))) *
    Q'.recipPos (localLower w (4*size)*localLower w (4*size))
      (Q'.mul_pos (localLower_positive hw0 hw1 _) (localLower_positive hw0 hw1 _))

theorem channelFirstOrderVarianceConstant_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') < channelFirstOrderVarianceConstant hw0 hw1 size :=
  Q'.mul_pos (Q'.mul_pos (by decide)
    (Q'.mul_pos (localUpper_positive hw0 hw1 _) (localUpper_positive hw0 hw1 _)))
    (Q'.recipPos_pos _ _)

theorem family_channel_firstOrder_variance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (c : Z4Plaq → Q') (qs : List Z4Plaq)
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces base) :
    familyChannelFirstOrder w K width (n+1) c qs ≤
      channelFirstOrderVarianceConstant hw0 hw1 qs.length *
        (oddMass w K width (n+1) *
          oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width c qs)) := by
  let l := localLower w (4*qs.length)
  let u := localUpper w (4*qs.length)
  let L := l*l
  let a := Q'.recipPos L
    (Q'.mul_pos (localLower_positive hw0 hw1 _) (localLower_positive hw0 hw1 _))
  let A := familyChannelFirstOrder w K width (n+1) c qs
  let V := oddMass w K width (n+1) *
    oddVariance hw0 hw1 K width hK (n+1) (spatialSpan width c qs)
  have h := Q'.mul_le_mul_of_nonneg_right _ _ a
    (family_channel_firstOrder_variance_cleared hw0 hw1 K hK hwidth n c qs hqs)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hleft : (L*A)*a ≈ A := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ a (Q'.mul_comm_eqv L A))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A L a)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv L _))
        (Q'.mul_one_eqv A)))
  have hright : ((12*(u*u))*V)*a ≈ channelFirstOrderVarianceConstant hw0 hw1 qs.length*V :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => 12*(u*u) | 1 => V | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

#print axioms projectedFamilySpectator
#print axioms projectedFamilySpectator_outside_passive
#print axioms projectedFamily_lowerCertificate
#print axioms projectedFamily_upperCertificate
#print axioms familyChannelFirstOrder
#print axioms family_channel_firstOrder_variance_cleared
#print axioms channelFirstOrderVarianceConstant
#print axioms channelFirstOrderVarianceConstant_positive
#print axioms family_channel_firstOrder_variance_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
