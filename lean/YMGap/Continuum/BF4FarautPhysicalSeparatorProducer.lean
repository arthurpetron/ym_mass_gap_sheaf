/-
M2d/M3b -- derive the BF4 macro physical-length field from the existing
AF/Faraut bit-growth budget.

`BF4PhysicalSeparatorProducer` deliberately asks for a uniform bound on the
physical length of the grouped cylinder.  The main `46 * bits` portion of that
bound is already a theorem in `BF4FarautJointCarrierAFBudget`: an
`O(1/t)` Faraut bit cost cancels the AF relation between heat time and lattice
spacing.  The exact Perron depth has three additional endpoint steps.  Their
uniform cost follows directly from the quadratic spacing envelope and the
coupling window, so no separate endpoint bound is needed.

The resulting record removes the free depth and physical-length fields from
the BF4 producer seam.  It also pins the genuine physical local-gluing depth to the
Faraut depth, rather than carrying two unrelated macro lengths.  It still does
not manufacture the physical separator, the same-object correlator pin,
or the normalized rate-sharpness witness.  Given those witnesses, however,
`groupedPhysicalSameObject` is now a theorem rather than an analytic field.
The direct physical local-slice witnesses inside `bf4` remain open.
-/

import YMGap.Continuum.BF4PhysicalSeparatorProducer
import YMGap.Continuum.BF4FarautJointCarrierAFBudget

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4AFHeatSpacing
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The AF/Faraut-reduced producer data -/

/-- Physical BF4 quarter contraction together with a tied Faraut bit schedule
and the still-open same-object identification.

Unlike `BF4QuarterPhysicalSeparatorProducer`, this structure does not ask for
an arbitrary macro depth or arbitrary physical-length proof: both are derived
below from `farautRequiredDepth` and `FarautAFBitGrowth`. -/
structure BF4FarautQuarterPhysicalSeparatorProducer
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat -> Q')
    (bits : Nat -> Nat)
    (P : PhysicalSeparator) : Type 1 where
  /-- Direct positive-physical local-gluing certificate on the same AF
  trajectory. -/
  bf4 : PhysicalLocalGluingAFCertificate
    family law spacing coupling
  /-- The local gluing certificate uses exactly the AF/Faraut macro depth. -/
  depth_matches : forall scale : Nat,
    bf4.depth scale = farautRequiredDepth (bits scale)
  /-- The centered physical BF4 macro is the selected connected correlator of the
  same physical separator object. -/
  sameObject : BF4PhysicalSeparatorSameObjectPin
    family coupling P bf4.depth
  /-- The Faraut window cost is tied to the same coupling and bit functions. -/
  growth : FarautAFBitGrowth
    (physicalAFEnvelope family law spacing) coupling bits
  /-- **OPEN RATE-SHARPNESS FIELD.**  A normalized same-object correlator
  witnesses the physical separator power.  The grouped quarter bound is then
  derived from the BF4 sixteenth. -/
  rateSharpness : BF4PhysicalSeparatorRateSharpnessPin
    family coupling P bf4.depth sameObject

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

/-- The positive AF coefficient `kappa = alpha Lambda/(4C)`. -/
def afRate
    (_producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Q' :=
  heatSpacingRate (physicalAFEnvelope family law spacing)

theorem afRate_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    (0 : Q') < producer.afRate :=
  heatSpacingRate_pos (physicalAFEnvelope family law spacing)

/-- The quotient ceiling for the `46 * bits` core of the Perron depth. -/
def coreLengthCeiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Q' :=
  Q'.divPos
    (Q'.ofNat 46 * producer.growth.costCeiling)
    producer.afRate producer.afRate_pos

/-- The core ceiling is nonnegative even when the supplied Faraut cost ceiling
is zero. -/
theorem coreLengthCeiling_nonnegative
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    (0 : Q') <= producer.coreLengthCeiling := by
  unfold coreLengthCeiling Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat 46)
      producer.growth.costCeiling_nonnegative)
    (Q'.le_of_lt (Q'.recipPos_pos producer.afRate producer.afRate_pos))

/-- The quadratic spacing envelope evaluated at the positive coupling-window
endpoint.  This uniformly pays each of the three fixed endpoint steps. -/
def envelopeSpacingCeiling
    (_producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Q' :=
  Q'.divPos (spacing.C * (law.g₁ * law.g₁))
    spacing.Λ spacing.Λ_pos

theorem envelopeSpacingCeiling_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    (0 : Q') < producer.envelopeSpacingCeiling := by
  unfold envelopeSpacingCeiling
  exact Q'.divPos_pos _ _ spacing.Λ_pos
    (Q'.mul_pos spacing.C_pos (Q'.mul_pos law.g₁_pos law.g₁_pos))

/-- Every AF-trajectory spacing lies below the endpoint value furnished by
the quadratic envelope. -/
theorem spacing_le_envelopeSpacingCeiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (scale : Nat) :
    spacing.a (coupling scale) <= producer.envelopeSpacingCeiling := by
  have hg0 : (0 : Q') <= coupling scale :=
    Q'.le_of_lt (producer.bf4.coupling_pos scale)
  have hg₁0 : (0 : Q') <= law.g₁ := Q'.le_of_lt law.g₁_pos
  have hsquare :
      coupling scale * coupling scale <= law.g₁ * law.g₁ := by
    have hleft :
        coupling scale * coupling scale <= law.g₁ * coupling scale :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (producer.bf4.coupling_le_window scale) hg0
    have hright : law.g₁ * coupling scale <= law.g₁ * law.g₁ :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (producer.bf4.coupling_le_window scale) hg₁0
    exact Q'.le_trans' _ _ _ hleft hright
  have hscaled :
      spacing.C * (coupling scale * coupling scale) <=
        spacing.C * (law.g₁ * law.g₁) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsquare
      (Q'.le_of_lt spacing.C_pos)
  have hmul :
      spacing.a (coupling scale) * spacing.Λ <=
        spacing.C * (law.g₁ * law.g₁) :=
    Q'.le_trans' _ _ _
      (spacing.spacing_quad (coupling scale)
        (producer.bf4.coupling_pos scale)
        (producer.bf4.coupling_le_window scale))
      hscaled
  exact Q'.le_divPos_of_mul_le _ _ spacing.Λ_pos hmul

/-- The complete cylinder ceiling pays the three exact endpoint steps in
addition to the AF/Faraut core. -/
def lengthCeiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Q' :=
  Q'.ofNat 3 * producer.envelopeSpacingCeiling +
    producer.coreLengthCeiling

theorem lengthCeiling_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    (0 : Q') < producer.lengthCeiling := by
  unfold lengthCeiling
  exact Q'.pos_add_nonneg
    (Q'.mul_pos (by decide) producer.envelopeSpacingCeiling_pos)
    producer.coreLengthCeiling_nonnegative

/-! ## 2. Derivation of the uniform physical cylinder -/

/-- AF/Faraut cancellation bounds the growing `46 * bits` core after division
by the positive AF rate. -/
theorem core_physical_length_le
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (scale : Nat) :
    Q'.ofNat (46 * bits scale) * spacing.a (coupling scale) <=
      producer.coreLengthCeiling := by
  have hAF := faraut_af_family_core_length_uniform producer.growth scale
  have hmul :
      (Q'.ofNat (46 * bits scale) * spacing.a (coupling scale)) *
          producer.afRate <=
        Q'.ofNat 46 * producer.growth.costCeiling := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (Q'.ofNat (46 * bits scale) * spacing.a (coupling scale))
          producer.afRate))
      hAF
  exact Q'.le_divPos_of_mul_le
    (Q'.ofNat 46 * producer.growth.costCeiling)
    producer.afRate producer.afRate_pos hmul

/-- The exact `46 * bits + 3` Perron depth occupies a uniformly bounded
physical length.  The growing core is paid by AF/Faraut cancellation; only the
three fixed endpoints use the derived envelope ceiling. -/
theorem requiredDepth_physical_length_le
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (scale : Nat) :
    Q'.ofNat (farautRequiredDepth (bits scale)) *
        spacing.a (coupling scale) <=
      producer.lengthCeiling := by
  have hcore := producer.core_physical_length_le scale
  have hendpoint :
      Q'.ofNat 3 * spacing.a (coupling scale) <=
        Q'.ofNat 3 * producer.envelopeSpacingCeiling :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (producer.spacing_le_envelopeSpacingCeiling scale)
      (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat 3)
  have hsum :
      (Q'.ofNat (46 * bits scale) * spacing.a (coupling scale)) +
          (Q'.ofNat 3 * spacing.a (coupling scale)) <=
        producer.coreLengthCeiling +
          (Q'.ofNat 3 * producer.envelopeSpacingCeiling) :=
    Q'.add_le_add hcore hendpoint
  have hleft :
      (Q'.ofNat (farautRequiredDepth (bits scale)) *
          spacing.a (coupling scale)) ≈
        (Q'.ofNat (46 * bits scale) * spacing.a (coupling scale)) +
          (Q'.ofNat 3 * spacing.a (coupling scale)) := by
    unfold farautRequiredDepth
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right
        (Q'.ofNat (46 * bits scale + 3))
        (Q'.ofNat (46 * bits scale) + Q'.ofNat 3)
        (spacing.a (coupling scale))
        (Q'.ofNat_add_eqv (46 * bits scale) 3))
      (Q'.add_mul_eqv
        (Q'.ofNat (46 * bits scale)) (Q'.ofNat 3)
        (spacing.a (coupling scale)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv
        (Q'.add_comm_eqv producer.coreLengthCeiling
          (Q'.ofNat 3 * producer.envelopeSpacingCeiling))))

/-! ## 3. The reduced record feeds the fixed-distance separator theorem -/

/-- The AF/Faraut data canonically produce the earlier BF4 fixed-distance
contract.  No free depth or physical-length witness remains. -/
def toBF4QuarterPhysicalSeparatorProducer
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    BF4QuarterPhysicalSeparatorProducer family law spacing coupling P where
  bf4 := producer.bf4
  sameObject := producer.sameObject
  rateSharpness := producer.rateSharpness
  depth_pos := by
    intro scale
    rw [producer.depth_matches scale]
    unfold farautRequiredDepth
    omega
  lengthCeiling := producer.lengthCeiling
  lengthCeiling_pos := producer.lengthCeiling_pos
  physicalLengthBound := by
    intro scale
    rw [producer.depth_matches scale]
    exact producer.requiredDepth_physical_length_le scale

/-- The AF/Faraut-selected separator power is at most one quarter, derived
from rate sharpness and the centered positive-physical BF4 contraction. -/
theorem groupedPhysicalSameObject
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (scale : Nat) :
    qpow (P.sep scale) (farautRequiredDepth (bits scale)) <=
      FiveHolonomyPerronCutoff.quarter := by
  rw [← producer.depth_matches scale]
  exact producer.toBF4QuarterPhysicalSeparatorProducer
    |>.groupedPhysicalSameObject scale

/-- Consequently the AF/Faraut-reduced producer has the same strictly positive
dimensionful BF4 floor as the general producer. -/
theorem physicalFloorRate_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    (0 : Q') <
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate :=
  producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate_pos

/-- The derived floor bounds the rational margin rate at every scale. -/
theorem physicalFloorRate_le_marginRate
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (scale : Nat) :
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate <=
      marginRate P
        producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing scale :=
  producer.toBF4QuarterPhysicalSeparatorProducer
    |>.physicalFloorRate_le_marginRate scale

/-- At the exact AF/Faraut depth, the selected physical connected correlator
inherits the centered BF4 sixteenth contraction. -/
theorem physical_connected_corr_le_sixteenth_at_requiredDepth
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable) :
    P.corrIface.connectedCorr scale
        (producer.sameObject.embed scale observable)
        (farautRequiredDepth (bits scale)) <=
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable := by
  rw [← producer.depth_matches scale]
  exact producer.toBF4QuarterPhysicalSeparatorProducer
    |>.physical_connected_corr_le_sixteenth_at scale observable hmean

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.afRate_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.coreLengthCeiling_nonnegative
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.envelopeSpacingCeiling_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.spacing_le_envelopeSpacingCeiling
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.lengthCeiling_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.core_physical_length_le
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.groupedPhysicalSameObject
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.physical_connected_corr_le_sixteenth_at_requiredDepth
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.requiredDepth_physical_length_le
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.toBF4QuarterPhysicalSeparatorProducer
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.physicalFloorRate_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.physicalFloorRate_le_marginRate
