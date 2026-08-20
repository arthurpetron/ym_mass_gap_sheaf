/-
M2c -- the explicit producer seam from physical BF4 to a physical separator.

`BF4PhysicalLocalGluingAFCertificate` proves a sixteenth contraction directly
for the normalized positive BF4 joint quadratic on the
stationary-mean-zero subspace once its genuine local-slice gluing witnesses
are supplied.  `FixedDistancePhysicalSeparator` proves that a contraction of
`q_j ^ n_j` over bounded physical distance gives a positive dimensionful mass
floor.

The record in this file joins those layers without pretending that the join is
automatic.  `BF4PhysicalSeparatorSameObjectPin` identifies the BF4 contracted
macro observable with a connected correlator of the same physical separator,
and `BF4PhysicalSeparatorRateSharpnessPin` supplies a normalized near-top-mode
witness for that separator.  Their combination with the BF4 sixteenth proves
`groupedPhysicalSameObject`; the grouped quarter is no longer a primitive
field.  The macro depth is definitionally the depth carried by the direct
physical local-gluing certificate.  This prevents both the logically invalid shortcut
`sep_phys := 1/4` at every vanishing lattice spacing and reuse of the refuted
all-observable or centered same-action premises.

No inhabitant is constructed here.  In particular, the genuine local slice
inside `bf4`, the physical correlator separator `P`, the same-object physical
correlation pin, and the rate-sharpness witness remain analytic producer
obligations.
-/

import YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
import YMGap.Continuum.FixedDistancePhysicalSeparator

namespace YMGap.Continuum.BF4PhysicalSeparatorProducer

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FixedDistancePhysicalSeparator
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Physical BF4 plus the named same-object identification -/

/-- A concrete same-object pin from each centered physical BF4 macro quadratic to a
connected gauge-invariant correlator carried by `P`.  The equality is imposed
at the same spacing index and at the same macro depth used by the local-gluing
certificate.  Thus the positive finite action and the physical separator no
longer merely occur as unrelated fields in one record. -/
structure BF4PhysicalSeparatorSameObjectPin
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (P : PhysicalSeparator)
    (depth : Nat → Nat) : Type 1 where
  /-- Embed a finite BF4 boundary observable in the physical correlator
  interface at the selected scale. -/
  embed : Nat → (EdgeLabelling → Q') → P.corrIface.Obs
  /-- Every embedded centered boundary observable is a local gauge-invariant
  physical observable. -/
  gaugeInvariantLocal :
    ∀ scale observable,
      CentralPhysicalMeanZero
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable →
        P.corrIface.GaugeInvariantLocal (embed scale observable)
  /-- At the macro depth, the selected physical connected-correlation
  magnitude is exactly the normalized positive BF4 joint-quadratic
  magnitude. -/
  macroCorrelation :
    ∀ scale observable
      (_hmean :
        CentralPhysicalMeanZero
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable),
      P.corrIface.connectedCorr scale (embed scale observable) (depth scale) ≈
        Q'.abs
          (centralPhysicalJointQuadratic
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            0 observable)

namespace BF4PhysicalSeparatorSameObjectPin

/-- The same-object pin and the defining decay property of `P` turn every
centered physical BF4 macro quadratic into a bound by a power of the very same
physical separator. -/
def physical_joint_quadratic_abs_decay
    {family : MatchedBlockFamily}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    {depth : Nat → Nat}
    (pin : BF4PhysicalSeparatorSameObjectPin family coupling P depth)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable) :
    Σ' C : Q', (0 : Q') < C ∧
      Q'.abs
          (centralPhysicalJointQuadratic
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            0 observable) ≤
        C * (P.sep scale) ^ (depth scale) := by
  obtain ⟨C, hC, hdecay⟩ :=
    P.controlsGaugeInvariantCorr
      (pin.embed scale observable)
      (pin.gaugeInvariantLocal scale observable hmean)
  exact ⟨C, hC,
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (pin.macroCorrelation scale observable hmean))
      (hdecay scale (depth scale))⟩

end BF4PhysicalSeparatorSameObjectPin

/-- A quantitative near-extremizer pin showing that `P.sep` is not merely a
loose rate that happens to dominate correlations.  At each scale, one
unit-normalized centered BF4 observable witnesses the selected separator power
from below, up to the fixed factor four.  Combined with the same-object BF4
sixteenth, this constructively yields the quarter grouped-power bound.

For a finite self-adjoint transfer operator this is the place where a
top-mode/near-top-mode witness belongs.  It is left as explicit analytic data;
the producer does not pretend that upper correlation control alone supplies
such a witness. -/
structure BF4PhysicalSeparatorRateSharpnessPin
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (P : PhysicalSeparator)
    (depth : Nat → Nat)
    (sameObject :
      BF4PhysicalSeparatorSameObjectPin family coupling P depth) : Type 1 where
  /-- A centered finite BF4 observable witnessing the physical rate. -/
  probe : Nat → EdgeLabelling → Q'
  /-- The rate probe lies in the same physical stationary-mean-zero subspace. -/
  probe_meanZero :
    ∀ scale,
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (probe scale)
  /-- The rate probe is normalized in the physical stationary inner product. -/
  probe_inner_le_one :
    ∀ scale,
      centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (probe scale) (probe scale) <= (1 : Q')
  /-- The selected physical rate is witnessed, up to factor four, by the
  connected correlation of the same embedded BF4 probe. -/
  separatorPower_le_four_correlation :
    ∀ scale,
      qpow (P.sep scale) (depth scale) <=
        Q'.ofNat 4 *
          P.corrIface.connectedCorr scale
            (sameObject.embed scale (probe scale)) (depth scale)

/-- Physical BF4 quarter contraction, a bounded macro depth, and the explicit
identification of that macro contraction with powers of a physical separator.

The physical spacing is not an unrelated sequence: it is definitionally
`spacing.a (coupling scale)` on the very AF chart used by the BF4 certificate. -/
structure BF4QuarterPhysicalSeparatorProducer
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat -> Q')
    (P : PhysicalSeparator) : Type 1 where
  /-- The viable positive-physical BF4 certificate: genuine local-slice
  gluing at every scale, without either refuted exact-Haar same-action seam. -/
  bf4 : PhysicalLocalGluingAFCertificate
    family law spacing coupling
  /-- The centered physical BF4 macro is a connected correlator of this very
  physical separator object, at the certificate's own macro depth. -/
  sameObject : BF4PhysicalSeparatorSameObjectPin
    family coupling P bf4.depth
  /-- Every macro slab contains at least one transfer step. -/
  depth_pos : forall scale : Nat, 0 < bf4.depth scale
  /-- One scale-independent upper bound on macro physical length. -/
  lengthCeiling : Q'
  /-- The macro physical-length bound is positive. -/
  lengthCeiling_pos : (0 : Q') < lengthCeiling
  /-- The BF4 depth fits in the fixed physical cylinder. -/
  physicalLengthBound : forall scale : Nat,
    Q'.ofNat (bf4.depth scale) * spacing.a (coupling scale) <= lengthCeiling
  /-- **OPEN RATE-SHARPNESS FIELD.**  A unit centered physical correlator
  witnesses the selected separator power from below.  The quarter
  grouped-power estimate is derived from this field and the physical BF4
  sixteenth, rather than being assumed independently. -/
  rateSharpness : BF4PhysicalSeparatorRateSharpnessPin
    family coupling P bf4.depth sameObject

namespace BF4QuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {P : PhysicalSeparator}

/-- The physical spacing sequence on the exact AF coupling trajectory. -/
def physicalSpacing
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) : PhysicalSpacing where
  spacing := fun scale => spacing.a (coupling scale)
  spacing_pos := fun scale =>
    spacing.a_pos (coupling scale)
      (producer.bf4.coupling_pos scale)
      (producer.bf4.coupling_le_window scale)

/-- The selected physical separator power is at most one quarter.  This is no
longer a primitive producer field: rate sharpness, same-object correlation,
and the physical BF4 sixteenth prove it. -/
theorem groupedPhysicalSameObject
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) :
    qpow (P.sep scale) (producer.bf4.depth scale) <= quarter := by
  let observable := producer.rateSharpness.probe scale
  have hmean := producer.rateSharpness.probe_meanZero scale
  have hcorrPhysical :
      P.corrIface.connectedCorr scale
          (producer.sameObject.embed scale observable)
          (producer.bf4.depth scale) <=
        Q'.abs
          (centralPhysicalJointQuadratic
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            0 observable) :=
    Q'.le_of_eqv
      (producer.sameObject.macroCorrelation scale observable hmean)
  have hphysical :=
    producer.bf4.physical_joint_quadratic_abs_le_sixteenth_at
      scale observable hmean
  have hinner :
      Q'.mkPos 1 16 (by decide) *
          centralPhysicalWeightedInner
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0
            observable observable <=
        Q'.mkPos 1 16 (by decide) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (producer.rateSharpness.probe_inner_le_one scale) (by decide))
      (Q'.le_of_eqv
        (Q'.mul_one_eqv (Q'.mkPos 1 16 (by decide))))
  have hcorr :
      P.corrIface.connectedCorr scale
          (producer.sameObject.embed scale observable)
          (producer.bf4.depth scale) <=
        Q'.mkPos 1 16 (by decide) :=
    Q'.le_trans' _ _ _ hcorrPhysical
      (Q'.le_trans' _ _ _ hphysical hinner)
  have hfour :
      Q'.ofNat 4 *
          P.corrIface.connectedCorr scale
            (producer.sameObject.embed scale observable)
            (producer.bf4.depth scale) <=
        Q'.ofNat 4 * Q'.mkPos 1 16 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcorr (by decide)
  exact Q'.le_trans' _ _ _
    (producer.rateSharpness.separatorPower_le_four_correlation scale)
    (Q'.le_trans' _ _ _ hfour (by decide))

/-- Forgetting the BF4-specific finite carrier data leaves precisely the
fixed-distance physical-separator contract, with macro rate `1/4`. -/
def fixedDistance
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) :
    FixedDistanceContraction P producer.physicalSpacing where
  depth := producer.bf4.depth
  depth_pos := producer.depth_pos
  macroRate := quarter
  macroRate_nonnegative := by decide
  macroRate_lt_one := by decide
  lengthCeiling := producer.lengthCeiling
  lengthCeiling_pos := producer.lengthCeiling_pos
  groupedBound := producer.groupedPhysicalSameObject
  physicalLengthBound := producer.physicalLengthBound

/-- The finite positive-physical BF4 quadratic contraction carried by this
producer is the centered local-gluing sixteenth on the very macro depth used by the
fixed-distance separator. -/
theorem physical_joint_quadratic_abs_le_sixteenth_at
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          0 observable) <=
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable observable :=
  producer.bf4.physical_joint_quadratic_abs_le_sixteenth_at
    scale observable hmean

/-- The same-object pin turns the physical BF4 sixteenth into a literal bound on
the selected physical connected correlator at the certificate's own macro
depth.  Unlike `groupedPhysicalSameObject`, this conclusion does not refer to
an arbitrary separator power: it is the direct finite-action correlation
statement. -/
theorem physical_connected_corr_le_sixteenth_at
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable) :
    P.corrIface.connectedCorr scale
        (producer.sameObject.embed scale observable)
        (producer.bf4.depth scale) <=
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (producer.sameObject.macroCorrelation scale observable hmean))
    (producer.physical_joint_quadratic_abs_le_sixteenth_at
      scale observable hmean)

/-- Unit-normalized centered BF4 observables have physical connected
correlation at most `1/16` at the selected macro depth. -/
theorem physical_connected_corr_le_sixteenth_of_inner_le_one
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable)
    (hinner :
      centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable <= (1 : Q')) :
    P.corrIface.connectedCorr scale
        (producer.sameObject.embed scale observable)
        (producer.bf4.depth scale) <=
      Q'.mkPos 1 16 (by decide) := by
  exact Q'.le_trans' _ _ _
    (producer.physical_connected_corr_le_sixteenth_at
      scale observable hmean)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hinner (by decide))
      (Q'.le_of_eqv
        (Q'.mul_one_eqv (Q'.mkPos 1 16 (by decide)))))

/-- The producer's physical BF4 macro is controlled by a power of its selected
physical correlator separator, with an observable-dependent positive
amplitude supplied by `PhysicalSeparator.controlsGaugeInvariantCorr`. -/
def physical_joint_quadratic_abs_decay
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable) :
    Σ' C : Q', (0 : Q') < C ∧
      Q'.abs
          (centralPhysicalJointQuadratic
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            0 observable) ≤
        C * (P.sep scale) ^ (producer.bf4.depth scale) :=
  producer.sameObject.physical_joint_quadratic_abs_decay
    scale observable hmean

/-- The exact floor extracted from a BF4 quarter over fixed physical length is
`(1 - 1/4)/L = (3/4)/L`, retained definitionally through `floorRate`. -/
def physicalFloorRate
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) : Q' :=
  producer.fixedDistance.floorRate

/-- The BF4 physical floor is constructively strictly positive. -/
theorem physicalFloorRate_pos
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) :
    (0 : Q') < producer.physicalFloorRate :=
  producer.fixedDistance.floorRate_pos

/-- The fixed-distance BF4 producer gives the rational physical mass floor. -/
theorem physicalFloorRate_le_marginRate
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) (scale : Nat) :
    producer.physicalFloorRate <=
      marginRate P producer.physicalSpacing scale :=
  producer.fixedDistance.floorRate_le_marginRate scale

/-- On a supplied direct log window, physical BF4 plus the same-object grouped
identification gives a uniform positive floor for `-log(q_j)/a_j`. -/
def exactLogRateFloor
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (W : PhysicalLogWindow P) :
    UniformPhysicalLogRateFloor
      (exactRateFamilyOfPhysicalData P
        producer.physicalSpacing.spacing
        producer.physicalSpacing.spacing_pos W) :=
  producer.fixedDistance.exactLogRateFloor W

/-- The independent upper-rate input required to turn the BF4 lower producer
into a finite two-sided physical mass band. -/
abbrev MarginRateCeiling
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) : Type :=
  FixedDistanceContraction.MarginRateCeiling producer.fixedDistance

/-- BF4 fixed-distance lower production plus an independent finiteness ceiling
packages the exact physical separator certificate. -/
def exactPhysicalSeparatorCertificate
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (W : PhysicalLogWindow P)
    (U : producer.MarginRateCeiling) :
    PhysicalSeparatorLogRate.ExactPhysicalSeparatorCertificate :=
  producer.fixedDistance.exactPhysicalSeparatorCertificate W U

end BF4QuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4PhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.physicalSpacing
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.groupedPhysicalSameObject
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.fixedDistance
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.physical_joint_quadratic_abs_le_sixteenth_at
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.physical_connected_corr_le_sixteenth_at
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.physical_connected_corr_le_sixteenth_of_inner_le_one
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4PhysicalSeparatorSameObjectPin.physical_joint_quadratic_abs_decay
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.physical_joint_quadratic_abs_decay
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.physicalFloorRate_pos
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.physicalFloorRate_le_marginRate
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.exactLogRateFloor
#print axioms YMGap.Continuum.BF4PhysicalSeparatorProducer.BF4QuarterPhysicalSeparatorProducer.exactPhysicalSeparatorCertificate
