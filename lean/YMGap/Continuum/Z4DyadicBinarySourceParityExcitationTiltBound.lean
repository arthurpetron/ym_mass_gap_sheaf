/-
# The cutoff-four lowering tilt is paid by parity excitation

The exact cutoff-one blocking row has a source-dependent integer tilt.  Its
five-by-five local table is small enough to compare directly with the
source's parity-ground channel.  If `k` is the number of two-spin raises
above parity ground, then

  loweringMultiplicity source target
    <= 2^k * parityGroundMultiplicity source.

Multiplying this inequality over the complete coarse face carrier gives a
volume-free activity statement: all growth of the integer tilt is charged to
the same additive excitation mass whose SU(2) Casimir cost is at least eight
units per raise.  This is the combinatorial half of a direct polymer estimate;
the link-multiplicity comparison is deliberately not asserted here.

Constructive contract: the kernel-checked five-by-five lowering table, finite
products, and bounded natural arithmetic only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess

namespace YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
open YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact local activity comparison -/

/-- The finite SU(2) lowering reward above parity ground grows by at most one
factor `2` for each two-spin excitation step. -/
theorem spinFourLoweringMultiplicity_le_twoPow_mul_parityGround
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin <= 4) (htarget : targetSpin <= 4)
    (hlowering : targetSpin <= sourceSpin /\
      targetSpin % 2 = sourceSpin % 2) :
    spinFourLoweringMultiplicity sourceSpin targetSpin <=
      2 ^ spinFourParityExcitationLevel sourceSpin targetSpin *
        spinFourParityGroundMultiplicity sourceSpin := by
  rw [spinFourLoweringMultiplicity_eq_table hsource htarget]
  have hs : sourceSpin = 0 \/ sourceSpin = 1 \/ sourceSpin = 2 \/
      sourceSpin = 3 \/ sourceSpin = 4 := by
    omega
  have ht : targetSpin = 0 \/ targetSpin = 1 \/ targetSpin = 2 \/
      targetSpin = 3 \/ targetSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    simp [spinFourLoweringMultiplicityTable,
      spinFourParityExcitationLevel,
      spinFourParityGroundMultiplicity] at *

/-! ## 2. Casimir payment contracts the tilt to one activity base -/

/-- Activity paid by one two-spin excitation before link multiplicities are
compared: a factor `2` for the exact lowering tilt and eight powers of the
heat parameter for the SU(2) Casimir excess. -/
def spinFourParityExcitationTiltActivityRate (w : Q') : Q' :=
  Q'.ofNat 2 * qpow w 8

private theorem ofNat_mul_eqv_local (left right : Nat) :
    Q'.ofNat left * Q'.ofNat right ≈ Q'.ofNat (left * right) := by
  show ((left : Int) * (right : Int)) * 1 =
    ((left * right : Nat) : Int) * 1
  push_cast
  simp

private theorem qpow_ofNat_two_eqv_twoPow : forall exponent : Nat,
    qpow (Q'.ofNat 2) exponent ≈ Q'.ofNat (2 ^ exponent)
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      show qpow (Q'.ofNat 2) exponent * Q'.ofNat 2 ≈
        Q'.ofNat (2 ^ (exponent + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Q'.ofNat 2)
          (qpow_ofNat_two_eqv_twoPow exponent)) ?_
      rw [Nat.pow_succ]
      exact ofNat_mul_eqv_local _ _

private theorem qpow_ofNat_five_eqv_fivePow : forall exponent : Nat,
    qpow (Q'.ofNat 5) exponent ≈ Q'.ofNat (5 ^ exponent)
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      show qpow (Q'.ofNat 5) exponent * Q'.ofNat 5 ≈
        Q'.ofNat (5 ^ (exponent + 1))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Q'.ofNat 5)
          (qpow_ofNat_five_eqv_fivePow exponent)) ?_
      rw [Nat.pow_succ]
      exact ofNat_mul_eqv_local _ _

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d)))
  refine Q'.mul_eqv_congr_left a _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c)) ?_
  exact Q'.mul_assoc_eqv c b d

private theorem qpow_mul_base_local (left right : Q') :
    forall exponent : Nat,
      qpow (left * right) exponent ≈
        qpow left exponent * qpow right exponent
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | exponent + 1 => by
      show qpow (left * right) exponent * (left * right) ≈
        (qpow left exponent * left) * (qpow right exponent * right)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (left * right)
          (qpow_mul_base_local left right exponent)) ?_
      exact mul_four_regroup_local _ _ _ _

/-- The `k`-fold activity base is exactly the product of the `2^k` tilt
allowance and the minimum `w^(8k)` Casimir payment. -/
theorem qpow_spinFourParityExcitationTiltActivityRate_eqv
    (w : Q') (excitationMass : Nat) :
    qpow (spinFourParityExcitationTiltActivityRate w) excitationMass ≈
      Q'.ofNat (2 ^ excitationMass) * qpow w (8 * excitationMass) := by
  unfold spinFourParityExcitationTiltActivityRate
  refine Q'.eqv_trans _ _ _
    (qpow_mul_base_local (Q'.ofNat 2) (qpow w 8) excitationMass) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow (qpow w 8) excitationMass)
      (qpow_ofNat_two_eqv_twoPow excitationMass)) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (2 ^ excitationMass)) _ _
    (qpow_qpow w 8 excitationMass)

/-- If an excitation of mass `k` pays at least `8k` heat powers, then its
integer tilt times its heat weight is bounded by the `k`th power of the single
activity base `2*w^8`. -/
theorem twoPow_mul_qpow_excess_le_excitationTiltActivity
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (excitationMass casimirExcess : Nat)
    (hcost : 8 * excitationMass <= casimirExcess) :
    Q'.ofNat (2 ^ excitationMass) * qpow w casimirExcess <=
      qpow (spinFourParityExcitationTiltActivityRate w) excitationMass := by
  have hheat : qpow w casimirExcess <= qpow w (8 * excitationMass) :=
    qpow_antitone hw0 hw1 _ _ hcost
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (2 ^ excitationMass)) hheat (zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.ge_of_eqv
      (qpow_spinFourParityExcitationTiltActivityRate_eqv
        w excitationMass))

/-- Generic contraction of a natural-valued tilt estimate and an eight-unit
Casimir floor into one ground-relative activity estimate. -/
theorem naturalTilt_mul_qpow_excess_le_ground_mul_activity
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (tilt groundMultiplicity excitationMass casimirExcess : Nat)
    (htilt : tilt <= 2 ^ excitationMass * groundMultiplicity)
    (hcost : 8 * excitationMass <= casimirExcess) :
    Q'.ofNat tilt * qpow w casimirExcess <=
      Q'.ofNat groundMultiplicity *
        qpow (spinFourParityExcitationTiltActivityRate w) excitationMass := by
  have hcast : Q'.ofNat tilt <=
      Q'.ofNat (2 ^ excitationMass * groundMultiplicity) :=
    CReal.ofNat_le_ofNat htilt
  have hheat0 : (0 : Q') <= qpow w casimirExcess :=
    qpow_nonneg w hw0 casimirExcess
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _
    (qpow w casimirExcess) hcast hheat0
  have hregroup :
      Q'.ofNat (2 ^ excitationMass * groundMultiplicity) *
          qpow w casimirExcess ≈
        Q'.ofNat groundMultiplicity *
          (Q'.ofNat (2 ^ excitationMass) * qpow w casimirExcess) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow w casimirExcess)
        (Q'.eqv_symm (ofNat_mul_eqv_local _ _))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow w casimirExcess)
        (Q'.mul_comm_eqv
          (Q'.ofNat (2 ^ excitationMass))
          (Q'.ofNat groundMultiplicity))) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hactivity :=
    twoPow_mul_qpow_excess_le_excitationTiltActivity
      w hw0 hw1 excitationMass casimirExcess hcost
  have hlast := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat groundMultiplicity) hactivity (zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) hlast)

/-- Local cutoff-four SU(2) activity bound.  The source-dependent parity-ground
factor is retained explicitly; every target excitation is charged only to the
uniform base `2*w^8`. -/
theorem spinFourLoweringMultiplicity_mul_excitationHeat_le_ground_mul_activity
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin <= 4) (htarget : targetSpin <= 4)
    (hlowering : targetSpin <= sourceSpin /\
      targetSpin % 2 = sourceSpin % 2) :
    Q'.ofNat (spinFourLoweringMultiplicity sourceSpin targetSpin) *
        qpow w (spinFourParityExcitationCasimirExcess sourceSpin targetSpin) <=
      Q'.ofNat (spinFourParityGroundMultiplicity sourceSpin) *
        qpow (spinFourParityExcitationTiltActivityRate w)
          (spinFourParityExcitationLevel sourceSpin targetSpin) := by
  exact naturalTilt_mul_qpow_excess_le_ground_mul_activity
    w hw0 hw1
    (spinFourLoweringMultiplicity sourceSpin targetSpin)
    (spinFourParityGroundMultiplicity sourceSpin)
    (spinFourParityExcitationLevel sourceSpin targetSpin)
    (spinFourParityExcitationCasimirExcess sourceSpin targetSpin)
    (spinFourLoweringMultiplicity_le_twoPow_mul_parityGround
      hsource htarget hlowering)
    (eight_mul_spinFourParityExcitationLevel_le_casimirExcess
      hsource htarget hlowering)

/-! ## 3. The complete face coefficient: fusion tilt times dimension -/

/-- Dimension of the parity-ground SU(2) representation. -/
def spinFourParityGroundDimension (sourceSpin : Nat) : Nat :=
  sourceSpin % 2 + 1

/-- Once the target representation dimension is included, one two-spin
excitation costs at most a factor `5` relative to the parity-ground face
coefficient.  This is the sharp integral base needed uniformly by the exact
five-by-five cutoff-four lowering table (`9/2` is its largest rational ratio). -/
theorem spinFourLoweringMultiplicity_mul_targetDimension_le_fivePow_mul_ground
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin <= 4) (htarget : targetSpin <= 4)
    (hlowering : targetSpin <= sourceSpin /\
      targetSpin % 2 = sourceSpin % 2) :
    spinFourLoweringMultiplicity sourceSpin targetSpin * (targetSpin + 1) <=
      5 ^ spinFourParityExcitationLevel sourceSpin targetSpin *
        (spinFourParityGroundMultiplicity sourceSpin *
          spinFourParityGroundDimension sourceSpin) := by
  rw [spinFourLoweringMultiplicity_eq_table hsource htarget]
  have hs : sourceSpin = 0 \/ sourceSpin = 1 \/ sourceSpin = 2 \/
      sourceSpin = 3 \/ sourceSpin = 4 := by
    omega
  have ht : targetSpin = 0 \/ targetSpin = 1 \/ targetSpin = 2 \/
      targetSpin = 3 \/ targetSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    simp [spinFourLoweringMultiplicityTable,
      spinFourParityExcitationLevel,
      spinFourParityGroundMultiplicity,
      spinFourParityGroundDimension] at *

/-- Full face activity base: the exact fusion-path multiplicity and the SU(2)
representation dimension are both paid, while the eight-unit Casimir gain
supplies the heat factor. -/
def spinFourParityExcitationFaceActivityRate (w : Q') : Q' :=
  Q'.ofNat 5 * qpow w 8

theorem qpow_spinFourParityExcitationFaceActivityRate_eqv
    (w : Q') (excitationMass : Nat) :
    qpow (spinFourParityExcitationFaceActivityRate w) excitationMass ≈
      Q'.ofNat (5 ^ excitationMass) * qpow w (8 * excitationMass) := by
  unfold spinFourParityExcitationFaceActivityRate
  refine Q'.eqv_trans _ _ _
    (qpow_mul_base_local (Q'.ofNat 5) (qpow w 8) excitationMass) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow (qpow w 8) excitationMass)
      (qpow_ofNat_five_eqv_fivePow excitationMass)) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (5 ^ excitationMass)) _ _
    (qpow_qpow w 8 excitationMass)

/-- Generic natural face tilt contracted against the SU(2) Casimir payment. -/
theorem naturalFaceTilt_mul_qpow_excess_le_ground_mul_activity
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (faceTilt groundFaceWeight excitationMass casimirExcess : Nat)
    (htilt : faceTilt <= 5 ^ excitationMass * groundFaceWeight)
    (hcost : 8 * excitationMass <= casimirExcess) :
    Q'.ofNat faceTilt * qpow w casimirExcess <=
      Q'.ofNat groundFaceWeight *
        qpow (spinFourParityExcitationFaceActivityRate w) excitationMass := by
  have hcast : Q'.ofNat faceTilt <=
      Q'.ofNat (5 ^ excitationMass * groundFaceWeight) :=
    CReal.ofNat_le_ofNat htilt
  have hheat0 : (0 : Q') <= qpow w casimirExcess :=
    qpow_nonneg w hw0 casimirExcess
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _
    (qpow w casimirExcess) hcast hheat0
  have hregroup :
      Q'.ofNat (5 ^ excitationMass * groundFaceWeight) *
          qpow w casimirExcess ≈
        Q'.ofNat groundFaceWeight *
          (Q'.ofNat (5 ^ excitationMass) * qpow w casimirExcess) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow w casimirExcess)
        (Q'.eqv_symm (ofNat_mul_eqv_local _ _))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow w casimirExcess)
        (Q'.mul_comm_eqv
          (Q'.ofNat (5 ^ excitationMass))
          (Q'.ofNat groundFaceWeight))) ?_
    exact Q'.mul_assoc_eqv _ _ _
  have hheat : qpow w casimirExcess <= qpow w (8 * excitationMass) :=
    qpow_antitone hw0 hw1 _ _ hcost
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (5 ^ excitationMass)) hheat (zero_le_ofNat _)
  have hactivity :
      Q'.ofNat (5 ^ excitationMass) * qpow w casimirExcess <=
        qpow (spinFourParityExcitationFaceActivityRate w) excitationMass :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.ge_of_eqv
        (qpow_spinFourParityExcitationFaceActivityRate_eqv
          w excitationMass))
  have hlast := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat groundFaceWeight) hactivity (zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) hlast)

/-- Local physically complete face activity estimate. -/
theorem spinFourLoweringFaceCoefficient_mul_excitationHeat_le_ground_mul_activity
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin <= 4) (htarget : targetSpin <= 4)
    (hlowering : targetSpin <= sourceSpin /\
      targetSpin % 2 = sourceSpin % 2) :
    Q'.ofNat
          (spinFourLoweringMultiplicity sourceSpin targetSpin *
            (targetSpin + 1)) *
        qpow w (spinFourParityExcitationCasimirExcess sourceSpin targetSpin) <=
      Q'.ofNat
          (spinFourParityGroundMultiplicity sourceSpin *
            spinFourParityGroundDimension sourceSpin) *
        qpow (spinFourParityExcitationFaceActivityRate w)
          (spinFourParityExcitationLevel sourceSpin targetSpin) := by
  exact naturalFaceTilt_mul_qpow_excess_le_ground_mul_activity
    w hw0 hw1 _ _ _ _
    (spinFourLoweringMultiplicity_mul_targetDimension_le_fivePow_mul_ground
      hsource htarget hlowering)
    (eight_mul_spinFourParityExcitationLevel_le_casimirExcess
      hsource htarget hlowering)

/-! ## 4. The additive excitation coordinate on a face list -/

def spinFourParityExcitationMassOn
    (sourceState targetState : EdgeLabelling) (faces : List Nat) : Nat :=
  listNatWeight
    (fun faceId => spinFourParityExcitationLevel
      (sourceState faceId) (targetState faceId)) faces

def spinFourParityExcitationCasimirExcessOn
    (sourceState targetState : EdgeLabelling) (faces : List Nat) : Nat :=
  listNatWeight
    (fun faceId => spinFourParityExcitationCasimirExcess
      (sourceState faceId) (targetState faceId)) faces

def spinFourParityGroundMultiplicityProductOn
    (sourceState : EdgeLabelling) (faces : List Nat) : Nat :=
  natListProduct
    (fun faceId => spinFourParityGroundMultiplicity (sourceState faceId))
    faces

/-- Natural product containing both the lowering multiplicity and the target
SU(2) representation dimension on every selected face. -/
def spinFourLoweringFaceCoefficientProductOn
    (sourceState targetState : EdgeLabelling) (faces : List Nat) : Nat :=
  natListProduct
    (fun faceId =>
      spinFourLoweringMultiplicity
          (sourceState faceId) (targetState faceId) *
        (targetState faceId + 1))
    faces

/-- Corresponding parity-ground multiplicity-times-dimension product. -/
def spinFourParityGroundFaceCoefficientProductOn
    (sourceState : EdgeLabelling) (faces : List Nat) : Nat :=
  natListProduct
    (fun faceId =>
      spinFourParityGroundMultiplicity (sourceState faceId) *
        spinFourParityGroundDimension (sourceState faceId))
    faces

/-- Multiplicativity turns the local table comparison into one power whose
exponent is the total parity-excitation mass. -/
theorem spinFourLoweringMultiplicityProductOn_le_twoPow_mul_ground
    (sourceState targetState : EdgeLabelling) :
    forall faces : List Nat,
    (forall faceId, faceId ∈ faces -> sourceState faceId <= 4) ->
    (forall faceId, faceId ∈ faces -> targetState faceId <= 4) ->
    (forall faceId, faceId ∈ faces ->
      targetState faceId <= sourceState faceId /\
        targetState faceId % 2 = sourceState faceId % 2) ->
    spinFourLoweringMultiplicityProductOn sourceState targetState faces <=
      2 ^ spinFourParityExcitationMassOn sourceState targetState faces *
        spinFourParityGroundMultiplicityProductOn sourceState faces
  | [], _, _, _ => by
      simp [spinFourLoweringMultiplicityProductOn,
        spinFourParityExcitationMassOn,
        spinFourParityGroundMultiplicityProductOn,
        natListProduct, listNatWeight]
  | head :: tail, hsource, htarget, hlowering => by
      have hhead :=
        spinFourLoweringMultiplicity_le_twoPow_mul_parityGround
          (hsource head List.mem_cons_self)
          (htarget head List.mem_cons_self)
          (hlowering head List.mem_cons_self)
      have htail :=
        spinFourLoweringMultiplicityProductOn_le_twoPow_mul_ground
          sourceState targetState tail
          (fun faceId hface =>
            hsource faceId (List.mem_cons_of_mem head hface))
          (fun faceId hface =>
            htarget faceId (List.mem_cons_of_mem head hface))
          (fun faceId hface =>
            hlowering faceId (List.mem_cons_of_mem head hface))
      have hmul := Nat.mul_le_mul hhead htail
      unfold spinFourParityExcitationMassOn
        spinFourParityGroundMultiplicityProductOn
        spinFourLoweringMultiplicityProductOn
      simp only [listNatWeight, natListProduct]
      change
        spinFourLoweringMultiplicity (sourceState head) (targetState head) *
            natListProduct
              (fun faceId => spinFourLoweringMultiplicity
                (sourceState faceId) (targetState faceId)) tail <=
          2 ^
              (spinFourParityExcitationLevel
                  (sourceState head) (targetState head) +
                listNatWeight
                  (fun faceId => spinFourParityExcitationLevel
                    (sourceState faceId) (targetState faceId)) tail) *
            (spinFourParityGroundMultiplicity (sourceState head) *
              natListProduct
                (fun faceId =>
                  spinFourParityGroundMultiplicity (sourceState faceId)) tail)
      refine Nat.le_trans hmul ?_
      apply Nat.le_of_eq
      rw [Nat.pow_add]
      ac_rfl

/-- The physically complete face coefficient product grows by at most one
factor `5` per additive parity excitation. -/
theorem spinFourLoweringFaceCoefficientProductOn_le_fivePow_mul_ground
    (sourceState targetState : EdgeLabelling) :
    forall faces : List Nat,
    (forall faceId, faceId ∈ faces -> sourceState faceId <= 4) ->
    (forall faceId, faceId ∈ faces -> targetState faceId <= 4) ->
    (forall faceId, faceId ∈ faces ->
      targetState faceId <= sourceState faceId /\
        targetState faceId % 2 = sourceState faceId % 2) ->
    spinFourLoweringFaceCoefficientProductOn
        sourceState targetState faces <=
      5 ^ spinFourParityExcitationMassOn sourceState targetState faces *
        spinFourParityGroundFaceCoefficientProductOn sourceState faces
  | [], _, _, _ => by
      simp [spinFourLoweringFaceCoefficientProductOn,
        spinFourParityExcitationMassOn,
        spinFourParityGroundFaceCoefficientProductOn,
        natListProduct, listNatWeight]
  | head :: tail, hsource, htarget, hlowering => by
      have hhead :=
        spinFourLoweringMultiplicity_mul_targetDimension_le_fivePow_mul_ground
          (hsource head List.mem_cons_self)
          (htarget head List.mem_cons_self)
          (hlowering head List.mem_cons_self)
      have htail :=
        spinFourLoweringFaceCoefficientProductOn_le_fivePow_mul_ground
          sourceState targetState tail
          (fun faceId hface =>
            hsource faceId (List.mem_cons_of_mem head hface))
          (fun faceId hface =>
            htarget faceId (List.mem_cons_of_mem head hface))
          (fun faceId hface =>
            hlowering faceId (List.mem_cons_of_mem head hface))
      have hmul := Nat.mul_le_mul hhead htail
      change
        (spinFourLoweringMultiplicity
              (sourceState head) (targetState head) *
            (targetState head + 1)) *
            spinFourLoweringFaceCoefficientProductOn
              sourceState targetState tail <=
          5 ^
              (spinFourParityExcitationLevel
                  (sourceState head) (targetState head) +
                spinFourParityExcitationMassOn
                  sourceState targetState tail) *
            ((spinFourParityGroundMultiplicity (sourceState head) *
                spinFourParityGroundDimension (sourceState head)) *
              spinFourParityGroundFaceCoefficientProductOn
                sourceState tail)
      refine Nat.le_trans hmul ?_
      apply Nat.le_of_eq
      rw [Nat.pow_add]
      ac_rfl

/-- The local eight-unit SU(2) cost adds over any face carrier. -/
theorem eight_mul_spinFourParityExcitationMassOn_le_casimirExcessOn
    (sourceState targetState : EdgeLabelling) :
    forall faces : List Nat,
    (forall faceId, faceId ∈ faces -> sourceState faceId <= 4) ->
    (forall faceId, faceId ∈ faces -> targetState faceId <= 4) ->
    (forall faceId, faceId ∈ faces ->
      targetState faceId <= sourceState faceId /\
        targetState faceId % 2 = sourceState faceId % 2) ->
    8 * spinFourParityExcitationMassOn sourceState targetState faces <=
      spinFourParityExcitationCasimirExcessOn sourceState targetState faces
  | [], _, _, _ => by
      simp [spinFourParityExcitationMassOn,
        spinFourParityExcitationCasimirExcessOn, listNatWeight]
  | head :: tail, hsource, htarget, hlowering => by
      have hhead :=
        eight_mul_spinFourParityExcitationLevel_le_casimirExcess
          (hsource head List.mem_cons_self)
          (htarget head List.mem_cons_self)
          (hlowering head List.mem_cons_self)
      have htail :=
        eight_mul_spinFourParityExcitationMassOn_le_casimirExcessOn
          sourceState targetState tail
          (fun faceId hface =>
            hsource faceId (List.mem_cons_of_mem head hface))
          (fun faceId hface =>
            htarget faceId (List.mem_cons_of_mem head hface))
          (fun faceId hface =>
            hlowering faceId (List.mem_cons_of_mem head hface))
      have htail' :
          8 * listNatWeight
              (fun faceId => spinFourParityExcitationLevel
                (sourceState faceId) (targetState faceId)) tail <=
            listNatWeight
              (fun faceId => spinFourParityExcitationCasimirExcess
                (sourceState faceId) (targetState faceId)) tail := by
        simpa only [spinFourParityExcitationMassOn,
          spinFourParityExcitationCasimirExcessOn] using htail
      unfold spinFourParityExcitationMassOn
        spinFourParityExcitationCasimirExcessOn
      simp only [listNatWeight]
      omega

/-- Complete face-carrier version of the ground-relative activity estimate. -/
theorem spinFourLoweringMultiplicityProductOn_mul_excitationHeat_le_ground_mul_activity
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (sourceState targetState : EdgeLabelling) (faces : List Nat)
    (hsource : forall faceId, faceId ∈ faces -> sourceState faceId <= 4)
    (htarget : forall faceId, faceId ∈ faces -> targetState faceId <= 4)
    (hlowering : forall faceId, faceId ∈ faces ->
      targetState faceId <= sourceState faceId /\
        targetState faceId % 2 = sourceState faceId % 2) :
    Q'.ofNat
          (spinFourLoweringMultiplicityProductOn
            sourceState targetState faces) *
        qpow w
          (spinFourParityExcitationCasimirExcessOn
            sourceState targetState faces) <=
      Q'.ofNat (spinFourParityGroundMultiplicityProductOn sourceState faces) *
        qpow (spinFourParityExcitationTiltActivityRate w)
          (spinFourParityExcitationMassOn sourceState targetState faces) := by
  exact naturalTilt_mul_qpow_excess_le_ground_mul_activity
    w hw0 hw1
    (spinFourLoweringMultiplicityProductOn sourceState targetState faces)
    (spinFourParityGroundMultiplicityProductOn sourceState faces)
    (spinFourParityExcitationMassOn sourceState targetState faces)
    (spinFourParityExcitationCasimirExcessOn sourceState targetState faces)
    (spinFourLoweringMultiplicityProductOn_le_twoPow_mul_ground
      sourceState targetState faces hsource htarget hlowering)
    (eight_mul_spinFourParityExcitationMassOn_le_casimirExcessOn
      sourceState targetState faces hsource htarget hlowering)

/-- Complete physically weighted face-carrier activity estimate.  This is the
face part of the desired ground-relative Gibbs comparison; only the link
multiplicity ratio remains outside this theorem. -/
theorem spinFourLoweringFaceCoefficientProductOn_mul_excitationHeat_le_ground_mul_activity
    (w : Q') (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    (sourceState targetState : EdgeLabelling) (faces : List Nat)
    (hsource : forall faceId, faceId ∈ faces -> sourceState faceId <= 4)
    (htarget : forall faceId, faceId ∈ faces -> targetState faceId <= 4)
    (hlowering : forall faceId, faceId ∈ faces ->
      targetState faceId <= sourceState faceId /\
        targetState faceId % 2 = sourceState faceId % 2) :
    Q'.ofNat
          (spinFourLoweringFaceCoefficientProductOn
            sourceState targetState faces) *
        qpow w
          (spinFourParityExcitationCasimirExcessOn
            sourceState targetState faces) <=
      Q'.ofNat
          (spinFourParityGroundFaceCoefficientProductOn sourceState faces) *
        qpow (spinFourParityExcitationFaceActivityRate w)
          (spinFourParityExcitationMassOn sourceState targetState faces) := by
  exact naturalFaceTilt_mul_qpow_excess_le_ground_mul_activity
    w hw0 hw1
    (spinFourLoweringFaceCoefficientProductOn sourceState targetState faces)
    (spinFourParityGroundFaceCoefficientProductOn sourceState faces)
    (spinFourParityExcitationMassOn sourceState targetState faces)
    (spinFourParityExcitationCasimirExcessOn sourceState targetState faces)
    (spinFourLoweringFaceCoefficientProductOn_le_fivePow_mul_ground
      sourceState targetState faces hsource htarget hlowering)
    (eight_mul_spinFourParityExcitationMassOn_le_casimirExcessOn
      sourceState targetState faces hsource htarget hlowering)

/-! ## 5. Complete lowering-row specialization -/

/-- Total two-spin excitation mass of one target in a source-dependent
cutoff-four lowering row. -/
def positivePhysicalSourceParityExcitationActivity
    (S : SlabScalePair) (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling) : Nat :=
  spinFourParityExcitationMassOn
    (wholeSlabFinePacketTotalLabelling S source.1) targetState
    S.coarse.faceEdges

/-- Total target Casimir excess above the source's parity-ground channel. -/
def positivePhysicalSourceParityExcitationCasimirExcess
    (S : SlabScalePair) (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling) : Nat :=
  spinFourParityExcitationCasimirExcessOn
    (wholeSlabFinePacketTotalLabelling S source.1) targetState
    S.coarse.faceEdges

/-- All-face lowering multiplicity times target representation dimension. -/
def positivePhysicalSourceLoweringFaceCoefficientProduct
    (S : SlabScalePair) (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling) : Nat :=
  spinFourLoweringFaceCoefficientProductOn
    (wholeSlabFinePacketTotalLabelling S source.1) targetState
    S.coarse.faceEdges

/-- All-face parity-ground multiplicity times parity-ground dimension. -/
def positivePhysicalSourceParityGroundFaceCoefficientProduct
    (S : SlabScalePair) (source : PositivePhysicalSource S) : Nat :=
  spinFourParityGroundFaceCoefficientProductOn
    (wholeSlabFinePacketTotalLabelling S source.1)
    S.coarse.faceEdges

private theorem coarseTargetSpin_le_four
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {targetState : EdgeLabelling}
    (htarget : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    targetState faceId <= 4 := by
  have hsound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htarget
  have hbound := Nat.le_of_lt_succ (hsound.1 faceId hface)
  rw [S.coarse_cutoff, hfineCutoff] at hbound
  omega

/-- On a complete positive source row, the exact all-face fusion tilt is at
most `2^activity` times the certified parity-ground tilt. -/
theorem spinFourLoweringMultiplicityProduct_le_twoPow_mul_parityGroundProduct
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    spinFourLoweringMultiplicityProduct S
        (wholeSlabFinePacketTotalLabelling S source.1) targetState <=
      2 ^ positivePhysicalSourceParityExcitationActivity
          S source targetState *
        spinFourParityGroundMultiplicityProduct S
          (wholeSlabFinePacketTotalLabelling S source.1) := by
  have hparts := (mem_spinFourLoweringTargets_iff S _ _).mp htarget
  unfold spinFourLoweringMultiplicityProduct
    spinFourParityGroundMultiplicityProduct
    positivePhysicalSourceParityExcitationActivity
  exact spinFourLoweringMultiplicityProductOn_le_twoPow_mul_ground
    (wholeSlabFinePacketTotalLabelling S source.1) targetState
      S.coarse.faceEdges
      (fun faceId hface =>
        wholeSlabFinePacketTotalLabelling_le_four
          S hfineCutoff source.2.1 faceId hface)
      (fun faceId hface =>
        coarseTargetSpin_le_four S hfineCutoff hparts.1 faceId hface)
      hparts.2

/-- On the actual complete cutoff-one-to-cutoff-four lowering row, the full
face coefficient (fusion multiplicity and SU(2) dimension) times its excess
heat power is bounded by the parity-ground face coefficient and the explicit
activity `(5*w^8)^K`.  Link multiplicities are not part of this statement. -/
theorem positivePhysicalSourceLoweringFaceCoefficient_mul_excitationHeat_le_ground_mul_activity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarse0 : (0 : Q') <= S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling <= (1 : Q'))
    (source : PositivePhysicalSource S) (targetState : EdgeLabelling)
    (htarget : targetState ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)) :
    Q'.ofNat
          (positivePhysicalSourceLoweringFaceCoefficientProduct
            S source targetState) *
        qpow S.coarse.coupling
          (positivePhysicalSourceParityExcitationCasimirExcess
            S source targetState) <=
      Q'.ofNat
          (positivePhysicalSourceParityGroundFaceCoefficientProduct S source) *
        qpow
          (spinFourParityExcitationFaceActivityRate S.coarse.coupling)
          (positivePhysicalSourceParityExcitationActivity
            S source targetState) := by
  have hparts := (mem_spinFourLoweringTargets_iff S _ _).mp htarget
  unfold positivePhysicalSourceLoweringFaceCoefficientProduct
    positivePhysicalSourceParityExcitationCasimirExcess
    positivePhysicalSourceParityGroundFaceCoefficientProduct
    positivePhysicalSourceParityExcitationActivity
  exact
    spinFourLoweringFaceCoefficientProductOn_mul_excitationHeat_le_ground_mul_activity
      S.coarse.coupling hcoarse0 hcoarse1
      (wholeSlabFinePacketTotalLabelling S source.1) targetState
      S.coarse.faceEdges
      (fun faceId hface =>
        wholeSlabFinePacketTotalLabelling_le_four
          S hfineCutoff source.2.1 faceId hface)
      (fun faceId hface =>
        coarseTargetSpin_le_four S hfineCutoff hparts.1 faceId hface)
      hparts.2

#print axioms spinFourLoweringMultiplicity_le_twoPow_mul_parityGround
#print axioms spinFourParityExcitationTiltActivityRate
#print axioms qpow_spinFourParityExcitationTiltActivityRate_eqv
#print axioms twoPow_mul_qpow_excess_le_excitationTiltActivity
#print axioms naturalTilt_mul_qpow_excess_le_ground_mul_activity
#print axioms spinFourLoweringMultiplicity_mul_excitationHeat_le_ground_mul_activity
#print axioms spinFourParityGroundDimension
#print axioms spinFourLoweringMultiplicity_mul_targetDimension_le_fivePow_mul_ground
#print axioms spinFourParityExcitationFaceActivityRate
#print axioms qpow_spinFourParityExcitationFaceActivityRate_eqv
#print axioms naturalFaceTilt_mul_qpow_excess_le_ground_mul_activity
#print axioms spinFourLoweringFaceCoefficient_mul_excitationHeat_le_ground_mul_activity
#print axioms spinFourParityExcitationMassOn
#print axioms spinFourParityExcitationCasimirExcessOn
#print axioms spinFourParityGroundMultiplicityProductOn
#print axioms spinFourLoweringFaceCoefficientProductOn
#print axioms spinFourParityGroundFaceCoefficientProductOn
#print axioms spinFourLoweringMultiplicityProductOn_le_twoPow_mul_ground
#print axioms spinFourLoweringFaceCoefficientProductOn_le_fivePow_mul_ground
#print axioms eight_mul_spinFourParityExcitationMassOn_le_casimirExcessOn
#print axioms spinFourLoweringMultiplicityProductOn_mul_excitationHeat_le_ground_mul_activity
#print axioms spinFourLoweringFaceCoefficientProductOn_mul_excitationHeat_le_ground_mul_activity
#print axioms positivePhysicalSourceParityExcitationActivity
#print axioms positivePhysicalSourceParityExcitationCasimirExcess
#print axioms positivePhysicalSourceLoweringFaceCoefficientProduct
#print axioms positivePhysicalSourceParityGroundFaceCoefficientProduct
#print axioms spinFourLoweringMultiplicityProduct_le_twoPow_mul_parityGroundProduct
#print axioms positivePhysicalSourceLoweringFaceCoefficient_mul_excitationHeat_le_ground_mul_activity

end YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound
