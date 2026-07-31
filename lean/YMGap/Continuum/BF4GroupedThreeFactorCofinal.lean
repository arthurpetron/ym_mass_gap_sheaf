/-
# Three-factor cofinality for the grouped BF4 packet

The finite grouped-carrier theorem rewrites the all-label packet square as
one boundary insertion times three positive Taylor factors: source diagonal,
target diagonal, and kinetic cross.  This file supplies the analytic net
layer.  The three cutoffs are allowed to vary independently, and an explicit
factorial-tail modulus controls the resulting rectangular Haar net.

The argument is deliberately coefficientwise.  Each change of one cutoff is
one literal Taylor block.  Haar integration contracts coefficient `L¹`, while
the other two factors have uniform positive-exponential bounds.  Splitting
the requested tolerance into quarters therefore gives a common modulus for
all three directions without choosing a diagonal subnet.

## Axiom gate

Finite lists, exact `Q'` algebra, and the constructive factorial-tail bounds
only.  No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom,
choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedCarrierMertens
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.BF4GroupedThreeFactorCofinal

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.RatNat
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ExpProductFloor
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionShiftedLimit
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedCarrierMertens
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.BF4GroupedHolonomyCrossMajorant
open YMGap.Continuum.BF4GroupedHolonomyPositiveLimit
open YMGap.Continuum.BF4GroupedPhysicalActionShift
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Q'.invSucc_num, Q'.invSucc_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic positive Taylor blocks -/

/-- One ordinary positive polynomial Taylor coefficient. -/
def positivePolynomialTaylorTerm
    (polynomial : RatPoly) (exponent : Nat) : RatPoly :=
  polySmul (ExpNeg.termAbs 1 exponent)
    (polynomialPower polynomial exponent)

/-- Literal coefficient block with exponents in `[start,start+distance)`. -/
def positivePolynomialTaylorBlock
    (polynomial : RatPoly) (start : Nat) : Nat → RatPoly
  | 0 => polyZero
  | distance + 1 =>
      polyAdd
        (positivePolynomialTaylorBlock polynomial start distance)
        (positivePolynomialTaylorTerm polynomial (start + distance))

private theorem polyMul_add_left_exact_local
    (left right factor : RatPoly) :
    polyMul (polyAdd left right) factor =
      polyAdd (polyMul left factor) (polyMul right factor) := by
  simp [polyMul, polyAdd]

private theorem quaternionHaar_polyMul_one_left_local
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks (polyMul polyOne polynomial) ≈
      quaternionHaar blocks polynomial := by
  exact Q'.eqv_trans _ _ _
    (quaternionHaar_polyMul_comm blocks polyOne polynomial)
    (quaternionHaar_polyMul_one_right blocks polynomial)

private theorem mul_four_move_first_local
    (outer selected second third : Q') :
    outer * ((selected * second) * third) ≈
      ((outer * second) * third) * selected := by
  q_ring

private theorem mul_four_move_second_local
    (outer first selected third : Q') :
    outer * ((first * selected) * third) ≈
      ((outer * first) * third) * selected := by
  q_ring

private theorem mul_four_keep_last_local
    (outer first second selected : Q') :
    outer * ((first * second) * selected) ≈
      ((outer * first) * second) * selected := by
  q_ring

private theorem add_four_reassoc_local (outer quarter : Q') :
    (((outer + quarter) + quarter) + quarter) + quarter ≈
      outer + (((quarter + quarter) + quarter) + quarter) := by
  q_ring

private theorem two_halves_trans_local
    (first middle last epsilon : Q')
    (hfirst : first ≤ middle + HalfPow.half * epsilon)
    (hlast : middle ≤ last + HalfPow.half * epsilon) :
    first ≤ last + epsilon := by
  refine Q'.le_trans' _ _ _ hfirst ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ (HalfPow.half * epsilon) hlast) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _
    (last +
      ((HalfPow.half * epsilon) +
        (HalfPow.half * epsilon))) _
    (Q'.add_assoc_eqv last
      (HalfPow.half * epsilon)
      (HalfPow.half * epsilon)) ?_
  exact Q'.add_eqv_congr_left last _ _
    (ExpNeg.two_halves epsilon)

/-- A later ordinary positive Taylor partial is the earlier partial plus its
literal omitted coefficient block. -/
theorem positivePolynomialTaylorPartial_add_block
    (polynomial : RatPoly) (start : Nat) :
    ∀ distance : Nat,
      positivePolynomialTaylorPartial polynomial (start + distance) =
        polyAdd
          (positivePolynomialTaylorPartial polynomial start)
          (positivePolynomialTaylorBlock polynomial start distance)
  | 0 => by
      simp [positivePolynomialTaylorBlock, polyAdd, polyZero]
  | distance + 1 => by
      rw [show start + (distance + 1) =
        (start + distance) + 1 by omega]
      change
        polyAdd
            (positivePolynomialTaylorPartial polynomial (start + distance))
            (positivePolynomialTaylorTerm polynomial (start + distance)) =
          polyAdd
            (positivePolynomialTaylorPartial polynomial start)
            (polyAdd
              (positivePolynomialTaylorBlock polynomial start distance)
              (positivePolynomialTaylorTerm polynomial (start + distance)))
      rw [positivePolynomialTaylorPartial_add_block polynomial start distance]
      exact List.append_assoc _ _ _

/-- The syntactic coefficient norm used by the generic Taylor majorant. -/
def positivePolynomialTaylorL1 (polynomial : RatPoly) : Q' :=
  polynomialCoefficientL1 polynomial

theorem positivePolynomialTaylorL1_nonnegative
    (polynomial : RatPoly) :
    (0 : Q') ≤ positivePolynomialTaylorL1 polynomial :=
  polynomialCoefficientL1_nonnegative polynomial

/-- One ordinary polynomial Taylor coefficient is bounded by the matching
scalar factorial coefficient at the polynomial's coefficient norm. -/
theorem positivePolynomialTaylorTerm_l1_le
    (polynomial : RatPoly) (exponent : Nat) :
    polynomialCoefficientL1
        (positivePolynomialTaylorTerm polynomial exponent) ≤
      ExpNeg.termAbs
        (positivePolynomialTaylorL1 polynomial) exponent := by
  let unitTerm := ExpNeg.termAbs 1 exponent
  let size := positivePolynomialTaylorL1 polynomial
  have hunit0 : (0 : Q') ≤ unitTerm :=
    ExpNeg.termAbs_nonneg 1 (by decide) exponent
  have habsUnit : Q'.abs unitTerm = unitTerm := by
    unfold Q'.abs
    rw [if_pos hunit0]
  unfold positivePolynomialTaylorTerm
  refine Q'.le_trans' _ _ _
    (polynomialCoefficientL1_smul_le unitTerm
      (polynomialPower polynomial exponent)) ?_
  rw [habsUnit]
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (polynomialCoefficientL1_polynomialPower_le
        polynomial exponent)
      hunit0) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv unitTerm (qpow size exponent))
      (Q'.eqv_symm
        (termAbs_eq_qpow_mul_unit size exponent)))

/-- The coefficient norm of a finite ordinary positive Taylor partial is
bounded by the corresponding scalar exponential partial. -/
theorem positivePolynomialTaylorPartial_l1_le
    (polynomial : RatPoly) :
    ∀ order : Nat,
      polynomialCoefficientL1
          (positivePolynomialTaylorPartial polynomial order) ≤
        ExpNeg.partialSumAbs
          (positivePolynomialTaylorL1 polynomial) order
  | 0 => Q'.le_refl' 0
  | order + 1 => by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (polynomialCoefficientL1_polyAdd
            (positivePolynomialTaylorPartial polynomial order)
            (positivePolynomialTaylorTerm polynomial order))) ?_
      exact Q'.add_le_add
        (positivePolynomialTaylorPartial_l1_le polynomial order)
        (positivePolynomialTaylorTerm_l1_le polynomial order)

/-- Uniform coefficient bound for every cutoff of one ordinary positive
Taylor factor. -/
def positivePolynomialTaylorBound (polynomial : RatPoly) : Q' :=
  expPosBound (positivePolynomialTaylorL1 polynomial)

theorem positivePolynomialTaylorBound_nonnegative
    (polynomial : RatPoly) :
    (0 : Q') ≤ positivePolynomialTaylorBound polynomial :=
  Q'.le_of_lt
    (expPosBound_pos
      (positivePolynomialTaylorL1 polynomial)
      (positivePolynomialTaylorL1_nonnegative polynomial))

theorem positivePolynomialTaylorPartial_l1_uniform
    (polynomial : RatPoly) (order : Nat) :
    polynomialCoefficientL1
        (positivePolynomialTaylorPartial polynomial order) ≤
      positivePolynomialTaylorBound polynomial := by
  exact Q'.le_trans' _ _ _
    (positivePolynomialTaylorPartial_l1_le polynomial order)
    (partialSumAbs_le_expPosBound
      (positivePolynomialTaylorL1 polynomial)
      (positivePolynomialTaylorL1_nonnegative polynomial)
      order)

/-- Scalar coefficient mass of a literal ordinary Taylor block. -/
def positivePolynomialTaylorL1Block
    (polynomial : RatPoly) (start : Nat) : Nat → Q'
  | 0 => 0
  | distance + 1 =>
      positivePolynomialTaylorL1Block polynomial start distance +
        polynomialCoefficientL1
          (positivePolynomialTaylorTerm polynomial (start + distance))

theorem positivePolynomialTaylorL1Block_le
    (polynomial : RatPoly) (start : Nat) :
    ∀ distance : Nat,
      positivePolynomialTaylorL1Block polynomial start distance ≤
        ExpNeg.blockAbs
          (positivePolynomialTaylorL1 polynomial) start distance
  | 0 => Q'.le_refl' 0
  | distance + 1 =>
      Q'.add_le_add
        (positivePolynomialTaylorL1Block_le
          polynomial start distance)
        (positivePolynomialTaylorTerm_l1_le
          polynomial (start + distance))

theorem positivePolynomialTaylorBlock_l1_le
    (polynomial : RatPoly) (start : Nat) :
    ∀ distance : Nat,
      polynomialCoefficientL1
          (positivePolynomialTaylorBlock polynomial start distance) ≤
        positivePolynomialTaylorL1Block polynomial start distance
  | 0 => Q'.le_refl' 0
  | distance + 1 => by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (polynomialCoefficientL1_polyAdd
            (positivePolynomialTaylorBlock polynomial start distance)
            (positivePolynomialTaylorTerm polynomial (start + distance)))) ?_
      exact Q'.add_le_add
        (positivePolynomialTaylorBlock_l1_le
          polynomial start distance)
        (Q'.le_refl' _)

/-- Explicit unscaled tail modulus for every omitted ordinary Taylor block. -/
def positivePolynomialTaylorModulus
    (polynomial : RatPoly) (epsilon : Q') : Nat :=
  max
    (halfRatioCutoff (positivePolynomialTaylorL1 polynomial))
    (ExpNeg.termAbsModulus
      (positivePolynomialTaylorL1 polynomial)
      (HalfPow.half * epsilon))

theorem positivePolynomialTaylorBlock_l1_le_of_modulus
    (polynomial : RatPoly)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (start distance : Nat)
    (hstart :
      positivePolynomialTaylorModulus polynomial epsilon ≤ start) :
    polynomialCoefficientL1
        (positivePolynomialTaylorBlock polynomial start distance) ≤
      epsilon := by
  let size := positivePolynomialTaylorL1 polynomial
  have hsize0 : (0 : Q') ≤ size :=
    positivePolynomialTaylorL1_nonnegative polynomial
  have hepsilon0 : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  have hhalf : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hcut : halfRatioCutoff size ≤ start :=
    Nat.le_trans (Nat.le_max_left _ _) hstart
  have hterm :
      ExpNeg.termAbs size start ≤ HalfPow.half * epsilon :=
    ExpNeg.termAbs_le_of_modulus_le
      size (HalfPow.half * epsilon) hsize0 hhalf start
      (Nat.le_trans (Nat.le_max_right _ _) hstart)
  exact Q'.le_trans' _ _ _
    (positivePolynomialTaylorBlock_l1_le polynomial start distance)
    (Q'.le_trans' _ _ _
      (positivePolynomialTaylorL1Block_le polynomial start distance)
      (ExpNeg.expNeg_tail_bound
        size hsize0 epsilon hepsilon0 start hcut hterm distance))

/-! ## 2. The literal three-factor rectangular Haar net -/

/-- Ordinary cross Taylor notation agrees with the all-label cross partial. -/
theorem sourceTargetKineticCrossTaylorPartial_eq_positive :
    ∀ order : Nat,
      sourceTargetKineticCrossTaylorPartial order =
        positivePolynomialTaylorPartial
          sourceTargetKineticCrossPolynomial order
  | 0 => rfl
  | order + 1 => by
      simp only [sourceTargetKineticCrossTaylorPartial,
        positivePolynomialTaylorPartial]
      change
        polyAdd (sourceTargetKineticCrossTaylorPartial order)
            (polySmul (ExpNeg.termAbs 1 order)
              (polynomialPower sourceTargetKineticCrossPolynomial order)) =
          polyAdd
            (positivePolynomialTaylorPartial
              sourceTargetKineticCrossPolynomial order)
            (polySmul (ExpNeg.termAbs 1 order)
              (polynomialPower sourceTargetKineticCrossPolynomial order))
      rw [sourceTargetKineticCrossTaylorPartial_eq_positive order]

/-- The independent source/target/cross Taylor rectangle under the literal
reflected packet boundary. -/
def abstractPacketRectangularHaar
    (sourceOrder targetOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  quaternionHaar 10
    (polyMul
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (polyMul
        (polyMul
          (positivePolynomialTaylorPartial
            sourceDiagonalComplementPolynomial sourceOrder)
          (positivePolynomialTaylorPartial
            targetDiagonalComplementPolynomial targetOrder))
        (positivePolynomialTaylorPartial
          sourceTargetKineticCrossPolynomial crossOrder)))

/-- The finite all-label grouped square is the `(d,d,c+1)` member of the
ordinary three-factor rectangle. -/
theorem bf4PacketGroupedSquare_haar_eqv_abstractRectangle
    (diagonalOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    quaternionHaar 10
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder packet) ≈
      abstractPacketRectangularHaar
        diagonalOrder diagonalOrder (crossOrder + 1) packet := by
  have hfinite :=
    bf4PacketGroupedSquarePolynomial_eqv_rectangularPartial
      diagonalOrder crossOrder packet
  have hsource := sourceDiagonalFeynmanKacPartial_eqv_ordinary diagonalOrder
  have hcross : TenHaarCarrierEqv
      (sourceTargetKineticCrossTaylorPartial (crossOrder + 1))
      (positivePolynomialTaylorPartial
        sourceTargetKineticCrossPolynomial (crossOrder + 1)) := by
    rw [sourceTargetKineticCrossTaylorPartial_eq_positive]
    exact TenHaarCarrierEqv.refl _
  have hrect : TenHaarCarrierEqv
      (polyMul
        (bf4PacketRawReflectedBoundaryPolynomial packet)
        (polyMul
          (polyMul
            (sourceDiagonalFeynmanKacPartial diagonalOrder)
            (targetDiagonalFeynmanKacPartial diagonalOrder))
          (sourceTargetKineticCrossTaylorPartial (crossOrder + 1))))
      (polyMul
        (bf4PacketRawReflectedBoundaryPolynomial packet)
        (polyMul
          (polyMul
            (positivePolynomialTaylorPartial
              sourceDiagonalComplementPolynomial diagonalOrder)
            (positivePolynomialTaylorPartial
              targetDiagonalComplementPolynomial diagonalOrder))
          (positivePolynomialTaylorPartial
            sourceTargetKineticCrossPolynomial (crossOrder + 1)))) := by
    exact TenHaarCarrierEqv.mul_left
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (TenHaarCarrierEqv.mul_congr
        (TenHaarCarrierEqv.mul_congr hsource
          (TenHaarCarrierEqv.refl _))
        hcross)
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul polyOne
        (bf4PacketGroupedSquarePolynomial
          diagonalOrder crossOrder packet))) _
    (Q'.eqv_symm
      (quaternionHaar_polyMul_one_left_local 10 _)) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul polyOne
        (polyMul
          (bf4PacketRawReflectedBoundaryPolynomial packet)
          (polyMul
            (polyMul
              (sourceDiagonalFeynmanKacPartial diagonalOrder)
              (targetDiagonalFeynmanKacPartial diagonalOrder))
            (sourceTargetKineticCrossTaylorPartial
              (crossOrder + 1)))))) _
    (hfinite polyOne) ?_
  refine Q'.eqv_trans _
    (quaternionHaar 10
      (polyMul polyOne
        (polyMul
          (bf4PacketRawReflectedBoundaryPolynomial packet)
          (polyMul
            (polyMul
              (positivePolynomialTaylorPartial
                sourceDiagonalComplementPolynomial diagonalOrder)
              (positivePolynomialTaylorPartial
                targetDiagonalComplementPolynomial diagonalOrder))
            (positivePolynomialTaylorPartial
              sourceTargetKineticCrossPolynomial
              (crossOrder + 1)))))) _
    (hrect polyOne) ?_
  exact quaternionHaar_polyMul_one_left_local 10 _

/-! ## 3. Uniform spectator bounds and scaled moduli -/

def abstractPacketBoundaryL1
    (packet : BF4HolonomyStatePacket) : Q' :=
  polynomialCoefficientL1
    (bf4PacketRawReflectedBoundaryPolynomial packet)

theorem abstractPacketBoundaryL1_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤ abstractPacketBoundaryL1 packet :=
  polynomialCoefficientL1_nonnegative _

def abstractPacketSourceTaylorBound : Q' :=
  positivePolynomialTaylorBound
    sourceDiagonalComplementPolynomial

def abstractPacketTargetTaylorBound : Q' :=
  positivePolynomialTaylorBound
    targetDiagonalComplementPolynomial

def abstractPacketCrossTaylorBound : Q' :=
  positivePolynomialTaylorBound
    sourceTargetKineticCrossPolynomial

theorem abstractPacketSourceTaylorBound_nonnegative :
    (0 : Q') ≤ abstractPacketSourceTaylorBound :=
  positivePolynomialTaylorBound_nonnegative _

theorem abstractPacketTargetTaylorBound_nonnegative :
    (0 : Q') ≤ abstractPacketTargetTaylorBound :=
  positivePolynomialTaylorBound_nonnegative _

theorem abstractPacketCrossTaylorBound_nonnegative :
    (0 : Q') ≤ abstractPacketCrossTaylorBound :=
  positivePolynomialTaylorBound_nonnegative _

/-- Spectator scale when the source cutoff changes. -/
def abstractPacketSourceTailScale
    (packet : BF4HolonomyStatePacket) : Q' :=
  (abstractPacketBoundaryL1 packet *
      abstractPacketTargetTaylorBound) *
    abstractPacketCrossTaylorBound

/-- Spectator scale when the target cutoff changes. -/
def abstractPacketTargetTailScale
    (packet : BF4HolonomyStatePacket) : Q' :=
  (abstractPacketBoundaryL1 packet *
      abstractPacketSourceTaylorBound) *
    abstractPacketCrossTaylorBound

/-- Spectator scale when the cross cutoff changes. -/
def abstractPacketCrossTailScale
    (packet : BF4HolonomyStatePacket) : Q' :=
  (abstractPacketBoundaryL1 packet *
      abstractPacketSourceTaylorBound) *
    abstractPacketTargetTaylorBound

theorem abstractPacketSourceTailScale_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤ abstractPacketSourceTailScale packet :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (abstractPacketBoundaryL1_nonnegative packet)
      abstractPacketTargetTaylorBound_nonnegative)
    abstractPacketCrossTaylorBound_nonnegative

theorem abstractPacketTargetTailScale_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤ abstractPacketTargetTailScale packet :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (abstractPacketBoundaryL1_nonnegative packet)
      abstractPacketSourceTaylorBound_nonnegative)
    abstractPacketCrossTaylorBound_nonnegative

theorem abstractPacketCrossTailScale_nonnegative
    (packet : BF4HolonomyStatePacket) :
    (0 : Q') ≤ abstractPacketCrossTailScale packet :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (abstractPacketBoundaryL1_nonnegative packet)
      abstractPacketSourceTaylorBound_nonnegative)
    abstractPacketTargetTaylorBound_nonnegative

/-- Tolerance paid to an unscaled Taylor block before its spectator scale is
restored.  `invSucc` keeps this definition total at scale zero. -/
def abstractPacketScaledTailTolerance
    (scale epsilon : Q') : Q' :=
  epsilon * Q'.invSucc scale.num.toNat

theorem abstractPacketScaledTailTolerance_pos
    (scale epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < abstractPacketScaledTailTolerance scale epsilon :=
  Q'.mul_pos hepsilon (Q'.invSucc_pos scale.num.toNat)

/-- Generic scaled modulus for one polynomial Taylor factor. -/
def positivePolynomialScaledTaylorModulus
    (polynomial : RatPoly) (scale epsilon : Q') : Nat :=
  positivePolynomialTaylorModulus polynomial
    (abstractPacketScaledTailTolerance scale epsilon)

theorem positivePolynomialTaylorBlock_scaled_le
    (polynomial : RatPoly) (scale epsilon : Q')
    (hscale : (0 : Q') ≤ scale)
    (hepsilon : (0 : Q') < epsilon)
    (start distance : Nat)
    (hstart :
      positivePolynomialScaledTaylorModulus
        polynomial scale epsilon ≤ start) :
    scale * polynomialCoefficientL1
        (positivePolynomialTaylorBlock polynomial start distance) ≤
      epsilon := by
  let delta := abstractPacketScaledTailTolerance scale epsilon
  have hdelta : (0 : Q') < delta :=
    abstractPacketScaledTailTolerance_pos scale epsilon hepsilon
  have hdelta0 : (0 : Q') ≤ delta := Q'.le_of_lt hdelta
  have hepsilon0 : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (positivePolynomialTaylorBlock_l1_le_of_modulus
        polynomial delta hdelta start distance hstart)
      hscale) ?_
  exact ExpNeg.mul_le_of_mul_invSucc_toNat
    scale epsilon hscale hepsilon0

/-! ## 4. One-coordinate rectangular increments -/

def abstractPacketSourceIncrement
    (start distance targetOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  quaternionHaar 10
    (polyMul
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (polyMul
        (polyMul
          (positivePolynomialTaylorBlock
            sourceDiagonalComplementPolynomial start distance)
          (positivePolynomialTaylorPartial
            targetDiagonalComplementPolynomial targetOrder))
        (positivePolynomialTaylorPartial
          sourceTargetKineticCrossPolynomial crossOrder)))

def abstractPacketTargetIncrement
    (sourceOrder start distance crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  quaternionHaar 10
    (polyMul
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (polyMul
        (polyMul
          (positivePolynomialTaylorPartial
            sourceDiagonalComplementPolynomial sourceOrder)
          (positivePolynomialTaylorBlock
            targetDiagonalComplementPolynomial start distance))
        (positivePolynomialTaylorPartial
          sourceTargetKineticCrossPolynomial crossOrder)))

def abstractPacketCrossIncrement
    (sourceOrder targetOrder start distance : Nat)
    (packet : BF4HolonomyStatePacket) : Q' :=
  quaternionHaar 10
    (polyMul
      (bf4PacketRawReflectedBoundaryPolynomial packet)
      (polyMul
        (polyMul
          (positivePolynomialTaylorPartial
            sourceDiagonalComplementPolynomial sourceOrder)
          (positivePolynomialTaylorPartial
            targetDiagonalComplementPolynomial targetOrder))
        (positivePolynomialTaylorBlock
          sourceTargetKineticCrossPolynomial start distance)))

private theorem quaternionHaar_four_product_abs_le
    (boundary first second third : RatPoly) :
    Q'.abs
        (quaternionHaar 10
          (polyMul boundary
            (polyMul (polyMul first second) third))) ≤
      polynomialCoefficientL1 boundary *
        ((polynomialCoefficientL1 first *
            polynomialCoefficientL1 second) *
          polynomialCoefficientL1 third) := by
  have hfirst0 : (0 : Q') ≤ polynomialCoefficientL1 first :=
    polynomialCoefficientL1_nonnegative first
  have hsecond0 : (0 : Q') ≤ polynomialCoefficientL1 second :=
    polynomialCoefficientL1_nonnegative second
  have hthird0 : (0 : Q') ≤ polynomialCoefficientL1 third :=
    polynomialCoefficientL1_nonnegative third
  have hinner0 :
      (0 : Q') ≤ polynomialCoefficientL1 (polyMul first second) :=
    polynomialCoefficientL1_nonnegative _
  have hlast0 :
      (0 : Q') ≤
        polynomialCoefficientL1
          (polyMul (polyMul first second) third) :=
    polynomialCoefficientL1_nonnegative _
  refine Q'.le_trans' _ _ _
    (quaternionHaar_abs_le_coefficientL1 10 _) ?_
  refine Q'.le_trans' _ _ _
    (polynomialCoefficientL1_mul_le boundary
      (polyMul (polyMul first second) third)) ?_
  refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_
    (polynomialCoefficientL1_nonnegative boundary)
  refine Q'.le_trans' _ _ _
    (polynomialCoefficientL1_mul_le
      (polyMul first second) third) ?_
  refine Q'.mul_le_mul_of_nonneg_right _ _ _
    (polynomialCoefficientL1_mul_le first second)
    hthird0

private theorem quaternionHaar_four_product_abs_le_of_bounds
    (boundary first second third : RatPoly)
    (firstBound secondBound thirdBound : Q')
    (hfirst : polynomialCoefficientL1 first ≤ firstBound)
    (hsecond : polynomialCoefficientL1 second ≤ secondBound)
    (hthird : polynomialCoefficientL1 third ≤ thirdBound)
    (hfirstBound : (0 : Q') ≤ firstBound)
    (hsecondBound : (0 : Q') ≤ secondBound) :
    Q'.abs
        (quaternionHaar 10
          (polyMul boundary
            (polyMul (polyMul first second) third))) ≤
      polynomialCoefficientL1 boundary *
        ((firstBound * secondBound) * thirdBound) := by
  refine Q'.le_trans' _ _ _
    (quaternionHaar_four_product_abs_le
      boundary first second third) ?_
  refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_
    (polynomialCoefficientL1_nonnegative boundary)
  have hpairs :
      polynomialCoefficientL1 first *
          polynomialCoefficientL1 second ≤
        firstBound * secondBound :=
    Q'.mul_le_mul_of_nonneg
      hfirst hsecond hfirstBound
      (polynomialCoefficientL1_nonnegative second)
  exact Q'.mul_le_mul_of_nonneg
    hpairs hthird
    (Q'.mul_nonneg _ _ hfirstBound hsecondBound)
    (polynomialCoefficientL1_nonnegative third)

theorem abstractPacketSourceIncrement_abs_le
    (start distance targetOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    Q'.abs
        (abstractPacketSourceIncrement
          start distance targetOrder crossOrder packet) ≤
      abstractPacketSourceTailScale packet *
        polynomialCoefficientL1
          (positivePolynomialTaylorBlock
            sourceDiagonalComplementPolynomial start distance) := by
  let boundary := bf4PacketRawReflectedBoundaryPolynomial packet
  let block := positivePolynomialTaylorBlock
    sourceDiagonalComplementPolynomial start distance
  let target := positivePolynomialTaylorPartial
    targetDiagonalComplementPolynomial targetOrder
  let cross := positivePolynomialTaylorPartial
    sourceTargetKineticCrossPolynomial crossOrder
  have hblock0 : (0 : Q') ≤ polynomialCoefficientL1 block :=
    polynomialCoefficientL1_nonnegative block
  have hraw := quaternionHaar_four_product_abs_le_of_bounds
    boundary block target cross
    (polynomialCoefficientL1 block)
    abstractPacketTargetTaylorBound
    abstractPacketCrossTaylorBound
    (Q'.le_refl' _)
    (positivePolynomialTaylorPartial_l1_uniform
      targetDiagonalComplementPolynomial targetOrder)
    (positivePolynomialTaylorPartial_l1_uniform
      sourceTargetKineticCrossPolynomial crossOrder)
    hblock0
    abstractPacketTargetTaylorBound_nonnegative
  change
    Q'.abs
        (quaternionHaar 10
          (polyMul boundary
            (polyMul (polyMul block target) cross))) ≤
      abstractPacketSourceTailScale packet *
        polynomialCoefficientL1 block
  refine Q'.le_trans' _ _ _ hraw ?_
  exact Q'.le_of_eqv
    (mul_four_move_first_local
      (abstractPacketBoundaryL1 packet)
      (polynomialCoefficientL1 block)
      abstractPacketTargetTaylorBound
      abstractPacketCrossTaylorBound)

theorem abstractPacketTargetIncrement_abs_le
    (sourceOrder start distance crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    Q'.abs
        (abstractPacketTargetIncrement
          sourceOrder start distance crossOrder packet) ≤
      abstractPacketTargetTailScale packet *
        polynomialCoefficientL1
          (positivePolynomialTaylorBlock
            targetDiagonalComplementPolynomial start distance) := by
  let boundary := bf4PacketRawReflectedBoundaryPolynomial packet
  let source := positivePolynomialTaylorPartial
    sourceDiagonalComplementPolynomial sourceOrder
  let block := positivePolynomialTaylorBlock
    targetDiagonalComplementPolynomial start distance
  let cross := positivePolynomialTaylorPartial
    sourceTargetKineticCrossPolynomial crossOrder
  have hblock0 : (0 : Q') ≤ polynomialCoefficientL1 block :=
    polynomialCoefficientL1_nonnegative block
  have hraw := quaternionHaar_four_product_abs_le_of_bounds
    boundary source block cross
    abstractPacketSourceTaylorBound
    (polynomialCoefficientL1 block)
    abstractPacketCrossTaylorBound
    (positivePolynomialTaylorPartial_l1_uniform
      sourceDiagonalComplementPolynomial sourceOrder)
    (Q'.le_refl' _)
    (positivePolynomialTaylorPartial_l1_uniform
      sourceTargetKineticCrossPolynomial crossOrder)
    abstractPacketSourceTaylorBound_nonnegative
    hblock0
  change
    Q'.abs
        (quaternionHaar 10
          (polyMul boundary
            (polyMul (polyMul source block) cross))) ≤
      abstractPacketTargetTailScale packet *
        polynomialCoefficientL1 block
  refine Q'.le_trans' _ _ _ hraw ?_
  exact Q'.le_of_eqv
    (mul_four_move_second_local
      (abstractPacketBoundaryL1 packet)
      abstractPacketSourceTaylorBound
      (polynomialCoefficientL1 block)
      abstractPacketCrossTaylorBound)

theorem abstractPacketCrossIncrement_abs_le
    (sourceOrder targetOrder start distance : Nat)
    (packet : BF4HolonomyStatePacket) :
    Q'.abs
        (abstractPacketCrossIncrement
          sourceOrder targetOrder start distance packet) ≤
      abstractPacketCrossTailScale packet *
        polynomialCoefficientL1
          (positivePolynomialTaylorBlock
            sourceTargetKineticCrossPolynomial start distance) := by
  let boundary := bf4PacketRawReflectedBoundaryPolynomial packet
  let source := positivePolynomialTaylorPartial
    sourceDiagonalComplementPolynomial sourceOrder
  let target := positivePolynomialTaylorPartial
    targetDiagonalComplementPolynomial targetOrder
  let block := positivePolynomialTaylorBlock
    sourceTargetKineticCrossPolynomial start distance
  have hblock0 : (0 : Q') ≤ polynomialCoefficientL1 block :=
    polynomialCoefficientL1_nonnegative block
  have hraw := quaternionHaar_four_product_abs_le_of_bounds
    boundary source target block
    abstractPacketSourceTaylorBound
    abstractPacketTargetTaylorBound
    (polynomialCoefficientL1 block)
    (positivePolynomialTaylorPartial_l1_uniform
      sourceDiagonalComplementPolynomial sourceOrder)
    (positivePolynomialTaylorPartial_l1_uniform
      targetDiagonalComplementPolynomial targetOrder)
    (Q'.le_refl' _)
    abstractPacketSourceTaylorBound_nonnegative
    abstractPacketTargetTaylorBound_nonnegative
  change
    Q'.abs
        (quaternionHaar 10
          (polyMul boundary
            (polyMul (polyMul source target) block))) ≤
      abstractPacketCrossTailScale packet *
        polynomialCoefficientL1 block
  refine Q'.le_trans' _ _ _ hraw ?_
  exact Q'.le_of_eqv
    (mul_four_keep_last_local
      (abstractPacketBoundaryL1 packet)
      abstractPacketSourceTaylorBound
      abstractPacketTargetTaylorBound
      (polynomialCoefficientL1 block))

theorem abstractPacketRectangularHaar_source_add_block
    (start distance targetOrder crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    abstractPacketRectangularHaar
        (start + distance) targetOrder crossOrder packet ≈
      abstractPacketRectangularHaar
          start targetOrder crossOrder packet +
        abstractPacketSourceIncrement
          start distance targetOrder crossOrder packet := by
  unfold abstractPacketRectangularHaar
    abstractPacketSourceIncrement
  rw [positivePolynomialTaylorPartial_add_block]
  rw [polyMul_add_left_exact_local]
  rw [polyMul_add_left_exact_local]
  exact quaternionHaar_polyMul_add_right 10 _ _ _

theorem abstractPacketRectangularHaar_target_add_block
    (sourceOrder start distance crossOrder : Nat)
    (packet : BF4HolonomyStatePacket) :
    abstractPacketRectangularHaar
        sourceOrder (start + distance) crossOrder packet ≈
      abstractPacketRectangularHaar
          sourceOrder start crossOrder packet +
        abstractPacketTargetIncrement
          sourceOrder start distance crossOrder packet := by
  unfold abstractPacketRectangularHaar
    abstractPacketTargetIncrement
  rw [positivePolynomialTaylorPartial_add_block]
  let source := positivePolynomialTaylorPartial
    sourceDiagonalComplementPolynomial sourceOrder
  let earlier := positivePolynomialTaylorPartial
    targetDiagonalComplementPolynomial start
  let block := positivePolynomialTaylorBlock
    targetDiagonalComplementPolynomial start distance
  let cross := positivePolynomialTaylorPartial
    sourceTargetKineticCrossPolynomial crossOrder
  have hfirst := tenHaarCarrierEqv_polyMul_add_right
    source earlier block
  have hcross := TenHaarCarrierEqv.mul_right hfirst cross
  rw [polyMul_add_left_exact_local] at hcross
  exact Q'.eqv_trans _ _ _
    (hcross (bf4PacketRawReflectedBoundaryPolynomial packet))
    (quaternionHaar_polyMul_add_right 10 _ _ _)

theorem abstractPacketRectangularHaar_cross_add_block
    (sourceOrder targetOrder start distance : Nat)
    (packet : BF4HolonomyStatePacket) :
    abstractPacketRectangularHaar
        sourceOrder targetOrder (start + distance) packet ≈
      abstractPacketRectangularHaar
          sourceOrder targetOrder start packet +
        abstractPacketCrossIncrement
          sourceOrder targetOrder start distance packet := by
  unfold abstractPacketRectangularHaar
    abstractPacketCrossIncrement
  rw [positivePolynomialTaylorPartial_add_block]
  exact Q'.eqv_trans _ _ _
    ((tenHaarCarrierEqv_polyMul_add_right
      (polyMul
        (positivePolynomialTaylorPartial
          sourceDiagonalComplementPolynomial sourceOrder)
        (positivePolynomialTaylorPartial
          targetDiagonalComplementPolynomial targetOrder))
      (positivePolynomialTaylorPartial
        sourceTargetKineticCrossPolynomial start)
      (positivePolynomialTaylorBlock
        sourceTargetKineticCrossPolynomial start distance))
      (bf4PacketRawReflectedBoundaryPolynomial packet))
    (quaternionHaar_polyMul_add_right 10 _ _ _)

private theorem add_increment_close
    (earlier later increment epsilon : Q')
    (hdecompose : later ≈ earlier + increment)
    (hbound : Q'.abs increment ≤ epsilon) :
    later ≤ earlier + epsilon ∧
      earlier ≤ later + epsilon := by
  have hdifference : later + (-earlier) ≈ increment := by
    refine Q'.eqv_trans _
      ((earlier + increment) + (-earlier)) _
      (Q'.add_eqv_congr_right _ _ (-earlier) hdecompose) ?_
    refine Q'.eqv_trans _
      (earlier + (increment + (-earlier))) _
      (Q'.add_assoc_eqv earlier increment (-earlier)) ?_
    refine Q'.eqv_trans _
      (earlier + ((-earlier) + increment)) _
      (Q'.add_eqv_congr_left earlier _ _
        (Q'.add_comm_eqv increment (-earlier))) ?_
    refine Q'.eqv_trans _
      ((earlier + (-earlier)) + increment) _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv earlier (-earlier) increment)) ?_
    refine Q'.eqv_trans _ (0 + increment) _
      (Q'.add_eqv_congr_right _ _ increment
        (Q'.add_neg_self_eqv earlier)) ?_
    exact QPoly.q_zero_add_eqv increment
  have habs : Q'.abs (later + (-earlier)) ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) hbound
  exact
    ⟨ExpNeg.le_add_of_abs_sub_le habs,
     ExpNeg.le_add_of_abs_sub_le
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (ExpNeg.abs_sub_comm earlier later))
        habs)⟩

/-! ## 5. The quantitative three-factor cofinal modulus -/

def abstractPacketSourceModulus
    (packet : BF4HolonomyStatePacket) (epsilon : Q') : Nat :=
  positivePolynomialScaledTaylorModulus
    sourceDiagonalComplementPolynomial
    (abstractPacketSourceTailScale packet) epsilon

def abstractPacketTargetModulus
    (packet : BF4HolonomyStatePacket) (epsilon : Q') : Nat :=
  positivePolynomialScaledTaylorModulus
    targetDiagonalComplementPolynomial
    (abstractPacketTargetTailScale packet) epsilon

def abstractPacketCrossModulus
    (packet : BF4HolonomyStatePacket) (epsilon : Q') : Nat :=
  positivePolynomialScaledTaylorModulus
    sourceTargetKineticCrossPolynomial
    (abstractPacketCrossTailScale packet) epsilon

theorem abstractPacketRectangularHaar_source_cauchy
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (targetOrder crossOrder first second : Nat)
    (hfirst : abstractPacketSourceModulus packet epsilon ≤ first)
    (hsecond : abstractPacketSourceModulus packet epsilon ≤ second) :
    abstractPacketRectangularHaar first targetOrder crossOrder packet ≤
        abstractPacketRectangularHaar second targetOrder crossOrder packet + epsilon ∧
      abstractPacketRectangularHaar second targetOrder crossOrder packet ≤
        abstractPacketRectangularHaar first targetOrder crossOrder packet + epsilon := by
  have dir : ∀ smaller larger,
      abstractPacketSourceModulus packet epsilon ≤ smaller →
      smaller ≤ larger →
      abstractPacketRectangularHaar larger targetOrder crossOrder packet ≤
          abstractPacketRectangularHaar smaller targetOrder crossOrder packet + epsilon ∧
        abstractPacketRectangularHaar smaller targetOrder crossOrder packet ≤
          abstractPacketRectangularHaar larger targetOrder crossOrder packet + epsilon := by
    intro smaller larger hsmall hle
    obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le hle
    apply add_increment_close _ _ _ epsilon
      (abstractPacketRectangularHaar_source_add_block
        smaller distance targetOrder crossOrder packet)
    refine Q'.le_trans' _ _ _
      (abstractPacketSourceIncrement_abs_le
        smaller distance targetOrder crossOrder packet) ?_
    exact positivePolynomialTaylorBlock_scaled_le
      sourceDiagonalComplementPolynomial
      (abstractPacketSourceTailScale packet) epsilon
      (abstractPacketSourceTailScale_nonnegative packet)
      hepsilon smaller distance hsmall
  rcases Nat.le_total first second with h | h
  · exact (dir first second hfirst h).symm
  · exact dir second first hsecond h

theorem abstractPacketRectangularHaar_target_cauchy
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (sourceOrder crossOrder first second : Nat)
    (hfirst : abstractPacketTargetModulus packet epsilon ≤ first)
    (hsecond : abstractPacketTargetModulus packet epsilon ≤ second) :
    abstractPacketRectangularHaar sourceOrder first crossOrder packet ≤
        abstractPacketRectangularHaar sourceOrder second crossOrder packet + epsilon ∧
      abstractPacketRectangularHaar sourceOrder second crossOrder packet ≤
        abstractPacketRectangularHaar sourceOrder first crossOrder packet + epsilon := by
  have dir : ∀ smaller larger,
      abstractPacketTargetModulus packet epsilon ≤ smaller →
      smaller ≤ larger →
      abstractPacketRectangularHaar sourceOrder larger crossOrder packet ≤
          abstractPacketRectangularHaar sourceOrder smaller crossOrder packet + epsilon ∧
        abstractPacketRectangularHaar sourceOrder smaller crossOrder packet ≤
          abstractPacketRectangularHaar sourceOrder larger crossOrder packet + epsilon := by
    intro smaller larger hsmall hle
    obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le hle
    apply add_increment_close _ _ _ epsilon
      (abstractPacketRectangularHaar_target_add_block
        sourceOrder smaller distance crossOrder packet)
    refine Q'.le_trans' _ _ _
      (abstractPacketTargetIncrement_abs_le
        sourceOrder smaller distance crossOrder packet) ?_
    exact positivePolynomialTaylorBlock_scaled_le
      targetDiagonalComplementPolynomial
      (abstractPacketTargetTailScale packet) epsilon
      (abstractPacketTargetTailScale_nonnegative packet)
      hepsilon smaller distance hsmall
  rcases Nat.le_total first second with h | h
  · exact (dir first second hfirst h).symm
  · exact dir second first hsecond h

theorem abstractPacketRectangularHaar_cross_cauchy
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (sourceOrder targetOrder first second : Nat)
    (hfirst : abstractPacketCrossModulus packet epsilon ≤ first)
    (hsecond : abstractPacketCrossModulus packet epsilon ≤ second) :
    abstractPacketRectangularHaar sourceOrder targetOrder first packet ≤
        abstractPacketRectangularHaar sourceOrder targetOrder second packet + epsilon ∧
      abstractPacketRectangularHaar sourceOrder targetOrder second packet ≤
        abstractPacketRectangularHaar sourceOrder targetOrder first packet + epsilon := by
  have dir : ∀ smaller larger,
      abstractPacketCrossModulus packet epsilon ≤ smaller →
      smaller ≤ larger →
      abstractPacketRectangularHaar sourceOrder targetOrder larger packet ≤
          abstractPacketRectangularHaar sourceOrder targetOrder smaller packet + epsilon ∧
        abstractPacketRectangularHaar sourceOrder targetOrder smaller packet ≤
          abstractPacketRectangularHaar sourceOrder targetOrder larger packet + epsilon := by
    intro smaller larger hsmall hle
    obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le hle
    apply add_increment_close _ _ _ epsilon
      (abstractPacketRectangularHaar_cross_add_block
        sourceOrder targetOrder smaller distance packet)
    refine Q'.le_trans' _ _ _
      (abstractPacketCrossIncrement_abs_le
        sourceOrder targetOrder smaller distance packet) ?_
    exact positivePolynomialTaylorBlock_scaled_le
      sourceTargetKineticCrossPolynomial
      (abstractPacketCrossTailScale packet) epsilon
      (abstractPacketCrossTailScale_nonnegative packet)
      hepsilon smaller distance hsmall
  rcases Nat.le_total first second with h | h
  · exact (dir first second hfirst h).symm
  · exact dir second first hsecond h

private theorem three_quarters_trans
    (first second third last epsilon : Q')
    (hepsilon0 : (0 : Q') ≤ epsilon)
    (hfirst : first ≤ second + HalfPow.half * (HalfPow.half * epsilon))
    (hsecond : second ≤ third + HalfPow.half * (HalfPow.half * epsilon))
    (hthird : third ≤ last + HalfPow.half * (HalfPow.half * epsilon)) :
    first ≤ last + epsilon := by
  let quarter := HalfPow.half * (HalfPow.half * epsilon)
  refine Q'.le_trans' _ _ _ hfirst ?_
  have hthroughSecond :
      second + quarter ≤ (third + quarter) + quarter :=
    Q'.add_le_add_right _ _ quarter hsecond
  refine Q'.le_trans' _ _ _ hthroughSecond ?_
  have hthroughThird :
      (third + quarter) + quarter ≤
        ((last + quarter) + quarter) + quarter :=
    Q'.add_le_add_right _ _ quarter
      (Q'.add_le_add_right _ _ quarter hthird)
  refine Q'.le_trans' _ _ _ hthroughThird ?_
  have hquarter0 : (0 : Q') ≤ quarter := by
    exact Q'.mul_nonneg _ _ HalfPow.half_nonneg
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg hepsilon0)
  have hpad :
      ((last + quarter) + quarter) + quarter ≤
        (((last + quarter) + quarter) + quarter) + quarter :=
    Q'.add_le_self_of_nonneg _ quarter hquarter0
  refine Q'.le_trans' _ _ _ hpad ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _
    (last + (((quarter + quarter) + quarter) + quarter)) _
    (add_four_reassoc_local last quarter) ?_
  refine Q'.add_eqv_congr_left last _ _ ?_
  unfold quarter
  let halfEpsilon := HalfPow.half * epsilon
  have hpair :
      HalfPow.half * halfEpsilon +
          HalfPow.half * halfEpsilon ≈ halfEpsilon :=
    ExpNeg.two_halves halfEpsilon
  change
    (((HalfPow.half * halfEpsilon +
        HalfPow.half * halfEpsilon) +
      HalfPow.half * halfEpsilon) +
      HalfPow.half * halfEpsilon) ≈ epsilon
  refine Q'.eqv_trans _
    ((HalfPow.half * halfEpsilon +
        HalfPow.half * halfEpsilon) +
      (HalfPow.half * halfEpsilon +
        HalfPow.half * halfEpsilon)) _
    (Q'.add_assoc_eqv
      (HalfPow.half * halfEpsilon +
        HalfPow.half * halfEpsilon)
      (HalfPow.half * halfEpsilon)
      (HalfPow.half * halfEpsilon)) ?_
  refine Q'.eqv_trans _ (halfEpsilon + halfEpsilon) _
    (Q'.add_eqv_congr' hpair hpair) ?_
  exact ExpNeg.two_halves epsilon

/-- One cutoff dominating the source, target, and kinetic-cross factorial
tails at quarter tolerance. -/
def abstractPacketThreeFactorModulus
    (packet : BF4HolonomyStatePacket) (epsilon : Q') : Nat :=
  max
    (max
      (abstractPacketSourceModulus packet
        (HalfPow.half * (HalfPow.half * epsilon)))
      (abstractPacketTargetModulus packet
        (HalfPow.half * (HalfPow.half * epsilon))))
    (abstractPacketCrossModulus packet
      (HalfPow.half * (HalfPow.half * epsilon)))

/-- **Three-factor rectangular-net Cauchy theorem.**  All six cutoffs may be
unrelated.  Common cofinality beyond one explicit modulus suffices. -/
theorem abstractPacketRectangularHaar_joint_cauchy
    (packet : BF4HolonomyStatePacket)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (source₁ target₁ cross₁ source₂ target₂ cross₂ : Nat)
    (hsource₁ : abstractPacketThreeFactorModulus packet epsilon ≤ source₁)
    (htarget₁ : abstractPacketThreeFactorModulus packet epsilon ≤ target₁)
    (hcross₁ : abstractPacketThreeFactorModulus packet epsilon ≤ cross₁)
    (hsource₂ : abstractPacketThreeFactorModulus packet epsilon ≤ source₂)
    (htarget₂ : abstractPacketThreeFactorModulus packet epsilon ≤ target₂)
    (hcross₂ : abstractPacketThreeFactorModulus packet epsilon ≤ cross₂) :
    abstractPacketRectangularHaar source₁ target₁ cross₁ packet ≤
        abstractPacketRectangularHaar source₂ target₂ cross₂ packet + epsilon ∧
      abstractPacketRectangularHaar source₂ target₂ cross₂ packet ≤
        abstractPacketRectangularHaar source₁ target₁ cross₁ packet + epsilon := by
  let quarter := HalfPow.half * (HalfPow.half * epsilon)
  have hquarter : (0 : Q') < quarter :=
    ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon)
  have hsourceMod₁ : abstractPacketSourceModulus packet quarter ≤ source₁ :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hsource₁
  have hsourceMod₂ : abstractPacketSourceModulus packet quarter ≤ source₂ :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hsource₂
  have htargetMod₁ : abstractPacketTargetModulus packet quarter ≤ target₁ :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) htarget₁
  have htargetMod₂ : abstractPacketTargetModulus packet quarter ≤ target₂ :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) htarget₂
  have hcrossMod₁ : abstractPacketCrossModulus packet quarter ≤ cross₁ :=
    Nat.le_trans (Nat.le_max_right _ _) hcross₁
  have hcrossMod₂ : abstractPacketCrossModulus packet quarter ≤ cross₂ :=
    Nat.le_trans (Nat.le_max_right _ _) hcross₂
  have hs := abstractPacketRectangularHaar_source_cauchy
    packet quarter hquarter target₁ cross₁ source₁ source₂
    hsourceMod₁ hsourceMod₂
  have ht := abstractPacketRectangularHaar_target_cauchy
    packet quarter hquarter source₂ cross₁ target₁ target₂
    htargetMod₁ htargetMod₂
  have hc := abstractPacketRectangularHaar_cross_cauchy
    packet quarter hquarter source₂ target₂ cross₁ cross₂
    hcrossMod₁ hcrossMod₂
  exact
    ⟨three_quarters_trans
      (abstractPacketRectangularHaar source₁ target₁ cross₁ packet)
      (abstractPacketRectangularHaar source₂ target₁ cross₁ packet)
      (abstractPacketRectangularHaar source₂ target₂ cross₁ packet)
      (abstractPacketRectangularHaar source₂ target₂ cross₂ packet)
      epsilon (Q'.le_of_lt hepsilon) hs.1 ht.1 hc.1,
     three_quarters_trans
      (abstractPacketRectangularHaar source₂ target₂ cross₂ packet)
      (abstractPacketRectangularHaar source₂ target₂ cross₁ packet)
      (abstractPacketRectangularHaar source₂ target₁ cross₁ packet)
      (abstractPacketRectangularHaar source₁ target₁ cross₁ packet)
      epsilon (Q'.le_of_lt hepsilon) hc.2 ht.2 hs.2⟩

/-! ## 6. Located rectangular endpoint and arbitrary cofinal schedules -/

/-- The diagonal member matching the grouped convention: `stage` source and
target terms and `stage+1` cross terms. -/
def abstractPacketRectangularDiagonalPartial
    (packet : BF4HolonomyStatePacket) (stage : Nat) : Q' :=
  abstractPacketRectangularHaar
    stage stage (stage + 1) packet

/-- Located endpoint of the three-factor rectangular net. -/
def abstractPacketRectangularLimit
    (packet : BF4HolonomyStatePacket) : CReal where
  approx := abstractPacketRectangularDiagonalPartial packet
  cauchy := by
    intro epsilon hepsilon
    refine
      ⟨abstractPacketThreeFactorModulus packet epsilon,
       fun first second hfirst hsecond => ?_⟩
    exact abstractPacketRectangularHaar_joint_cauchy
      packet epsilon hepsilon
      first first (first + 1)
      second second (second + 1)
      hfirst hfirst (Nat.le_trans hfirst (Nat.le_add_right first 1))
      hsecond hsecond (Nat.le_trans hsecond (Nat.le_add_right second 1))

@[simp] theorem abstractPacketRectangularLimit_approx
    (packet : BF4HolonomyStatePacket) (stage : Nat) :
    (abstractPacketRectangularLimit packet).approx stage =
      abstractPacketRectangularHaar stage stage (stage + 1) packet :=
  rfl

/-- The located rectangle is exactly the already-constructed all-label joint
grouped endpoint.  This is an endpoint identification, not merely agreement
along one chosen numerical subsequence. -/
theorem abstractPacketRectangularLimit_equiv_groupedJoint
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketRectangularLimit packet)
      (bf4PacketGroupedSquareJointLimit packet) := by
  exact YMGap.Constructive.SumOfSquares.Equiv_of_approx_eqv
    (fun stage =>
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (bf4PacketGroupedSquare_haar_eqv_abstractRectangle
            stage stage packet))
        (bf4PacketGroupedSquare_haar_eq_jointLimit_approx
          packet stage))

/-- Restore the omitted source and target sphere shifts on the rectangular
endpoint. -/
def abstractPacketPhysicalNormalizedRectangularLimit
    (packet : BF4HolonomyStatePacket) : CReal :=
  CReal.mul
    (ExpNeg.expNeg groupedPhysicalNormalization
      groupedPhysicalNormalization_nonnegative)
    (abstractPacketRectangularLimit packet)

/-- The normalized rectangle is exactly the physical normalization of the
all-label grouped joint endpoint. -/
theorem abstractPacketPhysicalNormalizedRectangularLimit_equiv_grouped
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketPhysicalNormalizedRectangularLimit packet)
      (bf4PacketPhysicalNormalizedGroupedLimit packet) := by
  unfold abstractPacketPhysicalNormalizedRectangularLimit
    bf4PacketPhysicalNormalizedGroupedLimit
  refine CReal.Equiv.trans
    (CRealAlg.cmul_comm
      (ExpNeg.expNeg groupedPhysicalNormalization
        groupedPhysicalNormalization_nonnegative)
      (abstractPacketRectangularLimit packet)) ?_
  refine CReal.Equiv.trans
    (CReal.mul_congr_left
      (abstractPacketRectangularLimit_equiv_groupedJoint packet)) ?_
  exact CRealAlg.cmul_comm
    (bf4PacketGroupedSquareJointLimit packet)
    (ExpNeg.expNeg groupedPhysicalNormalization
      groupedPhysicalNormalization_nonnegative)

/-- Three independently cofinal cutoff schedules. -/
structure BF4ThreeFactorCofinalSchedule where
  sourceOrder : Nat → Nat
  targetOrder : Nat → Nat
  crossOrder : Nat → Nat
  source_cofinal : ∀ stage, stage ≤ sourceOrder stage
  target_cofinal : ∀ stage, stage ≤ targetOrder stage
  cross_cofinal : ∀ stage, stage ≤ crossOrder stage

/-- Located rectangular endpoint along an arbitrary explicit cofinal
three-factor schedule. -/
def abstractPacketRectangularScheduledLimit
    (schedule : BF4ThreeFactorCofinalSchedule)
    (packet : BF4HolonomyStatePacket) : CReal where
  approx := fun stage =>
    abstractPacketRectangularHaar
      (schedule.sourceOrder stage)
      (schedule.targetOrder stage)
      (schedule.crossOrder stage) packet
  cauchy := by
    intro epsilon hepsilon
    refine
      ⟨abstractPacketThreeFactorModulus packet epsilon,
       fun first second hfirst hsecond => ?_⟩
    exact abstractPacketRectangularHaar_joint_cauchy
      packet epsilon hepsilon
      (schedule.sourceOrder first)
      (schedule.targetOrder first)
      (schedule.crossOrder first)
      (schedule.sourceOrder second)
      (schedule.targetOrder second)
      (schedule.crossOrder second)
      (Nat.le_trans hfirst (schedule.source_cofinal first))
      (Nat.le_trans hfirst (schedule.target_cofinal first))
      (Nat.le_trans hfirst (schedule.cross_cofinal first))
      (Nat.le_trans hsecond (schedule.source_cofinal second))
      (Nat.le_trans hsecond (schedule.target_cofinal second))
      (Nat.le_trans hsecond (schedule.cross_cofinal second))

/-- Every explicitly cofinal rectangular schedule has the same located
endpoint. -/
theorem abstractPacketRectangularScheduledLimit_equiv_diagonal
    (schedule : BF4ThreeFactorCofinalSchedule)
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPacketRectangularScheduledLimit schedule packet)
      (abstractPacketRectangularLimit packet) := by
  intro epsilon hepsilon
  refine
    ⟨abstractPacketThreeFactorModulus packet epsilon,
     fun stage hstage => ?_⟩
  exact abstractPacketRectangularHaar_joint_cauchy
    packet epsilon hepsilon
    (schedule.sourceOrder stage)
    (schedule.targetOrder stage)
    (schedule.crossOrder stage)
    stage stage (stage + 1)
    (Nat.le_trans hstage (schedule.source_cofinal stage))
    (Nat.le_trans hstage (schedule.target_cofinal stage))
    (Nat.le_trans hstage (schedule.cross_cofinal stage))
    hstage hstage (Nat.le_trans hstage (Nat.le_add_right stage 1))

/-- The rational rectangles along every cofinal schedule converge to the
canonical located rectangular endpoint. -/
theorem abstractPacketRectangularSchedule_converges
    (schedule : BF4ThreeFactorCofinalSchedule)
    (packet : BF4HolonomyStatePacket) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        (abstractPacketRectangularHaar
          (schedule.sourceOrder stage)
          (schedule.targetOrder stage)
          (schedule.crossOrder stage) packet))
      (abstractPacketRectangularLimit packet) := by
  have hself := CReal.convergesTo_self
    (abstractPacketRectangularScheduledLimit schedule packet)
  have hequiv :=
    abstractPacketRectangularScheduledLimit_equiv_diagonal
      schedule packet
  intro epsilon hepsilon
  let halfEpsilon := HalfPow.half * epsilon
  have hhalf : (0 : Q') < halfEpsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨termCutoff, hterm⟩ := hself halfEpsilon hhalf
  obtain ⟨equivCutoff, hequivCutoff⟩ := hequiv halfEpsilon hhalf
  refine
    ⟨max termCutoff equivCutoff, fun stage hstage => ?_⟩
  obtain ⟨approxCutoff, happ⟩ :=
    hterm stage (Nat.le_trans (Nat.le_max_left _ _) hstage)
  refine
    ⟨max approxCutoff equivCutoff, fun approximation happStage => ?_⟩
  have happrox := happ approximation
    (Nat.le_trans (Nat.le_max_left _ _) happStage)
  have heq := hequivCutoff approximation
    (Nat.le_trans (Nat.le_max_right _ _) happStage)
  change
    (abstractPacketRectangularScheduledLimit schedule packet).approx stage ≤
        (abstractPacketRectangularLimit packet).approx approximation + epsilon ∧
      (abstractPacketRectangularLimit packet).approx approximation ≤
        (abstractPacketRectangularScheduledLimit schedule packet).approx stage + epsilon
  exact
    ⟨two_halves_trans_local
      ((abstractPacketRectangularScheduledLimit schedule packet).approx stage)
      ((abstractPacketRectangularScheduledLimit schedule packet).approx approximation)
      ((abstractPacketRectangularLimit packet).approx approximation)
      epsilon happrox.1 heq.1,
     two_halves_trans_local
      ((abstractPacketRectangularLimit packet).approx approximation)
      ((abstractPacketRectangularScheduledLimit schedule packet).approx approximation)
      ((abstractPacketRectangularScheduledLimit schedule packet).approx stage)
      epsilon heq.2 happrox.2⟩

end YMGap.Continuum.BF4GroupedThreeFactorCofinal

#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.positivePolynomialTaylorPartial_add_block
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.positivePolynomialTaylorTerm_l1_le
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.positivePolynomialTaylorBlock_l1_le_of_modulus
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.bf4PacketGroupedSquare_haar_eqv_abstractRectangle
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.abstractPacketRectangularHaar_joint_cauchy
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.abstractPacketRectangularLimit
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.abstractPacketRectangularLimit_equiv_groupedJoint
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.abstractPacketRectangularSchedule_converges
#print axioms YMGap.Continuum.BF4GroupedThreeFactorCofinal.abstractPacketPhysicalNormalizedRectangularLimit_equiv_grouped
