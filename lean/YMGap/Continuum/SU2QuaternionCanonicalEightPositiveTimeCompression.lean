/-
# A genuine canonical Wilson positive-time compression

The canonical eight-coordinate quaternion state contains a two-dimensional
positive-time plane spanned by the vacuum and the rational boundary mode

    u = (g_0 + g_1) / 2.

In the interacting Wilson GNS form its Gram matrix is exactly
`diag(1, 1/8)`.  Boundary exchange sends `u` to `(h_0+h_1)/2`, whose
orthogonal projection back to this plane is `(1/8)u`.  Thus the exact
Peter--Weyl two-mode transfer is realized as a compression of the actual
state-preserving boundary exchange, rather than as an auxiliary finite model.

All constants are derived from the finite quaternion Haar functional.  The
only closed computations below are kernel `decide` on exact rationals.
-/

import YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence
import YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS

namespace YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.SU2PeterWeylReferenceWeightFidelityFence
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarLinearity
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarPairModule
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonGNS
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero];
             ac_rfl))

theorem canonicalRetained_E_congr_module {a b : Poly8}
    (h : canonicalHaarPairModule.veq a b) :
    canonicalRetainedReferenceWeight.E_Λ a ≈
      canonicalRetainedReferenceWeight.E_Λ b :=
  canonicalRetained_E_congr h

theorem canonicalRetained_E_add_module (a b : Poly8) :
    canonicalRetainedReferenceWeight.E_Λ
        (canonicalHaarPairModule.add a b) ≈
      canonicalRetainedReferenceWeight.E_Λ a +
        canonicalRetainedReferenceWeight.E_Λ b :=
  canonicalRetained_E_add a b

theorem canonicalRetained_E_smul_module (s : Q') (a : Poly8) :
    canonicalRetainedReferenceWeight.E_Λ
        (canonicalHaarPairModule.smul s a) ≈
      s * canonicalRetainedReferenceWeight.E_Λ a :=
  canonicalRetained_E_smul s a

theorem canonicalRetained_E_hconj_module (a b : Poly8) :
    canonicalRetainedReferenceWeight.E_Λ
        (canonicalQuaternionPairAlg.mul
          (canonicalQuaternionPairAlg.star a) b) ≈
      canonicalRetainedReferenceWeight.E_Λ
        (canonicalQuaternionPairAlg.mul
          (canonicalQuaternionPairAlg.star b) a) :=
  canonicalRetained_E_hconj a b

abbrev canonicalReferenceWilsonData :=
  referenceWilsonData canonicalRetainedReferenceWeight canonicalHaarPairModule
    canonicalRetained_E_congr_module canonicalRetained_E_add_module
    canonicalRetained_E_smul_module canonicalRetained_E_hconj_module

abbrev canonicalWilsonGNS : GNSData :=
  canonicalReferenceWilsonData.toGNSData

def gBoundaryCoordinate8 (i : Fin 4) : Poly8 :=
  [(basisMono8 (gIndex8 i), 1)]

/-- A rationally normalized non-vacuum boundary mode. -/
def canonicalFundamentalBoundaryMode8 : Poly8 :=
  polySmul8 coupling
    (polyAdd8 (gBoundaryCoordinate8 0) (gBoundaryCoordinate8 1))

set_option maxRecDepth 1000000 in
theorem canonical_vacuum_norm_exact :
    canonicalWilsonGNS.B polyOne8 polyOne8 ≈ 1 := by
  decide

set_option maxRecDepth 1000000 in
theorem canonical_vacuum_fundamental_orthogonal :
    canonicalWilsonGNS.B polyOne8 canonicalFundamentalBoundaryMode8 ≈ 0 := by
  decide

set_option maxRecDepth 1000000 in
theorem canonical_fundamental_vacuum_orthogonal :
    canonicalWilsonGNS.B canonicalFundamentalBoundaryMode8 polyOne8 ≈ 0 := by
  decide

set_option maxRecDepth 1000000 in
theorem canonical_fundamental_norm_exact :
    canonicalWilsonGNS.B canonicalFundamentalBoundaryMode8
      canonicalFundamentalBoundaryMode8 ≈ eighth := by
  decide

set_option maxRecDepth 1000000 in
theorem canonical_swapped_fundamental_vacuum_orthogonal :
    canonicalWilsonGNS.B (swapPoly8 canonicalFundamentalBoundaryMode8)
      polyOne8 ≈ 0 := by
  decide

set_option maxRecDepth 1000000 in
theorem canonical_swapped_fundamental_overlap_exact :
    canonicalWilsonGNS.B (swapPoly8 canonicalFundamentalBoundaryMode8)
      canonicalFundamentalBoundaryMode8 ≈ eighth * eighth := by
  decide

/-- The retained two-mode plane embedded in the actual canonical Wilson
observable carrier. -/
def canonicalModeEmbed (a : ModeVec) : Poly8 :=
  polyAdd8 (polySmul8 a.1 polyOne8)
    (polySmul8 a.2 canonicalFundamentalBoundaryMode8)

theorem canonicalModeEmbed_form (a b : ModeVec) :
    canonicalWilsonGNS.B (canonicalModeEmbed a) (canonicalModeEmbed b) ≈
      wilsonModeGNS.B a b := by
  refine Q'.eqv_trans _
    (canonicalWilsonGNS.B (polySmul8 a.1 polyOne8) (canonicalModeEmbed b) +
      canonicalWilsonGNS.B
        (polySmul8 a.2 canonicalFundamentalBoundaryMode8)
        (canonicalModeEmbed b)) _
    (canonicalWilsonGNS.B_add_left _ _ _ ) ?_
  refine Q'.eqv_trans _
    (a.1 * canonicalWilsonGNS.B polyOne8 (canonicalModeEmbed b) +
      a.2 * canonicalWilsonGNS.B canonicalFundamentalBoundaryMode8
        (canonicalModeEmbed b)) _
    (Q'.add_eqv_congr'
      (canonicalWilsonGNS.B_smul_left a.1 polyOne8 (canonicalModeEmbed b))
      (canonicalWilsonGNS.B_smul_left a.2
        canonicalFundamentalBoundaryMode8 (canonicalModeEmbed b))) ?_
  refine Q'.eqv_trans _
    (a.1 *
        (b.1 * canonicalWilsonGNS.B polyOne8 polyOne8 +
          b.2 * canonicalWilsonGNS.B polyOne8
            canonicalFundamentalBoundaryMode8) +
      a.2 *
        (b.1 * canonicalWilsonGNS.B canonicalFundamentalBoundaryMode8 polyOne8 +
          b.2 * canonicalWilsonGNS.B canonicalFundamentalBoundaryMode8
            canonicalFundamentalBoundaryMode8)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left a.1 _ _
        (Q'.eqv_trans _ _ _
          (canonicalWilsonGNS.B_add_right polyOne8
            (polySmul8 b.1 polyOne8)
            (polySmul8 b.2 canonicalFundamentalBoundaryMode8))
          (Q'.add_eqv_congr'
            (canonicalWilsonGNS.B_smul_right b.1 polyOne8 polyOne8)
            (canonicalWilsonGNS.B_smul_right b.2 polyOne8
              canonicalFundamentalBoundaryMode8))))
      (Q'.mul_eqv_congr_left a.2 _ _
        (Q'.eqv_trans _ _ _
          (canonicalWilsonGNS.B_add_right canonicalFundamentalBoundaryMode8
            (polySmul8 b.1 polyOne8)
            (polySmul8 b.2 canonicalFundamentalBoundaryMode8))
          (Q'.add_eqv_congr'
            (canonicalWilsonGNS.B_smul_right b.1
              canonicalFundamentalBoundaryMode8 polyOne8)
            (canonicalWilsonGNS.B_smul_right b.2
              canonicalFundamentalBoundaryMode8
              canonicalFundamentalBoundaryMode8))))
  · refine Q'.eqv_trans _
      (a.1 * b.1 + eighth * (a.2 * b.2)) _ ?_ ?_
    · refine Q'.eqv_trans _
        (a.1 * (b.1 * 1 + b.2 * 0) +
          a.2 * (b.1 * 0 + b.2 * eighth)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left a.1 _ _
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left b.1 _ _ canonical_vacuum_norm_exact)
              (Q'.mul_eqv_congr_left b.2 _ _
                canonical_vacuum_fundamental_orthogonal)))
          (Q'.mul_eqv_congr_left a.2 _ _
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left b.1 _ _
                canonical_fundamental_vacuum_orthogonal)
              (Q'.mul_eqv_congr_left b.2 _ _
                canonical_fundamental_norm_exact)))
      · ring_qeqv
    · exact Q'.eqv_symm (reflectedWilsonGram_diagonal a b)

theorem canonicalBoundaryLinearPair_expand
    (v0 v1 : Poly8) (x0 x1 : Q') (b : ModeVec) :
    canonicalWilsonGNS.B
        (polyAdd8 (polySmul8 x0 v0) (polySmul8 x1 v1))
        (canonicalModeEmbed b) ≈
      x0 *
          (b.1 * canonicalWilsonGNS.B v0 polyOne8 +
            b.2 * canonicalWilsonGNS.B v0
              canonicalFundamentalBoundaryMode8) +
        x1 *
          (b.1 * canonicalWilsonGNS.B v1 polyOne8 +
            b.2 * canonicalWilsonGNS.B v1
              canonicalFundamentalBoundaryMode8) := by
  refine Q'.eqv_trans _
    (canonicalWilsonGNS.B (polySmul8 x0 v0) (canonicalModeEmbed b) +
      canonicalWilsonGNS.B (polySmul8 x1 v1) (canonicalModeEmbed b)) _
    (canonicalWilsonGNS.B_add_left _ _ _) ?_
  refine Q'.eqv_trans _
    (x0 * canonicalWilsonGNS.B v0 (canonicalModeEmbed b) +
      x1 * canonicalWilsonGNS.B v1 (canonicalModeEmbed b)) _
    (Q'.add_eqv_congr'
      (canonicalWilsonGNS.B_smul_left x0 v0 (canonicalModeEmbed b))
      (canonicalWilsonGNS.B_smul_left x1 v1 (canonicalModeEmbed b))) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left x0 _ _
      (Q'.eqv_trans _ _ _
        (canonicalWilsonGNS.B_add_right v0
          (polySmul8 b.1 polyOne8)
          (polySmul8 b.2 canonicalFundamentalBoundaryMode8))
        (Q'.add_eqv_congr'
          (canonicalWilsonGNS.B_smul_right b.1 v0 polyOne8)
          (canonicalWilsonGNS.B_smul_right b.2 v0
            canonicalFundamentalBoundaryMode8))))
    (Q'.mul_eqv_congr_left x1 _ _
      (Q'.eqv_trans _ _ _
        (canonicalWilsonGNS.B_add_right v1
          (polySmul8 b.1 polyOne8)
          (polySmul8 b.2 canonicalFundamentalBoundaryMode8))
        (Q'.add_eqv_congr'
          (canonicalWilsonGNS.B_smul_right b.1 v1 polyOne8)
          (canonicalWilsonGNS.B_smul_right b.2 v1
            canonicalFundamentalBoundaryMode8))))

/-- The ambient boundary exchange has exactly the same matrix coefficients as
the two-mode same-state transfer after compression. -/
theorem canonical_swapped_mode_overlap (a b : ModeVec) :
    canonicalWilsonGNS.B (swapPoly8 (canonicalModeEmbed a))
        (canonicalModeEmbed b) ≈
      wilsonModeGNS.B (sameStateTransfer a) b := by
  rw [canonicalModeEmbed, swapPoly8_add, swapPoly8_smul, swapPoly8_one,
    swapPoly8_smul]
  refine Q'.eqv_trans _
    (a.1 *
        (b.1 * canonicalWilsonGNS.B polyOne8 polyOne8 +
          b.2 * canonicalWilsonGNS.B polyOne8
            canonicalFundamentalBoundaryMode8) +
      a.2 *
        (b.1 * canonicalWilsonGNS.B
            (swapPoly8 canonicalFundamentalBoundaryMode8) polyOne8 +
          b.2 * canonicalWilsonGNS.B
            (swapPoly8 canonicalFundamentalBoundaryMode8)
            canonicalFundamentalBoundaryMode8)) _
    (canonicalBoundaryLinearPair_expand polyOne8
      (swapPoly8 canonicalFundamentalBoundaryMode8) a.1 a.2 b) ?_
  refine Q'.eqv_trans _
    (a.1 * (b.1 * 1 + b.2 * 0) +
      a.2 * (b.1 * 0 + b.2 * (eighth * eighth))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left a.1 _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left b.1 _ _ canonical_vacuum_norm_exact)
          (Q'.mul_eqv_congr_left b.2 _ _
            canonical_vacuum_fundamental_orthogonal)))
      (Q'.mul_eqv_congr_left a.2 _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left b.1 _ _
            canonical_swapped_fundamental_vacuum_orthogonal)
          (Q'.mul_eqv_congr_left b.2 _ _
            canonical_swapped_fundamental_overlap_exact)))
  · refine Q'.eqv_trans _
      ((sameStateTransfer a).1 * b.1 +
        eighth * ((sameStateTransfer a).2 * b.2)) _ (by
          unfold sameStateTransfer
          ring_qeqv) ?_
    exact Q'.eqv_symm (reflectedWilsonGram_diagonal (sameStateTransfer a) b)

/-! ## The actual ambient time/reflection geometry -/

def canonicalAmbientTimeReflection : AmbientTimeReflection where
  space := canonicalWilsonGNS
  tau := swapPoly8
  tauInv := swapPoly8
  theta := id
  tau_map_veq := canonicalRetainedBoundarySwapHaarPairGeometry.map_veq
  tau_map_add := canonicalRetainedBoundarySwapHaarPairGeometry.map_add
  tau_map_neg := canonicalRetainedBoundarySwapHaarPairGeometry.map_neg
  tau_map_smul := canonicalRetainedBoundarySwapHaarPairGeometry.map_smul
  tau_left_inv := by
    intro a
    rw [swapPoly8_involutive]
    exact canonicalWilsonGNS.veq_refl a
  tau_right_inv := by
    intro a
    rw [swapPoly8_involutive]
    exact canonicalWilsonGNS.veq_refl a
  tau_isometry :=
    canonicalRetainedBoundarySwapHaarPairGeometry.wilsonForm_translation_invariant
      canonicalRetained_E_congr canonicalRetained_E_add
      canonicalRetained_E_smul canonicalRetained_E_hconj
  theta_involutive := fun a => canonicalWilsonGNS.veq_refl a
  theta_time_inverse := fun a => canonicalWilsonGNS.veq_refl (swapPoly8 a)

def eightScalar : Q' := Q'.mkPos 8 1 (by decide)

def canonicalModeProject (p : Poly8) : ModeVec :=
  (canonicalWilsonGNS.B p
      (canonicalModeEmbed SU2PeterWeylWilsonBlock.vacuumMode),
    eightScalar *
      canonicalWilsonGNS.B p
        (canonicalModeEmbed SU2PeterWeylWilsonBlock.fundamentalMode))

theorem canonicalModeProject_embed (a : ModeVec) :
    modeEqv (canonicalModeProject (canonicalModeEmbed a)) a := by
  constructor
  · refine Q'.eqv_trans _
      (wilsonModeGNS.B a SU2PeterWeylWilsonBlock.vacuumMode) _
      (canonicalModeEmbed_form a SU2PeterWeylWilsonBlock.vacuumMode) ?_
    unfold SU2PeterWeylWilsonBlock.vacuumMode
    refine Q'.eqv_trans _
      (a.1 * 1 + eighth * (a.2 * 0)) _
      (reflectedWilsonGram_diagonal a (1, 0)) ?_
    ring_qeqv
  · refine Q'.eqv_trans _
      (eightScalar *
        wilsonModeGNS.B a SU2PeterWeylWilsonBlock.fundamentalMode) _
      (Q'.mul_eqv_congr_left eightScalar _ _
        (canonicalModeEmbed_form a
          SU2PeterWeylWilsonBlock.fundamentalMode)) ?_
    unfold SU2PeterWeylWilsonBlock.fundamentalMode
    refine Q'.eqv_trans _
      (eightScalar * (a.1 * 0 + eighth * (a.2 * 1))) _
      (Q'.mul_eqv_congr_left eightScalar _ _
        (reflectedWilsonGram_diagonal a (0, 1))) ?_
    unfold eightScalar eighth
    ring_qeqv

theorem canonicalModeProject_swapped_embed (a : ModeVec) :
    modeEqv (canonicalModeProject (swapPoly8 (canonicalModeEmbed a)))
      (sameStateTransfer a) := by
  constructor
  · refine Q'.eqv_trans _
      (wilsonModeGNS.B (sameStateTransfer a)
        SU2PeterWeylWilsonBlock.vacuumMode) _
      (canonical_swapped_mode_overlap a
        SU2PeterWeylWilsonBlock.vacuumMode) ?_
    unfold sameStateTransfer SU2PeterWeylWilsonBlock.vacuumMode
    refine Q'.eqv_trans _
      (a.1 * 1 + eighth * ((eighth * a.2) * 0)) _
      (reflectedWilsonGram_diagonal (a.1, eighth * a.2) (1, 0)) ?_
    ring_qeqv
  · refine Q'.eqv_trans _
      (eightScalar *
        wilsonModeGNS.B (sameStateTransfer a)
          SU2PeterWeylWilsonBlock.fundamentalMode) _
      (Q'.mul_eqv_congr_left eightScalar _ _
        (canonical_swapped_mode_overlap a
          SU2PeterWeylWilsonBlock.fundamentalMode)) ?_
    unfold sameStateTransfer SU2PeterWeylWilsonBlock.fundamentalMode
    refine Q'.eqv_trans _
      (eightScalar * (a.1 * 0 + eighth * ((eighth * a.2) * 1))) _
      (Q'.mul_eqv_congr_left eightScalar _ _
        (reflectedWilsonGram_diagonal (a.1, eighth * a.2) (0, 1))) ?_
    unfold eightScalar eighth
    ring_qeqv

/-- The projection is honest on the canonical Haar-test carrier quotient; it
cannot manufacture dynamics by distinguishing equivalent representatives. -/
theorem canonicalModeProject_map_veq {p q : Poly8}
    (h : canonicalWilsonGNS.veq p q) :
    modeEqv (canonicalModeProject p) (canonicalModeProject q) :=
  ⟨canonicalWilsonGNS.B_congr_left
      (canonicalModeEmbed SU2PeterWeylWilsonBlock.vacuumMode) h,
    Q'.mul_eqv_congr_left eightScalar _ _
      (canonicalWilsonGNS.B_congr_left
        (canonicalModeEmbed SU2PeterWeylWilsonBlock.fundamentalMode) h)⟩

/-- Boundary exchange is genuinely nontrivial after the Haar-test quotient on
the selected non-vacuum mode. -/
theorem canonical_swapped_fundamental_not_veq :
    ¬ canonicalWilsonGNS.veq
      (swapPoly8 canonicalFundamentalBoundaryMode8)
      canonicalFundamentalBoundaryMode8 := by
  intro h
  have hpair :
      canonicalWilsonGNS.B
          (swapPoly8 canonicalFundamentalBoundaryMode8)
          canonicalFundamentalBoundaryMode8 ≈
        canonicalWilsonGNS.B canonicalFundamentalBoundaryMode8
          canonicalFundamentalBoundaryMode8 :=
    canonicalWilsonGNS.B_congr_left canonicalFundamentalBoundaryMode8 h
  have hbad : eighth * eighth ≈ eighth :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm canonical_swapped_fundamental_overlap_exact)
      (Q'.eqv_trans _ _ _ hpair canonical_fundamental_norm_exact)
  exact (by decide : ¬ (eighth * eighth ≈ eighth)) hbad

def canonicalModeResidual (a : ModeVec) : Poly8 :=
  canonicalWilsonGNS.sub (swapPoly8 (canonicalModeEmbed a))
    (canonicalModeEmbed (sameStateTransfer a))

theorem canonicalModeResidual_orthogonal (a : ModeVec) :
    canonicalWilsonGNS.B (canonicalModeEmbed (sameStateTransfer a))
      (canonicalModeResidual a) ≈ 0 := by
  unfold canonicalModeResidual GNSData.sub
  refine Q'.eqv_trans _
    (canonicalWilsonGNS.B (canonicalModeEmbed (sameStateTransfer a))
        (swapPoly8 (canonicalModeEmbed a)) +
      canonicalWilsonGNS.B (canonicalModeEmbed (sameStateTransfer a))
        (canonicalWilsonGNS.neg
          (canonicalModeEmbed (sameStateTransfer a)))) _
    (canonicalWilsonGNS.B_add_right _ _ _) ?_
  refine Q'.eqv_trans _
    (canonicalWilsonGNS.B (canonicalModeEmbed (sameStateTransfer a))
        (swapPoly8 (canonicalModeEmbed a)) +
      -(canonicalWilsonGNS.B (canonicalModeEmbed (sameStateTransfer a))
        (canonicalModeEmbed (sameStateTransfer a)))) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (canonicalWilsonGNS.B_neg_right _ _)) ?_
  have hoverlap :
      canonicalWilsonGNS.B (canonicalModeEmbed (sameStateTransfer a))
          (swapPoly8 (canonicalModeEmbed a)) ≈
        wilsonModeGNS.B (sameStateTransfer a) (sameStateTransfer a) :=
    Q'.eqv_trans _ _ _
      (canonicalWilsonGNS.B_symm _ _)
      (canonical_swapped_mode_overlap a (sameStateTransfer a))
  have hembed :
      canonicalWilsonGNS.B (canonicalModeEmbed (sameStateTransfer a))
          (canonicalModeEmbed (sameStateTransfer a)) ≈
        wilsonModeGNS.B (sameStateTransfer a) (sameStateTransfer a) :=
    canonicalModeEmbed_form _ _
  refine Q'.eqv_trans _
    (wilsonModeGNS.B (sameStateTransfer a) (sameStateTransfer a) +
      -(wilsonModeGNS.B (sameStateTransfer a) (sameStateTransfer a))) _
    (Q'.add_eqv_congr' hoverlap
      (Q'.neg_eqv_congr _ _ hembed)) ?_
  exact OSReconstructionProgress.q_add_neg_self _

def canonicalModeCoordinate (a : ModeVec) (i : Nat) : Q' :=
  if i = 0 then a.1 else a.2

def canonicalModeWeight (i : Nat) : Q' :=
  if i = 0 then 1 else eighth * eighth

/-- The exact two-dimensional positive-time compression inside the canonical
interacting Wilson GNS carrier. -/
def canonicalPositiveTimeCompression :
    PositiveTimeCompression canonicalAmbientTimeReflection where
  positive := wilsonModeGNS
  embed := canonicalModeEmbed
  project := canonicalModeProject
  transfer := sameStateTransfer
  residual := canonicalModeResidual
  embed_form := canonicalModeEmbed_form
  reflected_form := canonicalModeEmbed_form
  project_embed := canonicalModeProject_embed
  transfer_projected_time := fun a =>
    wilsonModeGNS.veq_symm (canonicalModeProject_swapped_embed a)
  transfer_map_veq := sameStateTransfer_map_veq
  transfer_map_zero := by
    change modeEqv (sameStateTransfer modeZero) modeZero
    unfold sameStateTransfer modeZero modeEqv
    exact ⟨by decide, by decide⟩
  transfer_map_add := sameStateTransfer_map_add
  transfer_map_neg := by
    intro a
    change modeEqv (sameStateTransfer (modeNeg a))
      (modeNeg (sameStateTransfer a))
    exact ⟨Q'.eqv_refl _, Q'.mul_neg_eqv eighth a.2⟩
  transfer_map_smul := sameStateTransfer_map_smul
  compressed_decomposition := by
    intro a
    change canonicalWilsonGNS.veq (swapPoly8 (canonicalModeEmbed a))
      (canonicalWilsonGNS.add (canonicalModeEmbed (sameStateTransfer a))
        (canonicalWilsonGNS.sub (swapPoly8 (canonicalModeEmbed a))
          (canonicalModeEmbed (sameStateTransfer a))))
    exact canonicalWilsonGNS.veq_symm
      (canonicalWilsonGNS.veq_trans
        (canonicalWilsonGNS.add_comm
          (canonicalModeEmbed (sameStateTransfer a))
          (canonicalWilsonGNS.sub (swapPoly8 (canonicalModeEmbed a))
            (canonicalModeEmbed (sameStateTransfer a))))
        (canonicalWilsonGNS.sub_add_cancel
          (swapPoly8 (canonicalModeEmbed a))
          (canonicalModeEmbed (sameStateTransfer a))))
  compressed_orthogonal := canonicalModeResidual_orthogonal
  modeCount := 2
  coordinate := canonicalModeCoordinate
  modeWeight := canonicalModeWeight
  modeWeight_nonneg := by
    intro i
    by_cases h : i = 0
    · simp [canonicalModeWeight, h]
      exact by decide
    · simp [canonicalModeWeight, h]
      exact Q'.mul_nonneg eighth eighth (by decide) (by decide)
  transfer_weightedGram := by
    intro a b
    refine Q'.eqv_trans _
      ((sameStateTransfer a).1 * b.1 +
        eighth * ((sameStateTransfer a).2 * b.2)) _
      (reflectedWilsonGram_diagonal (sameStateTransfer a) b) ?_
    change
      (sameStateTransfer a).1 * b.1 +
          eighth * ((sameStateTransfer a).2 * b.2) ≈
        (0 + 1 * (a.1 * b.1)) +
          (eighth * eighth) * (a.2 * b.2)
    unfold sameStateTransfer
    ring_qeqv

theorem canonical_compressed_vacuum_eigen :
    modeEqv
      (canonicalPositiveTimeCompression.transfer
        SU2PeterWeylWilsonBlock.vacuumMode)
      SU2PeterWeylWilsonBlock.vacuumMode :=
  vacuum_eigen

theorem canonical_compressed_fundamental_eighth_eigen :
    modeEqv
      (canonicalPositiveTimeCompression.transfer
        SU2PeterWeylWilsonBlock.fundamentalMode)
      (modeSmul eighth SU2PeterWeylWilsonBlock.fundamentalMode) :=
  fundamental_eighth_eigen

/-! ## Fidelity to the canonical ReferenceWeight -/

theorem canonicalModeEmbed_vacuum_veq_one :
    canonicalWilsonGNS.veq
      (canonicalModeEmbed SU2PeterWeylWilsonBlock.vacuumMode) polyOne8 := by
  intro r
  change canonicalProductHaar
      (polyMul8 r
        (polyAdd8 (polySmul8 1 polyOne8)
          (polySmul8 0 canonicalFundamentalBoundaryMode8))) ≈
    canonicalProductHaar (polyMul8 r polyOne8)
  refine Q'.eqv_trans _
    (canonicalProductHaar (polyMul8 r (polySmul8 1 polyOne8)) +
      canonicalProductHaar
        (polyMul8 r (polySmul8 0 canonicalFundamentalBoundaryMode8))) _
    (canonicalProductHaar_mul_add_right r _ _) ?_
  refine Q'.eqv_trans _
    (1 * canonicalProductHaar (polyMul8 r polyOne8) +
      0 * canonicalProductHaar
        (polyMul8 r canonicalFundamentalBoundaryMode8)) _
    (Q'.add_eqv_congr'
      (canonicalProductHaar_mul_smul_right 1 r polyOne8)
      (canonicalProductHaar_mul_smul_right 0 r
        canonicalFundamentalBoundaryMode8)) ?_
  ring_qeqv

/-- The special vacuum branch provides the strict observable unit required by
the corrected fidelity interface; all other modes use the linear embedding. -/
def canonicalBoundaryObservable (a : ModeVec) : Poly8 :=
  if a = SU2PeterWeylWilsonBlock.vacuumMode then
    polyOne8
  else
    canonicalModeEmbed a

theorem canonicalBoundaryObservable_vacuum :
    canonicalBoundaryObservable SU2PeterWeylWilsonBlock.vacuumMode =
      polyOne8 := by
  simp [canonicalBoundaryObservable]

theorem canonicalModeEmbed_boundary_veq (a : ModeVec) :
    canonicalWilsonGNS.veq (canonicalModeEmbed a)
      (canonicalBoundaryObservable a) := by
  by_cases h : a = SU2PeterWeylWilsonBlock.vacuumMode
  · subst a
    simpa [canonicalBoundaryObservable] using
      canonicalModeEmbed_vacuum_veq_one
  · simp [canonicalBoundaryObservable, h]
    exact canonicalWilsonGNS.veq_refl (canonicalModeEmbed a)

theorem canonicalBoundaryObservable_form (a b : ModeVec) :
    canonicalWilsonGNS.B (canonicalBoundaryObservable a)
        (canonicalBoundaryObservable b) ≈
      wilsonModeGNS.B a b := by
  refine Q'.eqv_trans _
    (canonicalWilsonGNS.B (canonicalModeEmbed a)
      (canonicalBoundaryObservable b)) _
    (canonicalWilsonGNS.B_congr_left
      (canonicalBoundaryObservable b)
      (canonicalWilsonGNS.veq_symm (canonicalModeEmbed_boundary_veq a))) ?_
  refine Q'.eqv_trans _
    (canonicalWilsonGNS.B (canonicalModeEmbed a) (canonicalModeEmbed b)) _
    (canonicalWilsonGNS.B_congr_right (canonicalModeEmbed a)
      (canonicalWilsonGNS.veq_symm (canonicalModeEmbed_boundary_veq b))) ?_
  exact canonicalModeEmbed_form a b

/- The corrected two-boundary fidelity target is inhabited by the actual
canonical interacting ReferenceWeight and its exact compressed transfer. -/
set_option maxHeartbeats 2000000 in
def canonicalReferenceWeightPositiveTimeRealization :
    TwoBoundaryReferenceWeightPositiveTimeRealization
      canonicalRetainedReferenceWeight canonicalHaarPairModule
      canonicalRetained_E_congr_module canonicalRetained_E_add_module
      canonicalRetained_E_smul_module canonicalRetained_E_hconj_module where
  ambient := canonicalAmbientTimeReflection
  compression := canonicalPositiveTimeCompression
  ambientObservable := id
  boundaryObservable := canonicalBoundaryObservable
  state := id
  vacuum_is_unit := canonicalBoundaryObservable_vacuum
  ambient_reference_form := fun x y => Q'.eqv_refl _
  state_embeds := canonicalModeEmbed_boundary_veq
  positive_reflected_form := by
    intro a b
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (canonicalModeEmbed_form a b))
      (Q'.eqv_trans _ _ _
        (canonicalWilsonGNS.B_congr_left
          (canonicalModeEmbed b)
          (canonicalModeEmbed_boundary_veq a))
        (canonicalWilsonGNS.B_congr_right (canonicalBoundaryObservable a)
          (canonicalModeEmbed_boundary_veq b)))
  reflected_schur_form := canonicalBoundaryObservable_form
  state_map_veq := fun h => h
  state_map_smul := fun s a =>
    wilsonModeGNS.veq_refl (modeSmul s a)
  compression_intertwines := fun a =>
    wilsonModeGNS.veq_refl (sameStateTransfer a)

theorem canonical_realization_vacuum_nonzero :
    ¬ (canonicalPositiveTimeCompression.positive.B
      ((canonicalReferenceWeightPositiveTimeRealization).state
        SU2PeterWeylWilsonBlock.vacuumMode)
      ((canonicalReferenceWeightPositiveTimeRealization).state
        SU2PeterWeylWilsonBlock.vacuumMode) ≈ 0) :=
  TwoBoundaryReferenceWeightPositiveTimeRealization.vacuum_state_form_nonzero
    canonicalReferenceWeightPositiveTimeRealization

theorem canonical_realization_fundamental_nonzero :
    ¬ (canonicalPositiveTimeCompression.positive.B
      ((canonicalReferenceWeightPositiveTimeRealization).state
        SU2PeterWeylWilsonBlock.fundamentalMode)
      ((canonicalReferenceWeightPositiveTimeRealization).state
        SU2PeterWeylWilsonBlock.fundamentalMode) ≈ 0) :=
  TwoBoundaryReferenceWeightPositiveTimeRealization.fundamental_state_form_nonzero
    canonicalReferenceWeightPositiveTimeRealization

end YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonical_vacuum_norm_exact
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonical_fundamental_norm_exact
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonical_swapped_fundamental_overlap_exact
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonicalModeEmbed_form
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonicalModeProject_map_veq
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonical_swapped_fundamental_not_veq
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonicalPositiveTimeCompression
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonicalReferenceWeightPositiveTimeRealization
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression.canonical_realization_fundamental_nonzero
