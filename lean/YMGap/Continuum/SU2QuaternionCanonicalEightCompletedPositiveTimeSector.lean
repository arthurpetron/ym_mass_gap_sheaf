/-
# The canonical two-mode sector inside the completed interacting Wilson GNS space

The canonical quaternion calculation already identifies the positive-time
vacuum/fundamental plane and its compressed transfer.  This file closes the
completion bridge to the *actual* interacting Wilson GNS carrier.  The bridge
uses only preservation of all pairwise Gram coefficients.  Bilinearity then
reconstructs squared distances, so no stronger full-state time isometry or
strict representative-level linearity is assumed.

The resulting completed map is injective, preserves the completed inner
product, sends the mode vacuum to the literal polynomial unit, and sends the
mode excitation to the literal canonical boundary Wilson observable.

Honest scope: this is a completed finite two-mode subcarrier of one canonical
finite interacting Wilson state.  It is not an ambient transfer operator on
all Wilson observables, a uniform-volume gap, or a continuum theorem.
-/

import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap

namespace YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SU2QuaternionCanonicalEightCompressedSpectralGap
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2QuaternionCanonicalEightPositiveTimeCompression

local infix:50 " ≈ " => Q'.eqv

/-! ## A Gram-only completion isometry -/

/-- Pairwise Gram preservation is the minimal datum needed to map one GNS
completion isometrically into another.  In particular, no representative-level
linearity field is needed. -/
structure DenseGNSGramIsometry (D E : GNSData) where
  map : D.V → E.V
  gram : ∀ a b, E.B (map a) (map b) ≈ D.B a b

namespace DenseGNSGramIsometry

variable {D E : GNSData} (I : DenseGNSGramIsometry D E)

/-- Gram preservation reconstructs preservation of squared distances by
expanding both differences through bilinearity. -/
theorem distSq_eqv (a b : D.V) :
    E.distSqQ (I.map a) (I.map b) ≈ D.distSqQ a b := by
  refine Q'.eqv_trans _
    (((E.B (I.map a) (I.map a)) + (-(E.B (I.map a) (I.map b)))) +
      ((-(E.B (I.map a) (I.map b))) + (E.B (I.map b) (I.map b)))) _
    (E.B_sub_diag_expand (I.map a) (I.map b)) ?_
  refine Q'.eqv_trans _
    (((D.B a a) + (-(D.B a b))) + ((-(D.B a b)) + (D.B b b))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (I.gram a a)
        (Q'.neg_eqv_congr _ _ (I.gram a b)))
      (Q'.add_eqv_congr'
        (Q'.neg_eqv_congr _ _ (I.gram a b))
        (I.gram b b))
  · exact Q'.eqv_symm (D.B_sub_diag_expand a b)

def applyCauchy (x : CauchyGNS D) : CauchyGNS E where
  seq := fun n => I.map (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (I.distSq_eqv (x.seq p) (x.seq q)))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyCauchy_null {x y : CauchyGNS D} (h : CauchyNull D x y) :
    CauchyNull E (I.applyCauchy x) (I.applyCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (Q'.le_of_eqv (I.distSq_eqv (x.seq n) (y.seq n))) (hN n hn)⟩

/-- The completed isometric map induced by a Gram-preserving dense map. -/
def completed : GNSCompletionSpace D → GNSCompletionSpace E :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid E) (I.applyCauchy x))
    (fun _ _ h => Quotient.sound (I.applyCauchy_null h))

theorem completed_embed (a : D.V) :
    I.completed (embedV D a) = embedV E (I.map a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

/-- The completed map preserves every inner product, not only norms. -/
theorem completed_cinner (x y : GNSCompletionSpace D) :
    E.cinnerCompl (I.completed x) (I.completed y) = D.cinnerCompl x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (E.cInnerSeq (I.applyCauchy u) (I.applyCauchy v) n))
    (bSeq := fun n => CReal.ofQ' (D.cInnerSeq u v n))
    (fun n => CReal.ofQ'_equiv_of_eqv (I.gram (u.seq n) (v.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

/-- Distance reflection makes the completed Gram isometry injective. -/
theorem completed_injective {x y : GNSCompletionSpace D}
    (h : I.completed x = I.completed y) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro u v h
  apply Quotient.sound
  change Quotient.mk (cauchySetoid E) (I.applyCauchy u) =
    Quotient.mk (cauchySetoid E) (I.applyCauchy v) at h
  have hnull : CauchyNull E (I.applyCauchy u) (I.applyCauchy v) :=
    Quotient.exact h
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hnull epsilon hepsilon
  exact ⟨N, fun n hn => le_of_eqv_le
    (Q'.eqv_symm (I.distSq_eqv (u.seq n) (v.seq n))) (hN n hn)⟩

end DenseGNSGramIsometry

/-! ## The actual canonical Wilson specialization -/

def canonicalModeGramIsometry :
    DenseGNSGramIsometry wilsonModeGNS canonicalWilsonGNS where
  map := canonicalModeEmbed
  gram := canonicalModeEmbed_form

/-- The completed canonical two-mode positive-time sector as an actual
subcarrier of the interacting Wilson GNS completion. -/
def canonicalCompletedModeEmbedding :
    GNSCompletionSpace wilsonModeGNS → GNSCompletionSpace canonicalWilsonGNS :=
  canonicalModeGramIsometry.completed

theorem canonicalCompletedModeEmbedding_cinner
    (x y : GNSCompletionSpace wilsonModeGNS) :
    canonicalWilsonGNS.cinnerCompl
        (canonicalCompletedModeEmbedding x)
        (canonicalCompletedModeEmbedding y) =
      wilsonModeGNS.cinnerCompl x y :=
  canonicalModeGramIsometry.completed_cinner x y

theorem canonicalCompletedModeEmbedding_injective
    {x y : GNSCompletionSpace wilsonModeGNS}
    (h : canonicalCompletedModeEmbedding x = canonicalCompletedModeEmbedding y) :
    x = y :=
  canonicalModeGramIsometry.completed_injective h

theorem canonicalCompletedModeEmbedding_embed (a : ModeVec) :
    canonicalCompletedModeEmbedding (embedV wilsonModeGNS a) =
      embedV canonicalWilsonGNS (canonicalModeEmbed a) :=
  canonicalModeGramIsometry.completed_embed a

/-- The completed mode vacuum is the literal unit observable in the actual
interacting Wilson GNS completion. -/
theorem canonicalCompletedModeEmbedding_vacuum :
    canonicalCompletedModeEmbedding (embedV wilsonModeGNS vacuumMode) =
      embedV canonicalWilsonGNS
        SU2QuaternionCanonicalEightCarrier.polyOne8 := by
  refine Eq.trans (canonicalCompletedModeEmbedding_embed vacuumMode) ?_
  apply Quotient.sound
  exact embed_null_of_rad canonicalWilsonGNS
    (rad_of_veq canonicalWilsonGNS canonicalModeEmbed_vacuum_veq_one)

set_option maxRecDepth 1000000 in
theorem canonicalModeEmbed_fundamental_rad :
    canonicalWilsonGNS.rad (canonicalModeEmbed fundamentalMode)
      canonicalFundamentalBoundaryMode8 := by
  unfold GNSData.rad GNSData.sub canonicalModeEmbed fundamentalMode
  decide

/-- The completed excited mode is the literal canonical fundamental boundary
Wilson observable, not an independently named surrogate. -/
theorem canonicalCompletedModeEmbedding_fundamental :
    canonicalCompletedModeEmbedding (embedV wilsonModeGNS fundamentalMode) =
      embedV canonicalWilsonGNS canonicalFundamentalBoundaryMode8 := by
  refine Eq.trans (canonicalCompletedModeEmbedding_embed fundamentalMode) ?_
  apply Quotient.sound
  exact embed_null_of_rad canonicalWilsonGNS canonicalModeEmbed_fundamental_rad

/-! ## The literal connected transfer-power path -/

/-- The exact compressed transfer power on the non-vacuum mode. -/
theorem canonicalCompleted_fundamental_Tpow (n : Nat) :
    BoundedTransferCalculus.Tpow canonicalCompressedTransferOperator n
        (embedV wilsonModeGNS fundamentalMode) =
      embedV wilsonModeGNS (modeSmul (eighth ^ n) fundamentalMode) := by
  induction n with
  | zero =>
      apply Quotient.sound
      exact embed_null_of_rad wilsonModeGNS
        (rad_of_veq wilsonModeGNS (by
          change modeEqv fundamentalMode
            (modeSmul (eighth ^ (0 : Nat)) fundamentalMode)
          unfold modeSmul fundamentalMode modeEqv
          exact ⟨by decide, by decide⟩))
  | succ n ih =>
      change canonicalCompressedTransferOperator.T
          (BoundedTransferCalculus.Tpow canonicalCompressedTransferOperator n
            (embedV wilsonModeGNS fundamentalMode)) = _
      rw [ih]
      refine Eq.trans
        (canonicalPositiveTimeCompression.completedTransfer_embed
          (modeSmul (eighth ^ n) fundamentalMode)) ?_
      apply Quotient.sound
      exact embed_null_of_rad wilsonModeGNS
        (rad_of_veq wilsonModeGNS (by
          change modeEqv
            (sameStateTransfer (modeSmul (eighth ^ n) fundamentalMode))
            (modeSmul (eighth ^ (n + 1)) fundamentalMode)
          unfold sameStateTransfer modeSmul fundamentalMode modeEqv
          rw [Q'.pow_succ]
          constructor
          · exact Q'.eqv_trans _ _ _
              (QPoly.q_mul_zero (eighth ^ n))
              (Q'.eqv_symm (QPoly.q_mul_zero (eighth * eighth ^ n)))
          · exact Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_left eighth _ _
                (Q'.mul_one_eqv (eighth ^ n)))
              (Q'.eqv_symm (Q'.mul_one_eqv (eighth * eighth ^ n)))))

/-- The transferred fundamental vector, now regarded as a vector of the
completed interacting Wilson GNS space. -/
def canonicalEmbeddedFundamentalAt (n : Nat) :
    GNSCompletionSpace canonicalWilsonGNS :=
  canonicalCompletedModeEmbedding
    (BoundedTransferCalculus.Tpow canonicalCompressedTransferOperator n
      (embedV wilsonModeGNS fundamentalMode))

/-- At time zero the embedded vector is the literal canonical boundary Wilson
observable. -/
theorem canonicalEmbeddedFundamentalAt_zero :
    canonicalEmbeddedFundamentalAt 0 =
      embedV canonicalWilsonGNS canonicalFundamentalBoundaryMode8 :=
  canonicalCompletedModeEmbedding_fundamental

/-- Every transferred fundamental vector remains orthogonal to the literal
unit vacuum in the actual completed Wilson GNS space. -/
theorem canonicalEmbeddedFundamentalAt_vacuum_orthogonal (n : Nat) :
    canonicalWilsonGNS.cinnerCompl
        (canonicalEmbeddedFundamentalAt n)
        (embedV canonicalWilsonGNS
          SU2QuaternionCanonicalEightCarrier.polyOne8) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) := by
  unfold canonicalEmbeddedFundamentalAt
  rw [canonicalCompleted_fundamental_Tpow]
  rw [← canonicalCompletedModeEmbedding_vacuum]
  rw [canonicalCompletedModeEmbedding_cinner]
  change wilsonModeGNS.cinnerCompl
      (embedQuot wilsonModeGNS
        (wilsonModeGNS.qmk (modeSmul (eighth ^ n) fundamentalMode)))
      (embedQuot wilsonModeGNS (wilsonModeGNS.qmk vacuumMode)) = _
  rw [wilsonModeGNS.cinnerCompl_embed]
  apply Quotient.sound
  have hfundVac : wilsonModeGNS.B fundamentalMode vacuumMode ≈ 0 := by
    decide
  exact CReal.ofQ'_equiv_of_eqv
    (Q'.eqv_trans _ _ _
      (wilsonModeGNS.B_smul_left (eighth ^ n) fundamentalMode vacuumMode)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (eighth ^ n) _ _ hfundVac)
        (QPoly.q_mul_zero (eighth ^ n))))

/-- The same-object connected autocorrelation: both entries live in the actual
completed interacting Wilson GNS space, and the time-zero entry is the literal
canonical boundary Wilson observable. -/
def canonicalEmbeddedFundamentalConnectedMoment (n : Nat) : CReal.RC :=
  canonicalWilsonGNS.cinnerCompl
    (canonicalEmbeddedFundamentalAt n)
    (embedV canonicalWilsonGNS canonicalFundamentalBoundaryMode8)

/-- The ambient connected moment is exactly `(1/8)^n * (1/8)`. -/
theorem canonicalEmbeddedFundamentalConnectedMoment_exact (n : Nat) :
    canonicalEmbeddedFundamentalConnectedMoment n =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' ((eighth ^ n) * eighth)) := by
  unfold canonicalEmbeddedFundamentalConnectedMoment
    canonicalEmbeddedFundamentalAt
  rw [canonicalCompleted_fundamental_Tpow]
  rw [← canonicalCompletedModeEmbedding_fundamental]
  rw [canonicalCompletedModeEmbedding_cinner]
  change wilsonModeGNS.cinnerCompl
      (embedQuot wilsonModeGNS
        (wilsonModeGNS.qmk (modeSmul (eighth ^ n) fundamentalMode)))
      (embedQuot wilsonModeGNS (wilsonModeGNS.qmk fundamentalMode)) = _
  rw [wilsonModeGNS.cinnerCompl_embed]
  apply Quotient.sound
  exact CReal.ofQ'_equiv_of_eqv
    (Q'.eqv_trans _ _ _
      (wilsonModeGNS.B_smul_left
        (eighth ^ n) fundamentalMode fundamentalMode)
      (Q'.mul_eqv_congr_left (eighth ^ n) _ _ fundamental_norm))

end YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.DenseGNSGramIsometry.distSq_eqv
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.DenseGNSGramIsometry.completed
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.DenseGNSGramIsometry.completed_cinner
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.DenseGNSGramIsometry.completed_injective
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.canonicalCompletedModeEmbedding_vacuum
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.canonicalCompletedModeEmbedding_fundamental
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.canonicalCompleted_fundamental_Tpow
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.canonicalEmbeddedFundamentalAt_vacuum_orthogonal
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightCompletedPositiveTimeSector.canonicalEmbeddedFundamentalConnectedMoment_exact
