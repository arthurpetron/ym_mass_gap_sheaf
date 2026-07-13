/-
The exact bridge -- and exact obstruction -- between the harmonic character
operator and the reconstructed Wilson transfer spectrum.

`TransferCorr.reconTransfer` reconstructs the Wilson connected chain
correlator exactly, but its diagonal datum uses

  weight_i = coeffW w (i+1),   eigenvalue_i = coeffW w (i+1).

Peter--Weyl gives the exact factorization

  coeffW w (i+1) = dim(i+1) * qpow w (c4(i+1)).

Thus the raw reconstruction places the representation dimension in the
eigenvalue as well as in the endpoint spectral weight.  This file removes
that dimension from the eigenvalue by the exact rational factor
`invSucc (i+1) = 1/(i+2)`.  The resulting finite diagonal operator is
intertwined, on every vector and every coordinate, with the excited character
operator by the concrete identity mode map.  The unconditional harmonic
separator therefore gives a located gap for the normalized Wilson spectrum at
every harmonic scale.

The normalization is essential, not cosmetic.  Two kernel-checked fences are
banked for the raw reconstruction:

  * already at harmonic scale zero its leading eigenvalue exceeds the fused
    harmonic separator, so no positive rank-one intertwiner can carry that
    eigenspace to the harmonic line;
  * at harmonic scale three, where `1/2 <= w^3`, the raw reconstruction has no
    located spectral gap at all, for every nonempty truncation.

This is also the precise boundary with `WilsonGNS`: `WilsonGNSData` constructs
the Wilson form and positive-definite quotient, but supplies no
`TransferOperator` on that quotient.  `ReconstructionCapstone` still takes such
an operator externally.  Consequently the theorem below is a genuine bridge
between the Wilson *correlator reconstruction* and the concrete finite diagonal
character operator; it does not pretend to identify an unconstructed operator
on the general Wilson GNS completion.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`, no
`native_decide`; the finite counterexamples use kernel `decide` on closed
rationals.
-/

import YMGap.Continuum.HarmonicTransferSectorDominationAll
import YMGap.Continuum.PushedReconTransferGap
import YMGap.Continuum.CompactTransferGNS
import YMGap.Continuum.FusedOperatorIntertwinerFence
import YMGap.Continuum.WilsonGNS

namespace YMGap.Continuum.HarmonicWilsonTransferBridge

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.FusedOperatorIntertwinerFence
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicTransferSectorDominationAll
open YMGap.Continuum.PushedReconTransferGap
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.WilsonSpectralBridge

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. Exact Peter--Weyl normalization of the Wilson reconstruction -/

/-- The raw reconstructed Wilson eigenvalue contains both the representation
dimension (stored as the character model's weight) and the heat-kernel
eigenvalue.  This is definitional for the existing exact character formula. -/
theorem rawWilson_lam_factorization
    (w : Q') (hw : (0 : Q') <= w) (M i : Nat) :
    (reconTransfer w hw M).lam i =
      (excitedCharModel w hw M).w i *
        (excitedCharModel w hw M).lam i := rfl

/-- The reconstructed Wilson spectral model with the Peter--Weyl dimension
removed from each transfer eigenvalue.  Its endpoint weights remain the exact
Wilson weights; only the operator spectrum is normalized. -/
def peterWeylNormalizedReconTransfer
    (w : Q') (hw : (0 : Q') <= w) (M : Nat) : SpectralModel where
  k := M
  w := (reconTransfer w hw M).w
  lam := fun i => (reconTransfer w hw M).lam i * Q'.invSucc (i + 1)
  w_nonneg := (reconTransfer w hw M).w_nonneg
  lam_nonneg := fun i => Q'.mul_nonneg _ _
    ((reconTransfer w hw M).lam_nonneg i) (Q'.invSucc_nonneg (i + 1))

/-- Exact modewise Peter--Weyl cancellation:
`coeffW(w,i+1)/(i+2) = qpow(w,c4(i+1))`. -/
theorem peterWeylNormalized_lam_eqv_character
    (w : Q') (hw : (0 : Q') <= w) (M i : Nat) :
    (peterWeylNormalizedReconTransfer w hw M).lam i ≈
      (excitedCharModel w hw M).lam i := by
  change (coeffW w (i + 1) * Q'.invSucc (i + 1)) ≈
    qpow w (c4 (i + 1))
  unfold coeffW dimQ
  refine Q'.eqv_trans _
    (qpow w (c4 (i + 1)) *
      (Q'.ofNat (i + 2) * Q'.invSucc (i + 1))) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.ofNat_succ_mul_invSucc (i + 1))) ?_
  exact Q'.mul_one_eqv _

/-! ## 2. A concrete all-coordinate operator intertwiner -/

/-- The concrete diagonal finite operator carried by the raw Wilson
reconstruction. -/
def rawWilsonFiniteOp
    (w : Q') (hw : (0 : Q') <= w) (M : Nat) : FiniteOp :=
  diagOp (reconTransfer w hw M).lam M

/-- The Peter--Weyl-normalized reconstructed Wilson operator. -/
def peterWeylNormalizedWilsonFiniteOp
    (w : Q') (hw : (0 : Q') <= w) (M : Nat) : FiniteOp :=
  diagOp (peterWeylNormalizedReconTransfer w hw M).lam M

/-- The excited character transfer operator on the same finite mode window. -/
def characterFiniteOp
    (w : Q') (hw : (0 : Q') <= w) (M : Nat) : FiniteOp :=
  diagOp (excitedCharModel w hw M).lam M

/-- The concrete carrier map: normalized Wilson and character coordinates have
the same Peter--Weyl mode labels, so the carrier map is the identity. -/
def characterModeMap (v : QSeq) : QSeq := v

/-- **Full finite-operator intertwining equation.**  On every vector and every
coordinate, the Peter--Weyl-normalized Wilson diagonal operator commutes with
the identity mode map and agrees with the character diagonal operator, up to
the substrate's rational equivalence. -/
theorem peterWeylNormalizedWilson_intertwines_character
    (w : Q') (hw : (0 : Q') <= w) (M : Nat) (v : QSeq) (i : Nat) :
    ((peterWeylNormalizedWilsonFiniteOp w hw M).apply
        (characterModeMap v) i) ≈
      characterModeMap ((characterFiniteOp w hw M).apply v) i := by
  unfold peterWeylNormalizedWilsonFiniteOp characterFiniteOp characterModeMap
    FiniteOp.apply diagOp
  apply finSum_eqv
  intro j
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact Q'.mul_eqv_congr_right _ _ (v j)
      (peterWeylNormalized_lam_eqv_character w hw M i)
  · simp only [if_neg hij]
    exact Q'.eqv_refl _

/-! ## 3. Unconditional harmonic separator on the normalized Wilson tower -/

/-- The unconditional fused harmonic separator bounds every eigenvalue of the
Peter--Weyl-normalized Wilson reconstruction, at every harmonic scale and the
prescribed quadratic cutoff. -/
def peterWeylNormalizedHarmonicLocatedGap (k : Nat) :
    LocatedSpectralGap
      (peterWeylNormalizedReconTransfer
        (harmW k) (harmW_nonneg k) (Ncut k)) where
  sep := lamPW (harmW k) (Ncut k) 1
  sep_lt_one := (harmonicCharLocatedGap_all k).sep_lt_one
  bound := fun i =>
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (peterWeylNormalized_lam_eqv_character
        (harmW k) (harmW_nonneg k) (Ncut k) i))
      (Q'.le_trans' _ _ _
        (casimir_qpow_le (harmW_nonneg k) (harmW_le_one k) i)
        (heatKernelSep_le_lamPW_all k))

/-- The transferred normalized-Wilson gap has exactly the established fused
harmonic mass margin. -/
theorem peterWeylNormalizedHarmonic_gapMargin_eq (k : Nat) :
    (peterWeylNormalizedHarmonicLocatedGap k).gapMargin =
      HarmonicFusedSchurObstruction.harmonicMass k := rfl

/-! ## 4. Exact no-go fences for the raw Wilson reconstruction -/

/-- At the first harmonic scale, the raw Wilson head eigenvalue already
exceeds the fused harmonic separator.  The missing Peter--Weyl normalization
cannot be hidden inside a domination estimate. -/
theorem rawWilson_head_not_bounded_by_harmonicSeparator_zero :
    ¬ ((reconTransfer (harmW 0) (harmW_nonneg 0) (Ncut 0)).lam 0 <=
      lamPW (harmW 0) (Ncut 0) 1) := by
  decide

/-- Hence no positive rank-one carrier map can exactly intertwine the raw
Wilson fundamental eigenspace with the fused harmonic line at scale zero. -/
theorem no_rawWilson_harmonic_rankOne_intertwiner_zero :
    PositiveRankOneIntertwiner
      ((reconTransfer (harmW 0) (harmW_nonneg 0) (Ncut 0)).lam 0)
      (lamPW (harmW 0) (Ncut 0) 1) -> False := by
  intro I
  exact (by decide :
      ¬ (((reconTransfer (harmW 0) (harmW_nonneg 0) (Ncut 0)).lam 0) ≈
        lamPW (harmW 0) (Ncut 0) 1))
    (positive_rankOne_intertwiner_forces_eigen_eq I)

/-- The raw reconstruction fails more drastically by harmonic scale three:
for every nonempty finite window it admits no separator below the vacuum. -/
theorem rawWilson_no_located_gap_harmonic_three (M : Nat) :
    LocatedSpectralGap
      (reconTransfer (harmW 3) (harmW_nonneg 3) (M + 1)) -> False := by
  exact no_located_gap_above_ceiling (harmW_nonneg 3) (by decide) M

end YMGap.Continuum.HarmonicWilsonTransferBridge

#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.rawWilson_lam_factorization
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.peterWeylNormalizedReconTransfer
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.peterWeylNormalized_lam_eqv_character
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.rawWilsonFiniteOp
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.peterWeylNormalizedWilsonFiniteOp
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.characterFiniteOp
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.characterModeMap
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.peterWeylNormalizedWilson_intertwines_character
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.peterWeylNormalizedHarmonicLocatedGap
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.peterWeylNormalizedHarmonic_gapMargin_eq
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.rawWilson_head_not_bounded_by_harmonicSeparator_zero
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.no_rawWilson_harmonic_rankOne_intertwiner_zero
#print axioms YMGap.Continuum.HarmonicWilsonTransferBridge.rawWilson_no_located_gap_harmonic_three
