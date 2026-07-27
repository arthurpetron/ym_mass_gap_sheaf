/-
# Constructive completion of the nonlinear five-fusion Haar square

This module turns the spacing-uniform common-carrier estimate into an actual
constructive real.  Starting one label before the explicit dimension-weighted
cutoff, successive genuine fivefold Clebsch--Gordan Haar squares have a
geometric increment majorant.  The project's constructive geometric-tail
engine therefore supplies a `CReal` whose approximations are exactly those
finite nonlinear Haar squares, and the full unshifted sequence converges to
that real.

No independent five-label tensor carrier is used: every comparison is made
after directed padding on the actual SU(2) fusion carrier.

# Axiom gate

Constructive `Nat`/`Q'`/`CReal` mathematics only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, or noncomputable witness.
-/

import YMGap.Continuum.SU2NonlinearFiveFusionTail

namespace YMGap.Continuum.SU2NonlinearFiveFusionCompletion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.TruncationTailChannelBound
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2DimensionWeightedHeatTail
open YMGap.Continuum.SU2FusionWeightedMass
open YMGap.Continuum.SU2GroupedFiveHolonomyHilbertSchmidt
open YMGap.Continuum.SU2NonlinearFiveFusionTail

local infix:50 " ≈ " => Q'.eqv

/-- A rational SU(2) heat nome in the physical interval. -/
structure NonlinearFiveHeatData where
  q : Q'
  q_pos : (0 : Q') < q
  q_lt_one : q < 1

/-- First label where the dimension-weighted ratio is certified at most
one half. -/
def labelCutoff (D : NonlinearFiveHeatData) : Nat :=
  explicitWeightedLabelCutoff D.q

/-- The finite packet cutoff immediately before the first controlled omitted
label. -/
def startingCutoff (D : NonlinearFiveHeatData) : Nat :=
  labelCutoff D - 1

theorem labelCutoff_pos (D : NonlinearFiveHeatData) :
    1 ≤ labelCutoff D :=
  explicitWeightedLabelCutoff_pos D.q

theorem startingCutoff_succ (D : NonlinearFiveHeatData) :
    startingCutoff D + 1 = labelCutoff D := by
  have hpos := labelCutoff_pos D
  unfold startingCutoff
  omega

/-- Uniform weighted-mass ceiling shared by all finite heat packets. -/
def massCeiling (D : NonlinearFiveHeatData) : Q' :=
  weightedOnePlaquetteCeiling D.q (labelCutoff D)

/-- Geometric ratio at the first controlled omitted label. -/
def tailRatio (D : NonlinearFiveHeatData) : Q' :=
  weightedDiscardedRatio D.q (labelCutoff D)

/-- The fixed nonlinear Lipschitz envelope shared by every cutoff. -/
def haarAmplifier (D : NonlinearFiveHeatData) : Q' :=
  nonlinearFiveAmplifier (massCeiling D)

/-- Geometric increment constant for the nonlinear Haar-square sequence. -/
def incrementConstant (D : NonlinearFiveHeatData) : Q' :=
  (weightedChanCoeff D.q (labelCutoff D) * Q'.ofNat 2) *
    haarAmplifier D

/-- The cofinal nonlinear Haar-square sequence beginning one packet cutoff
before the controlled label. -/
def shiftedHaarSq (D : NonlinearFiveHeatData) (l : Nat) : Q' :=
  packetHaarSq
    (fusionPacketFive
      (heatPacket D.q (startingCutoff D + l)))

theorem tailRatio_pos (D : NonlinearFiveHeatData) :
    (0 : Q') < tailRatio D := by
  unfold tailRatio weightedDiscardedRatio
  exact Q'.mul_pos (by decide)
    (HKPos.pow_pos D.q_pos _)

theorem tailRatio_lt_one (D : NonlinearFiveHeatData) :
    tailRatio D < 1 := by
  exact Q'.lt_of_le_of_lt
    (explicitWeightedLabelCutoff_ratio_le_half
      D.q_pos D.q_lt_one)
    (by decide)

theorem massCeiling_nonneg (D : NonlinearFiveHeatData) :
    (0 : Q') ≤ massCeiling D := by
  unfold massCeiling weightedOnePlaquetteCeiling
  exact Q'.zero_le_add _ _
    (SU2HeatChannelHilbertSchmidtCompletion.finSum_nonneg_local _
      (weightedChanCoeff_nonneg
        (Q'.le_of_lt D.q_pos))
      (labelCutoff D))
    (Q'.mul_nonneg _ _
      (weightedChanCoeff_nonneg
        (Q'.le_of_lt D.q_pos)
        (labelCutoff D))
      (by decide))

theorem haarAmplifier_nonneg (D : NonlinearFiveHeatData) :
    (0 : Q') ≤ haarAmplifier D :=
  nonlinearFiveAmplifier_nonneg
    (massCeiling_nonneg D)

theorem incrementConstant_nonneg
    (D : NonlinearFiveHeatData) :
    (0 : Q') ≤ incrementConstant D :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (weightedChanCoeff_nonneg
        (Q'.le_of_lt D.q_pos)
        (labelCutoff D))
      (by decide))
    (haarAmplifier_nonneg D)

private theorem q_lt_of_lt_of_le_local
    {a b c : Q'} (hab : a < b) (hbc : b ≤ c) :
    a < c := by
  have hbd : (0 : Int) < (b.den : Int) := by
    exact_mod_cast b.den_pos
  have hacScaled :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (c.num * (a.den : Int)) * (b.den : Int) := by
    have h1 := Int.mul_lt_mul_of_pos_right hab
      (by exact_mod_cast c.den_pos :
        (0 : Int) < (c.den : Int))
    have h2 := Int.mul_le_mul_of_nonneg_left hbc
      (by exact_mod_cast Nat.zero_le a.den :
        (0 : Int) ≤ (a.den : Int))
    calc
      (a.num * (c.den : Int)) * (b.den : Int)
          = (a.num * (b.den : Int)) * (c.den : Int) := by
              ac_rfl
      _ < (b.num * (a.den : Int)) * (c.den : Int) := h1
      _ ≤ (c.num * (b.den : Int)) * (a.den : Int) := by
              simpa only [Int.mul_assoc, Int.mul_comm,
                Int.mul_left_comm] using h2
      _ = (c.num * (a.den : Int)) * (b.den : Int) := by
              ac_rfl
  exact Int.lt_of_mul_lt_mul_right hacScaled
    (Int.le_of_lt hbd)

theorem massCeiling_pos (D : NonlinearFiveHeatData) :
    (0 : Q') < massCeiling D := by
  let tail :=
    weightedChanCoeff D.q (labelCutoff D) * Q'.ofNat 2
  have htail : (0 : Q') < tail :=
    Q'.mul_pos
      (weightedChanCoeff_pos D.q_pos (labelCutoff D))
      (by decide)
  have hprefix :
      (0 : Q') ≤
        finSum (weightedChanCoeff D.q) (labelCutoff D) :=
    SU2HeatChannelHilbertSchmidtCompletion.finSum_nonneg_local _
      (weightedChanCoeff_nonneg
        (Q'.le_of_lt D.q_pos))
      (labelCutoff D)
  have htailCeiling : tail ≤ massCeiling D := by
    unfold massCeiling weightedOnePlaquetteCeiling
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.eqv_of_eq (Q'.zero_add' tail))))
      (Q'.add_le_add_right _ _ tail hprefix)
  exact q_lt_of_lt_of_le_local htail htailCeiling

theorem haarAmplifier_pos (D : NonlinearFiveHeatData) :
    (0 : Q') < haarAmplifier D := by
  have hW := massCeiling_pos D
  have h4 : (0 : Q') < scalarPowerFour (massCeiling D) := by
    unfold scalarPowerFour
    exact Q'.mul_pos
      (Q'.mul_pos (Q'.mul_pos hW hW) hW) hW
  have hfiveCopies :
      (0 : Q') < fiveFourthCopies (massCeiling D) := by
    unfold fiveFourthCopies
    exact Q'.add_pos
      (Q'.add_pos
        (Q'.add_pos
          (Q'.add_pos h4 h4) h4) h4) h4
  have h5 :
      (0 : Q') < scalarPowerFive (massCeiling D) := by
    unfold scalarPowerFive
    exact Q'.mul_pos
      (Q'.mul_pos
        (Q'.mul_pos
          (Q'.mul_pos hW hW) hW) hW) hW
  unfold haarAmplifier nonlinearFiveAmplifier
  exact Q'.mul_pos hfiveCopies
    (Q'.add_pos h5 h5)

theorem incrementConstant_pos
    (D : NonlinearFiveHeatData) :
    (0 : Q') < incrementConstant D := by
  unfold incrementConstant
  exact Q'.mul_pos
    (Q'.mul_pos
      (weightedChanCoeff_pos D.q_pos (labelCutoff D))
      (by decide))
    (haarAmplifier_pos D)

/-! ## Geometric single-step domination -/

theorem shiftedOmittedIndex
    (D : NonlinearFiveHeatData) (l : Nat) :
    (startingCutoff D + l) + 1 =
      labelCutoff D + l := by
  have hstart := startingCutoff_succ D
  omega

theorem shiftedWeightedCoeff_le
    (D : NonlinearFiveHeatData) (l : Nat) :
    weightedChanCoeff D.q
        ((startingCutoff D + l) + 1)
      ≤ weightedChanCoeff D.q (labelCutoff D) *
          tailRatio D ^ l := by
  rw [shiftedOmittedIndex]
  exact weightedChanCoeff_geoDom
    (Q'.le_of_lt D.q_pos)
    (Q'.le_trans' _ _ _
      (Q'.le_of_lt D.q_lt_one)
      (Q'.le_refl' 1))
    (labelCutoff D)
    (labelCutoff_pos D)
    l

theorem nonlinearStepError_le_geo
    (D : NonlinearFiveHeatData) (l : Nat) :
    (weightedChanCoeff D.q
        ((startingCutoff D + l) + 1) *
        Q'.ofNat 2) *
        haarAmplifier D
      ≤ geoIncrBase
          (incrementConstant D) (tailRatio D) l := by
  have hb := shiftedWeightedCoeff_le D l
  have htwo :
      weightedChanCoeff D.q
          ((startingCutoff D + l) + 1) *
          Q'.ofNat 2
        ≤
      (weightedChanCoeff D.q (labelCutoff D) *
          tailRatio D ^ l) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hb (by decide)
  have hamp :
      (weightedChanCoeff D.q
          ((startingCutoff D + l) + 1) *
          Q'.ofNat 2) *
          haarAmplifier D
        ≤
      ((weightedChanCoeff D.q (labelCutoff D) *
          tailRatio D ^ l) * Q'.ofNat 2) *
          haarAmplifier D :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      htwo (haarAmplifier_nonneg D)
  refine Q'.le_trans' _ _ _ hamp
    (Q'.le_of_eqv ?_)
  unfold geoIncrBase incrementConstant
  let b := weightedChanCoeff D.q (labelCutoff D)
  let rpow := tailRatio D ^ l
  let A := haarAmplifier D
  change ((b * rpow) * Q'.ofNat 2) * A
    ≈ ((b * Q'.ofNat 2) * A) * rpow
  refine Q'.eqv_trans _ ((b * rpow) * (Q'.ofNat 2 * A)) _
    (Q'.mul_assoc_eqv (b * rpow) (Q'.ofNat 2) A) ?_
  refine Q'.eqv_trans _ ((b * Q'.ofNat 2) * (rpow * A)) _
    (RingNormaliser.q_mul4_swap b rpow (Q'.ofNat 2) A) ?_
  refine Q'.eqv_trans _ ((b * Q'.ofNat 2) * (A * rpow)) _
    (Q'.mul_eqv_congr_left (b * Q'.ofNat 2)
      (rpow * A) (A * rpow)
      (Q'.mul_comm_eqv rpow A)) ?_
  exact Q'.eqv_symm
    (Q'.mul_assoc_eqv (b * Q'.ofNat 2) A rpow)

/-- Upper single-step inequality consumed by the geometric completion
engine. -/
theorem shiftedHaarSq_up
    (D : NonlinearFiveHeatData) (l : Nat) :
    shiftedHaarSq D (l + 1)
      ≤ shiftedHaarSq D l +
          geoIncrBase
            (incrementConstant D) (tailRatio D) l := by
  have hcut :
      labelCutoff D ≤
        startingCutoff D + l + 1 := by
    rw [shiftedOmittedIndex]
    exact Nat.le_add_right _ _
  have hstep :=
    heatFusionPacketFive_haarSq_le_twoLead
      D.q_pos D.q_lt_one
      (N := startingCutoff D + l)
      (M := startingCutoff D + l + 1)
      (by omega) hcut
  have hstep' :
      shiftedHaarSq D (l + 1)
        ≤ shiftedHaarSq D l +
            (weightedChanCoeff D.q
              ((startingCutoff D + l) + 1) *
              Q'.ofNat 2) *
              haarAmplifier D := by
    simpa [shiftedHaarSq, haarAmplifier,
      massCeiling, Nat.add_assoc] using hstep
  exact Q'.le_trans' _ _ _ hstep'
    (Q'.add_le_add_left _ _ _
      (nonlinearStepError_le_geo D l))

/-- Lower single-step inequality.  It is immediate from monotonicity, with
the nonnegative geometric error added on the right. -/
theorem shiftedHaarSq_lo
    (D : NonlinearFiveHeatData) (l : Nat) :
    shiftedHaarSq D l
      ≤ shiftedHaarSq D (l + 1) +
          geoIncrBase
            (incrementConstant D) (tailRatio D) l := by
  have hmono :
      shiftedHaarSq D l ≤ shiftedHaarSq D (l + 1) := by
    unfold shiftedHaarSq
    exact heatFusionPacketFive_haarSq_mono
      (Q'.le_of_lt D.q_pos) (by omega)
  exact Q'.le_trans' _ _ _ hmono
    (Q'.add_le_self_of_nonneg _ _
      (geoIncrBase_nonneg
        (incrementConstant_nonneg D)
        (Q'.le_of_lt (tailRatio_pos D)) l))

theorem incrementModulus
    (D : NonlinearFiveHeatData) :
    ∀ ε : Q', (0 : Q') < ε →
      ∃ δ : Q', (0 : Q') < δ ∧
        (incrementConstant D *
          HKConv.divPos 1 (1 + (-tailRatio D))) *
          δ ≤ ε := by
  intro ε hε
  let scale :=
    incrementConstant D *
      HKConv.divPos 1 (1 + (-tailRatio D))
  have hScalePos : (0 : Q') < scale :=
    Q'.mul_pos
      (incrementConstant_pos D)
      (HKConv.divPos_pos (by decide))
  have hScaleNum : 0 < scale.num :=
    CReal.num_pos_of_pos hScalePos
  refine
    ⟨HKConv.divPos ε scale,
      HKConv.divPos_pos
        (CReal.num_pos_of_pos hε), ?_⟩
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv scale
      (HKConv.divPos ε scale)) ?_
  exact HKConv.divPos_mul_eqv hScaleNum

/-! ## The constructive nonlinear Hilbert--Schmidt completion -/

/-- The cutoff-free constructive real defined by the genuine fivefold
Clebsch--Gordan heat carriers. -/
def nonlinearFiveHeatHSSq
    (D : NonlinearFiveHeatData) : CReal :=
  crealOfGeoIncrementBase
    (shiftedHaarSq D)
    (incrementConstant D)
    (tailRatio D)
    (incrementConstant_nonneg D)
    (tailRatio_pos D)
    (tailRatio_lt_one D)
    (shiftedHaarSq_up D)
    (shiftedHaarSq_lo D)
    (incrementModulus D)

@[simp] theorem nonlinearFiveHeatHSSq_approx
    (D : NonlinearFiveHeatData) (l : Nat) :
    (nonlinearFiveHeatHSSq D).approx l =
      shiftedHaarSq D l := rfl

/-- The cofinal controlled sequence converges to the constructed nonlinear
Hilbert--Schmidt square. -/
theorem shiftedHaarSq_converges
    (D : NonlinearFiveHeatData) :
    CReal.ConvergesTo
      (fun l => CReal.ofQ' (shiftedHaarSq D l))
      (nonlinearFiveHeatHSSq D) := by
  simpa [nonlinearFiveHeatHSSq] using
    (CReal.convergesTo_self
      (nonlinearFiveHeatHSSq D))

/-- **Nonlinear Hilbert--Schmidt convergence.**  The full sequence of finite
fivefold SU(2) heat-character Haar squares converges constructively to the
cutoff-free `nonlinearFiveHeatHSSq`. -/
theorem nonlinearFiveHeatHaarSq_converges
    (D : NonlinearFiveHeatData) :
    CReal.ConvergesTo
      (fun N =>
        CReal.ofQ'
          (packetHaarSq
            (fusionPacketFive
              (heatPacket D.q N))))
      (nonlinearFiveHeatHSSq D) := by
  apply
    SU2HeatChannelHilbertSchmidtCompletion.convergesTo_of_fixedShift
      (startingCutoff D)
  simpa [shiftedHaarSq, Nat.add_comm] using
    shiftedHaarSq_converges D

/-! ## Identification with the canonical grouped five-holonomy observable -/

/-- The canonical descended nonlinear packet and the direct genuine fivefold
packet have exactly the same rational Haar square. -/
theorem nonlinearFiveHaarL2SqQ_eqv_direct
    (q : Q') (N : Nat) :
    SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarL2SqQ q N
      ≈ packetHaarSq
          (fusionPacketFive (heatPacket q N)) := by
  change
    packetHaarSq
        (SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarPacket q N)
      ≈ packetHaarSq
          (fusionPacketFive (heatPacket q N))
  exact packetHaarSq_congr_synthesis
    (nonlinearFiveHaarPacket_eqv_direct_synthesis q N)

/-- The rational canonical grouped observable converges to the same
cutoff-free nonlinear Hilbert--Schmidt square. -/
theorem nonlinearFiveCanonicalQ_converges
    (D : NonlinearFiveHeatData) :
    CReal.ConvergesTo
      (fun N =>
        CReal.ofQ'
          (SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarL2SqQ
            D.q N))
      (nonlinearFiveHeatHSSq D) := by
  have hterm :
      ∀ N,
        CReal.Equiv
          (CReal.ofQ'
            (packetHaarSq
              (fusionPacketFive
                (heatPacket D.q N))))
          (CReal.ofQ'
            (SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarL2SqQ
              D.q N)) := by
    intro N
    exact SumOfSquares.Equiv_of_approx_eqv
      (fun _ =>
        Q'.eqv_symm
          (nonlinearFiveHaarL2SqQ_eqv_direct D.q N))
  exact ChebOrthoMatrix.convergesTo_congr_seq
    hterm
    (nonlinearFiveHeatHaarSq_converges D)

/-- The existing finite `CReal` grouped five-holonomy Haar observables
themselves converge to the constructed cutoff-free nonlinear square. -/
theorem nonlinearFiveCanonicalHaar_converges
    (D : NonlinearFiveHeatData) :
    CReal.ConvergesTo
      (fun N =>
        SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarL2Sq
          D.q N)
      (nonlinearFiveHeatHSSq D) := by
  exact ChebOrthoMatrix.convergesTo_congr_seq
    (fun N =>
      SumOfSquares.Equiv_of_approx_eqv
        (fun p => by
          rw [
            SU2GroupedFiveHolonomyHilbertSchmidt.nonlinearFiveHaarL2Sq_approx]
          exact Q'.eqv_refl _))
    (nonlinearFiveCanonicalQ_converges D)

end YMGap.Continuum.SU2NonlinearFiveFusionCompletion

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.tailRatio_pos
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.massCeiling_pos
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.incrementConstant_pos
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.shiftedHaarSq_up
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.nonlinearFiveHeatHSSq
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.nonlinearFiveHeatHaarSq_converges
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.nonlinearFiveHaarL2SqQ_eqv_direct
#print axioms YMGap.Continuum.SU2NonlinearFiveFusionCompletion.nonlinearFiveCanonicalHaar_converges
