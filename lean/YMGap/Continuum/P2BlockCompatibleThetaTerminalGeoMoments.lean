/-
Track 11.7-fusion / R3o -- logarithmic-time geometric-moment evaluator.

# Result

The ten-chord endpoint contains length-`H` sums of a geometric progression
weighted by polynomials of degree at most two.  Direct evaluation costs `H`
power terms and becomes unusable on the dyadic physical tail.  This module
proves exact doubling recurrences for the zeroth, first, and second weighted
geometric moments and packages them as a structurally recursive evaluator at
length `2^k`.  A cutoff block of exponential length is therefore represented
by `k` algebraic steps, with a kernel proof that the compressed state equals
the literal finite sums.

No terminal inequality is asserted here.  The evaluator is proof-about-
computation infrastructure for the fixed ten-block certificate.

# Constructivity

Primitive recursion, finite-sum splitting, exact power laws, and the proved
reflective polynomial normalizer only.  No `Classical`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalTenChord

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalGeoMoments

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
open YMGap.Continuum.P2BlockCompatibleThetaTerminalTenChord
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadial
open YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Zeroth shifted geometric moment `sum_{j<H} r^(j+1)`. -/
def geoMoment0 (r : Q') (H : Nat) : Q' :=
  fsum (fun j => qpow r (j + 1)) H

/-- First shifted geometric moment `sum_{j<H} (j+1) r^(j+1)`. -/
def geoMoment1 (r : Q') (H : Nat) : Q' :=
  fsum (fun j => Q'.ofNat (j + 1) * qpow r (j + 1)) H

/-- Second shifted geometric moment `sum_{j<H} (j+1)^2 r^(j+1)`. -/
def geoMoment2 (r : Q') (H : Nat) : Q' :=
  fsum (fun j =>
    (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) * qpow r (j + 1)) H

private theorem qpow_shift (r : Q') (H j : Nat) :
    qpow r (H + j + 1) ≈ qpow r H * qpow r (j + 1) := by
  have h : H + j + 1 = H + (j + 1) := by omega
  rw [h]
  exact HeatKernelRGStep.qpow_add r H (j + 1)

private theorem ofNat_shift (H j : Nat) :
    Q'.ofNat (H + j + 1) ≈ Q'.ofNat H + Q'.ofNat (j + 1) := by
  have h : H + j + 1 = H + (j + 1) := by omega
  rw [h]
  exact Q'.ofNat_add_eqv H (j + 1)

/-- Exact doubling recurrence for the zeroth moment. -/
theorem geoMoment0_double (r : Q') (H : Nat) :
    geoMoment0 r (2 * H) ≈
      geoMoment0 r H + qpow r H * geoMoment0 r H := by
  have hlen : 2 * H = H + H := by omega
  rw [hlen]
  refine Q'.eqv_trans _ _ _
    (FusionCoreStepRoundH.fsum_split_at (fun j => qpow r (j + 1)) H H) ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _
    (fsum (fun j => qpow r H * qpow r (j + 1)) H) _ ?_ ?_
  · exact CubeRatioBounds.fsum_eqv_congr _ _
      (fun j => qpow_shift r H j) H
  · exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul (qpow r H)
        (fun j => qpow r (j + 1)) H)

private theorem geoMoment1_suffix (r : Q') (H : Nat) :
    fsum (fun j =>
      Q'.ofNat (H + j + 1) * qpow r (H + j + 1)) H ≈
      qpow r H *
        (Q'.ofNat H * geoMoment0 r H + geoMoment1 r H) := by
  let p := qpow r H
  let hq := Q'.ofNat H
  let t0 : Nat -> Q' := fun j => qpow r (j + 1)
  let t1 : Nat -> Q' := fun j => Q'.ofNat (j + 1) * qpow r (j + 1)
  have hterms : forall j,
      Q'.ofNat (H + j + 1) * qpow r (H + j + 1) ≈
        p * (hq * t0 j + t1 j) := by
    intro j
    have hc := ofNat_shift H j
    have hp := qpow_shift r H j
    refine Q'.eqv_trans _
      ((hq + Q'.ofNat (j + 1)) * (p * t0 j)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hc)
        (Q'.mul_eqv_congr_left _ _ _ hp)
    · dsimp only [p, hq, t0, t1]
      ring_qeqv
  refine Q'.eqv_trans _
    (fsum (fun j => p * (hq * t0 j + t1 j)) H) _
    (CubeRatioBounds.fsum_eqv_congr _ _ hterms H) ?_
  refine Q'.eqv_trans _
    (p * fsum (fun j => hq * t0 j + t1 j) H) _
    (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul p
      (fun j => hq * t0 j + t1 j) H)) ?_
  refine Q'.mul_eqv_congr_left p _ _ ?_
  refine Q'.eqv_trans _
    (fsum (fun j => hq * t0 j) H + fsum t1 H) _
    (CubeRatioBounds.fsum_add (fun j => hq * t0 j) t1 H) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul hq t0 H))
    (Q'.eqv_refl _)

/-- Exact doubling recurrence for the first moment. -/
theorem geoMoment1_double (r : Q') (H : Nat) :
    geoMoment1 r (2 * H) ≈
      geoMoment1 r H + qpow r H *
        (Q'.ofNat H * geoMoment0 r H + geoMoment1 r H) := by
  have hlen : 2 * H = H + H := by omega
  rw [hlen]
  exact Q'.eqv_trans _ _ _
    (FusionCoreStepRoundH.fsum_split_at
      (fun j => Q'.ofNat (j + 1) * qpow r (j + 1)) H H)
    (Q'.add_eqv_congr_left _ _ _ (geoMoment1_suffix r H))

private theorem geoMoment2_suffix (r : Q') (H : Nat) :
    fsum (fun j =>
      (Q'.ofNat (H + j + 1) * Q'.ofNat (H + j + 1)) *
        qpow r (H + j + 1)) H ≈
      qpow r H *
        ((Q'.ofNat H * Q'.ofNat H) * geoMoment0 r H +
          ((Q'.ofNat H * geoMoment1 r H) +
            (Q'.ofNat H * geoMoment1 r H)) +
          geoMoment2 r H) := by
  let p := qpow r H
  let hq := Q'.ofNat H
  let t0 : Nat -> Q' := fun j => qpow r (j + 1)
  let t1 : Nat -> Q' := fun j => Q'.ofNat (j + 1) * qpow r (j + 1)
  let t2 : Nat -> Q' := fun j =>
    (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) * qpow r (j + 1)
  have hterms : forall j,
      (Q'.ofNat (H + j + 1) * Q'.ofNat (H + j + 1)) *
          qpow r (H + j + 1) ≈
        p * (((hq * hq) * t0 j +
          ((hq * t1 j) + (hq * t1 j))) + t2 j) := by
    intro j
    have hc := ofNat_shift H j
    have hp := qpow_shift r H j
    have hsq := mul_eqv_both hc hc
    refine Q'.eqv_trans _
      (((hq + Q'.ofNat (j + 1)) *
          (hq + Q'.ofNat (j + 1))) * (p * t0 j)) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hsq)
        (Q'.mul_eqv_congr_left _ _ _ hp)
    · dsimp only [p, hq, t0, t1, t2]
      ring_qeqv
  refine Q'.eqv_trans _
    (fsum (fun j => p * (((hq * hq) * t0 j +
      ((hq * t1 j) + (hq * t1 j))) + t2 j)) H) _
    (CubeRatioBounds.fsum_eqv_congr _ _ hterms H) ?_
  refine Q'.eqv_trans _
    (p * fsum (fun j => (((hq * hq) * t0 j +
      ((hq * t1 j) + (hq * t1 j))) + t2 j)) H) _
    (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul p
      (fun j => (((hq * hq) * t0 j +
        ((hq * t1 j) + (hq * t1 j))) + t2 j)) H)) ?_
  refine Q'.mul_eqv_congr_left p _ _ ?_
  refine Q'.eqv_trans _
    (fsum (fun j => (hq * hq) * t0 j +
        ((hq * t1 j) + (hq * t1 j))) H + fsum t2 H) _
    (CubeRatioBounds.fsum_add
      (fun j => (hq * hq) * t0 j +
        ((hq * t1 j) + (hq * t1 j))) t2 H) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (fsum (fun j => (hq * hq) * t0 j) H +
      fsum (fun j => (hq * t1 j) + (hq * t1 j)) H) _
    (CubeRatioBounds.fsum_add
      (fun j => (hq * hq) * t0 j)
      (fun j => (hq * t1 j) + (hq * t1 j)) H) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul (hq * hq) t0 H)
  · refine Q'.eqv_trans _
      (fsum (fun j => hq * t1 j) H +
        fsum (fun j => hq * t1 j) H) _
      (CubeRatioBounds.fsum_add
        (fun j => hq * t1 j) (fun j => hq * t1 j) H) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul hq t1 H))
      (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul hq t1 H))

/-- Exact doubling recurrence for the second moment. -/
theorem geoMoment2_double (r : Q') (H : Nat) :
    geoMoment2 r (2 * H) ≈
      geoMoment2 r H + qpow r H *
        ((Q'.ofNat H * Q'.ofNat H) * geoMoment0 r H +
          ((Q'.ofNat H * geoMoment1 r H) +
            (Q'.ofNat H * geoMoment1 r H)) +
          geoMoment2 r H) := by
  have hlen : 2 * H = H + H := by omega
  rw [hlen]
  exact Q'.eqv_trans _ _ _
    (FusionCoreStepRoundH.fsum_split_at
      (fun j => (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) *
        qpow r (j + 1)) H H)
    (Q'.add_eqv_congr_left _ _ _ (geoMoment2_suffix r H))

/-- Compressed values for one power and the three moments. -/
structure GeoMomentState : Type where
  power : Q'
  moment0 : Q'
  moment1 : Q'
  moment2 : Q'

def GeoMomentState.base (r : Q') : GeoMomentState where
  power := r
  moment0 := r
  moment1 := r
  moment2 := r

/-- One exact length-doubling step. -/
def GeoMomentState.double (H : Nat) (S : GeoMomentState) : GeoMomentState where
  power := S.power * S.power
  moment0 := S.moment0 + S.power * S.moment0
  moment1 := S.moment1 + S.power *
    (Q'.ofNat H * S.moment0 + S.moment1)
  moment2 := S.moment2 + S.power *
    ((Q'.ofNat H * Q'.ofNat H) * S.moment0 +
      ((Q'.ofNat H * S.moment1) +
        (Q'.ofNat H * S.moment1)) + S.moment2)

/-- Logarithmic-time state at length `2^k`. -/
def dyadicGeoMomentState (r : Q') : Nat -> GeoMomentState
  | 0 => GeoMomentState.base r
  | k + 1 => (dyadicGeoMomentState r k).double (2 ^ k)

/-- Kernel specification of the compressed dyadic evaluator. -/
structure GeoMomentStateSpec (r : Q') (H : Nat)
    (S : GeoMomentState) : Prop where
  power : S.power ≈ qpow r H
  moment0 : S.moment0 ≈ geoMoment0 r H
  moment1 : S.moment1 ≈ geoMoment1 r H
  moment2 : S.moment2 ≈ geoMoment2 r H

private theorem base_spec (r : Q') :
    GeoMomentStateSpec r 1 (GeoMomentState.base r) := by
  have hp : qpow r 1 ≈ r := by
    change (1 : Q') * r ≈ r
    exact Q'.one_mul_eqv r
  have ht1 : Q'.ofNat 1 * qpow r 1 ≈ r := by
    change (1 : Q') * qpow r 1 ≈ r
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) hp
  have ht2 : (Q'.ofNat 1 * Q'.ofNat 1) * qpow r 1 ≈ r := by
    change ((1 : Q') * 1) * qpow r 1 ≈ r
    refine Q'.eqv_trans _ (1 * qpow r 1) _ ?_ ht1
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1)
  constructor
  · unfold GeoMomentState.base
    exact Q'.eqv_symm hp
  · unfold GeoMomentState.base geoMoment0
    change (r : Q') ≈ 0 + qpow r 1
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) hp)
  · unfold GeoMomentState.base geoMoment1
    change (r : Q') ≈ 0 + Q'.ofNat 1 * qpow r 1
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ht1)
  · unfold GeoMomentState.base geoMoment2
    change (r : Q') ≈ 0 +
      (Q'.ofNat 1 * Q'.ofNat 1) * qpow r 1
    exact Q'.eqv_symm
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ht2)

private theorem double_spec (r : Q') (H : Nat) (S : GeoMomentState)
    (hS : GeoMomentStateSpec r H S) :
    GeoMomentStateSpec r (2 * H) (S.double H) := by
  constructor
  · unfold GeoMomentState.double
    refine Q'.eqv_trans _ (qpow r H * qpow r H) _
      (mul_eqv_both hS.power hS.power) ?_
    exact Q'.eqv_symm (by
      have hlen : 2 * H = H + H := by omega
      rw [hlen]
      exact HeatKernelRGStep.qpow_add r H H)
  · unfold GeoMomentState.double
    refine Q'.eqv_trans _
      (geoMoment0 r H + qpow r H * geoMoment0 r H) _ ?_ ?_
    · exact Q'.add_eqv_congr' hS.moment0
        (mul_eqv_both hS.power hS.moment0)
    · exact Q'.eqv_symm (geoMoment0_double r H)
  · unfold GeoMomentState.double
    refine Q'.eqv_trans _
      (geoMoment1 r H + qpow r H *
        (Q'.ofNat H * geoMoment0 r H + geoMoment1 r H)) _ ?_ ?_
    · exact Q'.add_eqv_congr' hS.moment1
        (mul_eqv_both hS.power
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left (Q'.ofNat H) _ _ hS.moment0)
            hS.moment1))
    · exact Q'.eqv_symm (geoMoment1_double r H)
  · unfold GeoMomentState.double
    refine Q'.eqv_trans _
      (geoMoment2 r H + qpow r H *
        ((Q'.ofNat H * Q'.ofNat H) * geoMoment0 r H +
          ((Q'.ofNat H * geoMoment1 r H) +
            (Q'.ofNat H * geoMoment1 r H)) +
          geoMoment2 r H)) _ ?_ ?_
    · exact Q'.add_eqv_congr' hS.moment2
        (mul_eqv_both hS.power
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left (Q'.ofNat H * Q'.ofNat H)
                _ _ hS.moment0)
              (Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left (Q'.ofNat H) _ _ hS.moment1)
                (Q'.mul_eqv_congr_left (Q'.ofNat H) _ _ hS.moment1)))
            hS.moment2))
    · exact Q'.eqv_symm (geoMoment2_double r H)

/-- The state computed in `k` recursive steps is exactly the literal length
`2^k` power/moment quartet. -/
theorem dyadicGeoMomentState_spec (r : Q') : forall k,
    GeoMomentStateSpec r (2 ^ k) (dyadicGeoMomentState r k)
  | 0 => base_spec r
  | k + 1 => by
      have h := double_spec r (2 ^ k) (dyadicGeoMomentState r k)
        (dyadicGeoMomentState_spec r k)
      have hlen : 2 ^ (k + 1) = 2 * 2 ^ k := by
        rw [Nat.pow_succ]
        omega
      rw [hlen]
      exact h

/-! ## Exact identification with the physical chord block -/

/-- The degree-two moment polynomial obtained after translating a chord block
by its left endpoint `a`.  The duplicated mixed term avoids importing a
numeral-normalization convention into the reflective ring proof. -/
def shiftedSquareGeoMoment (a r : Q') (H : Nat) : Q' :=
  (a * a) * geoMoment0 r H +
    ((a * geoMoment1 r H) + (a * geoMoment1 r H)) +
    geoMoment2 r H

/-- One translated square-weighted geometric summand. -/
private def shiftedSquareGeoTerm (a r : Q') (j : Nat) : Q' :=
  ((a * a) * qpow r (j + 1) +
    ((a * (Q'.ofNat (j + 1) * qpow r (j + 1))) +
      (a * (Q'.ofNat (j + 1) * qpow r (j + 1))))) +
    (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) * qpow r (j + 1)

private theorem shiftedSquareGeoMoment_fsum (a r : Q') (H : Nat) :
    fsum (shiftedSquareGeoTerm a r) H ≈
      shiftedSquareGeoMoment a r H := by
  unfold shiftedSquareGeoTerm shiftedSquareGeoMoment
  refine Q'.eqv_trans _
    (fsum (fun j =>
        (a * a) * qpow r (j + 1) +
          ((a * (Q'.ofNat (j + 1) * qpow r (j + 1))) +
            (a * (Q'.ofNat (j + 1) * qpow r (j + 1))))) H +
      fsum (fun j =>
        (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) *
          qpow r (j + 1)) H) _
    (CubeRatioBounds.fsum_add
      (fun j =>
        (a * a) * qpow r (j + 1) +
          ((a * (Q'.ofNat (j + 1) * qpow r (j + 1))) +
            (a * (Q'.ofNat (j + 1) * qpow r (j + 1)))))
      (fun j =>
        (Q'.ofNat (j + 1) * Q'.ofNat (j + 1)) *
          qpow r (j + 1)) H) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (fsum (fun j => (a * a) * qpow r (j + 1)) H +
      fsum (fun j =>
        (a * (Q'.ofNat (j + 1) * qpow r (j + 1))) +
          (a * (Q'.ofNat (j + 1) * qpow r (j + 1)))) H) _
    (CubeRatioBounds.fsum_add
      (fun j => (a * a) * qpow r (j + 1))
      (fun j =>
        (a * (Q'.ofNat (j + 1) * qpow r (j + 1))) +
          (a * (Q'.ofNat (j + 1) * qpow r (j + 1)))) H) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul (a * a)
        (fun j => qpow r (j + 1)) H)
  · refine Q'.eqv_trans _
      (fsum (fun j => a *
          (Q'.ofNat (j + 1) * qpow r (j + 1))) H +
        fsum (fun j => a *
          (Q'.ofNat (j + 1) * qpow r (j + 1))) H) _
      (CubeRatioBounds.fsum_add
        (fun j => a * (Q'.ofNat (j + 1) * qpow r (j + 1)))
        (fun j => a * (Q'.ofNat (j + 1) * qpow r (j + 1))) H) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul a
        (fun j => Q'.ofNat (j + 1) * qpow r (j + 1)) H))
      (Q'.eqv_symm (CubeRatioBounds.fsum_const_mul a
        (fun j => Q'.ofNat (j + 1) * qpow r (j + 1)) H))

/-- Constant-size algebraic representation of one length-`H` chord block.
For dyadic `H`, its three moments are supplied by `dyadicGeoMomentState`. -/
def compressedWeightedChordBlock (q : Q') (H b : Nat) : Q' :=
  let aNat := b * H
  let slope := ((b + 1) * H) + b * H
  qpow q (aNat * aNat) *
    shiftedSquareGeoMoment (Q'.ofNat aNat) (qpow q slope) H

private theorem chordCoefficient_expand (H b j : Nat) :
    Q'.ofNat ((b * H + j + 1) * (b * H + j + 1)) ≈
      let a := Q'.ofNat (b * H)
      let x := Q'.ofNat (j + 1)
      (a * a) + ((a * x) + (a * x)) + (x * x) := by
  have hs := ofNat_shift (b * H) j
  refine Q'.eqv_trans _
    (Q'.ofNat (b * H + j + 1) * Q'.ofNat (b * H + j + 1)) _
    (HeatKernelRGStep.ofNat_mul_eqv _ _) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat (b * H) + Q'.ofNat (j + 1)) *
      (Q'.ofNat (b * H) + Q'.ofNat (j + 1))) _
    (mul_eqv_both hs hs) ?_
  dsimp only
  ring_qeqv

private theorem chordPower_factor (q : Q') (H b j : Nat) :
    qpow q (weightedChordExponent H b j) ≈
      qpow q ((b * H) * (b * H)) *
        qpow (qpow q (((b + 1) * H) + b * H)) (j + 1) := by
  unfold weightedChordExponent
  refine Q'.eqv_trans _
    (qpow q ((b * H) * (b * H)) *
      qpow q (((((b + 1) * H) + b * H) * (j + 1)))) _
    (HeatKernelRGStep.qpow_add q ((b * H) * (b * H))
      ((((b + 1) * H) + b * H) * (j + 1))) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (HeatKernelRGStep.qpow_qpow q
        (((b + 1) * H) + b * H) (j + 1)))

/-- The compressed moment expression is exactly—not approximately—the
literal weighted chord block.  This is the bridge that permits the terminal
certificate to reason in logarithmic dyadic state size. -/
theorem weightedChordBlock_eq_compressed (q : Q') (H b : Nat) :
    weightedChordBlock q H b ≈ compressedWeightedChordBlock q H b := by
  let a := Q'.ofNat (b * H)
  let ratio := qpow q (((b + 1) * H) + b * H)
  let seed := qpow q ((b * H) * (b * H))
  have hterm : forall j,
      Q'.ofNat ((b * H + j + 1) * (b * H + j + 1)) *
          qpow q (weightedChordExponent H b j) ≈
        seed * shiftedSquareGeoTerm a ratio j := by
    intro j
    have hc := chordCoefficient_expand H b j
    have hp := chordPower_factor q H b j
    refine Q'.eqv_trans _
      (((a * a) +
          ((a * Q'.ofNat (j + 1)) +
            (a * Q'.ofNat (j + 1))) +
          (Q'.ofNat (j + 1) * Q'.ofNat (j + 1))) *
        (seed * qpow ratio (j + 1))) _ ?_ ?_
    · exact mul_eqv_both hc hp
    · unfold shiftedSquareGeoTerm
      dsimp only [a, ratio, seed]
      ring_qeqv
  unfold weightedChordBlock
  refine Q'.eqv_trans _
    (fsum (fun j => seed * shiftedSquareGeoTerm a ratio j) H) _
    (CubeRatioBounds.fsum_eqv_congr _ _ hterm H) ?_
  refine Q'.eqv_trans _
    (seed * fsum (shiftedSquareGeoTerm a ratio) H) _
    (Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul seed
        (shiftedSquareGeoTerm a ratio) H)) ?_
  refine Q'.eqv_trans _
    (seed * shiftedSquareGeoMoment a ratio H) _
    (Q'.mul_eqv_congr_left seed _ _
      (shiftedSquareGeoMoment_fsum a ratio H)) ?_
  unfold compressedWeightedChordBlock
  dsimp only [a, ratio, seed]
  exact Q'.eqv_refl _

/-- Read the translated square moment directly from a compressed state. -/
def shiftedSquareGeoStateValue (a : Q') (S : GeoMomentState) : Q' :=
  (a * a) * S.moment0 +
    ((a * S.moment1) + (a * S.moment1)) + S.moment2

private theorem shiftedSquareGeoStateValue_spec
    (a r : Q') (H : Nat) (S : GeoMomentState)
    (hS : GeoMomentStateSpec r H S) :
    shiftedSquareGeoStateValue a S ≈ shiftedSquareGeoMoment a r H := by
  unfold shiftedSquareGeoStateValue shiftedSquareGeoMoment
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (a * a) _ _ hS.moment0)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left a _ _ hS.moment1)
        (Q'.mul_eqv_congr_left a _ _ hS.moment1)))
    hS.moment2

/-- One dyadic chord block evaluated through the logarithmic state rather
than through its exponentially long finite sum. -/
def dyadicCompressedWeightedChordBlock (q : Q') (k b : Nat) : Q' :=
  let H := 2 ^ k
  let aNat := b * H
  let slope := ((b + 1) * H) + b * H
  let S := dyadicGeoMomentState (qpow q slope) k
  qpow q (aNat * aNat) *
    shiftedSquareGeoStateValue (Q'.ofNat aNat) S

/-- Exact block-level soundness of the logarithmic evaluator. -/
theorem weightedChordBlock_eq_dyadicCompressed
    (q : Q') (k b : Nat) :
    weightedChordBlock q (2 ^ k) b ≈
      dyadicCompressedWeightedChordBlock q k b := by
  let H := 2 ^ k
  let aNat := b * H
  let slope := ((b + 1) * H) + b * H
  let seed := qpow q (aNat * aNat)
  let S := dyadicGeoMomentState (qpow q slope) k
  have hS : GeoMomentStateSpec (qpow q slope) H S := by
    dsimp only [S, H]
    exact dyadicGeoMomentState_spec (qpow q slope) k
  have hm := shiftedSquareGeoStateValue_spec
    (Q'.ofNat aNat) (qpow q slope) H S hS
  refine Q'.eqv_trans _
    (compressedWeightedChordBlock q H b) _
    (weightedChordBlock_eq_compressed q H b) ?_
  unfold compressedWeightedChordBlock dyadicCompressedWeightedChordBlock
  dsimp only [H, aNat, slope, seed, S]
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hm)

/-- A fixed-block chord represented by independently compressed dyadic moment
states.  The evaluator is logarithmic in each block length and linear only in
the chosen, scale-independent block count `B`. -/
def dyadicCompressedChordBlocks (q : Q') (k B : Nat) : Q' :=
  fsum (fun b => dyadicCompressedWeightedChordBlock q k b) B

/-- The original fixed physical ten-block specialization. -/
def dyadicCompressedTenChord (q : Q') (k : Nat) : Q' :=
  dyadicCompressedChordBlocks q k 10

/-- Exact fixed-block soundness for every scale-independent block count. -/
theorem weightedChordBlocks_eq_dyadicCompressedChordBlocks
    (q : Q') (k B : Nat) :
    weightedChordBlocks q (2 ^ k) B ≈
      dyadicCompressedChordBlocks q k B := by
  unfold weightedChordBlocks dyadicCompressedChordBlocks
  exact CubeRatioBounds.fsum_eqv_congr _ _
    (fun b => weightedChordBlock_eq_dyadicCompressed q k b) B

/-- Exact ten-block soundness.  The literal `10 * 2^k`-scale chord has been
replaced by ten states, each produced in `k` proved doubling steps. -/
theorem weightedChordBlocks_eq_dyadicCompressedTenChord
    (q : Q') (k : Nat) :
    weightedChordBlocks q (2 ^ k) 10 ≈
      dyadicCompressedTenChord q k := by
  unfold dyadicCompressedTenChord
  exact weightedChordBlocks_eq_dyadicCompressedChordBlocks q k 10

/-- On the block-compatible schedule, the physical tenth at scale `k+1` is
exactly the dyadic length consumed by the logarithmic evaluator. -/
theorem physicalTenChord_eq_dyadicCompressed
    (q : Q') (k : Nat) :
    weightedChordBlocks q (blockTenth (k + 1)) 10 ≈
      dyadicCompressedTenChord q k := by
  change weightedChordBlocks q (2 ^ k) 10 ≈
    dyadicCompressedTenChord q k
  exact weightedChordBlocks_eq_dyadicCompressedTenChord q k

theorem physicalTenChord_eq_dyadicCompressed_pred
    (q : Q') {k : Nat} (hk : 1 <= k) :
    weightedChordBlocks q (blockTenth k) 10 ≈
      dyadicCompressedTenChord q (k - 1) := by
  cases k with
  | zero => omega
  | succ j =>
      simpa only [Nat.add_sub_cancel_left] using
        physicalTenChord_eq_dyadicCompressed q j

/-- Honest endpoint carrier whose only terminal Gaussian datum is the ten
logarithmic dyadic states.  The other three fields are unchanged physical
obligations; in particular this structure does not smuggle in a terminal
inequality through the evaluator soundness proof. -/
structure BlockCompatibleP2TerminalDyadicTenChordTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalDyadicTenChord : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    blockLength k * integerThetaTerm w4 (blockNcut k + 1) <=
      terminalOuterSplitCoeff *
        (w4 * dyadicCompressedTenChord (w4 * w4) (k - 1))
  terminalRadial : forall k, 7 <= k ->
    let w0 := blockWeight k
    fixedCutoffTerminalRadialDiagEnvelope w0 (blockNcut k) <=
      terminalRadialSplitCoeff *
        ((blockLength k * blockLength k) *
          coordNormSq w0 (blockNcut k))
  fineReserve : forall k, 7 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <=
      D1 * T4

/-- Soundness compiler from the logarithmic-state carrier back to the exact
ten-chord carrier already consumed by the physical coefficient sandwich. -/
def BlockCompatibleP2TerminalDyadicTenChordTailFromSeven.toTenChordTail
    (T : BlockCompatibleP2TerminalDyadicTenChordTailFromSeven) :
    BlockCompatibleP2TerminalTenChordTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalTenChord := fun k hk => by
    let w4 := qpow (blockWeight (k + 1)) 4
    have h := T.terminalDyadicTenChord k hk
    have heq := physicalTenChord_eq_dyadicCompressed_pred
      (w4 * w4) (show 1 <= k by omega)
    have hinner :
        w4 * dyadicCompressedTenChord (w4 * w4) (k - 1) ≈
          w4 * weightedChordBlocks (w4 * w4) (blockTenth k) 10 :=
      Q'.mul_eqv_congr_left w4 _ _ (Q'.eqv_symm heq)
    have houter :
        terminalOuterSplitCoeff *
            (w4 * dyadicCompressedTenChord (w4 * w4) (k - 1)) ≈
          terminalOuterSplitCoeff *
            (w4 * weightedChordBlocks (w4 * w4) (blockTenth k) 10) :=
      Q'.mul_eqv_congr_left terminalOuterSplitCoeff _ _ hinner
    exact Q'.le_trans' _ _ _ (by simpa only [w4] using h)
      (Q'.le_of_eqv houter)
  terminalRadial := T.terminalRadial
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalDyadicTenChordTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalDyadicTenChordTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toTenChordTail.toCoefficientSandwich

/-! ## A higher-slack fixed 320-block physical carrier -/

/-- Starting at scale six, the physical cutoff is 320 equal dyadic blocks.
This refinement increases the analytic chord margin while preserving a fixed
block count across the all-cutoff tail. -/
theorem blockCutoffLength_eq_320_dyadicBlocks
    {k : Nat} (hk : 6 <= k) :
    blockNcut k + 1 = 320 * 2 ^ (k - 6) := by
  have hdecomp : k = 6 + (k - 6) := by omega
  rw [blockCutoffLength_closed, hdecomp, Nat.pow_add]
  have hsub : 6 + (k - 6) - 6 = k - 6 := by omega
  rw [hsub]
  change 5 * (64 * 2 ^ (k - 6)) = 320 * 2 ^ (k - 6)
  omega

/-- The refined 320-block chord is still a lower bound for the complete
physical integer-theta sum. -/
theorem weighted320Chord_le_integerThetaSum
    {w : Q'} (hw0 : (0 : Q') <= w) (hw1 : w <= (1 : Q'))
    {k : Nat} (hk : 6 <= k) :
    weightedChordBlocks (w * w) (2 ^ (k - 6)) 320 <=
      integerThetaSum w (blockNcut k) := by
  have hpow : 0 < 2 ^ (k - 6) := Nat.pow_pos (by decide)
  have hlen : blockNcut k + 1 = 320 * 2 ^ (k - 6) :=
    blockCutoffLength_eq_320_dyadicBlocks hk
  have h := weightedChordBlocks_le_integerThetaSum hw0 hw1
    (H := 2 ^ (k - 6)) (B := 320) (by omega)
  have hN : 320 * 2 ^ (k - 6) - 1 = blockNcut k := by omega
  rw [hN] at h
  exact h

/-- Honest all-cutoff carrier using 320 logarithmic dyadic states in place of
the exponentially long terminal theta sum. -/
structure BlockCompatibleP2TerminalDyadic320ChordTailFromSeven : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  terminalDyadic320Chord : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    blockLength k * integerThetaTerm w4 (blockNcut k + 1) <=
      terminalOuterSplitCoeff *
        (w4 * dyadicCompressedChordBlocks
          (w4 * w4) (k - 6) 320)
  terminalRadial : forall k, 7 <= k ->
    let w0 := blockWeight k
    fixedCutoffTerminalRadialDiagEnvelope w0 (blockNcut k) <=
      terminalRadialSplitCoeff *
        ((blockLength k * blockLength k) *
          coordNormSq w0 (blockNcut k))
  fineReserve : forall k, 7 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <=
      D1 * T4

/-- Compile the refined logarithmic carrier directly to the exact physical
theta carrier.  The only order step is the proved 320-block chord minorant. -/
def BlockCompatibleP2TerminalDyadic320ChordTailFromSeven.toThetaFactorizedTail
    (T : BlockCompatibleP2TerminalDyadic320ChordTailFromSeven) :
    BlockCompatibleP2TerminalThetaFactorizedTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  terminalTheta := fun k hk => by
    let w4 := qpow (blockWeight (k + 1)) 4
    let H := 2 ^ (k - 6)
    let C := dyadicCompressedChordBlocks (w4 * w4) (k - 6) 320
    let W := weightedChordBlocks (w4 * w4) H 320
    have hw40 : (0 : Q') <= w4 := by
      unfold w4
      exact qpow_nonneg (blockWeight (k + 1))
        (blockWeight_nonneg (k + 1)) 4
    have hw41 : w4 <= (1 : Q') := by
      unfold w4
      exact HeatKernelGap.qpow_le_one
        (blockWeight_nonneg (k + 1)) (blockWeight_le_one (k + 1)) 4
    have heq : W ≈ C := by
      dsimp only [W, C, H]
      exact weightedChordBlocks_eq_dyadicCompressedChordBlocks
        (w4 * w4) (k - 6) 320
    have hminor : W <= integerThetaSum w4 (blockNcut k) := by
      dsimp only [W, H]
      exact weighted320Chord_le_integerThetaSum hw40 hw41 (by omega)
    have hcert :
        blockLength k * integerThetaTerm w4 (blockNcut k + 1) <=
          terminalOuterSplitCoeff * (w4 * C) := by
      simpa only [w4, C] using T.terminalDyadic320Chord k hk
    have hcomp :
        terminalOuterSplitCoeff * (w4 * C) ≈
          terminalOuterSplitCoeff * (w4 * W) :=
      Q'.mul_eqv_congr_left terminalOuterSplitCoeff _ _
        (Q'.mul_eqv_congr_left w4 _ _ (Q'.eqv_symm heq))
    have hscale0 : (0 : Q') <= terminalOuterSplitCoeff * w4 :=
      Q'.mul_nonneg _ _ (by unfold terminalOuterSplitCoeff; decide) hw40
    have hscaled : (terminalOuterSplitCoeff * w4) * W <=
        (terminalOuterSplitCoeff * w4) *
          integerThetaSum w4 (blockNcut k) :=
      Q'.mul_le_mul_of_nonneg_left _ _
        (terminalOuterSplitCoeff * w4) hminor hscale0
    have hleftAssoc : terminalOuterSplitCoeff * (w4 * W) ≈
        (terminalOuterSplitCoeff * w4) * W :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    have hrightAssoc :
        (terminalOuterSplitCoeff * w4) *
            integerThetaSum w4 (blockNcut k) ≈
          terminalOuterSplitCoeff *
            (w4 * integerThetaSum w4 (blockNcut k)) :=
      Q'.mul_assoc_eqv _ _ _
    exact Q'.le_trans' _ _ _ hcert
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomp)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleftAssoc)
          (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hrightAssoc))))
  terminalRadial := T.terminalRadial
  fineReserve := T.fineReserve

def BlockCompatibleP2TerminalDyadic320ChordTailFromSeven.toCoefficientSandwich
    (T : BlockCompatibleP2TerminalDyadic320ChordTailFromSeven) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toThetaFactorizedTail.toCoefficientSandwich

#print axioms geoMoment0_double
#print axioms geoMoment1_double
#print axioms geoMoment2_double
#print axioms dyadicGeoMomentState_spec
#print axioms weightedChordBlock_eq_compressed
#print axioms weightedChordBlock_eq_dyadicCompressed
#print axioms weightedChordBlocks_eq_dyadicCompressedChordBlocks
#print axioms weightedChordBlocks_eq_dyadicCompressedTenChord
#print axioms physicalTenChord_eq_dyadicCompressed
#print axioms physicalTenChord_eq_dyadicCompressed_pred
#print axioms BlockCompatibleP2TerminalDyadicTenChordTailFromSeven.toTenChordTail
#print axioms BlockCompatibleP2TerminalDyadicTenChordTailFromSeven.toCoefficientSandwich
#print axioms blockCutoffLength_eq_320_dyadicBlocks
#print axioms weighted320Chord_le_integerThetaSum
#print axioms BlockCompatibleP2TerminalDyadic320ChordTailFromSeven.toThetaFactorizedTail
#print axioms BlockCompatibleP2TerminalDyadic320ChordTailFromSeven.toCoefficientSandwich

end YMGap.Continuum.P2BlockCompatibleThetaTerminalGeoMoments
