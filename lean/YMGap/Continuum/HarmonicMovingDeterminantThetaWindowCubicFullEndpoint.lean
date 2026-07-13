/-
Exact full-window endpoint certificates for the cubic theta carrier.

The adverse cubic cells form a terminal suffix, so the remaining cumulative
problem is an endpoint estimate.  This file supplies its algebraic core.  A
single degree-seven antiderivative telescopes the cleared cell polynomial.
After the even/odd square-root-band substitutions, multiplication by 210
leaves only one negative coefficient, at remainder degree six.  The defining
band bound absorbs it into the degree-five coefficient; all lower terms have
manifestly nonnegative coefficients.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierSuffix

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def psub (a b : PE) : PE := padd a (pneg b)
private def ppow (a : PE) (n : Nat) : PE := .pow a n

/-- A polynomial with natural coefficients, stored low degree first. -/
def qNatPoly (x : Q') : List Nat → Q'
  | [] => 0
  | a :: as => Q'.ofNat a + x * qNatPoly x as

private def pNatPoly (x : PE) : List Nat → PE
  | [] => pc 0
  | a :: as => padd (pc (Int.ofNat a)) (pmul x (pNatPoly x as))

theorem qNatPoly_nonnegative {x : Q'} (hx : (0 : Q') ≤ x) :
    ∀ as, (0 : Q') ≤ qNatPoly x as
  | [] => Q'.le_refl' 0
  | _ :: as => Q'.zero_le_add _ _
      (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
      (Q'.mul_nonneg _ _ hx (qNatPoly_nonnegative hx as))

private theorem ringQpow_nonnegative {x : Q'} (hx : (0 : Q') ≤ x) :
    ∀ n, (0 : Q') ≤ RingNormaliser.qpow x n
  | 0 => (by decide : (0 : Q') ≤ 1)
  | n + 1 => Q'.mul_nonneg _ _ (ringQpow_nonnegative hx n) hx

/-! ## The cleared cell and its exact antiderivative -/

private def pSlope (D N : PE) : PE :=
  padd (pmul N (ppow D 3))
    (pneg (pmul (padd N (pc 1))
      (pmul (psub D (pc 1)) (ppow (psub D N) 2))))

private def pCell (D N : PE) : PE :=
  padd
    (pmul (pmul
      (padd (padd (pmul (pc 12) (ppow D 2)) D) (pc 1))
      (ppow N 2)) (ppow D 3))
    (pneg (pmul (pc 4) (ppow (pSlope D N) 2)))

/-- The numerator of a cubic mode cell after multiplication by `D^6`. -/
def thetaCubicClearedCell (D N : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => D | _ => N)
    (pCell (.var 0) (.var 1))

private def pTerm (c : Int) (D X : PE) (d x : Nat) : PE :=
  pmul (pc c) (pmul (ppow D d) (ppow X x))

private def pAntiderivative (D X : PE) : PE :=
  padd (pTerm (-840) D X 6 1) <|
  padd (pTerm 1960 D X 5 3) <|
  padd (pTerm (-420) D X 5 2) <|
  padd (pTerm 140 D X 5 1) <|
  padd (pTerm (-672) D X 4 5) <|
  padd (pTerm (-1260) D X 4 4) <|
  padd (pTerm (-490) D X 4 3) <|
  padd (pTerm 735 D X 4 2) <|
  padd (pTerm 847 D X 4 1) <|
  padd (pTerm 560 D X 3 6) <|
  padd (pTerm 1344 D X 3 5) <|
  padd (pTerm 140 D X 3 4) <|
  padd (pTerm (-1890) D X 3 3) <|
  padd (pTerm (-805) D X 3 2) <|
  padd (pTerm 651 D X 3 1) <|
  padd (pTerm (-120) D X 2 7) <|
  padd (pTerm (-980) D X 2 6) <|
  padd (pTerm (-84) D X 2 5) <|
  padd (pTerm 1960 D X 2 4) <|
  padd (pTerm 420 D X 2 3) <|
  padd (pTerm (-980) D X 2 2) <|
  padd (pTerm (-216) D X 2 1) <|
  padd (pTerm 240 D X 1 7) <|
  padd (pTerm 280 D X 1 6) <|
  padd (pTerm (-840) D X 1 5) <|
  padd (pTerm (-560) D X 1 4) <|
  padd (pTerm 840 D X 1 3) <|
  padd (pTerm 280 D X 1 2) <|
  padd (pTerm (-240) D X 1 1) <|
  padd (pTerm (-120) D X 0 7) <|
  padd (pTerm 140 D X 0 6) <|
  padd (pTerm 252 D X 0 5) <|
  padd (pTerm (-280) D X 0 4) <|
  padd (pTerm (-140) D X 0 3) <|
  padd (pTerm 140 D X 0 2)
    (pTerm 8 D X 0 1)

/-- `210` times an indefinite sum of the cleared cell polynomial, normalized
to vanish at zero.  The multiplier clears all Faulhaber denominators. -/
def thetaCubicCellAntiderivative (D X : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => D | _ => X)
    (pAntiderivative (.var 0) (.var 1))

private def pAntiderivativeStepL : PE :=
  let D : PE := .var 0
  let X : PE := .var 1
  pAntiderivative D (padd X (pc 1))

private def pCellExpanded (D N : PE) : PE :=
  padd (pTerm (-4) D N 2 6) <|
  padd (pTerm 8 D N 1 6) <|
  padd (pTerm (-4) D N 0 6) <|
  padd (pTerm 16 D N 3 5) <|
  padd (pTerm (-40) D N 2 5) <|
  padd (pTerm 32 D N 1 5) <|
  padd (pTerm (-8) D N 0 5) <|
  padd (pTerm (-16) D N 4 4) <|
  padd (pTerm 72 D N 3 4) <|
  padd (pTerm (-92) D N 2 4) <|
  padd (pTerm 40 D N 1 4) <|
  padd (pTerm (-4) D N 0 4) <|
  padd (pTerm (-56) D N 4 3) <|
  padd (pTerm 120 D N 3 3) <|
  padd (pTerm (-80) D N 2 3) <|
  padd (pTerm 16 D N 1 3) <|
  padd (pTerm 28 D N 5 2) <|
  padd (pTerm (-75) D N 4 2) <|
  padd (pTerm 81 D N 3 2) <|
  padd (pTerm (-24) D N 2 2) <|
  padd (pTerm 24 D N 5 1) <|
  padd (pTerm (-40) D N 4 1) <|
  padd (pTerm 16 D N 3 1) <|
  padd (pTerm (-4) D N 6 0) <|
  padd (pTerm 8 D N 5 0)
    (pTerm (-4) D N 4 0)

private def pAntiderivativeStepR : PE :=
  let D : PE := .var 0
  let X : PE := .var 1
  padd (pAntiderivative D X) (pmul (pc 210) (pCellExpanded D X))

private theorem pCellExpanded_normal :
    RingNormaliser.normalize (pCellExpanded (.var 0) (.var 1)) =
      RingNormaliser.normalize (pCell (.var 0) (.var 1)) := by decide

private theorem pCellExpanded_eqv (D N : Q') :
    RingNormaliser.eval (fun | 0 => D | _ => N)
        (pCellExpanded (.var 0) (.var 1)) ≈
      thetaCubicClearedCell D N := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    (pCellExpanded (.var 0) (.var 1)) (pCell (.var 0) (.var 1))
    pCellExpanded_normal (fun | 0 => D | _ => N)
  simpa [pCellExpanded, pTerm, thetaCubicClearedCell,
    pc, padd, pmul, pneg, psub, ppow,
    RingNormaliser.eval] using h

private theorem pAntiderivativeStep_normal :
    RingNormaliser.normalize pAntiderivativeStepL =
      RingNormaliser.normalize pAntiderivativeStepR := by decide

/-- Exact finite-difference identity for the degree-seven primitive. -/
theorem thetaCubicCellAntiderivative_step (D X : Q') :
    thetaCubicCellAntiderivative D (X + 1) ≈
      thetaCubicCellAntiderivative D X +
        Q'.ofNat 210 * thetaCubicClearedCell D X := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pAntiderivativeStepL pAntiderivativeStepR
    pAntiderivativeStep_normal (fun | 0 => D | _ => X)
  have h0 : thetaCubicCellAntiderivative D (X + 1) ≈
      thetaCubicCellAntiderivative D X + Q'.ofNat 210 *
        RingNormaliser.eval (fun | 0 => D | _ => X)
          (pCellExpanded (.var 0) (.var 1)) := by
    simpa [pAntiderivativeStepL, pAntiderivativeStepR, pAntiderivative,
      pTerm, pCellExpanded, thetaCubicCellAntiderivative,
      pc, padd, pmul, pneg, psub, ppow, RingNormaliser.eval] using h
  exact Q'.eqv_trans _ _ _ h0
    (Q'.add_eqv_congr_left (thetaCubicCellAntiderivative D X) _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 210) _ _
        (pCellExpanded_eqv D X)))

private theorem polyEval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const c => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb =>
      exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb =>
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ iha) ?_
      exact Q'.mul_eqv_congr_left _ _ _ ihb
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

theorem thetaCubicCellAntiderivative_eqv_congr {D D' X X' : Q'}
    (hD : D ≈ D') (hX : X ≈ X') :
    thetaCubicCellAntiderivative D X ≈
      thetaCubicCellAntiderivative D' X' := by
  unfold thetaCubicCellAntiderivative
  apply polyEval_eqv_congr
  intro i
  rcases i with _ | i
  · exact hD
  · exact hX

/-- A block of consecutive cleared cells, starting at the rational mode `X`. -/
def thetaCubicClearedBlock (D X : Q') (count : Nat) : Q' :=
  BondMovingStep.fsum
    (fun j => thetaCubicClearedCell D (X + Q'.ofNat j)) count

private theorem telescope_rearrange (A B C : Q') :
    (A + -B) + C ≈ (A + C) + -B := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A (-B) C) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A _ _ (Q'.add_comm_eqv (-B) C)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv A C (-B))

/-- Telescoping of the cleared cubic cell block by the exact degree-seven
primitive. -/
theorem thetaCubicClearedBlock_telescope (D X : Q') : ∀ count,
    Q'.ofNat 210 * thetaCubicClearedBlock D X count ≈
      thetaCubicCellAntiderivative D (X + Q'.ofNat count) +
        -thetaCubicCellAntiderivative D X
  | 0 => by
      have hL : Q'.ofNat 210 * (0 : Q') ≈ 0 :=
        Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ 0)
          (RingNormaliser.q_zero_mul _)
      have hR : thetaCubicCellAntiderivative D X +
          -thetaCubicCellAntiderivative D X ≈ 0 :=
        Q'.eqv_trans _ _ _
          (Q'.add_comm_eqv _ (-thetaCubicCellAntiderivative D X))
          (Q'.neg_add_self_eqv _)
      have hx0 : X + Q'.ofNat 0 ≈ X := by
        exact RingNormaliser.eqv_of_eq (Q'.add_zero' X)
      have hF0 := thetaCubicCellAntiderivative_eqv_congr
        (Q'.eqv_refl D) hx0
      have htarget : thetaCubicCellAntiderivative D X +
          -thetaCubicCellAntiderivative D X ≈
        thetaCubicCellAntiderivative D (X + Q'.ofNat 0) +
          -thetaCubicCellAntiderivative D X :=
        Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hF0)
      simpa [thetaCubicClearedBlock, BondMovingStep.fsum] using
        Q'.eqv_trans _ _ _ hL
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm hR) htarget)
  | count + 1 => by
      let Y := X + Q'.ofNat count
      let S := thetaCubicClearedBlock D X count
      let C := thetaCubicClearedCell D Y
      have ih := thetaCubicClearedBlock_telescope D X count
      have hdist : Q'.ofNat 210 * (S + C) ≈
          Q'.ofNat 210 * S + Q'.ofNat 210 * C :=
        Q'.mul_add_eqv _ _ _
      have hsum : Q'.ofNat 210 * (S + C) ≈
          (thetaCubicCellAntiderivative D Y +
              -thetaCubicCellAntiderivative D X) +
            Q'.ofNat 210 * C := by
        refine Q'.eqv_trans _ _ _ hdist ?_
        exact Q'.add_eqv_congr_right _ _ _ ih
      have hstep := thetaCubicCellAntiderivative_step D Y
      have hrearrange := telescope_rearrange
        (thetaCubicCellAntiderivative D Y)
        (thetaCubicCellAntiderivative D X) (Q'.ofNat 210 * C)
      have hnext :
          (thetaCubicCellAntiderivative D Y +
              -thetaCubicCellAntiderivative D X) + Q'.ofNat 210 * C ≈
            thetaCubicCellAntiderivative D (Y + 1) +
              -thetaCubicCellAntiderivative D X := by
        refine Q'.eqv_trans _ _ _ hrearrange ?_
        exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hstep)
      have hpoint : Y + 1 ≈ X + Q'.ofNat (count + 1) := by
        dsimp only [Y]
        have hcast : X + Q'.ofNat (count + 1) ≈
            X + (Q'.ofNat count + 1) := by
          exact Q'.add_eqv_congr_left X _ _ (Q'.ofNat_add_eqv count 1)
        have hassoc : X + (Q'.ofNat count + 1) ≈
            (X + Q'.ofNat count) + 1 :=
          Q'.eqv_symm (Q'.add_assoc_eqv X (Q'.ofNat count) 1)
        exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hcast hassoc)
      have hF := thetaCubicCellAntiderivative_eqv_congr
        (Q'.eqv_refl D) hpoint
      have htotal := Q'.eqv_trans _ _ _ hsum
        (Q'.eqv_trans _ _ _ hnext
          (Q'.add_eqv_congr_right _ _
            (-thetaCubicCellAntiderivative D X) hF))
      simpa [thetaCubicClearedBlock, BondMovingStep.fsum, S, C, Y] using htotal

/-! ## Even and odd endpoint coefficient certificates -/

private def evenB5 (M : Q') : Q' := qNatPoly M [967, 321, 26]
private def evenB4 (M : Q') : Q' :=
  qNatPoly M [6375435, 5028281, 1481414, 193276, 9424]
private def evenB3 (M : Q') : Q' :=
  qNatPoly M [104008763, 105949322, 43037476, 8713824, 879408, 35392]
private def evenB2 (M : Q') : Q' :=
  qNatPoly M [12392778307, 18012193558, 11200268775, 3861893350,
    797370562, 98576628, 6756064, 198016]
private def evenB1 (M : Q') : Q' :=
  qNatPoly M [79985529015, 153363676760, 130491021694, 64651859336,
    20551339157, 4346005438, 611343944, 55156856, 2896096, 67424]
private def evenB0 (M : Q') : Q' :=
  qNatPoly M [85501847942, 267938337023, 354768765302, 268999754458,
    131599027099, 43976918746, 10298061046, 1696010044, 193021120,
    14485680, 646128, 12992]

/-- The full even-centre endpoint after substitution `m=M+5`,
`D=2m^2+r`, grouped by powers of the band remainder `r`. -/
def thetaCubicEvenEndpointCertificate (M r : Q') : Q' :=
  let qp := RingNormaliser.qpow
  qp r 5 * ((M + 6) *
      (Q'.ofNat 140 * evenB5 M + -(Q'.ofNat 840 * r))) +
  qp r 4 * (Q'.ofNat 7 * (M + 6) * evenB4 M) +
  qp r 3 * (Q'.ofNat 7 * (M + 5) * (M + 6) * evenB3 M) +
  qp r 2 * (Q'.ofNat 2 * (M + 5) * (M + 6) * evenB2 M) +
  r * (Q'.ofNat 4 * (M + 5) * (M + 6) * evenB1 M) +
  Q'.ofNat 4 * (M + 5) * (M + 6) * evenB0 M

private def oddB5 (M : Q') : Q' := qNatPoly M [996, 319, 26]
private def oddB4 (M : Q') : Q' :=
  qNatPoly M [8555040, 6263623, 1713666, 207772, 9424]
private def oddB3 (M : Q') : Q' :=
  qNatPoly M [858369720, 964013739, 449780482, 111603348,
    15534016, 1150128, 35392]
private def oddB2 (M : Q') : Q' :=
  qNatPoly M [20957015880, 28330084821, 16367749065, 5238949558,
    1003306202, 114963684, 7298144, 198016]
private def oddB1 (M : Q') : Q' :=
  qNatPoly M [169697154720, 300474718500, 235773697527, 107601809998,
    31475390013, 6119907322, 790947600, 65523576, 3157280, 67424]
private def oddB0 (M : Q') : Q' :=
  qNatPoly M [349235129960, 890526477181, 998854823946, 655962626430,
    281744267887, 83406596880, 17410736758, 2567679716, 262564048,
    17750480, 714672, 12992]

/-- The full odd-centre endpoint after substitution `m=M+5`,
`D=2m(m+1)+r`, grouped by powers of the band remainder `r`. -/
def thetaCubicOddEndpointCertificate (M r : Q') : Q' :=
  let qp := RingNormaliser.qpow
  qp r 5 * ((M + 7) *
      (Q'.ofNat 140 * oddB5 M + -(Q'.ofNat 840 * r))) +
  qp r 4 * (Q'.ofNat 7 * (M + 7) * oddB4 M) +
  qp r 3 * (Q'.ofNat 7 * (M + 7) * oddB3 M) +
  qp r 2 * (Q'.ofNat 2 * (M + 6) * (M + 7) * oddB2 M) +
  r * (Q'.ofNat 4 * (M + 6) * (M + 7) * oddB1 M) +
  Q'.ofNat 4 * (M + 6) * (M + 7) * oddB0 M

private def pEvenB5 (M : PE) : PE := pNatPoly M [967, 321, 26]
private def pEvenB4 (M : PE) : PE :=
  pNatPoly M [6375435, 5028281, 1481414, 193276, 9424]
private def pEvenB3 (M : PE) : PE :=
  pNatPoly M [104008763, 105949322, 43037476, 8713824, 879408, 35392]
private def pEvenB2 (M : PE) : PE :=
  pNatPoly M [12392778307, 18012193558, 11200268775, 3861893350,
    797370562, 98576628, 6756064, 198016]
private def pEvenB1 (M : PE) : PE :=
  pNatPoly M [79985529015, 153363676760, 130491021694, 64651859336,
    20551339157, 4346005438, 611343944, 55156856, 2896096, 67424]
private def pEvenB0 (M : PE) : PE :=
  pNatPoly M [85501847942, 267938337023, 354768765302, 268999754458,
    131599027099, 43976918746, 10298061046, 1696010044, 193021120,
    14485680, 646128, 12992]

private def pEvenCertificate (M r : PE) : PE :=
  padd
    (pmul (ppow r 5) (pmul (padd M (pc 6))
      (psub (pmul (pc 140) (pEvenB5 M)) (pmul (pc 840) r)))) <|
  padd (pmul (ppow r 4)
      (pmul (pmul (pc 7) (padd M (pc 6))) (pEvenB4 M))) <|
  padd (pmul (ppow r 3)
      (pmul (pmul (pmul (pc 7) (padd M (pc 5)))
        (padd M (pc 6))) (pEvenB3 M))) <|
  padd (pmul (ppow r 2)
      (pmul (pmul (pmul (pc 2) (padd M (pc 5)))
        (padd M (pc 6))) (pEvenB2 M)))
    (padd (pmul r
      (pmul (pmul (pmul (pc 4) (padd M (pc 5)))
        (padd M (pc 6))) (pEvenB1 M)))
      (pmul (pmul (pmul (pc 4) (padd M (pc 5)))
        (padd M (pc 6))) (pEvenB0 M)))

private def pOddB5 (M : PE) : PE := pNatPoly M [996, 319, 26]
private def pOddB4 (M : PE) : PE :=
  pNatPoly M [8555040, 6263623, 1713666, 207772, 9424]
private def pOddB3 (M : PE) : PE :=
  pNatPoly M [858369720, 964013739, 449780482, 111603348,
    15534016, 1150128, 35392]
private def pOddB2 (M : PE) : PE :=
  pNatPoly M [20957015880, 28330084821, 16367749065, 5238949558,
    1003306202, 114963684, 7298144, 198016]
private def pOddB1 (M : PE) : PE :=
  pNatPoly M [169697154720, 300474718500, 235773697527, 107601809998,
    31475390013, 6119907322, 790947600, 65523576, 3157280, 67424]
private def pOddB0 (M : PE) : PE :=
  pNatPoly M [349235129960, 890526477181, 998854823946, 655962626430,
    281744267887, 83406596880, 17410736758, 2567679716, 262564048,
    17750480, 714672, 12992]

private def pOddCertificate (M r : PE) : PE :=
  padd
    (pmul (ppow r 5) (pmul (padd M (pc 7))
      (psub (pmul (pc 140) (pOddB5 M)) (pmul (pc 840) r)))) <|
  padd (pmul (ppow r 4)
      (pmul (pmul (pc 7) (padd M (pc 7))) (pOddB4 M))) <|
  padd (pmul (ppow r 3)
      (pmul (pmul (pc 7) (padd M (pc 7))) (pOddB3 M))) <|
  padd (pmul (ppow r 2)
      (pmul (pmul (pmul (pc 2) (padd M (pc 6)))
        (padd M (pc 7))) (pOddB2 M)))
    (padd (pmul r
      (pmul (pmul (pmul (pc 4) (padd M (pc 6)))
        (padd M (pc 7))) (pOddB1 M)))
      (pmul (pmul (pmul (pc 4) (padd M (pc 6)))
        (padd M (pc 7))) (pOddB0 M)))

private def pEvenAbsorbL : PE :=
  let M : PE := .var 0
  padd (pmul (pc 840) (padd (pmul (pc 2) M) (pc 9)))
    (pmul (pc 140) (pNatPoly M [913, 309, 26]))

private def pEvenAbsorbR : PE :=
  pmul (pc 140) (pNatPoly (.var 0) [967, 321, 26])

private def pOddAbsorbL : PE :=
  let M : PE := .var 0
  padd (pmul (pc 840) (padd (pmul (pc 2) M) (pc 11)))
    (pmul (pc 140) (pNatPoly M [930, 307, 26]))

private def pOddAbsorbR : PE :=
  pmul (pc 140) (pNatPoly (.var 0) [996, 319, 26])

private theorem pEvenAbsorb_normal :
    RingNormaliser.normalize pEvenAbsorbL =
      RingNormaliser.normalize pEvenAbsorbR := by decide

private theorem pOddAbsorb_normal :
    RingNormaliser.normalize pOddAbsorbL =
      RingNormaliser.normalize pOddAbsorbR := by decide

private theorem even_absorb_identity (M : Q') :
    Q'.ofNat 840 * (Q'.ofNat 2 * M + 9) +
        Q'.ofNat 140 * qNatPoly M [913, 309, 26] ≈
      Q'.ofNat 140 * evenB5 M := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pEvenAbsorbL pEvenAbsorbR pEvenAbsorb_normal (fun _ => M)
  simpa [pEvenAbsorbL, pEvenAbsorbR, pNatPoly, qNatPoly, evenB5,
    pc, padd, pmul, RingNormaliser.eval] using h

private theorem odd_absorb_identity (M : Q') :
    Q'.ofNat 840 * (Q'.ofNat 2 * M + 11) +
        Q'.ofNat 140 * qNatPoly M [930, 307, 26] ≈
      Q'.ofNat 140 * oddB5 M := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pOddAbsorbL pOddAbsorbR pOddAbsorb_normal (fun _ => M)
  simpa [pOddAbsorbL, pOddAbsorbR, pNatPoly, qNatPoly, oddB5,
    pc, padd, pmul, RingNormaliser.eval] using h

/-- Nonnegativity of the full even-centre endpoint throughout its entire
square-root band. -/
theorem thetaCubicEvenEndpointCertificate_nonnegative {M r : Q'}
    (hM : (0 : Q') ≤ M) (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * M + 9) :
    (0 : Q') ≤ thetaCubicEvenEndpointCertificate M r := by
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 840) hrTop
    (by decide : (0 : Q') ≤ Q'.ofNat 840)
  have hdiff : (0 : Q') ≤ qNatPoly M [913, 309, 26] :=
    qNatPoly_nonnegative hM _
  have hbonus : (0 : Q') ≤
      Q'.ofNat 140 * qNatPoly M [913, 309, 26] :=
    Q'.mul_nonneg _ _ (by decide) hdiff
  have hbase := Q'.add_le_self_of_nonneg
    (Q'.ofNat 840 * (Q'.ofNat 2 * M + 9))
    (Q'.ofNat 140 * qNatPoly M [913, 309, 26]) hbonus
  have htop : Q'.ofNat 840 * r ≤ Q'.ofNat 140 * evenB5 M :=
    Q'.le_trans' _ _ _ hscale
      (Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv (even_absorb_identity M)))
  have hinner : (0 : Q') ≤
      Q'.ofNat 140 * evenB5 M + -(Q'.ofNat 840 * r) :=
    Q'.sub_nonneg_of_le htop
  have hM5 : (0 : Q') ≤ M + 5 := Q'.zero_le_add _ _ hM (by decide)
  have hM6 : (0 : Q') ≤ M + 6 := Q'.zero_le_add _ _ hM (by decide)
  have h5 : (0 : Q') ≤ RingNormaliser.qpow r 5 *
      ((M + 6) * (Q'.ofNat 140 * evenB5 M + -(Q'.ofNat 840 * r))) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 5)
      (Q'.mul_nonneg _ _ hM6 hinner)
  have h4 : (0 : Q') ≤ RingNormaliser.qpow r 4 *
      (Q'.ofNat 7 * (M + 6) * evenB4 M) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 4)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hM6)
        (qNatPoly_nonnegative hM _))
  have h3 : (0 : Q') ≤ RingNormaliser.qpow r 3 *
      (Q'.ofNat 7 * (M + 5) * (M + 6) * evenB3 M) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 3)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM5) hM6)
        (qNatPoly_nonnegative hM _))
  have h2 : (0 : Q') ≤ RingNormaliser.qpow r 2 *
      (Q'.ofNat 2 * (M + 5) * (M + 6) * evenB2 M) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 2)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM5) hM6)
        (qNatPoly_nonnegative hM _))
  have h1 : (0 : Q') ≤ r *
      (Q'.ofNat 4 * (M + 5) * (M + 6) * evenB1 M) :=
    Q'.mul_nonneg _ _ hr
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM5) hM6)
        (qNatPoly_nonnegative hM _))
  have h0 : (0 : Q') ≤
      Q'.ofNat 4 * (M + 5) * (M + 6) * evenB0 M :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM5) hM6)
      (qNatPoly_nonnegative hM _)
  unfold thetaCubicEvenEndpointCertificate
  have h54 := Q'.zero_le_add _ _ h5 h4
  have h543 := Q'.zero_le_add _ _ h54 h3
  have h5432 := Q'.zero_le_add _ _ h543 h2
  have h54321 := Q'.zero_le_add _ _ h5432 h1
  exact Q'.zero_le_add _ _ h54321 h0

/-- Nonnegativity of the full odd-centre endpoint throughout its entire
square-root band. -/
theorem thetaCubicOddEndpointCertificate_nonnegative {M r : Q'}
    (hM : (0 : Q') ≤ M) (hr : (0 : Q') ≤ r)
    (hrTop : r ≤ Q'.ofNat 2 * M + 11) :
    (0 : Q') ≤ thetaCubicOddEndpointCertificate M r := by
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 840) hrTop
    (by decide : (0 : Q') ≤ Q'.ofNat 840)
  have hdiff : (0 : Q') ≤ qNatPoly M [930, 307, 26] :=
    qNatPoly_nonnegative hM _
  have hbonus : (0 : Q') ≤
      Q'.ofNat 140 * qNatPoly M [930, 307, 26] :=
    Q'.mul_nonneg _ _ (by decide) hdiff
  have hbase := Q'.add_le_self_of_nonneg
    (Q'.ofNat 840 * (Q'.ofNat 2 * M + 11))
    (Q'.ofNat 140 * qNatPoly M [930, 307, 26]) hbonus
  have htop : Q'.ofNat 840 * r ≤ Q'.ofNat 140 * oddB5 M :=
    Q'.le_trans' _ _ _ hscale
      (Q'.le_trans' _ _ _ hbase (Q'.le_of_eqv (odd_absorb_identity M)))
  have hinner : (0 : Q') ≤
      Q'.ofNat 140 * oddB5 M + -(Q'.ofNat 840 * r) :=
    Q'.sub_nonneg_of_le htop
  have hM6 : (0 : Q') ≤ M + 6 := Q'.zero_le_add _ _ hM (by decide)
  have hM7 : (0 : Q') ≤ M + 7 := Q'.zero_le_add _ _ hM (by decide)
  have h5 : (0 : Q') ≤ RingNormaliser.qpow r 5 *
      ((M + 7) * (Q'.ofNat 140 * oddB5 M + -(Q'.ofNat 840 * r))) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 5)
      (Q'.mul_nonneg _ _ hM7 hinner)
  have h4 : (0 : Q') ≤ RingNormaliser.qpow r 4 *
      (Q'.ofNat 7 * (M + 7) * oddB4 M) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 4)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hM7)
        (qNatPoly_nonnegative hM _))
  have h3 : (0 : Q') ≤ RingNormaliser.qpow r 3 *
      (Q'.ofNat 7 * (M + 7) * oddB3 M) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 3)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hM7)
        (qNatPoly_nonnegative hM _))
  have h2 : (0 : Q') ≤ RingNormaliser.qpow r 2 *
      (Q'.ofNat 2 * (M + 6) * (M + 7) * oddB2 M) :=
    Q'.mul_nonneg _ _ (ringQpow_nonnegative hr 2)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM6) hM7)
        (qNatPoly_nonnegative hM _))
  have h1 : (0 : Q') ≤ r *
      (Q'.ofNat 4 * (M + 6) * (M + 7) * oddB1 M) :=
    Q'.mul_nonneg _ _ hr
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM6) hM7)
        (qNatPoly_nonnegative hM _))
  have h0 : (0 : Q') ≤
      Q'.ofNat 4 * (M + 6) * (M + 7) * oddB0 M :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hM6) hM7)
      (qNatPoly_nonnegative hM _)
  unfold thetaCubicOddEndpointCertificate
  have h54 := Q'.zero_le_add _ _ h5 h4
  have h543 := Q'.zero_le_add _ _ h54 h3
  have h5432 := Q'.zero_le_add _ _ h543 h2
  have h54321 := Q'.zero_le_add _ _ h5432 h1
  exact Q'.zero_le_add _ _ h54321 h0

#print axioms qNatPoly
#print axioms qNatPoly_nonnegative
#print axioms thetaCubicClearedCell
#print axioms thetaCubicCellAntiderivative
#print axioms thetaCubicCellAntiderivative_step
#print axioms thetaCubicCellAntiderivative_eqv_congr
#print axioms thetaCubicClearedBlock
#print axioms thetaCubicClearedBlock_telescope
#print axioms thetaCubicEvenEndpointCertificate
#print axioms thetaCubicOddEndpointCertificate
#print axioms thetaCubicEvenEndpointCertificate_nonnegative
#print axioms thetaCubicOddEndpointCertificate_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint
