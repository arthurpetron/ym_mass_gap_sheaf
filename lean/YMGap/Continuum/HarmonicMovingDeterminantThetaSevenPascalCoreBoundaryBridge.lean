/-
Exact splice from the seven-coordinate gap formulas to the corrected
six-coordinate projective boundary.

The endpoint correction changes only deficits zero through three.  On the
common scale `630`, the first six corrected coefficients are precisely the
integer polynomial used by the positive boundary factorisation.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryFactor
import YMGap.Continuum.BernsteinProjectiveBoundarySix

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryBridge

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinProjectiveBoundarySix
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCore
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryFactor
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence

local infix:50 " ≈ " => Q'.eqv

private theorem bridge_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

private theorem bridge_ofInt_num_cast (z : Int) :
    (Q'.ofInt z).num = z := rfl

private theorem bridge_ofInt_den_cast (z : Int) :
    ((Q'.ofInt z).den : Int) = 1 := rfl

private theorem bridge_one_den_cast : (((1 : Q').den : Int)) = 1 := rfl

local macro "bridge_integer_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, bridge_neg_num_cast,
               bridge_ofInt_num_cast, bridge_ofInt_den_cast,
               bridge_one_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.natCast_one,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- The first six corrected core coefficients on the common scale `630`. -/
def correctedCoreBoundary630 : Nat → Int → Int
  | 0, m => intPolyEval m [0, -2520]
  | 1, m => intPolyEval m [0, -6300, -3780, 2520]
  | 2, m => intPolyEval m [0, -4935, -7875, 5250]
  | 3, m => intPolyEval m [0, -1260, -4410, 3990, 0, -840]
  | 4, m => intPolyEval m [0, -483, 0, 2415, 0, -1932]
  | 5, m => intPolyEval m [0, -570, 0, 2954, 0, -2800, 0, 416]
  | _, _ => 0

private theorem scale_nine_sub {g f c q : Int}
    (hg : 5670 * g = f) (hq : f - 5670 * c = 9 * q) :
    630 * (g - c) = q := by omega

private theorem scale_nine {g f q : Int}
    (hg : 5670 * g = f) (hq : f = 9 * q) :
    630 * g = q := by omega

set_option maxRecDepth 100000 in
private theorem pCore_zero_normal :
    RingNormaliser.normalize
        (ps (pFormula 0 pv)
          (pm (pc 5670) (pm (pc 4) (pm pv pv)))) =
      RingNormaliser.normalize
        (pm (pc 9) (pIntPoly pv [0, -2520])) := by decide

set_option maxRecDepth 100000 in
private theorem pCore_one_normal :
    RingNormaliser.normalize
        (ps (pFormula 1 pv)
          (pm (pc 5670) (pm (pc 3) (pm (pc 4) (pm pv pv))))) =
      RingNormaliser.normalize
        (pm (pc 9) (pIntPoly pv [0, -6300, -3780, 2520])) := by decide

set_option maxRecDepth 100000 in
private theorem pCore_two_normal :
    RingNormaliser.normalize
        (ps (pFormula 2 pv)
          (pm (pc 5670) (pm (pc 3) (pm (pc 4) (pm pv pv))))) =
      RingNormaliser.normalize
        (pm (pc 9) (pIntPoly pv [0, -4935, -7875, 5250])) := by decide

set_option maxRecDepth 100000 in
private theorem pCore_three_normal :
    RingNormaliser.normalize
        (ps (pFormula 3 pv)
          (pm (pc 5670) (pm (pc 4) (pm pv pv)))) =
      RingNormaliser.normalize
        (pm (pc 9) (pIntPoly pv [0, -1260, -4410, 3990, 0, -840])) := by decide

set_option maxRecDepth 100000 in
private theorem pCore_four_normal :
    RingNormaliser.normalize (pFormula 4 pv) =
      RingNormaliser.normalize
        (pm (pc 9) (pIntPoly pv [0, -483, 0, 2415, 0, -1932])) := by decide

set_option maxRecDepth 100000 in
private theorem pCore_five_normal :
    RingNormaliser.normalize (pFormula 5 pv) =
      RingNormaliser.normalize
        (pm (pc 9)
          (pIntPoly pv [0, -570, 0, 2954, 0, -2800, 0, 416])) := by decide

/-- Exact coordinate identification between the seven-gap formulas and the
corrected core boundary. -/
theorem sevenCoreDeficit_boundary630 (m r : Nat)
    (hm : 1 ≤ m) (hr : r ≤ 5) :
    630 * sevenCoreDeficit m r = correctedCoreBoundary630 r (m : Int) := by
  have hg := sevenGapDeficit_boundary_scaled m r hm (by omega : r ≤ 6)
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 by omega) with
    h | h | h | h | h | h <;> subst r
  · rw [sevenCoreDeficit_zero m hm]
    apply scale_nine_sub hg
    have h := IntRingNormaliser.poly_identity_of_normal_eq
      (ps (pFormula 0 pv) (pm (pc 5670) (pm (pc 4) (pm pv pv))))
      (pm (pc 9) (pIntPoly pv [0, -2520])) pCore_zero_normal
      (fun _ => (m : Int))
    simpa [sevenBoundaryScaledFormula, correctedCoreBoundary630,
      intPolyEval, pFormula, pIntPoly, pc, pv, pa, pm, pn, ps,
      IntRingNormaliser.eval, Int.mul_assoc] using h
  · rw [sevenCoreDeficit_one m hm]
    apply scale_nine_sub hg
    have h := IntRingNormaliser.poly_identity_of_normal_eq
      (ps (pFormula 1 pv)
        (pm (pc 5670) (pm (pc 3) (pm (pc 4) (pm pv pv)))))
      (pm (pc 9) (pIntPoly pv [0, -6300, -3780, 2520]))
      pCore_one_normal (fun _ => (m : Int))
    simpa [sevenBoundaryScaledFormula, correctedCoreBoundary630,
      intPolyEval, pFormula, pIntPoly, pc, pv, pa, pm, pn, ps,
      IntRingNormaliser.eval, Int.mul_assoc] using h
  · rw [sevenCoreDeficit_two m hm]
    apply scale_nine_sub hg
    have h := IntRingNormaliser.poly_identity_of_normal_eq
      (ps (pFormula 2 pv)
        (pm (pc 5670) (pm (pc 3) (pm (pc 4) (pm pv pv)))))
      (pm (pc 9) (pIntPoly pv [0, -4935, -7875, 5250]))
      pCore_two_normal (fun _ => (m : Int))
    simpa [sevenBoundaryScaledFormula, correctedCoreBoundary630,
      intPolyEval, pFormula, pIntPoly, pc, pv, pa, pm, pn, ps,
      IntRingNormaliser.eval, Int.mul_assoc] using h
  · rw [sevenCoreDeficit_three m hm]
    apply scale_nine_sub hg
    have h := IntRingNormaliser.poly_identity_of_normal_eq
      (ps (pFormula 3 pv) (pm (pc 5670) (pm (pc 4) (pm pv pv))))
      (pm (pc 9) (pIntPoly pv [0, -1260, -4410, 3990, 0, -840]))
      pCore_three_normal (fun _ => (m : Int))
    simpa [sevenBoundaryScaledFormula, correctedCoreBoundary630,
      intPolyEval, pFormula, pIntPoly, pc, pv, pa, pm, pn, ps,
      IntRingNormaliser.eval, Int.mul_assoc] using h
  · rw [sevenCoreDeficit_eq_sevenGapDeficit_of_four_le m 4 hm (by omega)]
    apply scale_nine hg
    have h := IntRingNormaliser.poly_identity_of_normal_eq
      (pFormula 4 pv) (pm (pc 9)
        (pIntPoly pv [0, -483, 0, 2415, 0, -1932]))
      pCore_four_normal (fun _ => (m : Int))
    simpa [sevenBoundaryScaledFormula, correctedCoreBoundary630,
      intPolyEval, pFormula, pIntPoly, pc, pv, pa, pm,
      IntRingNormaliser.eval, Int.mul_assoc] using h
  · rw [sevenCoreDeficit_eq_sevenGapDeficit_of_four_le m 5 hm (by omega)]
    apply scale_nine hg
    have h := IntRingNormaliser.poly_identity_of_normal_eq
      (pFormula 5 pv) (pm (pc 9)
        (pIntPoly pv [0, -570, 0, 2954, 0, -2800, 0, 416]))
      pCore_five_normal (fun _ => (m : Int))
    simpa [sevenBoundaryScaledFormula, correctedCoreBoundary630,
      intPolyEval, pFormula, pIntPoly, pc, pv, pa, pm,
      IntRingNormaliser.eval, Int.mul_assoc] using h

/-- The scaled six-coordinate bracket in deficit order. -/
def correctedCoreBoundaryScaledBracket (m : Nat) (t : Q') : Q' :=
  Q'.ofInt (correctedCoreBoundary630 0 (m : Int)) * t ^ 5 +
    (Q'.ofInt (correctedCoreBoundary630 1 (m : Int)) * t ^ 4 +
      (Q'.ofInt (correctedCoreBoundary630 2 (m : Int)) * t ^ 3 +
        (Q'.ofInt (correctedCoreBoundary630 3 (m : Int)) * t ^ 2 +
          (Q'.ofInt (correctedCoreBoundary630 4 (m : Int)) * t +
            Q'.ofInt (correctedCoreBoundary630 5 (m : Int))))))

/-- Integer evaluation of the same scaled bracket. -/
def correctedCoreBoundaryScaledInt (m t : Int) : Int :=
  correctedCoreBoundary630 0 m * (t * t * t * t * t) +
    (correctedCoreBoundary630 1 m * (t * t * t * t) +
      (correctedCoreBoundary630 2 m * (t * t * t) +
        (correctedCoreBoundary630 3 m * (t * t) +
          (correctedCoreBoundary630 4 m * t +
            correctedCoreBoundary630 5 m))))

private def pCorrectedBoundary (m t : PE) : PE :=
  pa (pm (pIntPoly m [0, -2520]) (pp t 5)) <|
  pa (pm (pIntPoly m [0, -6300, -3780, 2520]) (pp t 4)) <|
  pa (pm (pIntPoly m [0, -4935, -7875, 5250]) (pp t 3)) <|
  pa (pm (pIntPoly m [0, -1260, -4410, 3990, 0, -840]) (pp t 2))
    (pa (pm (pIntPoly m [0, -483, 0, 2415, 0, -1932]) t)
      (pIntPoly m [0, -570, 0, 2954, 0, -2800, 0, 416]))

private def pCorrectedPositive (t : PE) : PE :=
  pIntPoly t [1033830, 3269037, 4205732, 2841717, 1085894, 232296,
    23264]

set_option maxRecDepth 100000 in
private theorem pCorrectedBoundary_factor_normal :
    RingNormaliser.normalize
        (pCorrectedBoundary (pa (pm (pc 2) pv) (pc 4)) pv) =
      RingNormaliser.normalize
        (pm (pc 2) (pm (pa pv (pc 2)) (pCorrectedPositive pv))) := by decide

/-- Exact integer factorisation on the physical ray. -/
theorem correctedCoreBoundaryScaledInt_physical_factor (t : Nat) :
    correctedCoreBoundaryScaledInt (2 * (t : Int) + 4) (t : Int) =
      2 * ((t : Int) + 2) *
        intPolyEval (t : Int)
          [1033830, 3269037, 4205732, 2841717, 1085894, 232296,
            23264] := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pCorrectedBoundary (pa (pm (pc 2) pv) (pc 4)) pv)
    (pm (pc 2) (pm (pa pv (pc 2)) (pCorrectedPositive pv)))
    pCorrectedBoundary_factor_normal (fun _ => (t : Int))
  simpa [correctedCoreBoundaryScaledInt, correctedCoreBoundary630,
    pCorrectedBoundary, pCorrectedPositive, intPolyEval, pIntPoly,
    pc, pv, pa, pm, pp, IntRingNormaliser.eval,
    IntRingNormaliser.intPow, Int.mul_assoc] using h

private theorem intPolyEval_positive_coeff_nonnegative {x : Int}
    (hx : 0 ≤ x) : ∀ cs : List Nat,
    0 ≤ intPolyEval x (cs.map Int.ofNat)
  | [] => by simp [intPolyEval]
  | a :: as => by
      simp only [List.map, intPolyEval]
      exact Int.add_nonneg (Int.natCast_nonneg a)
        (Int.mul_nonneg hx (intPolyEval_positive_coeff_nonnegative hx as))

/-- The scaled corrected boundary bracket is nonnegative on the physical
integer ray. -/
theorem correctedCoreBoundaryScaledInt_physical_nonnegative (t : Nat) :
    0 ≤ correctedCoreBoundaryScaledInt (2 * (t : Int) + 4) (t : Int) := by
  rw [correctedCoreBoundaryScaledInt_physical_factor]
  have ht : (0 : Int) ≤ (t : Int) := Int.natCast_nonneg t
  have hp : (0 : Int) ≤ intPolyEval (t : Int)
      [1033830, 3269037, 4205732, 2841717, 1085894, 232296, 23264] := by
    simpa using intPolyEval_positive_coeff_nonnegative ht
      [1033830, 3269037, 4205732, 2841717, 1085894, 232296, 23264]
  exact Int.mul_nonneg (Int.mul_nonneg (by decide) (by omega)) hp

/-- Embedding the integer bracket agrees with the constructive-rational
bracket. -/
theorem correctedCoreBoundaryScaledBracket_eqv_int (m t : Nat) :
    correctedCoreBoundaryScaledBracket m (Q'.ofNat t) ≈
      Q'.ofInt (correctedCoreBoundaryScaledInt (m : Int) (t : Int)) := by
  unfold correctedCoreBoundaryScaledBracket correctedCoreBoundaryScaledInt
    correctedCoreBoundary630
  simp only [intPolyEval, Q'.pow_succ, Q'.pow_zero]
  bridge_integer_qeqv

private theorem ofInt_nonnegative {z : Int} (hz : 0 ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

/-- Constructive-rational form of the corrected boundary payment. -/
theorem correctedCoreBoundaryScaledBracket_physical_nonnegative (t : Nat) :
    (0 : Q') ≤ correctedCoreBoundaryScaledBracket
      (2 * t + 4) (Q'.ofNat t) := by
  exact Q'.le_trans' _ _ _
    (ofInt_nonnegative (correctedCoreBoundaryScaledInt_physical_nonnegative t))
    (Q'.ge_of_eqv (correctedCoreBoundaryScaledBracket_eqv_int
      (2 * t + 4) t))

/-- Generic six-coordinate projective bracket after removal of the common
lowest power. -/
def projectiveBoundaryBracketSix (D : Nat) (c : Nat → Int) (x : Q') : Q' :=
  Q'.ofInt (c D) * x ^ 5 +
    (Q'.ofInt (c (D - 1)) * x ^ 4 +
      (Q'.ofInt (c (D - 2)) * x ^ 3 +
        (Q'.ofInt (c (D - 3)) * x ^ 2 +
          (Q'.ofInt (c (D - 4)) * x + Q'.ofInt (c (D - 5))))))

/-- The six-coordinate projective boundary factors out `x^(D-5)`. -/
theorem projectiveBoundarySix_eqv_factor (D : Nat) (c : Nat → Int)
    (x : Q') (hD : 5 ≤ D) :
    projectiveBoundarySix D c x ≈
      x ^ (D - 5) * projectiveBoundaryBracketSix D c x := by
  have h0n : D = (D - 5) + 5 := by omega
  have h1n : D - 1 = (D - 5) + 4 := by omega
  have h2n : D - 2 = (D - 5) + 3 := by omega
  have h3n : D - 3 = (D - 5) + 2 := by omega
  have h4n : D - 4 = (D - 5) + 1 := by omega
  have h0 : x ^ D ≈ x ^ (D - 5) * x ^ 5 := by
    rw [h0n]
    exact Q'.pow_add_eqv x (D - 5) 5
  have h1 : x ^ (D - 1) ≈ x ^ (D - 5) * x ^ 4 := by
    rw [h1n]
    exact Q'.pow_add_eqv x (D - 5) 4
  have h2 : x ^ (D - 2) ≈ x ^ (D - 5) * x ^ 3 := by
    rw [h2n]
    exact Q'.pow_add_eqv x (D - 5) 3
  have h3 : x ^ (D - 3) ≈ x ^ (D - 5) * x ^ 2 := by
    rw [h3n]
    exact Q'.pow_add_eqv x (D - 5) 2
  have h4 : x ^ (D - 4) ≈ x ^ (D - 5) * x := by
    rw [h4n]
    refine Q'.eqv_trans _ _ _ (Q'.pow_add_eqv x (D - 5) 1) ?_
    exact Q'.mul_eqv_congr_left (x ^ (D - 5)) _ _
      (Q'.mul_one_eqv x)
  unfold projectiveBoundarySix
  simp only [finSum_succ, finSum_zero, Nat.sub_zero, Q'.zero_add']
  refine Q'.eqv_trans _
    (((((Q'.ofInt (c D) * (x ^ (D - 5) * x ^ 5) +
      Q'.ofInt (c (D - 1)) * (x ^ (D - 5) * x ^ 4)) +
      Q'.ofInt (c (D - 2)) * (x ^ (D - 5) * x ^ 3)) +
      Q'.ofInt (c (D - 3)) * (x ^ (D - 5) * x ^ 2)) +
      Q'.ofInt (c (D - 4)) * (x ^ (D - 5) * x)) +
      Q'.ofInt (c (D - 5)) * x ^ (D - 5)) _ ?_ ?_
  · refine Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr'
              (Q'.mul_eqv_congr_left _ _ _ h0)
              (Q'.mul_eqv_congr_left _ _ _ h1))
            (Q'.mul_eqv_congr_left _ _ _ h2))
          (Q'.mul_eqv_congr_left _ _ _ h3))
        (Q'.mul_eqv_congr_left _ _ _ h4))
      (Q'.eqv_refl _)
  · unfold projectiveBoundaryBracketSix
    bridge_integer_qeqv

private theorem scaled_ofInt_eqv {z q : Int} (h : 630 * z = q) :
    Q'.ofNat 630 * Q'.ofInt z ≈ Q'.ofInt q := by
  unfold Q'.eqv
  change (630 : Int) * z * 1 = q * 1
  omega

private theorem coreDeficit_eq_coefficient (m r : Nat)
    (hr : r ≤ sevenGapDegree m) :
    sevenCoreDeficit m r =
      sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m - r) := by
  unfold sevenCoreDeficit
  rw [if_pos hr]

/-- Multiplying the actual core boundary bracket by `630` gives exactly the
closed scaled bracket. -/
theorem projectiveCoreBoundaryBracketSix_scaled (m : Nat) (x : Q')
    (hm : 2 ≤ m) :
    Q'.ofNat 630 * projectiveBoundaryBracketSix (sevenGapDegree m)
        (sevenCoreBernCoeff (sevenGapDegree m) m) x ≈
      correctedCoreBoundaryScaledBracket m x := by
  let D := sevenGapDegree m
  have hD : 5 ≤ D := by
    have hs : 4 ≤ m * m := Nat.mul_le_mul hm hm
    have h8 : 8 ≤ 2 * (m * m) := Nat.mul_le_mul_left 2 hs
    have h9 : 9 ≤ 2 * (m * m) + 1 := by omega
    exact Nat.le_trans (by decide : 5 ≤ 9) (by
      simpa [D, sevenGapDegree, Nat.mul_assoc] using h9)
  have hc (r : Nat) (hr : r ≤ 5) :
      630 * sevenCoreBernCoeff D m (D - r) =
        correctedCoreBoundary630 r (m : Int) := by
    rw [← coreDeficit_eq_coefficient m r (by omega)]
    exact sevenCoreDeficit_boundary630 m r (by omega) hr
  have h0 := scaled_ofInt_eqv (hc 0 (by omega))
  have h1 := scaled_ofInt_eqv (hc 1 (by omega))
  have h2 := scaled_ofInt_eqv (hc 2 (by omega))
  have h3 := scaled_ofInt_eqv (hc 3 (by omega))
  have h4 := scaled_ofInt_eqv (hc 4 (by omega))
  have h5 := scaled_ofInt_eqv (hc 5 (by omega))
  unfold projectiveBoundaryBracketSix correctedCoreBoundaryScaledBracket
  refine Q'.eqv_trans _
    ((Q'.ofNat 630 * Q'.ofInt
          (sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m))) * x ^ 5 +
      ((Q'.ofNat 630 * Q'.ofInt
          (sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m - 1))) * x ^ 4 +
      ((Q'.ofNat 630 * Q'.ofInt
          (sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m - 2))) * x ^ 3 +
      ((Q'.ofNat 630 * Q'.ofInt
          (sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m - 3))) * x ^ 2 +
      ((Q'.ofNat 630 * Q'.ofInt
          (sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m - 4))) * x +
        Q'.ofNat 630 * Q'.ofInt
          (sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m - 5))))))) _
    (by bridge_integer_qeqv) ?_
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ (x ^ 5) h0)
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ (x ^ 4) h1)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ (x ^ 3) h2)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ (x ^ 2) h3)
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_right _ _ x h4) h5))))

/-- The actual unscaled projective boundary is nonnegative on the harmonic
ray. -/
theorem projectiveCoreBoundaryBracketSix_physical_nonnegative (t : Nat) :
    let m := 2 * t + 4
    (0 : Q') ≤ projectiveBoundaryBracketSix (sevenGapDegree m)
      (sevenCoreBernCoeff (sevenGapDegree m) m) (Q'.ofNat t) := by
  let m := 2 * t + 4
  let B := projectiveBoundaryBracketSix (sevenGapDegree m)
    (sevenCoreBernCoeff (sevenGapDegree m) m) (Q'.ofNat t)
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hs := projectiveCoreBoundaryBracketSix_scaled m (Q'.ofNat t) hm
  have hp := correctedCoreBoundaryScaledBracket_physical_nonnegative t
  have hscaled : (0 : Q') ≤ Q'.ofNat 630 * B :=
    Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv hs)
  have hmul : Q'.ofNat 630 * (0 : Q') ≤ Q'.ofNat 630 * B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 630)))
      hscaled
  exact Q'.le_of_mul_le_mul_left hmul (Q'.ofNat_succ_pos 629)

/-- Consumer splice: once the genuine deficit-six bulk is nonnegative, the
closed corrected boundary pays every exceptional coordinate and the entire
projective core row is nonnegative. -/
theorem sevenCore_projectiveDeficit_nonnegative_of_bulk (t : Nat)
    (hbulk : let m := 2 * t + 4
      let D := sevenGapDegree m
      ∀ r, 6 ≤ r → r ≤ D →
        (0 : Int) ≤ sevenCoreBernCoeff D m (D - r)) :
    let m := 2 * t + 4
    let D := sevenGapDegree m
    (0 : Q') ≤ projectiveDeficitEval D (sevenCoreBernCoeff D m)
      (Q'.ofNat t) := by
  let m := 2 * t + 4
  let D := sevenGapDegree m
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hD : 5 ≤ D := by
    have hs : 4 ≤ m * m := Nat.mul_le_mul hm hm
    have h8 : 8 ≤ 2 * (m * m) := Nat.mul_le_mul_left 2 hs
    have h9 : 9 ≤ 2 * (m * m) + 1 := by omega
    exact Nat.le_trans (by decide : 5 ≤ 9) (by
      simpa [D, sevenGapDegree, Nat.mul_assoc] using h9)
  have ht : (0 : Q') ≤ Q'.ofNat t := by
    rw [Q'.zero_le_iff_num_nonneg, Q'.ofNat_num_cast]
    exact Int.natCast_nonneg t
  have hb := projectiveCoreBoundaryBracketSix_physical_nonnegative t
  have hf := projectiveBoundarySix_eqv_factor D
    (sevenCoreBernCoeff D m) (Q'.ofNat t) hD
  have hprod : (0 : Q') ≤ (Q'.ofNat t) ^ (D - 5) *
      projectiveBoundaryBracketSix D (sevenCoreBernCoeff D m)
        (Q'.ofNat t) :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ht (D - 5)) hb
  have hboundary : (0 : Q') ≤ projectiveBoundarySix D
      (sevenCoreBernCoeff D m) (Q'.ofNat t) :=
    Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hf)
  exact projectiveDeficitEval_nonnegative_of_boundary_six_bulk D
    (sevenCoreBernCoeff D m) (Q'.ofNat t) hD ht hboundary
    (by simpa only [m, D] using hbulk)

#print axioms correctedCoreBoundary630
#print axioms sevenCoreDeficit_boundary630
#print axioms correctedCoreBoundaryScaledBracket
#print axioms correctedCoreBoundaryScaledInt
#print axioms correctedCoreBoundaryScaledInt_physical_factor
#print axioms correctedCoreBoundaryScaledInt_physical_nonnegative
#print axioms correctedCoreBoundaryScaledBracket_eqv_int
#print axioms correctedCoreBoundaryScaledBracket_physical_nonnegative
#print axioms projectiveBoundaryBracketSix
#print axioms projectiveBoundarySix_eqv_factor
#print axioms projectiveCoreBoundaryBracketSix_scaled
#print axioms projectiveCoreBoundaryBracketSix_physical_nonnegative
#print axioms sevenCore_projectiveDeficit_nonnegative_of_bulk

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryBridge
