/-
Staged odd square-root-band substitution for the cubic full endpoint.

The denominator relation is `D = 2m(m+1)+r`.  Powers of `D` are expanded
one at a time through an independent-power carrier, avoiding a monolithic
sixth-power normalization.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointEvenShift

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddSubstitution

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointRaw

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pIntPoly (x : PE) : List Int → PE
  | [] => pc 0
  | a :: as => padd (pc a) (pmul x (pIntPoly x as))

private def pOddRaw (D m : PE) : PE :=
  padd (pneg (pmul (pmul (pc 840) (padd m (pc 2))) (ppow D 6))) <|
  padd (pmul (pmul (pmul (pc 140) (padd m (pc 2)))
      (pIntPoly m [51, 131, 98])) (ppow D 5)) <|
  padd (pneg (pmul (pmul (pmul (pc 7) (padd m (pc 2)))
      (pIntPoly m [2925, 12337, 18514, 12108, 2976])) (ppow D 4))) <|
  padd (pmul (pmul (pmul (pc 21) (padd m (pc 2)))
      (pIntPoly m [1525, 8473, 17986, 18212, 8864, 1680])) (ppow D 3)) <|
  padd (pneg (pmul (pmul (pmul (pmul (pc 12) (padd m (pc 1)))
      (padd m (pc 2)))
      (pIntPoly m [2100, 12259, 26184, 25032, 10295, 1270])) (ppow D 2)))
    (padd (pmul (pmul (pmul (pmul (pc 120) (padd m (pc 1)))
        (padd m (pc 2)))
        (pIntPoly m [84, 601, 1608, 2016, 1177, 254])) D)
      (pneg (pmul (pmul (pmul (pc 4) (padd m (pc 1)))
        (padd m (pc 2)))
        (pIntPoly m [420, 3569, 11604, 17892, 13245, 3810]))))

private def pOddMid (m r : PE) : PE :=
  padd (pmul (ppow r 6) (pIntPoly m [-1680, -840])) <|
  padd (pmul (ppow r 5) (pIntPoly m [14280, 23660, 15540, 3640])) <|
  padd (pmul (ppow r 4)
      (pIntPoly m [-40950, -50393, 134645, 344890, 266980, 65968])) <|
  padd (pmul (ppow r 3)
      (pIntPoly m [64050, 60291, -368599, -540974, 564620,
        1606864, 1114064, 247744])) <|
  padd (pmul (ppow r 2)
      (pIntPoly m [-50400, 14484, 633906, 777084, -1026494,
        -1927296, 733124, 2953096, 1923264, 396032]))
    (padd (pmul r
      (pIntPoly m [20160, -27120, -299904, 157308, 2366588,
        3098284, -579964, -3344024, -980928, 1673696, 1301888,
        269696]))
      (pIntPoly m [-3360, 6728, 50340, -93044, -427440, 468724,
        3121412, 3878104, 506328, -2612400, -2074752, -371200,
        156352, 51968]))

private def pOddSubMid : PE := pOddMid (.var 0) (.var 1)

private def pBinomPow (A r : PE) : Nat → PE
  | 0 => pc 1
  | 1 => padd A r
  | 2 => padd (ppow A 2)
      (padd (pmul (pc 2) (pmul A r)) (ppow r 2))
  | 3 => padd (ppow A 3)
      (padd (pmul (pc 3) (pmul (ppow A 2) r))
        (padd (pmul (pc 3) (pmul A (ppow r 2))) (ppow r 3)))
  | 4 => padd (ppow A 4)
      (padd (pmul (pc 4) (pmul (ppow A 3) r))
        (padd (pmul (pc 6) (pmul (ppow A 2) (ppow r 2)))
          (padd (pmul (pc 4) (pmul A (ppow r 3))) (ppow r 4))))
  | 5 => padd (ppow A 5)
      (padd (pmul (pc 5) (pmul (ppow A 4) r))
        (padd (pmul (pc 10) (pmul (ppow A 3) (ppow r 2)))
          (padd (pmul (pc 10) (pmul (ppow A 2) (ppow r 3)))
            (padd (pmul (pc 5) (pmul A (ppow r 4))) (ppow r 5)))))
  | 6 => padd (ppow A 6)
      (padd (pmul (pc 6) (pmul (ppow A 5) r))
        (padd (pmul (pc 15) (pmul (ppow A 4) (ppow r 2)))
          (padd (pmul (pc 20) (pmul (ppow A 3) (ppow r 3)))
            (padd (pmul (pc 15) (pmul (ppow A 2) (ppow r 4)))
              (padd (pmul (pc 6) (pmul A (ppow r 5))) (ppow r 6))))))
  | _ => pc 0

private def pOddRawPowers (m : PE) (d : Nat → PE) : PE :=
  padd (pneg (pmul (pmul (pc 840) (padd m (pc 2))) (d 6))) <|
  padd (pmul (pmul (pmul (pc 140) (padd m (pc 2)))
      (pIntPoly m [51, 131, 98])) (d 5)) <|
  padd (pneg (pmul (pmul (pmul (pc 7) (padd m (pc 2)))
      (pIntPoly m [2925, 12337, 18514, 12108, 2976])) (d 4))) <|
  padd (pmul (pmul (pmul (pc 21) (padd m (pc 2)))
      (pIntPoly m [1525, 8473, 17986, 18212, 8864, 1680])) (d 3)) <|
  padd (pneg (pmul (pmul (pmul (pmul (pc 12) (padd m (pc 1)))
      (padd m (pc 2)))
      (pIntPoly m [2100, 12259, 26184, 25032, 10295, 1270])) (d 2)))
    (padd (pmul (pmul (pmul (pmul (pc 120) (padd m (pc 1)))
        (padd m (pc 2)))
        (pIntPoly m [84, 601, 1608, 2016, 1177, 254])) (d 1))
      (pneg (pmul (pmul (pmul (pc 4) (padd m (pc 1)))
        (padd m (pc 2)))
        (pIntPoly m [420, 3569, 11604, 17892, 13245, 3810]))))

private def pOddExpanded : PE :=
  let m : PE := .var 0
  let r : PE := .var 1
  let A := pmul (pc 2) (pmul m (padd m (pc 1)))
  pOddRawPowers m (pBinomPow A r)

private theorem pOddExpanded_normal :
    RingNormaliser.normalize pOddExpanded =
      RingNormaliser.normalize pOddSubMid := by decide

private def pPowL (j : Nat) : PE :=
  let m : PE := .var 0
  let r : PE := .var 1
  ppow (padd (pmul (pc 2) (pmul m (padd m (pc 1)))) r) j

private def pPowR (j : Nat) : PE :=
  let m : PE := .var 0
  let r : PE := .var 1
  pBinomPow (pmul (pc 2) (pmul m (padd m (pc 1)))) r j

private theorem pPow1_normal : RingNormaliser.normalize (pPowL 1) =
    RingNormaliser.normalize (pPowR 1) := by decide
private theorem pPow2_normal : RingNormaliser.normalize (pPowL 2) =
    RingNormaliser.normalize (pPowR 2) := by decide
private theorem pPow3_normal : RingNormaliser.normalize (pPowL 3) =
    RingNormaliser.normalize (pPowR 3) := by decide
private theorem pPow4_normal : RingNormaliser.normalize (pPowL 4) =
    RingNormaliser.normalize (pPowR 4) := by decide
private theorem pPow5_normal : RingNormaliser.normalize (pPowL 5) =
    RingNormaliser.normalize (pPowR 5) := by decide
private theorem pPow6_normal : RingNormaliser.normalize (pPowL 6) =
    RingNormaliser.normalize (pPowR 6) := by decide

private theorem oddRawFormula_eq_local (D m : Q') :
    thetaCubicOddRawFormula D m ≈
      RingNormaliser.eval (fun | 0 => D | _ => m)
        (pOddRaw (.var 0) (.var 1)) := by
  unfold thetaCubicOddRawFormula
  exact Q'.eqv_refl _

private def pOddPowerCarrier : PE :=
  pOddRawPowers (.var 0) (fun j => .var j)

private def actualPowerEnv (D m : Q') : Nat → Q'
  | 0 => m
  | 1 => D
  | 2 => RingNormaliser.qpow D 2
  | 3 => RingNormaliser.qpow D 3
  | 4 => RingNormaliser.qpow D 4
  | 5 => RingNormaliser.qpow D 5
  | 6 => RingNormaliser.qpow D 6
  | _ => 0

private def expandedPowerEnv (m r : Q') : Nat → Q'
  | 0 => m
  | j => RingNormaliser.eval (fun | 0 => m | _ => r) (pPowR j)

private theorem polyEval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const c => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb => exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb =>
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ iha) ?_
      exact Q'.mul_eqv_congr_left _ _ _ ihb
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

private theorem power_eq_expanded (j : Nat)
    (hnormal : RingNormaliser.normalize (pPowL j) =
      RingNormaliser.normalize (pPowR j)) (m r : Q') :
    RingNormaliser.qpow
        (Q'.ofInt 2 * (m * (m + Q'.ofInt 1)) + r) j ≈
      RingNormaliser.eval (fun | 0 => m | _ => r) (pPowR j) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    (pPowL j) (pPowR j) hnormal (fun | 0 => m | _ => r)
  simpa [pPowL, pc, padd, pmul, ppow, RingNormaliser.eval] using h

private theorem actualPowerEnv_eq_expanded (m r : Q') : ∀ i,
    actualPowerEnv
        (Q'.ofNat 2 * (m * (m + Q'.ofNat 1)) + r) m i ≈
      expandedPowerEnv m r i := by
  have hD : Q'.ofNat 2 * (m * (m + Q'.ofNat 1)) + r ≈
      Q'.ofInt 2 * (m * (m + Q'.ofInt 1)) + r := by
    exact Q'.add_eqv_congr_right _ _ r
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
        (Q'.mul_eqv_congr_left (Q'.ofInt 2) _ _
          (Q'.mul_eqv_congr_left m _ _
            (Q'.add_eqv_congr_left m _ _ (by decide)))))
  intro i
  rcases i with _ | i
  · exact Q'.eqv_refl m
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    refine Q'.eqv_trans _ _ _ hD ?_
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
      (power_eq_expanded 1 pPow1_normal m r)
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    exact Q'.eqv_trans _ _ _ (RingNormaliser.qpow_eqv_congr hD 2)
      (power_eq_expanded 2 pPow2_normal m r)
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    exact Q'.eqv_trans _ _ _ (RingNormaliser.qpow_eqv_congr hD 3)
      (power_eq_expanded 3 pPow3_normal m r)
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    exact Q'.eqv_trans _ _ _ (RingNormaliser.qpow_eqv_congr hD 4)
      (power_eq_expanded 4 pPow4_normal m r)
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    exact Q'.eqv_trans _ _ _ (RingNormaliser.qpow_eqv_congr hD 5)
      (power_eq_expanded 5 pPow5_normal m r)
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    exact Q'.eqv_trans _ _ _ (RingNormaliser.qpow_eqv_congr hD 6)
      (power_eq_expanded 6 pPow6_normal m r)
  · exact Q'.eqv_refl 0

private theorem oddRawLocal_eq_powerCarrier (D m : Q') :
    RingNormaliser.eval (fun | 0 => D | _ => m)
        (pOddRaw (.var 0) (.var 1)) ≈
      RingNormaliser.eval (actualPowerEnv D m) pOddPowerCarrier := by
  unfold pOddRaw pOddPowerCarrier pOddRawPowers actualPowerEnv
    pIntPoly pc padd pmul pneg ppow RingNormaliser.eval
  exact Q'.eqv_refl _

private theorem expandedCarrier_eq_expression (m r : Q') :
    RingNormaliser.eval (expandedPowerEnv m r) pOddPowerCarrier ≈
      RingNormaliser.eval (fun | 0 => m | _ => r) pOddExpanded := by
  unfold expandedPowerEnv pOddPowerCarrier pOddExpanded pOddRawPowers pPowR
  exact Q'.eqv_refl _

def thetaCubicOddCenteredPolynomial (m r : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => m | _ => r)
    (pOddMid (.var 0) (.var 1))

/-- Exact odd denominator substitution, before the Horner shift `m=M+5`. -/
theorem thetaCubicOddRaw_centered (m r : Q') :
    thetaCubicOddRawEndpoint
        (Q'.ofNat 2 * (m * (m + Q'.ofNat 1)) + r) m ≈
      thetaCubicOddCenteredPolynomial m r := by
  have hraw := thetaCubicOddRawEndpoint_eq_formula
    (Q'.ofNat 2 * (m * (m + Q'.ofNat 1)) + r) m
  have hlocalL := oddRawFormula_eq_local
    (Q'.ofNat 2 * (m * (m + Q'.ofNat 1)) + r) m
  have hcarrier := oddRawLocal_eq_powerCarrier
    (Q'.ofNat 2 * (m * (m + Q'.ofNat 1)) + r) m
  have hpowers := polyEval_eqv_congr pOddPowerCarrier
    (actualPowerEnv_eq_expanded m r)
  have hexpanded := expandedCarrier_eq_expression m r
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    pOddExpanded pOddSubMid pOddExpanded_normal (fun | 0 => m | _ => r)
  refine Q'.eqv_trans _ _ _ hraw ?_
  refine Q'.eqv_trans _ _ _ hlocalL ?_
  refine Q'.eqv_trans _ _ _ hcarrier ?_
  refine Q'.eqv_trans _ _ _ hpowers ?_
  refine Q'.eqv_trans _ _ _ hexpanded ?_
  refine Q'.eqv_trans _ _ _ hpoly ?_
  unfold thetaCubicOddCenteredPolynomial pOddSubMid
  exact Q'.eqv_refl _

#print axioms thetaCubicOddCenteredPolynomial
#print axioms thetaCubicOddRaw_centered

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointOddSubstitution
