/-
Staged square-root-band substitution for the cubic full endpoint.

The raw endpoint keeps `D` independent.  Here the even relation
`D=2m^2+r` is imposed while the positive certificate is parameterized by
`M=m-5`.  This avoids expanding the four-term expression
`2(M+5)^2+r` directly to the sixth power.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointRaw

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointSubstitution

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
private def psub (a b : PE) : PE := padd a (pneg b)
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pIntPoly (x : PE) : List Int → PE
  | [] => pc 0
  | a :: as => padd (pc a) (pmul x (pIntPoly x as))

private def pNatPoly (x : PE) : List Nat → PE
  | [] => pc 0
  | a :: as => padd (pc (Int.ofNat a)) (pmul x (pNatPoly x as))

private def pEvenRaw (D m : PE) : PE :=
  padd (pneg (pmul (pmul (pc 840) (padd m (pc 1))) (ppow D 6))) <|
  padd (pmul (pmul (pmul (pc 140) (padd m (pc 1)))
      (pIntPoly m [12, 61, 98])) (ppow D 5)) <|
  padd (pneg (pmul (pmul (pmul (pc 7) (padd m (pc 1)))
      (pIntPoly m [120, 2159, 6526, 7404, 2976])) (ppow D 4))) <|
  padd (pmul (pmul (pmul (pmul (pc 21) m) (padd m (pc 1)))
      (pIntPoly m [351, 2774, 6196, 5424, 1680])) (ppow D 3)) <|
  padd (pneg (pmul (pmul (pmul (pmul (pc 12) m) (padd m (pc 1)))
      (pIntPoly m [18, 1907, 9048, 14262, 8355, 1270])) (ppow D 2)))
    (padd (pmul (pmul (pmul (pmul (pc 120) m) (padd m (pc 1)))
        (pIntPoly m [-2, 9, 264, 786, 789, 254])) D)
      (pneg (pmul (pmul (pmul (pc 4) m) (padd m (pc 1)))
        (pIntPoly m [-2, -103, 348, 4062, 7425, 3810]))))

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

private def pEvenMid (m r : PE) : PE :=
  padd (pmul (ppow r 6) (pIntPoly m [-840, -840])) <|
  padd (pmul (ppow r 5) (pIntPoly m [1680, 10220, 12180, 3640])) <|
  padd (pmul (ppow r 4)
      (pIntPoly m [-840, -15953, -43995, 4690, 99540, 65968])) <|
  padd (pmul (ppow r 3)
      (pIntPoly m [0, 7371, 58905, 60746, -175140, -222096,
        210000, 247744])) <|
  padd (pmul (ppow r 2)
      (pIntPoly m [0, -216, -23100, -87234, 93870, 475944, 23940,
        -642776, 47040, 396032]))
    (padd (pmul r
      (pIntPoly m [0, -240, 840, 31896, 33600, -248388, -233100,
        694808, 655200, -573472, -282240, 269696]))
      (pIntPoly m [0, 8, 420, -1460, -15960, 18708, 114660,
        -104112, -357000, 227056, 571200, -100608, -221760, 51968]))

private def pEvenSubMid : PE :=
  let m : PE := .var 0
  let r : PE := .var 1
  pEvenMid m r

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

private def pEvenRawPowers (m : PE) (d : Nat → PE) : PE :=
  padd (pneg (pmul (pmul (pc 840) (padd m (pc 1))) (d 6))) <|
  padd (pmul (pmul (pmul (pc 140) (padd m (pc 1)))
      (pIntPoly m [12, 61, 98])) (d 5)) <|
  padd (pneg (pmul (pmul (pmul (pc 7) (padd m (pc 1)))
      (pIntPoly m [120, 2159, 6526, 7404, 2976])) (d 4))) <|
  padd (pmul (pmul (pmul (pmul (pc 21) m) (padd m (pc 1)))
      (pIntPoly m [351, 2774, 6196, 5424, 1680])) (d 3)) <|
  padd (pneg (pmul (pmul (pmul (pmul (pc 12) m) (padd m (pc 1)))
      (pIntPoly m [18, 1907, 9048, 14262, 8355, 1270])) (d 2)))
    (padd (pmul (pmul (pmul (pmul (pc 120) m) (padd m (pc 1)))
        (pIntPoly m [-2, 9, 264, 786, 789, 254])) (d 1))
      (pneg (pmul (pmul (pmul (pc 4) m) (padd m (pc 1)))
        (pIntPoly m [-2, -103, 348, 4062, 7425, 3810]))))

private def pEvenExpanded : PE :=
  let m : PE := .var 0
  let r : PE := .var 1
  let A := pmul (pc 2) (pmul m m)
  pEvenRawPowers m (pBinomPow A r)

private theorem pEvenExpanded_normal :
    RingNormaliser.normalize pEvenExpanded =
      RingNormaliser.normalize pEvenSubMid := by decide

private def pPowL (j : Nat) : PE :=
  let m : PE := .var 0
  let r : PE := .var 1
  ppow (padd (pmul (pc 2) (pmul m m)) r) j

private def pPowR (j : Nat) : PE :=
  let m : PE := .var 0
  let r : PE := .var 1
  pBinomPow (pmul (pc 2) (pmul m m)) r j

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

private theorem evenRawFormula_eq_local (D m : Q') :
    thetaCubicEvenRawFormula D m ≈
      RingNormaliser.eval (fun | 0 => D | _ => m)
        (pEvenRaw (.var 0) (.var 1)) := by
  unfold thetaCubicEvenRawFormula
  exact Q'.eqv_refl _

private def pEvenPowerCarrier : PE :=
  pEvenRawPowers (.var 0) (fun j => .var j)

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
    RingNormaliser.qpow (Q'.ofInt 2 * (m * m) + r) j ≈
      RingNormaliser.eval (fun | 0 => m | _ => r) (pPowR j) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    (pPowL j) (pPowR j) hnormal (fun | 0 => m | _ => r)
  simpa [pPowL, pc, padd, pmul, ppow, RingNormaliser.eval] using h

private theorem actualPowerEnv_eq_expanded (m r : Q') : ∀ i,
    actualPowerEnv (Q'.ofNat 2 * (m * m) + r) m i ≈
      expandedPowerEnv m r i := by
  have hD : Q'.ofNat 2 * (m * m) + r ≈
      Q'.ofInt 2 * (m * m) + r :=
    Q'.add_eqv_congr_right _ _ r
      (Q'.mul_eqv_congr_right _ _ (m * m) (by decide))
  intro i
  rcases i with _ | i
  · exact Q'.eqv_refl m
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    refine Q'.eqv_trans _ _ _ hD ?_
    have h := power_eq_expanded 1 pPow1_normal m r
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)) h
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    refine Q'.eqv_trans _ _ _
      (RingNormaliser.qpow_eqv_congr hD 2) ?_
    exact power_eq_expanded 2 pPow2_normal m r
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    refine Q'.eqv_trans _ _ _
      (RingNormaliser.qpow_eqv_congr hD 3) ?_
    exact power_eq_expanded 3 pPow3_normal m r
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    refine Q'.eqv_trans _ _ _
      (RingNormaliser.qpow_eqv_congr hD 4) ?_
    exact power_eq_expanded 4 pPow4_normal m r
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    refine Q'.eqv_trans _ _ _
      (RingNormaliser.qpow_eqv_congr hD 5) ?_
    exact power_eq_expanded 5 pPow5_normal m r
  rcases i with _ | i
  · dsimp only [actualPowerEnv, expandedPowerEnv]
    refine Q'.eqv_trans _ _ _
      (RingNormaliser.qpow_eqv_congr hD 6) ?_
    exact power_eq_expanded 6 pPow6_normal m r
  · exact Q'.eqv_refl 0

private theorem evenRawLocal_eq_powerCarrier (D m : Q') :
    RingNormaliser.eval (fun | 0 => D | _ => m)
        (pEvenRaw (.var 0) (.var 1)) ≈
      RingNormaliser.eval (actualPowerEnv D m) pEvenPowerCarrier := by
  unfold pEvenRaw pEvenPowerCarrier pEvenRawPowers actualPowerEnv
    pIntPoly pc padd pmul pneg ppow RingNormaliser.eval
  exact Q'.eqv_refl _

private theorem expandedCarrier_eq_expression (m r : Q') :
    RingNormaliser.eval (expandedPowerEnv m r) pEvenPowerCarrier ≈
      RingNormaliser.eval (fun | 0 => m | _ => r) pEvenExpanded := by
  unfold expandedPowerEnv pEvenPowerCarrier pEvenExpanded pEvenRawPowers
    pPowR
  exact Q'.eqv_refl _

def thetaCubicEvenCenteredPolynomial (m r : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => m | _ => r)
    (pEvenMid (.var 0) (.var 1))

/-- Exact even denominator substitution, before the final Horner shift
`m=M+5`. -/
theorem thetaCubicEvenRaw_centered (m r : Q') :
    thetaCubicEvenRawEndpoint (Q'.ofNat 2 * (m * m) + r) m ≈
      thetaCubicEvenCenteredPolynomial m r := by
  have hraw := thetaCubicEvenRawEndpoint_eq_formula
    (Q'.ofNat 2 * (m * m) + r) m
  have hlocalL := evenRawFormula_eq_local
    (Q'.ofNat 2 * (m * m) + r) m
  have hcarrier := evenRawLocal_eq_powerCarrier
    (Q'.ofNat 2 * (m * m) + r) m
  have hpowers := polyEval_eqv_congr pEvenPowerCarrier
    (actualPowerEnv_eq_expanded m r)
  have hexpanded := expandedCarrier_eq_expression m r
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    pEvenExpanded pEvenSubMid pEvenExpanded_normal (fun | 0 => m | _ => r)
  refine Q'.eqv_trans _ _ _ hraw ?_
  refine Q'.eqv_trans _ _ _ hlocalL ?_
  refine Q'.eqv_trans _ _ _ hcarrier ?_
  refine Q'.eqv_trans _ _ _ hpowers ?_
  refine Q'.eqv_trans _ _ _ hexpanded ?_
  refine Q'.eqv_trans _ _ _ hpoly ?_
  unfold thetaCubicEvenCenteredPolynomial pEvenSubMid
  exact Q'.eqv_refl _

#print axioms thetaCubicEvenCenteredPolynomial
#print axioms thetaCubicEvenRaw_centered

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointSubstitution
