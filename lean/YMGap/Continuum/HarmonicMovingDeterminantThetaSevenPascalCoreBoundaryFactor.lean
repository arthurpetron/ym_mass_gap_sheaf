/-
Positive factorisation of the corrected six-coordinate core boundary.

All displayed coefficients are exact integers.  The common scale is 630,
which clears the denominators in deficits zero through five.  The nonlinear
substitution `m=2t+4` is checked by the constructive reflective ring
normaliser; positivity then follows from the manifestly positive Horner
polynomial.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCore
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryFactor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr
private def pc (z : Int) : PE := .const z
private def pv : PE := .var 0
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def psub (a b : PE) : PE := padd a (pneg b)
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pNatPoly (x : PE) : List Nat → PE
  | [] => pc 0
  | a :: as => padd (pc (Int.ofNat a)) (pmul x (pNatPoly x as))

private def pCoreC0 (m : PE) : PE := pmul (pc (-2520)) m

private def pCoreC1 (m : PE) : PE :=
  pmul (pc 1260) <| pmul m <| pmul (padd m (pc 1))
    (psub (pmul (pc 2) m) (pc 5))

private def pCoreC2 (m : PE) : PE :=
  pmul (pc 105) <| pmul m <|
    psub (psub (pmul (pc 50) (ppow m 2)) (pmul (pc 75) m)) (pc 47)

private def pCoreC3 (m : PE) : PE :=
  pneg <| pmul (pc 210) <| pmul m <|
    padd (psub (pmul (pc 4) (ppow m 4))
      (pmul (pc 19) (ppow m 2)))
      (padd (pmul (pc 21) m) (pc 6))

private def pFiveFactor (m : PE) : PE :=
  pmul m <| pmul (psub m (pc 1)) <| pmul (padd m (pc 1)) <|
    pmul (psub (pmul (pc 2) m) (pc 1))
      (padd (pmul (pc 2) m) (pc 1))

private def pCoreC4 (m : PE) : PE :=
  pneg (pmul (pc 483) (pFiveFactor m))

private def pCoreC5 (m : PE) : PE :=
  pmul (pc 2) <| pmul (pFiveFactor m) <|
    psub (pmul (pc 52) (ppow m 2)) (pc 285)

private def pCoreBoundary (m t : PE) : PE :=
  padd (pmul (pCoreC0 m) (ppow t 5)) <|
  padd (pmul (pCoreC1 m) (ppow t 4)) <|
  padd (pmul (pCoreC2 m) (ppow t 3)) <|
  padd (pmul (pCoreC3 m) (ppow t 2))
    (padd (pmul (pCoreC4 m) t) (pCoreC5 m))

private def pPositive (t : PE) : PE :=
  pNatPoly t [1033830, 3269037, 4205732, 2841717, 1085894, 232296, 23264]

private def pSubstitutedBoundary : PE :=
  pCoreBoundary (padd (pmul (pc 2) pv) (pc 4)) pv

private def pFactoredBoundary : PE :=
  pmul (pc 2) (pmul (padd pv (pc 2)) (pPositive pv))

set_option maxRecDepth 100000 in
private theorem pBoundary_normal :
    RingNormaliser.normalize pSubstitutedBoundary =
      RingNormaliser.normalize pFactoredBoundary := by decide

/-- The exact scaled coefficient formula before the physical substitution. -/
def coreBoundaryScaledFormula (m t : Q') : Q' :=
  RingNormaliser.eval (fun | 0 => t | _ => m)
    (pCoreBoundary (.var 1) (.var 0))

/-- Manifestly positive degree-six factor in the physical variable `t`. -/
def coreBoundaryPositivePoly (t : Q') : Q' :=
  RingNormaliser.eval (fun _ => t) (pPositive (.var 0))

/-- Exact kernel-checked physical factorisation:
`630 B(2t+4,t) = 2(t+2)P(t)`. -/
theorem coreBoundaryScaledFormula_factor (t : Q') :
    coreBoundaryScaledFormula (Q'.ofInt 2 * t + Q'.ofInt 4) t ≈
      Q'.ofInt 2 * ((t + Q'.ofInt 2) * coreBoundaryPositivePoly t) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    pSubstitutedBoundary pFactoredBoundary pBoundary_normal (fun _ => t)
  simpa [coreBoundaryScaledFormula, coreBoundaryPositivePoly,
    pSubstitutedBoundary, pFactoredBoundary, pCoreBoundary, pCoreC0,
    pCoreC1, pCoreC2, pCoreC3, pCoreC4, pCoreC5, pFiveFactor,
    pPositive, pNatPoly, pc, pv, padd, pmul, pneg, psub, ppow,
    RingNormaliser.eval] using h

private theorem ofInt_nonnegative {z : Int} (hz : 0 ≤ z) :
    (0 : Q') ≤ Q'.ofInt z := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact hz

private theorem pNatPoly_nonnegative (t : Q') (ht : (0 : Q') ≤ t) :
    ∀ cs : List Nat,
      (0 : Q') ≤ RingNormaliser.eval (fun _ => t) (pNatPoly (.var 0) cs)
  | [] => Q'.le_refl' 0
  | a :: as => by
      exact Q'.zero_le_add _ _
        (ofInt_nonnegative (Int.natCast_nonneg a))
        (Q'.mul_nonneg _ _ ht (pNatPoly_nonnegative t ht as))

/-- The positive factor is nonnegative for every nonnegative `t`. -/
theorem coreBoundaryPositivePoly_nonnegative {t : Q'} (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ coreBoundaryPositivePoly t := by
  unfold coreBoundaryPositivePoly pPositive
  exact pNatPoly_nonnegative t ht _

/-- The corrected six-coordinate scaled boundary is nonnegative on the full
physical ray `t ≥ 0`. -/
theorem coreBoundaryScaledFormula_physical_nonnegative
    {t : Q'} (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ coreBoundaryScaledFormula
      (Q'.ofInt 2 * t + Q'.ofInt 4) t := by
  have h2 : (0 : Q') ≤ Q'.ofInt 2 := ofInt_nonnegative (by decide)
  have ht2 : (0 : Q') ≤ t + Q'.ofInt 2 :=
    Q'.zero_le_add _ _ ht (ofInt_nonnegative (by decide))
  have hp := coreBoundaryPositivePoly_nonnegative ht
  have hprod : (0 : Q') ≤
      Q'.ofInt 2 * ((t + Q'.ofInt 2) * coreBoundaryPositivePoly t) :=
    Q'.mul_nonneg _ _ h2 (Q'.mul_nonneg _ _ ht2 hp)
  exact Q'.le_trans' _ _ _ hprod
    (Q'.ge_of_eqv (coreBoundaryScaledFormula_factor t))

#print axioms coreBoundaryScaledFormula
#print axioms coreBoundaryPositivePoly
#print axioms coreBoundaryScaledFormula_factor
#print axioms coreBoundaryPositivePoly_nonnegative
#print axioms coreBoundaryScaledFormula_physical_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCoreBoundaryFactor
