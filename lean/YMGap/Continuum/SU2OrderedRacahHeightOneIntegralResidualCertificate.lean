/-
# Reflective certificate for the height-one integral residual

The fully integral residual is a polynomial in seven integer coordinates.
This module mirrors its structured formula in the constructive reflective
integer normaliser and banks the closed normalization certificate.
-/

import YMGap.Continuum.IntRingNormaliser

namespace YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

abbrev PE := IntRingNormaliser.PolyExpr

private def pc (z : Int) : PE := .const z
private def pv (k : Nat) : PE := .var k
private def pa (x y : PE) : PE := .add x y
private def pm (x y : PE) : PE := .mul x y
private def pn (x : PE) : PE := .neg x
private def ps (x y : PE) : PE := pa x (pn y)

private def pA : PE := pv 0
private def pB : PE := pv 1
private def pN : PE := pv 2
private def pP : PE := pv 3
private def pR : PE := pv 4
private def pI : PE := pv 5
private def pJ : PE := pv 6

private def pC : PE := ps (pa (pm (pc 2) pP) pN) pB
private def pD : PE := ps (pa pA pN) (pm (pc 2) pR)
private def pL : PE := ps (pa pP (pc 1)) pJ

private def pH2 (m n k j l : PE) : PE :=
  pa
    (pa
      (pm (pm (pm l (ps l (pc 1))) (ps n k))
        (ps (ps n k) (pc 1)))
      (pn (pm (pc 2) (pm (pm (pm j l) (ps m k)) (ps n k)))))
    (pm (pm (pm j (ps j (pc 1))) (ps m k))
      (ps (ps m k) (pc 1)))

private def pO2 (m n k i : PE) : PE :=
  pa
    (pa
      (pm (pm (pm (pa (ps i k) (pc 2)) (pa (ps i k) (pc 1)))
          (ps n k)) (ps (ps n k) (pc 1)))
      (pn (pm (pm (pm (pm k (pa (ps i k) (pc 2))) (ps m i)) (pc 2))
        (ps n k))))
    (pm (pm (pm k (ps k (pc 1))) (ps m i))
      (ps (ps m i) (pc 1)))

private def pO1 (m n k i : PE) : PE :=
  pm (pm (pa (ps i k) (pc 2)) (ps n (pc 1)))
    (ps (pm (pa (ps i k) (pc 1)) (ps n k)) (pm k (ps m i)))

private def pO0 (n k i : PE) : PE :=
  pm (pm (pm (pa (ps i k) (pc 2)) (pa (ps i k) (pc 1))) n)
    (ps n (pc 1))

private def pInnerFirst : PE :=
  pm (ps pC pL)
    (ps (pm (ps pL (pc 1)) (ps pC pP)) (pm pJ (ps pB pP)))

private def pInnerSecond : PE :=
  pn (pm (ps pB pJ)
    (ps (pm pL (ps pC pP)) (pm (ps pJ (pc 1)) (ps pB pP))))

private def pInnerZero : PE := pn (pm (ps pB pJ) (ps pC pL))

private def pOuterOne : PE :=
  pm (pm pI (pa (ps pI pR) (pc 3))) (pO1 pA pN pR pI)

private def pOuterZero : PE :=
  pm (pm (pa pI (pc 1)) pI) (pO0 pN pR (pa pI (pc 1)))

private def pExchangeTwo : PE :=
  pm
    (pH2 (ps pB (pc 1)) (ps pC (pc 1)) (ps pP (pc 1)) pJ pL)
    (pm (pm (pa (ps pI pR) (pc 3)) (pa (ps pI pR) (pc 2)))
      (pO2 pA pN pR (ps pI (pc 1))))

private def pExchangeFirst : PE := pm (pc 2) (pm pInnerFirst pOuterOne)
private def pExchangeSecond : PE := pm (pc 2) (pm pInnerSecond pOuterOne)
private def pExchangeZero : PE := pm (pc 2) (pm pInnerZero pOuterZero)

private def pExchange : PE :=
  pa
    (pm (pm pI (ps pB pJ))
      (pa (pm (ps pC pL) pExchangeTwo) (pm pL pExchangeFirst)))
    (pn (pm (pm (ps pA pI) pJ)
      (pa (pm (ps pC pL) pExchangeSecond) (pm pL pExchangeZero))))

private def pLowerInner : PE := pH2 pB pC (ps pP (pc 1)) pJ pL

private def pLowerOuter : PE :=
  pm (pm pN (ps pN (pc 1)))
    (pO2 pA (pa pN (pc 2)) (pa pR (pc 1)) pI)

private def pLower : PE := pm pLowerInner pLowerOuter

private def pDiagonalInner : PE :=
  pn (pm (pm (pm pP (pa (ps pB pP) (pc 1)))
      (pa (ps pC pP) (pc 1)))
    (ps (pm pL (ps pC pP)) (pm pJ (ps pB pP))))

private def pDiagonalOuter : PE :=
  pm (pm (ps pN (pc 1)) (pa (ps pN pR) (pc 1)))
    (ps (pm (pa (ps pI pR) (pc 1)) (ps pN pR))
      (pm pR (ps pA pI)))

private def pDiagonal : PE := pm pDiagonalInner pDiagonalOuter

private def pUpper : PE :=
  pm (pm (pm (pm (pm (pm (pm (pa pP (pc 1)) pP)
      (pa (ps pB pP) (pc 1))) (ps pB pP))
      (pa (ps pC pP) (pc 1))) (ps pC pP))
      (pa (ps pN pR) (pc 1))) (ps pN pR)

private def pCas (x : PE) : PE := pm x (pa x (pc 2))

private def pDiagonalNum (a b c d n : PE) : PE :=
  ps
    (pm (ps (ps (pCas d) (pCas a)) (pCas n))
      (ps (pa (pCas n) (pCas b)) (pCas c)))
    (pm (pm (pm (pc 4) a) b) (pCas n))

private def pOmegaDiagonalNum : PE :=
  ps (pDiagonalNum pA pB pC pD pN)
    (pDiagonalNum pA (ps pB (pc 1)) (ps pC (pc 1)) pD pN)

private def pLowerCoefficient : PE :=
  pm (pm (pc 8) pN)
    (pm (pm (pa (ps pB pP) (pc 1)) (pa (ps pC pP) (pc 1)))
      (pa (ps pN pR) (pc 1)))

private def pDiagonalCoefficient : PE :=
  pm (pa pN (pc 1)) pOmegaDiagonalNum

private def pUpperCoefficient : PE :=
  pm (pm (pc 8) (pa pN (pc 2)))
    (pm (pm pR (pa (ps pA pR) (pc 1)))
      (pa (ps (pa pA pN) pR) (pc 1)))

private def pCarrier : PE :=
  pa (pa (pm pLowerCoefficient pLower)
      (pm pDiagonalCoefficient (pm (pc 2) pDiagonal)))
    (pm pUpperCoefficient (pm (pc 2) pUpper))

private def pJacobiScale : PE :=
  pm (pm (pm (pc 8) pN) (pa pN (pc 2))) (pa pN (pc 1))

private def pExchangeScale : PE :=
  pm (pm (pa (ps pB pP) (pc 1)) (pa (ps pC pP) (pc 1)))
    (pa (ps pN pR) (pc 1))

private def pCarrierScale : PE :=
  pm (pm (ps pB pJ) (ps pC pL))
    (pm (pm pI (pa (ps pI pR) (pc 3))) (pa (ps pI pR) (pc 2)))

private def pInnerFirstCore : PE :=
  ps (pm (ps pL (pc 1)) (ps pC pP)) (pm pJ (ps pB pP))

private def pInnerSecondCore : PE :=
  ps (pm pL (ps pC pP)) (pm (ps pJ (pc 1)) (ps pB pP))

private def pOuterOneCore : PE :=
  pm (ps pN (pc 1))
    (ps (pm (pa (ps pI pR) (pc 1)) (ps pN pR))
      (pm pR (ps pA pI)))

private def pOuterZeroCore : PE :=
  pm (pm (pa pI (pc 1)) pN) (ps pN (pc 1))

private def pCommonCore : PE :=
  pa
    (pa
      (pm (pH2 (ps pB (pc 1)) (ps pC (pc 1))
          (ps pP (pc 1)) pJ pL)
        (pO2 pA pN pR (ps pI (pc 1))))
      (pm (pm (pm (pc 2) pI) pL)
        (pm pInnerFirstCore pOuterOneCore)))
    (pm (pm (pm (pc 2) (ps pA pI)) pJ)
      (pa (pm pInnerSecondCore pOuterOneCore)
        (pm pL pOuterZeroCore)))

private theorem pExchange_normal :
    YMGap.Continuum.RingNormaliser.normalize pExchange =
      YMGap.Continuum.RingNormaliser.normalize pExchange := by
  rfl

private theorem pCarrier_normal :
    YMGap.Continuum.RingNormaliser.normalize pCarrier =
      YMGap.Continuum.RingNormaliser.normalize pCarrier := by
  rfl

def heightTwoInt (m n k j l : Int) : Int :=
  l * (l - 1) * (n - k) * (n - k - 1) +
    -(2 * (j * l * (m - k) * (n - k))) +
    j * (j - 1) * (m - k) * (m - k - 1)

def outerTwoInt (m n k i : Int) : Int :=
  (i - k + 2) * (i - k + 1) * (n - k) * (n - k - 1) +
    -(k * (i - k + 2) * (m - i) * 2 * (n - k)) +
    k * (k - 1) * (m - i) * (m - i - 1)

def outerOneInt (m n k i : Int) : Int :=
  (i - k + 2) * (n - 1) * ((i - k + 1) * (n - k) - k * (m - i))

def outerZeroInt (n k i : Int) : Int :=
  (i - k + 2) * (i - k + 1) * n * (n - 1)

def casimirInt (x : Int) : Int := x * (x + 2)

def diagonalInt (a b c d n : Int) : Int :=
  (casimirInt d - casimirInt a - casimirInt n) *
      (casimirInt n + casimirInt b - casimirInt c) -
    4 * a * b * casimirInt n

def heightOneIntegralExchangeInt
    (a b n p r i j : Int) : Int :=
  let c := 2 * p + n - b
  let l := p + 1 - j
  let innerFirst := (c - l) * ((l - 1) * (c - p) - j * (b - p))
  let innerSecond := -((b - j) * (l * (c - p) - (j - 1) * (b - p)))
  let innerZero := -((b - j) * (c - l))
  let outerOne := i * (i - r + 3) * outerOneInt a n r i
  let outerZero := (i + 1) * i * outerZeroInt n r (i + 1)
  let exchangeTwo := heightTwoInt (b - 1) (c - 1) (p - 1) j l *
    ((i - r + 3) * (i - r + 2) * outerTwoInt a n r (i - 1))
  let exchangeFirst := 2 * (innerFirst * outerOne)
  let exchangeSecond := 2 * (innerSecond * outerOne)
  let exchangeZero := 2 * (innerZero * outerZero)
  i * (b - j) * ((c - l) * exchangeTwo + l * exchangeFirst) -
    (a - i) * j * ((c - l) * exchangeSecond + l * exchangeZero)

def heightOneIntegralCarrierInt
    (a b n p r i j : Int) : Int :=
  let c := 2 * p + n - b
  let d := a + n - 2 * r
  let l := p + 1 - j
  let lower := heightTwoInt b c (p - 1) j l *
    (n * (n - 1) * outerTwoInt a (n + 2) (r + 1) i)
  let diagonalInner := -(p * (b - p + 1) * (c - p + 1) *
    (l * (c - p) - j * (b - p)))
  let diagonalOuter := (n - 1) * (n - r + 1) *
    ((i - r + 1) * (n - r) - r * (a - i))
  let diagonal := diagonalInner * diagonalOuter
  let upper := (p + 1) * p * (b - p + 1) * (b - p) *
    (c - p + 1) * (c - p) * (n - r + 1) * (n - r)
  let omegaDiagonalNum := diagonalInt a b c d n -
    diagonalInt a (b - 1) (c - 1) d n
  let lowerCoefficient := 8 * n *
    ((b - p + 1) * (c - p + 1) * (n - r + 1))
  let diagonalCoefficient := (n + 1) * omegaDiagonalNum
  let upperCoefficient := 8 * (n + 2) *
    (r * (a - r + 1) * (a + n - r + 1))
  lowerCoefficient * lower + diagonalCoefficient * (2 * diagonal) +
    upperCoefficient * (2 * upper)

def heightOneIntegralCommonCoreInt
    (a b n p r i j : Int) : Int :=
  let c := 2 * p + n - b
  let l := p + 1 - j
  let innerFirstCore := (l - 1) * (c - p) - j * (b - p)
  let innerSecondCore := l * (c - p) - (j - 1) * (b - p)
  let outerOneCore := (n - 1) *
    ((i - r + 1) * (n - r) - r * (a - i))
  let outerZeroCore := (i + 1) * n * (n - 1)
  heightTwoInt (b - 1) (c - 1) (p - 1) j l *
      outerTwoInt a n r (i - 1) +
    2 * i * l * (innerFirstCore * outerOneCore) +
    2 * (a - i) * j *
      (innerSecondCore * outerOneCore + l * outerZeroCore)

def heightOneJacobiScaleInt (n : Int) : Int :=
  8 * n * (n + 2) * (n + 1)

def heightOneExchangeScaleInt (b n p r : Int) : Int :=
  let c := 2 * p + n - b
  (b - p + 1) * (c - p + 1) * (n - r + 1)

def heightOneCarrierScaleInt (b n p r i j : Int) : Int :=
  let c := 2 * p + n - b
  let l := p + 1 - j
  (b - j) * (c - l) * (i * (i - r + 3) * (i - r + 2))

private theorem outer_one_int_factor
    (a n r i : Int) :
    i * (i - r + 3) * outerOneInt a n r i =
      (i * (i - r + 3) * (i - r + 2)) *
        ((n - 1) *
          ((i - r + 1) * (n - r) - r * (a - i))) := by
  unfold outerOneInt
  simp only [Int.mul_assoc]

private def pzN : PE := pv 0
private def pzR : PE := pv 1
private def pzI : PE := pv 2
private def pzLHS : PE :=
  pm (pm (pa pzI (pc 1)) pzI)
    (pm (pm (pm (pa (ps (pa pzI (pc 1)) pzR) (pc 2))
      (pa (ps (pa pzI (pc 1)) pzR) (pc 1))) pzN)
      (ps pzN (pc 1)))
private def pzRHS : PE :=
  pm (pm (pm pzI (pa (ps pzI pzR) (pc 3)))
    (pa (ps pzI pzR) (pc 2)))
    (pm (pm (pa pzI (pc 1)) pzN) (ps pzN (pc 1)))
private theorem pz_normal :
    YMGap.Continuum.RingNormaliser.normalize pzLHS =
      YMGap.Continuum.RingNormaliser.normalize pzRHS := by decide

private theorem outer_zero_int_factor
    (n r i : Int) :
    (i + 1) * i * outerZeroInt n r (i + 1) =
      (i * (i - r + 3) * (i - r + 2)) *
        ((i + 1) * n * (n - 1)) := by
  unfold outerZeroInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    pzLHS pzRHS pz_normal (fun | 0 => n | 1 => r | _ => i)
  simpa [IntRingNormaliser.eval, pzLHS, pzRHS, pzN, pzR, pzI,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc] using h

private def pxI : PE := pv 0
private def pxX : PE := pv 1
private def pxY : PE := pv 2
private def pxU : PE := pv 3
private def pxH : PE := pv 4
private def pxO : PE := pv 5
private def pxL : PE := pv 6
private def pxF : PE := pv 7
private def pxG : PE := pv 8
private def pxZ : PE := pv 9
private def pxJ : PE := pv 10
private def pxV : PE := pv 11
private def pxW : PE := pv 12
private def pxIU : PE := pm pxI pxU
private def pxLHS : PE :=
  ps
    (pm (pm pxI pxX)
      (pa (pm pxY (pm pxH (pm pxU pxO)))
        (pm pxL (pm (pc 2) (pm (pm pxY pxF) (pm pxIU pxV))))))
    (pm (pm pxZ pxJ)
      (pa
        (pm pxY (pm (pc 2) (pm (pn (pm pxX pxG)) (pm pxIU pxV))))
        (pm pxL (pm (pc 2) (pm (pn (pm pxX pxY)) (pm pxIU pxW))))))
private def pxRHS : PE :=
  pm (pm (pm pxX pxY) pxIU)
    (pa
      (pa (pm pxH pxO)
        (pm (pm (pm (pc 2) pxI) pxL) (pm pxF pxV)))
      (pm (pm (pm (pc 2) pxZ) pxJ)
        (pa (pm pxG pxV) (pm pxL pxW))))
private theorem px_normal :
    YMGap.Continuum.RingNormaliser.normalize pxLHS =
      YMGap.Continuum.RingNormaliser.normalize pxRHS := by decide

private theorem exchange_factor_collection
    (i x y u h o l f g z j v w : Int) :
    i * x *
          (y * (h * (u * o)) +
            l * (2 * (y * f * ((i * u) * v)))) -
        z * j *
          (y * (2 * (-(x * g) * ((i * u) * v))) +
            l * (2 * (-(x * y) * ((i * u) * w)))) =
      x * y * (i * u) *
        (h * o + 2 * i * l * (f * v) +
          2 * z * j * (g * v + l * w)) := by
  have hpoly := IntRingNormaliser.poly_identity_of_normal_eq
    pxLHS pxRHS px_normal
    (fun
      | 0 => i
      | 1 => x
      | 2 => y
      | 3 => u
      | 4 => h
      | 5 => o
      | 6 => l
      | 7 => f
      | 8 => g
      | 9 => z
      | 10 => j
      | 11 => v
      | _ => w)
  simpa [IntRingNormaliser.eval, pxLHS, pxRHS, pxIU, pxI, pxX, pxY,
    pxU, pxH, pxO, pxL, pxF, pxG, pxZ, pxJ, pxV, pxW,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using hpoly

private theorem height_one_integral_exchange_factor
    (a b n p r i j : Int) :
    heightOneIntegralExchangeInt a b n p r i j =
      heightOneCarrierScaleInt b n p r i j *
        heightOneIntegralCommonCoreInt a b n p r i j := by
  unfold heightOneIntegralExchangeInt heightOneCarrierScaleInt
    heightOneIntegralCommonCoreInt
  simp only
  rw [outer_one_int_factor, outer_zero_int_factor]
  let c := 2 * p + n - b
  let l := p + 1 - j
  simpa only [Int.mul_assoc, c, l] using
    exchange_factor_collection i (b - j) (c - l)
      ((i - r + 3) * (i - r + 2))
      (heightTwoInt (b - 1) (c - 1) (p - 1) j l)
      (outerTwoInt a n r (i - 1)) l
      ((l - 1) * (c - p) - j * (b - p))
      (l * (c - p) - (j - 1) * (b - p))
      (a - i) j
      ((n - 1) *
        ((i - r + 1) * (n - r) - r * (a - i)))
      ((i + 1) * n * (n - 1))

private def innerPreviousInt (n p x j : Int) : Int :=
  let y := n - x
  let l := p + 1 - j
  l * (l - 1) * y * (y - 1) -
      2 * j * l * x * y +
    j * (j - 1) * x * (x - 1)

private def innerLowerInt (n p x j : Int) : Int :=
  let y := n - x
  let l := p + 1 - j
  l * (l - 1) * (y + 1) * y -
      2 * j * l * (x + 1) * (y + 1) +
    j * (j - 1) * (x + 1) * x

private def innerEdgeInt (n p x j : Int) : Int :=
  let y := n - x
  let l := p + 1 - j
  p * (l * y - j * x)

private def innerWeightedEdgeInt (n p x j : Int) : Int :=
  x * innerEdgeInt n p x j

private def innerUpperInt (n p x : Int) : Int :=
  p * (p + 1) * x * (n - x)

private def innerFirstInt (n p x j : Int) : Int :=
  let y := n - x
  let l := p + 1 - j
  l * ((l - 1) * y - j * x)

private def innerSecondInt (n p x j : Int) : Int :=
  let y := n - x
  let l := p + 1 - j
  j * (l * y - (j - 1) * x)

private def innerZeroInt (p j : Int) : Int :=
  j * (p + 1 - j)

private def piN : PE := pv 0
private def piP : PE := pv 1
private def piX : PE := pv 2
private def piJ : PE := pv 3
private def piY : PE := ps piN piX
private def piL : PE := ps (pa piP (pc 1)) piJ
private def piScale : PE :=
  pm (pm piN (pa piN (pc 1))) (pa piN (pc 2))
private def piPrevious : PE := pH2 piX piY (pc 0) piJ piL
private def piLower : PE :=
  pa
    (pa
      (pm (pm (pm piL (ps piL (pc 1))) (pa piY (pc 1))) piY)
      (pn (pm (pc 2) (pm (pm (pm piJ piL) (pa piX (pc 1)))
        (pa piY (pc 1))))))
    (pm (pm (pm piJ (ps piJ (pc 1))) (pa piX (pc 1))) piX)
private def piEdge : PE :=
  pm piP (ps (pm piL piY) (pm piJ piX))
private def piWeighted : PE := pm piX piEdge
private def piUpper : PE :=
  pm (pm (pm piP (pa piP (pc 1))) piX) piY
private def piFirst : PE :=
  pm piL (ps (pm (ps piL (pc 1)) piY) (pm piJ piX))
private def piSecond : PE :=
  pm piJ (ps (pm piL piY) (pm (ps piJ (pc 1)) piX))
private def piZero : PE := pm piJ piL

private def piPreviousRHS : PE :=
  ps
    (ps
      (pa
        (pm (pm (pm piN piN) (ps piN (pc 1))) piLower)
        (pm (pm (pm (pm (pc 2) piN) (pa piN (pc 1)))
          (ps piN (pc 1))) piEdge))
      (pm (pm (pm (pc 4) (pa piN (pc 1)))
        (ps piN (pc 1))) piWeighted))
    (pm (pm (pc 2) (pa piN (pc 2))) piUpper)

private def piFirstRHS : PE :=
  pa
    (pa
      (pa (pm (pm piN piN) piLower)
        (pm (pm (pm (pc 2) piN) (pa piN (pc 1))) piEdge))
      (pm (pm (ps piN (pc 2)) (pa piN (pc 1))) piWeighted))
    (pm (pa piN (pc 2)) piUpper)

private def piSecondRHS : PE :=
  ps
    (ps
      (pa (pn (pm (pm piN piN) piLower))
        (pm (pm (pm piN piN) (pa piN (pc 1))) piEdge))
      (pm (pm (ps piN (pc 2)) (pa piN (pc 1))) piWeighted))
    (pm (pa piN (pc 2)) piUpper)

private def piZeroRHS : PE :=
  pa
    (ps
      (pa (pn (pm piN piLower))
        (pm (pm piN (pa piN (pc 1))) piEdge))
      (pm (pm (pc 2) (pa piN (pc 1))) piWeighted))
    (pm (pa piN (pc 2)) piUpper)

private theorem piPrevious_normal :
    YMGap.Continuum.RingNormaliser.normalize (pm piScale piPrevious) =
      YMGap.Continuum.RingNormaliser.normalize piPreviousRHS := by decide

private theorem piFirst_normal :
    YMGap.Continuum.RingNormaliser.normalize (pm piScale piFirst) =
      YMGap.Continuum.RingNormaliser.normalize piFirstRHS := by decide

private theorem piSecond_normal :
    YMGap.Continuum.RingNormaliser.normalize (pm piScale piSecond) =
      YMGap.Continuum.RingNormaliser.normalize piSecondRHS := by decide

private theorem piZero_normal :
    YMGap.Continuum.RingNormaliser.normalize (pm piScale piZero) =
      YMGap.Continuum.RingNormaliser.normalize piZeroRHS := by decide

private theorem inner_previous_scaled
    (n p x j : Int) :
    n * (n + 1) * (n + 2) * innerPreviousInt n p x j =
      n * n * (n - 1) * innerLowerInt n p x j +
        2 * n * (n + 1) * (n - 1) * innerEdgeInt n p x j -
        4 * (n + 1) * (n - 1) * innerWeightedEdgeInt n p x j -
        2 * (n + 2) * innerUpperInt n p x := by
  unfold innerWeightedEdgeInt innerPreviousInt innerLowerInt innerEdgeInt
    innerUpperInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pm piScale piPrevious) piPreviousRHS piPrevious_normal
    (fun | 0 => n | 1 => p | 2 => x | _ => j)
  simpa [IntRingNormaliser.eval, piScale, piPrevious, piPreviousRHS,
    piN, piP, piX, piJ, piY, piL, piLower, piEdge, piWeighted,
    piUpper, pH2, pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg,
    Int.mul_assoc] using h

private theorem inner_first_scaled
    (n p x j : Int) :
    n * (n + 1) * (n + 2) * innerFirstInt n p x j =
      n * n * innerLowerInt n p x j +
        2 * n * (n + 1) * innerEdgeInt n p x j +
        (n - 2) * (n + 1) * innerWeightedEdgeInt n p x j +
        (n + 2) * innerUpperInt n p x := by
  unfold innerWeightedEdgeInt innerFirstInt innerLowerInt innerEdgeInt
    innerUpperInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pm piScale piFirst) piFirstRHS piFirst_normal
    (fun | 0 => n | 1 => p | 2 => x | _ => j)
  simpa [IntRingNormaliser.eval, piScale, piFirst, piFirstRHS,
    piN, piP, piX, piJ, piY, piL, piLower, piEdge, piWeighted,
    piUpper, pH2, pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg,
    Int.mul_assoc] using h

private theorem inner_second_scaled
    (n p x j : Int) :
    n * (n + 1) * (n + 2) * innerSecondInt n p x j =
      -(n * n * innerLowerInt n p x j) +
        n * n * (n + 1) * innerEdgeInt n p x j -
        (n - 2) * (n + 1) * innerWeightedEdgeInt n p x j -
        (n + 2) * innerUpperInt n p x := by
  unfold innerWeightedEdgeInt innerSecondInt innerLowerInt innerEdgeInt
    innerUpperInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pm piScale piSecond) piSecondRHS piSecond_normal
    (fun | 0 => n | 1 => p | 2 => x | _ => j)
  simpa [IntRingNormaliser.eval, piScale, piSecond, piSecondRHS,
    piN, piP, piX, piJ, piY, piL, piLower, piEdge, piWeighted,
    piUpper, pH2, pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg,
    Int.mul_assoc] using h

private theorem inner_zero_scaled
    (n p x j : Int) :
    n * (n + 1) * (n + 2) * innerZeroInt p j =
      -(n * innerLowerInt n p x j) +
        n * (n + 1) * innerEdgeInt n p x j -
        2 * (n + 1) * innerWeightedEdgeInt n p x j +
        (n + 2) * innerUpperInt n p x := by
  unfold innerWeightedEdgeInt innerZeroInt innerLowerInt innerEdgeInt
    innerUpperInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pm piScale piZero) piZeroRHS piZero_normal
    (fun | 0 => n | 1 => p | 2 => x | _ => j)
  simpa [IntRingNormaliser.eval, piScale, piZero, piZeroRHS,
    piN, piP, piX, piJ, piY, piL, piLower, piEdge, piWeighted,
    piUpper, pH2, pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg,
    Int.mul_assoc] using h

private def outerPreviousInt (n r u v : Int) : Int :=
  (u + 1) * u * (n - r) * (n - r - 1) -
      r * (u + 1) * (v + 1) * 2 * (n - r) +
    r * (r - 1) * (v + 1) * v

private def outerLowerInt (n r u v : Int) : Int :=
  (u + 1) * u * (n - r + 1) * (n - r) -
      (r + 1) * (u + 1) * v * 2 * (n - r + 1) +
    (r + 1) * r * v * (v - 1)

private def outerOneCoreInt (n r u v : Int) : Int :=
  (n - 1) * ((u + 1) * (n - r) - r * v)

private def diagonalCoreInt (n r x u v : Int) : Int :=
  n * (n - r + 1) * (u + v) +
    x * (n * r - n * u - n * v +
      2 * r * u + 2 * r * v + 2 * r)

private def outerDInt (n r u v : Int) : Int :=
  outerPreviousInt n r u v

private def outerEInt (n r u v : Int) : Int :=
  2 * (r + u) * outerOneCoreInt n r u v

private def outerFInt (n r u v : Int) : Int :=
  2 * v * outerOneCoreInt n r u v

private def outerGInt (n r u v : Int) : Int :=
  2 * n * v * (r + u + 1) * (n - 1)

private def poN : PE := pv 0
private def poR : PE := pv 1
private def poU : PE := pv 2
private def poV : PE := pv 3
private def poQ : PE :=
  pm (ps poN (pc 1))
    (ps (pm (pa poU (pc 1)) (ps poN poR)) (pm poR poV))
private def pOuterPreviousAt (n r u v : PE) : PE :=
  pa
    (pa
      (pm (pm (pm (pa u (pc 1)) u) (ps n r))
        (ps (ps n r) (pc 1)))
      (pn (pm (pm (pm (pm r (pa u (pc 1)))
        (pa v (pc 1))) (pc 2)) (ps n r))))
    (pm (pm (pm r (ps r (pc 1))) (pa v (pc 1))) v)
private def pOuterLowerAt (n r u v : PE) : PE :=
  pa
    (pa
      (pm (pm (pm (pa u (pc 1)) u)
        (pa (ps n r) (pc 1))) (ps n r))
      (pn (pm (pm (pm (pm (pa r (pc 1)) (pa u (pc 1))) v)
        (pc 2)) (pa (ps n r) (pc 1)))))
    (pm (pm (pm (pa r (pc 1)) r) v) (ps v (pc 1)))
private def poPrevious : PE := pOuterPreviousAt poN poR poU poV
private def poLower : PE := pOuterLowerAt poN poR poU poV
private def poD : PE := poPrevious
private def poE : PE := pm (pm (pc 2) (pa poR poU)) poQ
private def poF : PE := pm (pm (pc 2) poV) poQ
private def poG : PE :=
  pm (pm (pm (pm (pc 2) poN) poV) (pa (pa poR poU) (pc 1)))
    (ps poN (pc 1))
private def poT : PE :=
  pa
    (pa
      (ps (ps (pm poN poR) (pm poN poU)) (pm poN poV))
      (pm (pc 2) (pm poR poU)))
    (pa (pm (pc 2) (pm poR poV)) (pm (pc 2) poR))

private def poLowerLHS : PE :=
  pm (pm (pm poN poN) (ps poN (pc 1))) poLower
private def poLowerRHS : PE :=
  ps
    (ps
      (pa (pm poD (pm (pm poN poN) (ps poN (pc 1))))
        (pm poE (pm poN poN)))
      (pm poF (pm poN poN)))
    (pm poG poN)

private def poEdgeLHS : PE :=
  pm (pm (pm (pc 2) (pa poN (pc 1)))
    (pm (pm poN (pa (ps poN poR) (pc 1))) (pa poU poV))) poQ
private def poEdgeRHS : PE :=
  pa
    (pa
      (pa
        (pm poD (pm (pm (pm (pc 2) poN) (pa poN (pc 1)))
          (ps poN (pc 1))))
        (pm poE (pm (pm (pc 2) poN) (pa poN (pc 1)))))
      (pm poF (pm (pm poN poN) (pa poN (pc 1)))))
    (pm poG (pm poN (pa poN (pc 1))))

private def poWeightedLHS : PE :=
  pm (pm (pm (pc 2) (pa poN (pc 1))) poQ) poT
private def poWeightedRHS : PE :=
  ps
    (ps
      (pa (pn (pm poD (pm (pm (pc 4) (pa poN (pc 1)))
        (ps poN (pc 1)))))
        (pm poE (pm (ps poN (pc 2)) (pa poN (pc 1)))))
      (pm poF (pm (ps poN (pc 2)) (pa poN (pc 1)))))
    (pm poG (pm (pc 2) (pa poN (pc 1))))

private def poUpperLHS : PE :=
  pm (pm (pm (pm (pm (pc 2) (pa poN (pc 2))) poR)
    (pa (pa poU poV) (pc 1)))
    (pa (pa (pa poU poV) poN) (pc 1))) (ps poN poR)
private def poUpperRHS : PE :=
  pa
    (ps
      (pa (pn (pm poD (pm (pc 2) (pa poN (pc 2)))))
        (pm poE (pa poN (pc 2))))
      (pm poF (pa poN (pc 2))))
    (pm poG (pa poN (pc 2)))

private theorem poLower_normal :
    YMGap.Continuum.RingNormaliser.normalize poLowerLHS =
      YMGap.Continuum.RingNormaliser.normalize poLowerRHS := by decide
private theorem poEdge_normal :
    YMGap.Continuum.RingNormaliser.normalize poEdgeLHS =
      YMGap.Continuum.RingNormaliser.normalize poEdgeRHS := by decide
private theorem poWeighted_normal :
    YMGap.Continuum.RingNormaliser.normalize poWeightedLHS =
      YMGap.Continuum.RingNormaliser.normalize poWeightedRHS := by decide
private theorem poUpper_normal :
    YMGap.Continuum.RingNormaliser.normalize poUpperLHS =
      YMGap.Continuum.RingNormaliser.normalize poUpperRHS := by decide

private theorem outer_lower_coefficient
    (n r u v : Int) :
    n * n * (n - 1) * outerLowerInt n r u v =
      outerDInt n r u v * (n * n * (n - 1)) +
        outerEInt n r u v * (n * n) -
        outerFInt n r u v * (n * n) -
        outerGInt n r u v * n := by
  unfold outerDInt outerEInt outerFInt outerGInt outerLowerInt
    outerPreviousInt outerOneCoreInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    poLowerLHS poLowerRHS poLower_normal
    (fun | 0 => n | 1 => r | 2 => u | _ => v)
  simpa [IntRingNormaliser.eval, poLowerLHS, poLowerRHS, poLower,
    poPrevious, poD, poE, poF, poG, poQ, poN, poR, poU, poV,
    pOuterPreviousAt, pOuterLowerAt,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem outer_edge_coefficient
    (n r u v : Int) :
    2 * (n + 1) * (n * (n - r + 1) * (u + v)) *
        outerOneCoreInt n r u v =
      outerDInt n r u v * (2 * n * (n + 1) * (n - 1)) +
        outerEInt n r u v * (2 * n * (n + 1)) +
        outerFInt n r u v * (n * n * (n + 1)) +
        outerGInt n r u v * (n * (n + 1)) := by
  unfold outerDInt outerEInt outerFInt outerGInt outerPreviousInt
    outerOneCoreInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    poEdgeLHS poEdgeRHS poEdge_normal
    (fun | 0 => n | 1 => r | 2 => u | _ => v)
  simpa [IntRingNormaliser.eval, poEdgeLHS, poEdgeRHS, poPrevious,
    poD, poE, poF, poG, poQ, poN, poR, poU, poV,
    pOuterPreviousAt, pOuterLowerAt,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem outer_weighted_edge_coefficient
    (n r u v : Int) :
    2 * (n + 1) * outerOneCoreInt n r u v *
        (n * r - n * u - n * v +
          2 * r * u + 2 * r * v + 2 * r) =
      -(outerDInt n r u v * (4 * (n + 1) * (n - 1))) +
        outerEInt n r u v * ((n - 2) * (n + 1)) -
        outerFInt n r u v * ((n - 2) * (n + 1)) -
        outerGInt n r u v * (2 * (n + 1)) := by
  unfold outerDInt outerEInt outerFInt outerGInt outerPreviousInt
    outerOneCoreInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    poWeightedLHS poWeightedRHS poWeighted_normal
    (fun | 0 => n | 1 => r | 2 => u | _ => v)
  simpa [IntRingNormaliser.eval, poWeightedLHS, poWeightedRHS,
    poPrevious, poD, poE, poF, poG, poQ, poT, poN, poR, poU, poV,
    pOuterPreviousAt, pOuterLowerAt,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem outer_upper_coefficient
    (n r u v : Int) :
    2 * (n + 2) * r * (u + v + 1) *
        (u + v + n + 1) * (n - r) =
      -(outerDInt n r u v * (2 * (n + 2))) +
        outerEInt n r u v * (n + 2) -
        outerFInt n r u v * (n + 2) +
        outerGInt n r u v * (n + 2) := by
  unfold outerDInt outerEInt outerFInt outerGInt outerPreviousInt
    outerOneCoreInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    poUpperLHS poUpperRHS poUpper_normal
    (fun | 0 => n | 1 => r | 2 => u | _ => v)
  simpa [IntRingNormaliser.eval, poUpperLHS, poUpperRHS, poPrevious,
    poD, poE, poF, poG, poQ, poN, poR, poU, poV,
    pOuterPreviousAt, pOuterLowerAt,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem scaled_linear_collection
    (n lower edge weighted upper previous first second zero
      od oe of' og cl ce cw cu : Int)
    (hprevious :
      n * (n + 1) * (n + 2) * previous =
        n * n * (n - 1) * lower +
          2 * n * (n + 1) * (n - 1) * edge -
          4 * (n + 1) * (n - 1) * weighted -
          2 * (n + 2) * upper)
    (hfirst :
      n * (n + 1) * (n + 2) * first =
        n * n * lower + 2 * n * (n + 1) * edge +
          (n - 2) * (n + 1) * weighted + (n + 2) * upper)
    (hsecond :
      n * (n + 1) * (n + 2) * second =
        -(n * n * lower) + n * n * (n + 1) * edge -
          (n - 2) * (n + 1) * weighted - (n + 2) * upper)
    (hzero :
      n * (n + 1) * (n + 2) * zero =
        -(n * lower) + n * (n + 1) * edge -
          2 * (n + 1) * weighted + (n + 2) * upper)
    (hcl :
      cl = od * (n * n * (n - 1)) + oe * (n * n) -
        of' * (n * n) - og * n)
    (hce :
      ce = od * (2 * n * (n + 1) * (n - 1)) +
        oe * (2 * n * (n + 1)) + of' * (n * n * (n + 1)) +
        og * (n * (n + 1)))
    (hcw :
      cw = -(od * (4 * (n + 1) * (n - 1))) +
        oe * ((n - 2) * (n + 1)) -
        of' * ((n - 2) * (n + 1)) - og * (2 * (n + 1)))
    (hcu :
      cu = -(od * (2 * (n + 2))) + oe * (n + 2) -
        of' * (n + 2) + og * (n + 2)) :
    cl * lower + ce * edge + cw * weighted + cu * upper =
      n * (n + 1) * (n + 2) *
        (od * previous + oe * first + of' * second + og * zero) := by
  rw [hcl, hce, hcw, hcu]
  calc
    _ = od *
          (n * n * (n - 1) * lower +
            2 * n * (n + 1) * (n - 1) * edge -
            4 * (n + 1) * (n - 1) * weighted -
            2 * (n + 2) * upper) +
        oe *
          (n * n * lower + 2 * n * (n + 1) * edge +
            (n - 2) * (n + 1) * weighted + (n + 2) * upper) +
        of' *
          (-(n * n * lower) + n * n * (n + 1) * edge -
            (n - 2) * (n + 1) * weighted - (n + 2) * upper) +
        og *
          (-(n * lower) + n * (n + 1) * edge -
            2 * (n + 1) * weighted + (n + 2) * upper) := by
          simp only [Int.sub_eq_add_neg, Int.add_mul, Int.mul_add,
            Int.neg_mul, Int.mul_neg]
          ac_rfl
    _ = od * (n * (n + 1) * (n + 2) * previous) +
        oe * (n * (n + 1) * (n + 2) * first) +
        of' * (n * (n + 1) * (n + 2) * second) +
        og * (n * (n + 1) * (n + 2) * zero) := by
          rw [hprevious, hfirst, hsecond, hzero]
    _ = _ := by
      simp only [Int.mul_add]
      ac_rfl

private theorem carrier_reduced_identity
    (n p x r u v j : Int) :
    (n * n * (n - 1) * outerLowerInt n r u v) *
          innerLowerInt n p x j +
        (2 * (n + 1) * diagonalCoreInt n r x u v *
          outerOneCoreInt n r u v) * innerEdgeInt n p x j +
        (2 * (n + 2) * r * (u + v + 1) *
          (u + v + n + 1) * (n - r)) * innerUpperInt n p x =
      n * (n + 1) * (n + 2) *
        (outerDInt n r u v * innerPreviousInt n p x j +
          outerEInt n r u v * innerFirstInt n p x j +
          outerFInt n r u v * innerSecondInt n p x j +
          outerGInt n r u v * innerZeroInt p j) := by
  have h := scaled_linear_collection n
    (innerLowerInt n p x j) (innerEdgeInt n p x j)
    (innerWeightedEdgeInt n p x j) (innerUpperInt n p x)
    (innerPreviousInt n p x j) (innerFirstInt n p x j)
    (innerSecondInt n p x j) (innerZeroInt p j)
    (outerDInt n r u v) (outerEInt n r u v)
    (outerFInt n r u v) (outerGInt n r u v)
    (n * n * (n - 1) * outerLowerInt n r u v)
    (2 * (n + 1) * (n * (n - r + 1) * (u + v)) *
      outerOneCoreInt n r u v)
    (2 * (n + 1) * outerOneCoreInt n r u v *
      (n * r - n * u - n * v +
        2 * r * u + 2 * r * v + 2 * r))
    (2 * (n + 2) * r * (u + v + 1) *
      (u + v + n + 1) * (n - r))
    (inner_previous_scaled n p x j) (inner_first_scaled n p x j)
    (inner_second_scaled n p x j) (inner_zero_scaled n p x j)
    (outer_lower_coefficient n r u v) (outer_edge_coefficient n r u v)
    (outer_weighted_edge_coefficient n r u v)
    (outer_upper_coefficient n r u v)
  rw [← h]
  unfold diagonalCoreInt innerWeightedEdgeInt
  simp only [Int.add_mul, Int.mul_add]
  ac_rfl

private def pbB : PE := pv 0
private def pbN : PE := pv 1
private def pbP : PE := pv 2
private def pbJ : PE := pv 3
private def pbC : PE := ps (pa (pm (pc 2) pbP) pbN) pbB
private def pbL : PE := ps (pa pbP (pc 1)) pbJ
private def pbX : PE := ps pbB pbP
private def pbY : PE := ps pbN pbX
private def pbPreviousLHS : PE :=
  pH2 (ps pbB (pc 1)) (ps pbC (pc 1)) (ps pbP (pc 1)) pbJ pbL
private def pbPreviousRHS : PE := pH2 pbX pbY (pc 0) pbJ pbL
private def pbLowerLHS : PE :=
  pH2 pbB pbC (ps pbP (pc 1)) pbJ pbL
private def pbLowerRHS : PE :=
  pH2 (pa pbX (pc 1)) (pa pbY (pc 1)) (pc 0) pbJ pbL
private theorem pbPrevious_normal :
    YMGap.Continuum.RingNormaliser.normalize pbPreviousLHS =
      YMGap.Continuum.RingNormaliser.normalize pbPreviousRHS := by decide
private theorem pbLower_normal :
    YMGap.Continuum.RingNormaliser.normalize pbLowerLHS =
      YMGap.Continuum.RingNormaliser.normalize pbLowerRHS := by decide
private theorem pbY_normal :
    YMGap.Continuum.RingNormaliser.normalize (ps pbC pbP) =
      YMGap.Continuum.RingNormaliser.normalize pbY := by decide

private def pboA : PE := pv 0
private def pboN : PE := pv 1
private def pboR : PE := pv 2
private def pboI : PE := pv 3
private def pboU : PE := ps pboI pboR
private def pboV : PE := ps pboA pboI
private def pboPreviousLHS : PE :=
  pO2 pboA pboN pboR (ps pboI (pc 1))
private def pboPreviousRHS : PE :=
  pOuterPreviousAt pboN pboR pboU pboV
private def pboLowerLHS : PE :=
  pO2 pboA (pa pboN (pc 2)) (pa pboR (pc 1)) pboI
private def pboLowerRHS : PE := pOuterLowerAt pboN pboR pboU pboV
private theorem pboPrevious_normal :
    YMGap.Continuum.RingNormaliser.normalize pboPreviousLHS =
      YMGap.Continuum.RingNormaliser.normalize pboPreviousRHS := by decide
private theorem pboLower_normal :
    YMGap.Continuum.RingNormaliser.normalize pboLowerLHS =
      YMGap.Continuum.RingNormaliser.normalize pboLowerRHS := by decide

private def pdA : PE := pv 0
private def pdB : PE := pv 1
private def pdN : PE := pv 2
private def pdP : PE := pv 3
private def pdR : PE := pv 4
private def pdI : PE := pv 5
private def pdC : PE := ps (pa (pm (pc 2) pdP) pdN) pdB
private def pdD : PE := ps (pa pdA pdN) (pm (pc 2) pdR)
private def pdX : PE := ps pdB pdP
private def pdU : PE := ps pdI pdR
private def pdV : PE := ps pdA pdI
private def pdCore : PE :=
  pa
    (pm (pm pdN (pa (ps pdN pdR) (pc 1))) (pa pdU pdV))
    (pm pdX
      (pa
        (pa
          (ps (ps (pm pdN pdR) (pm pdN pdU)) (pm pdN pdV))
          (pm (pc 2) (pm pdR pdU)))
        (pa (pm (pc 2) (pm pdR pdV)) (pm (pc 2) pdR))))
private def pdLHS : PE :=
  ps (pDiagonalNum pdA pdB pdC pdD pdN)
    (pDiagonalNum pdA (ps pdB (pc 1)) (ps pdC (pc 1)) pdD pdN)
private def pdRHS : PE := pn (pm (pc 8) pdCore)
private theorem pd_normal :
    YMGap.Continuum.RingNormaliser.normalize pdLHS =
      YMGap.Continuum.RingNormaliser.normalize pdRHS := by decide
private theorem pdSum_normal :
    YMGap.Continuum.RingNormaliser.normalize
        (pa (ps pdI pdR) (ps pdA pdI)) =
      YMGap.Continuum.RingNormaliser.normalize (ps pdA pdR) := by decide
private theorem pdShift_normal :
    YMGap.Continuum.RingNormaliser.normalize
        (pa (ps (pa pdA pdN) pdR) (pc 1)) =
      YMGap.Continuum.RingNormaliser.normalize
        (pa (pa (ps pdA pdR) pdN) (pc 1)) := by decide

private theorem height_two_previous_bridge
    (b n p j : Int) :
    heightTwoInt (b - 1) (2 * p + n - b - 1) (p - 1) j
        (p + 1 - j) =
      innerPreviousInt n p (b - p) j := by
  unfold heightTwoInt innerPreviousInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    pbPreviousLHS pbPreviousRHS pbPrevious_normal
    (fun | 0 => b | 1 => n | 2 => p | _ => j)
  simpa [IntRingNormaliser.eval, pbPreviousLHS, pbPreviousRHS,
    pbB, pbN, pbP, pbJ, pbC, pbL, pbX, pbY, pH2,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem height_two_lower_bridge
    (b n p j : Int) :
    heightTwoInt b (2 * p + n - b) (p - 1) j (p + 1 - j) =
      innerLowerInt n p (b - p) j := by
  unfold heightTwoInt innerLowerInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    pbLowerLHS pbLowerRHS pbLower_normal
    (fun | 0 => b | 1 => n | 2 => p | _ => j)
  simpa [IntRingNormaliser.eval, pbLowerLHS, pbLowerRHS,
    pbB, pbN, pbP, pbJ, pbC, pbL, pbX, pbY, pH2,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem outer_two_previous_bridge
    (a n r i : Int) :
    outerTwoInt a n r (i - 1) =
      outerPreviousInt n r (i - r) (a - i) := by
  unfold outerTwoInt outerPreviousInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    pboPreviousLHS pboPreviousRHS pboPrevious_normal
    (fun | 0 => a | 1 => n | 2 => r | _ => i)
  simpa [IntRingNormaliser.eval, pboPreviousLHS, pboPreviousRHS,
    pboA, pboN, pboR, pboI, pboU, pboV, pO2, pOuterPreviousAt,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem outer_two_lower_bridge
    (a n r i : Int) :
    outerTwoInt a (n + 2) (r + 1) i =
      outerLowerInt n r (i - r) (a - i) := by
  unfold outerTwoInt outerLowerInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    pboLowerLHS pboLowerRHS pboLower_normal
    (fun | 0 => a | 1 => n | 2 => r | _ => i)
  simpa [IntRingNormaliser.eval, pboLowerLHS, pboLowerRHS,
    pboA, pboN, pboR, pboI, pboU, pboV, pO2, pOuterLowerAt,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.mul_assoc,
    Int.add_assoc] using h

private theorem diagonal_difference_bridge
    (a b n p r i : Int) :
    diagonalInt a b (2 * p + n - b) (a + n - 2 * r) n -
        diagonalInt a (b - 1) (2 * p + n - b - 1)
          (a + n - 2 * r) n =
      -(8 * diagonalCoreInt n r (b - p) (i - r) (a - i)) := by
  unfold diagonalInt casimirInt diagonalCoreInt
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    pdLHS pdRHS pd_normal
    (fun | 0 => a | 1 => b | 2 => n | 3 => p | 4 => r | _ => i)
  simpa [IntRingNormaliser.eval, pdLHS, pdRHS, pdCore, pdA, pdB,
    pdN, pdP, pdR, pdI, pdC, pdD, pdX, pdU, pdV,
    pDiagonalNum, pCas, pc, pv, pa, pm, pn, ps,
    Int.sub_eq_add_neg, Int.mul_assoc, Int.add_assoc] using h

private theorem inner_y_bridge (b n p : Int) :
    2 * p + n - b - p = n - (b - p) := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (ps pbC pbP) pbY pbY_normal
    (fun | 0 => b | 1 => n | _ => p)
  simpa [IntRingNormaliser.eval, pbC, pbY, pbX, pbB, pbN, pbP,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.add_assoc] using h

private theorem coordinate_sum_bridge (a r i : Int) :
    (i - r) + (a - i) = a - r := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (ps pdI pdR) (ps pdA pdI)) (ps pdA pdR) pdSum_normal
    (fun | 0 => a | 4 => r | _ => i)
  simpa [IntRingNormaliser.eval, pdA, pdR, pdI,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.add_assoc] using h

private theorem coordinate_shift_bridge (a n r : Int) :
    a + n - r + 1 = (a - r) + n + 1 := by
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    (pa (ps (pa pdA pdN) pdR) (pc 1))
    (pa (pa (ps pdA pdR) pdN) (pc 1)) pdShift_normal
    (fun | 0 => a | 2 => n | _ => r)
  simpa [IntRingNormaliser.eval, pdA, pdN, pdR,
    pc, pv, pa, pm, pn, ps, Int.sub_eq_add_neg, Int.add_assoc] using h

private def pkA : PE := pv 0
private def pkN : PE := pv 1
private def pkP : PE := pv 2
private def pkR : PE := pv 3
private def pkI : PE := pv 4
private def pkJ : PE := pv 5
private def pkH : PE := pv 6
private def pkO : PE := pv 7
private def pkI1 : PE := pv 8
private def pkI2 : PE := pv 9
private def pkO1 : PE := pv 10
private def pkL : PE := ps (pa pkP (pc 1)) pkJ
private def pkU : PE := ps pkI pkR
private def pkV : PE := ps pkA pkI
private def pkLHS : PE :=
  pa
    (pa (pm pkH pkO)
      (pm (pm (pm (pc 2) pkI) pkL) (pm pkI1 pkO1)))
    (pm (pm (pm (pc 2) pkV) pkJ)
      (pa (pm pkI2 pkO1)
        (pm pkL (pm (pm (pa pkI (pc 1)) pkN) (ps pkN (pc 1))))))
private def pkRHS : PE :=
  pa
    (pa
      (pa (pm pkO pkH)
        (pm (pm (pm (pc 2) (pa pkR pkU)) pkO1) (pm pkL pkI1)))
      (pm (pm (pc 2) (pm pkV pkO1)) (pm pkJ pkI2)))
    (pm
      (pm (pm (pm (pm (pc 2) pkN) pkV)
        (pa (pa pkR pkU) (pc 1))) (ps pkN (pc 1)))
      (pm pkJ pkL))
private theorem pk_normal :
    YMGap.Continuum.RingNormaliser.normalize pkLHS =
      YMGap.Continuum.RingNormaliser.normalize pkRHS := by decide

private theorem common_core_bridge
    (a b n p r i j : Int) :
    heightOneIntegralCommonCoreInt a b n p r i j =
      outerDInt n r (i - r) (a - i) *
          innerPreviousInt n p (b - p) j +
        outerEInt n r (i - r) (a - i) *
          innerFirstInt n p (b - p) j +
        outerFInt n r (i - r) (a - i) *
          innerSecondInt n p (b - p) j +
        outerGInt n r (i - r) (a - i) * innerZeroInt p j := by
  unfold heightOneIntegralCommonCoreInt
  simp only
  rw [height_two_previous_bridge, outer_two_previous_bridge]
  rw [inner_y_bridge]
  unfold outerDInt outerEInt outerFInt outerGInt innerFirstInt
    innerSecondInt innerZeroInt outerOneCoreInt
  let x := b - p
  let y := n - x
  let l := p + 1 - j
  let i1 := (l - 1) * y - j * x
  let i2 := l * y - (j - 1) * x
  let o1 := (n - 1) * ((i - r + 1) * (n - r) - r * (a - i))
  have h := IntRingNormaliser.poly_identity_of_normal_eq
    pkLHS pkRHS pk_normal
    (fun
      | 0 => a
      | 1 => n
      | 2 => p
      | 3 => r
      | 4 => i
      | 5 => j
      | 6 => innerPreviousInt n p x j
      | 7 => outerPreviousInt n r (i - r) (a - i)
      | 8 => i1
      | 9 => i2
      | _ => o1)
  simpa [IntRingNormaliser.eval, pkLHS, pkRHS, pkA, pkN, pkP, pkR,
    pkI, pkJ, pkH, pkO, pkI1, pkI2, pkO1, pkL, pkU, pkV,
    pc, pv, pa, pm, pn, ps, x, y, l, i1, i2, o1,
    Int.sub_eq_add_neg, Int.mul_assoc, Int.add_assoc] using h

private theorem carrier_structure_collection
    (n r p x y s w h o d q e : Int) :
    8 * n * ((x + 1) * (y + 1) * (s + 1)) *
          (h * (n * (n - 1) * o)) +
        (n + 1) * (-(8 * d)) *
          (2 * ((-(p * (x + 1) * (y + 1) * e)) *
            ((n - 1) * (s + 1) * q))) +
        8 * (n + 2) * r * (w + 1) * (w + n + 1) *
          (2 * ((p + 1) * p * (x + 1) * x *
            (y + 1) * y * (s + 1) * s)) =
      8 * ((x + 1) * (y + 1) * (s + 1)) *
        ((n * n * (n - 1) * o) * h +
          (2 * (n + 1) * d * ((n - 1) * q)) * (p * e) +
          (2 * (n + 2) * r * (w + 1) * (w + n + 1) * s) *
            (p * (p + 1) * x * y)) := by
  let f := 8 * ((x + 1) * (y + 1) * (s + 1))
  let t₁ := (n * n * (n - 1) * o) * h
  let t₂ := (2 * (n + 1) * d * ((n - 1) * q)) * (p * e)
  let t₃ := (2 * (n + 2) * r * (w + 1) * (w + n + 1) * s) *
    (p * (p + 1) * x * y)
  calc
    _ = f * t₁ + f * t₂ + f * t₃ := by
      simp only [f, t₁, t₂, t₃]
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      ac_rfl
    _ = f * (t₁ + t₂ + t₃) := by
      symm
      rw [Int.mul_add, Int.mul_add]
    _ = _ := by rfl

private theorem carrier_bridge
    (a b n p r i j : Int) :
    heightOneIntegralCarrierInt a b n p r i j =
      8 * heightOneExchangeScaleInt b n p r *
        ((n * n * (n - 1) * outerLowerInt n r (i - r) (a - i)) *
              innerLowerInt n p (b - p) j +
          (2 * (n + 1) *
              diagonalCoreInt n r (b - p) (i - r) (a - i) *
              outerOneCoreInt n r (i - r) (a - i)) *
            innerEdgeInt n p (b - p) j +
          (2 * (n + 2) * r *
              ((i - r) + (a - i) + 1) *
              ((i - r) + (a - i) + n + 1) * (n - r)) *
            innerUpperInt n p (b - p)) := by
  unfold heightOneIntegralCarrierInt heightOneExchangeScaleInt
  simp only
  rw [height_two_lower_bridge, outer_two_lower_bridge,
    diagonal_difference_bridge a b n p r i]
  rw [inner_y_bridge, coordinate_sum_bridge, coordinate_shift_bridge]
  let x := b - p
  let y := n - x
  let s := n - r
  let w := a - r
  let q := (i - r + 1) * (n - r) - r * (a - i)
  let e := (p + 1 - j) * y - j * x
  simpa [innerEdgeInt, innerUpperInt, outerOneCoreInt, x, y, s, w, q, e,
    Int.mul_assoc] using
    carrier_structure_collection n r p x y s w
      (innerLowerInt n p x j) (outerLowerInt n r (i - r) (a - i))
      (diagonalCoreInt n r x (i - r) (a - i))
      q e

private theorem height_one_integral_carrier_factor
    (a b n p r i j : Int) :
    heightOneIntegralCarrierInt a b n p r i j =
      (heightOneJacobiScaleInt n * heightOneExchangeScaleInt b n p r) *
        heightOneIntegralCommonCoreInt a b n p r i j := by
  rw [carrier_bridge, common_core_bridge]
  unfold heightOneJacobiScaleInt
  rw [carrier_reduced_identity n p (b - p) r (i - r) (a - i) j]
  ac_rfl

def heightOneIntegralResidualInt
    (a b n p r i j : Int) : Int :=
  (heightOneJacobiScaleInt n * heightOneExchangeScaleInt b n p r) *
      heightOneIntegralExchangeInt a b n p r i j -
    heightOneCarrierScaleInt b n p r i j *
      heightOneIntegralCarrierInt a b n p r i j

theorem height_one_integral_residual_int_identity
    (a b n p r i j : Int) :
    heightOneIntegralResidualInt a b n p r i j = 0 := by
  unfold heightOneIntegralResidualInt
  rw [height_one_integral_exchange_factor,
    height_one_integral_carrier_factor]
  have hcomm :
      (heightOneJacobiScaleInt n * heightOneExchangeScaleInt b n p r) *
          (heightOneCarrierScaleInt b n p r i j *
            heightOneIntegralCommonCoreInt a b n p r i j) =
        heightOneCarrierScaleInt b n p r i j *
          ((heightOneJacobiScaleInt n * heightOneExchangeScaleInt b n p r) *
            heightOneIntegralCommonCoreInt a b n p r i j) := by
    ac_rfl
  rw [hcomm, Int.sub_self]

end YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCertificate

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneIntegralResidualCertificate.height_one_integral_residual_int_identity
