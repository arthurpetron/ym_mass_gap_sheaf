/- Shared expression language for the exact seven-coordinate boundary formula. -/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPrefix
import YMGap.Continuum.IntRingNormaliser

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula

open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPrefix
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow
open YMGap.Continuum.ThetaResidualPascalTelescope

def intPolyEval (x : Int) : List Int → Int
  | [] => 0
  | a :: as => a + x * intPolyEval x as

def sevenBoundaryScaledFormula : Nat → Int → Int
  | 0, m => intPolyEval m [0, -22680, 22680]
  | 1, m => intPolyEval m [0, -56700, 34020, 22680]
  | 2, m => intPolyEval m [0, -44415, -2835, 47250]
  | 3, m => intPolyEval m [0, -11340, -17010, 35910, 0, -7560]
  | 4, m => intPolyEval m [0, -4347, 0, 21735, 0, -17388]
  | 5, m => intPolyEval m [0, -5130, 0, 26586, 0, -25200, 0, 3744]
  | 6, m => intPolyEval m [0, -5679, 0, 30613, 0, -33726, 0, 8472, 0, 320]
  | _, _ => 0

def choose720Poly (n : Int) : Nat → Int
  | 0 => 720
  | 1 => 720 * n
  | 2 => intPolyEval n [0, -360, 360]
  | 3 => intPolyEval n [0, 240, -360, 120]
  | 4 => intPolyEval n [0, -180, 330, -180, 30]
  | 5 => intPolyEval n [0, 144, -300, 210, -60, 6]
  | 6 => intPolyEval n [0, -120, 274, -225, 85, -15, 1]
  | _ => 0

def clearedCell (m : Int) (r : Nat) : Int :=
  let S := 4 * m + 2
  let T := 2 * m + 4
  7 * m * m * (if 2 ≤ r then choose720Poly (S + 1) (r - 2) else 0) -
    m * m *
      (choose720Poly (S + 3) r + 3 * choose720Poly (S + 2) r +
        3 * choose720Poly (S + 1) r + choose720Poly S r) +
    8 * m * (m + 1) * choose720Poly T r

def clearedOldPrefix (m : Int) : Nat → Int
  | 0 => choose720Poly (4 * m + 2) 0 * sevenBoundaryScaledFormula 0 m
  | 1 => choose720Poly (4 * m + 2) 1 * sevenBoundaryScaledFormula 0 m +
      choose720Poly (4 * m + 2) 0 * sevenBoundaryScaledFormula 1 m
  | 2 => choose720Poly (4 * m + 2) 2 * sevenBoundaryScaledFormula 0 m +
      choose720Poly (4 * m + 2) 1 * sevenBoundaryScaledFormula 1 m +
      choose720Poly (4 * m + 2) 0 * sevenBoundaryScaledFormula 2 m
  | 3 => choose720Poly (4 * m + 2) 3 * sevenBoundaryScaledFormula 0 m +
      choose720Poly (4 * m + 2) 2 * sevenBoundaryScaledFormula 1 m +
      choose720Poly (4 * m + 2) 1 * sevenBoundaryScaledFormula 2 m +
      choose720Poly (4 * m + 2) 0 * sevenBoundaryScaledFormula 3 m
  | 4 => choose720Poly (4 * m + 2) 4 * sevenBoundaryScaledFormula 0 m +
      choose720Poly (4 * m + 2) 3 * sevenBoundaryScaledFormula 1 m +
      choose720Poly (4 * m + 2) 2 * sevenBoundaryScaledFormula 2 m +
      choose720Poly (4 * m + 2) 1 * sevenBoundaryScaledFormula 3 m +
      choose720Poly (4 * m + 2) 0 * sevenBoundaryScaledFormula 4 m
  | 5 => choose720Poly (4 * m + 2) 5 * sevenBoundaryScaledFormula 0 m +
      choose720Poly (4 * m + 2) 4 * sevenBoundaryScaledFormula 1 m +
      choose720Poly (4 * m + 2) 3 * sevenBoundaryScaledFormula 2 m +
      choose720Poly (4 * m + 2) 2 * sevenBoundaryScaledFormula 3 m +
      choose720Poly (4 * m + 2) 1 * sevenBoundaryScaledFormula 4 m +
      choose720Poly (4 * m + 2) 0 * sevenBoundaryScaledFormula 5 m
  | 6 => choose720Poly (4 * m + 2) 6 * sevenBoundaryScaledFormula 0 m +
      choose720Poly (4 * m + 2) 5 * sevenBoundaryScaledFormula 1 m +
      choose720Poly (4 * m + 2) 4 * sevenBoundaryScaledFormula 2 m +
      choose720Poly (4 * m + 2) 3 * sevenBoundaryScaledFormula 3 m +
      choose720Poly (4 * m + 2) 2 * sevenBoundaryScaledFormula 4 m +
      choose720Poly (4 * m + 2) 1 * sevenBoundaryScaledFormula 5 m +
      choose720Poly (4 * m + 2) 0 * sevenBoundaryScaledFormula 6 m
  | _ => 0

def clearedStep (m : Int) (r : Nat) : Int :=
  clearedOldPrefix m r + 5670 * clearedCell m r

abbrev PE := IntRingNormaliser.PolyExpr
def pc (z : Int) : PE := .const z
def pv : PE := .var 0
def pa (x y : PE) : PE := .add x y
def pm (x y : PE) : PE := .mul x y
def pn (x : PE) : PE := .neg x
def ps (x y : PE) : PE := pa x (pn y)
def pp (x : PE) (n : Nat) : PE := .pow x n

def pIntPoly (x : PE) : List Int → PE
  | [] => pc 0
  | a :: as => pa (pc a) (pm x (pIntPoly x as))

def pFormula : Nat → PE → PE
  | 0, m => pIntPoly m [0, -22680, 22680]
  | 1, m => pIntPoly m [0, -56700, 34020, 22680]
  | 2, m => pIntPoly m [0, -44415, -2835, 47250]
  | 3, m => pIntPoly m [0, -11340, -17010, 35910, 0, -7560]
  | 4, m => pIntPoly m [0, -4347, 0, 21735, 0, -17388]
  | 5, m => pIntPoly m [0, -5130, 0, 26586, 0, -25200, 0, 3744]
  | 6, m => pIntPoly m [0, -5679, 0, 30613, 0, -33726, 0, 8472, 0, 320]
  | _, _ => pc 0

def pFalling (x : PE) : Nat → PE
  | 0 => pc 1
  | n + 1 => pm (pFalling x n) (ps x (pc n))

def pChoose720 (x : PE) : Nat → PE
  | 0 => pc 720
  | 1 => pm (pc 720) x
  | 2 => pIntPoly x [0, -360, 360]
  | 3 => pIntPoly x [0, 240, -360, 120]
  | 4 => pIntPoly x [0, -180, 330, -180, 30]
  | 5 => pIntPoly x [0, 144, -300, 210, -60, 6]
  | 6 => pIntPoly x [0, -120, 274, -225, 85, -15, 1]
  | _ => pc 0

def pClearedCell (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  let T := pa (pm (pc 2) m) (pc 4)
  pa
    (ps
      (pm (pc 7) <| pm m <| pm m <|
        if 2 ≤ r then pChoose720 (pa S (pc 1)) (r - 2) else pc 0)
      (pm m <| pm m <|
        pa (pChoose720 (pa S (pc 3)) r) <|
        pa (pm (pc 3) (pChoose720 (pa S (pc 2)) r)) <|
        pa (pm (pc 3) (pChoose720 (pa S (pc 1)) r))
          (pChoose720 S r)))
    (pm (pc 8) <| pm m <| pm (pa m (pc 1)) (pChoose720 T r))

def pOldPrefix (m : PE) : Nat → PE
  | 0 => pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 0 m)
  | 1 => pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 0 m))
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 1 m))
  | 2 => pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 0 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 1 m))
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 2 m))
  | 3 => pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 3) (pFormula 0 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 1 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 2 m))
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 3 m))
  | 4 => pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 4) (pFormula 0 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 3) (pFormula 1 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 2 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 3 m))
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 4 m))
  | 5 => pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 5) (pFormula 0 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 4) (pFormula 1 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 3) (pFormula 2 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 3 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 4 m))
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 5 m))
  | 6 => pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 6) (pFormula 0 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 5) (pFormula 1 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 4) (pFormula 2 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 3) (pFormula 3 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 4 m)) <| pa
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 5 m))
      (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 6 m))
  | _ => pc 0

def pStep (m : PE) (r : Nat) : PE :=
  pa (pOldPrefix m r) (pm (pc 5670) (pClearedCell m r))

def pOldFourA (m : PE) : PE :=
  pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 4) (pFormula 0 m))
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 3) (pFormula 1 m))

def pOldFourB (m : PE) : PE :=
  pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 2 m)) <| pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 3 m))
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 4 m))

def pCellA (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  pm (pc 7) <| pm m <| pm m <|
    if 2 ≤ r then pChoose720 (pa S (pc 1)) (r - 2) else pc 0

def pCellC (m : PE) (r : Nat) : PE :=
  let T := pa (pm (pc 2) m) (pc 4)
  pm (pc 8) <| pm m <| pm (pa m (pc 1)) (pChoose720 T r)

def pCellPos (m : PE) (r : Nat) : PE := pa (pCellA m r) (pCellC m r)

def pCellNegLeft (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  pn <| pm m <| pm m <|
    pa (pChoose720 (pa S (pc 3)) r)
      (pm (pc 3) (pChoose720 (pa S (pc 2)) r))

def pCellNegRight (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  pn <| pm m <| pm m <|
    pa (pm (pc 3) (pChoose720 (pa S (pc 1)) r)) (pChoose720 S r)

def pCellNegLL (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  pn <| pm m <| pm m <| pChoose720 (pa S (pc 3)) r

def pCellNegLR (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  pn <| pm m <| pm m <| pm (pc 3) (pChoose720 (pa S (pc 2)) r)

def pCellNegRL (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  pn <| pm m <| pm m <| pm (pc 3) (pChoose720 (pa S (pc 1)) r)

def pCellNegRR (m : PE) (r : Nat) : PE :=
  let S := pa (pm (pc 4) m) (pc 2)
  pn <| pm m <| pm m <| pChoose720 S r

def pCellSplit (m : PE) (r : Nat) : PE :=
  pa (pCellPos m r) (pa (pCellNegLeft m r) (pCellNegRight m r))

def pOldFiveA (m : PE) : PE :=
  pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 5) (pFormula 0 m)) <| pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 4) (pFormula 1 m))
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 3) (pFormula 2 m))

def pOldFiveB (m : PE) : PE :=
  pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 3 m)) <| pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 4 m))
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 5 m))

def pOldSixA (m : PE) : PE :=
  pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 6) (pFormula 0 m)) <| pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 5) (pFormula 1 m))
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 4) (pFormula 2 m))

def pOldSixB (m : PE) : PE :=
  pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 3) (pFormula 3 m)) <| pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 2) (pFormula 4 m)) <| pa
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 1) (pFormula 5 m))
    (pm (pChoose720 (pa (pm (pc 4) m) (pc 2)) 0) (pFormula 6 m))

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBoundaryFormula
