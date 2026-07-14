/-
# Strict canonical retained Wilson weight

The canonical `Fin 8 -> Nat` carrier admits a literal boundary-exchange
action.  Here the retained quaternion kernel is rebuilt on that carrier and
proved fixed by the action.  This is the nontrivial invariant weight needed
by the time-geometry interface; its positivity is supplied separately by the
exact product-Haar sum-of-squares calculation.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightHaarSymmetry

namespace YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier

/-- A coordinate monomial in the strict eight-variable representation. -/
def basisMono8 (i : Fin 8) : Mono8 := fun j => if j = i then 1 else 0

def gIndex8 (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
def hIndex8 (i : Fin 4) : Fin 8 := ⟨i.val + 4, by omega⟩

def crossMono8 (i : Fin 4) : Mono8 :=
  monoMul8 (basisMono8 (gIndex8 i)) (basisMono8 (hIndex8 i))

def crossCoordinate8 (i : Fin 4) : Term8 := (crossMono8 i, 1)

/-- `sum_i g_i h_i` in the canonical carrier. -/
def relativeDot8 : Poly8 :=
  [crossCoordinate8 0, crossCoordinate8 1,
    crossCoordinate8 2, crossCoordinate8 3]

/-- `chi_1(g h^-1) = 2 sum_i g_i h_i`. -/
def relativeFundamentalCharacter8 : Poly8 := polySmul8 2 relativeDot8

/-- The exact retained kernel `1 + (1/4) chi_1(g h^-1)`. -/
def retainedRelativeWeight8 : Poly8 :=
  polyAdd8 polyOne8 (polySmul8 quarter relativeFundamentalCharacter8)

theorem monoMul8_comm (a b : Mono8) : monoMul8 a b = monoMul8 b a := by
  funext i
  exact Nat.add_comm _ _

theorem swapBoundaryIndex8_gIndex (i : Fin 4) :
    swapBoundaryIndex8 (gIndex8 i) = hIndex8 i := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hi with hi | hi | hi | hi
  · have hEq : i = (0 : Fin 4) := Fin.ext hi
    subst i
    rfl
  · have hEq : i = (1 : Fin 4) := Fin.ext hi
    subst i
    rfl
  · have hEq : i = (2 : Fin 4) := Fin.ext hi
    subst i
    rfl
  · have hEq : i = (3 : Fin 4) := Fin.ext hi
    subst i
    rfl

theorem swapBoundaryIndex8_hIndex (i : Fin 4) :
    swapBoundaryIndex8 (hIndex8 i) = gIndex8 i := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hi with hi | hi | hi | hi
  · have hEq : i = (0 : Fin 4) := Fin.ext hi
    subst i
    rfl
  · have hEq : i = (1 : Fin 4) := Fin.ext hi
    subst i
    rfl
  · have hEq : i = (2 : Fin 4) := Fin.ext hi
    subst i
    rfl
  · have hEq : i = (3 : Fin 4) := Fin.ext hi
    subst i
    rfl

theorem swapMono8_basis (i : Fin 8) :
    swapMono8 (basisMono8 i) = basisMono8 (swapBoundaryIndex8 i) := by
  funext j
  unfold swapMono8 basisMono8
  by_cases h : swapBoundaryIndex8 j = i
  · have hj : j = swapBoundaryIndex8 i := by
      calc
        j = swapBoundaryIndex8 (swapBoundaryIndex8 j) := by
          rw [swapBoundaryIndex8_involutive]
        _ = swapBoundaryIndex8 i := congrArg swapBoundaryIndex8 h
    simp [hj, swapBoundaryIndex8_involutive]
  · have hj : j ≠ swapBoundaryIndex8 i := by
      intro hj
      apply h
      calc
        swapBoundaryIndex8 j =
            swapBoundaryIndex8 (swapBoundaryIndex8 i) :=
          congrArg swapBoundaryIndex8 hj
        _ = i := swapBoundaryIndex8_involutive i
    simp [h, hj]

theorem swapMono8_cross (i : Fin 4) :
    swapMono8 (crossMono8 i) = crossMono8 i := by
  unfold crossMono8
  rw [swapMono8_mul, swapMono8_basis, swapMono8_basis,
    swapBoundaryIndex8_gIndex, swapBoundaryIndex8_hIndex]
  exact monoMul8_comm _ _

theorem swapTerm8_cross (i : Fin 4) :
    swapTerm8 (crossCoordinate8 i) = crossCoordinate8 i := by
  apply Prod.ext
  · exact swapMono8_cross i
  · rfl

theorem swapPoly8_add (p q : Poly8) :
    swapPoly8 (polyAdd8 p q) = polyAdd8 (swapPoly8 p) (swapPoly8 q) := by
  exact List.map_append

theorem swapPoly8_smul (c : Q') (p : Poly8) :
    swapPoly8 (polySmul8 c p) = polySmul8 c (swapPoly8 p) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change
        (swapMono8 t.1, c * t.2) :: swapPoly8 (polySmul8 c p) =
          (swapMono8 t.1, c * t.2) :: polySmul8 c (swapPoly8 p)
      rw [ih]

theorem relativeDot8_swap_fixed : swapPoly8 relativeDot8 = relativeDot8 := by
  change
    swapTerm8 (crossCoordinate8 0) ::
      swapTerm8 (crossCoordinate8 1) ::
      swapTerm8 (crossCoordinate8 2) ::
      swapTerm8 (crossCoordinate8 3) :: [] = relativeDot8
  rw [swapTerm8_cross, swapTerm8_cross, swapTerm8_cross, swapTerm8_cross]
  rfl

theorem relativeFundamentalCharacter8_swap_fixed :
    swapPoly8 relativeFundamentalCharacter8 = relativeFundamentalCharacter8 := by
  rw [relativeFundamentalCharacter8, swapPoly8_smul,
    relativeDot8_swap_fixed]

/-- The nonconstant retained Wilson weight is literally fixed by strict
boundary exchange. -/
theorem retainedRelativeWeight8_swap_fixed :
    swapPoly8 retainedRelativeWeight8 = retainedRelativeWeight8 := by
  rw [retainedRelativeWeight8, swapPoly8_add, swapPoly8_one,
    swapPoly8_smul, relativeFundamentalCharacter8_swap_fixed]

end YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight.swapMono8_cross
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight.retainedRelativeWeight8_swap_fixed
