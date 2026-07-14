/-
# Global source reconstruction from all physical Hahn shells

For fixed bidegree `(m,n)`, a Clebsch--Gordan coordinate is a dependent pair
`(k,s)` with `k <= min m n` and `s <= m+n-2k`.  Its unique source shell is
`t=s+k`.  This module assembles the already-inverted physical Hahn matrices
over all such shells and proves the smallest global reconstruction statement:
every coefficient in the physical source rectangle is recovered.

The coordinates in this first assembly theorem are the exact per-shell Hahn
actions.  Identifying them with the actual transvectant evaluations is the
next, separate cross-shell support theorem.
-/

import YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction

open YMGap.Constructive
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence

local infix:50 " ≈ " => Q'.eqv

/-- A physical Clebsch--Gordan output coordinate: contraction order `k` and
output monomial index `s`. -/
structure PhysicalCGChannel (m n : Nat) where
  k : Nat
  k_le : k ≤ min m n
  s : Nat
  s_le : s ≤ m + n - 2 * k

/-- The unique source total-weight shell feeding a channel coordinate. -/
def PhysicalCGChannel.shell {m n : Nat}
    (q : PhysicalCGChannel m n) : Nat := q.s + q.k

theorem PhysicalCGChannel.shell_le {m n : Nat}
    (q : PhysicalCGChannel m n) : q.shell ≤ m + n := by
  have hkm := Nat.le_min.mp q.k_le
  have h2k : 2 * q.k ≤ m + n := by omega
  have hs2k : q.s + 2 * q.k ≤ m + n :=
    Nat.add_le_of_le_sub h2k q.s_le
  unfold PhysicalCGChannel.shell
  omega

/-- Convert an active row index on shell `t` into its dependent global
coordinate `(k,t-k)`. -/
def shellChannelOfIndex (m n t k : Nat) (ht : t ≤ m + n)
    (hk : k ≤ shellWidth m n t) : PhysicalCGChannel m n :=
  let hactive := channelActive_of_index m n t k ht hk
  { k := k
    k_le := Nat.le_min.mpr ⟨hactive.1, hactive.2.1⟩
    s := t - k
    s_le := hactive.2.2.2 }

theorem shellChannelOfIndex_shell (m n t k : Nat) (ht : t ≤ m + n)
    (hk : k ≤ shellWidth m n t) :
    (shellChannelOfIndex m n t k ht hk).shell = t := by
  have hactive := channelActive_of_index m n t k ht hk
  have hkt : k ≤ t := hactive.2.2.1
  unfold shellChannelOfIndex PhysicalCGChannel.shell
  dsimp only
  omega

/-- The physical source-coordinate vector on one total-weight shell. -/
def sourceShellCoordinates (n t : Nat) (x : BForm2) : Nat → Q' :=
  fun a => x (shellLo n t + a) (t - (shellLo n t + a))

/-- Global dependent channel coordinates obtained by applying the exact Hahn
row on the unique source shell `s+k`. -/
def globalHahnCoordinates (m n : Nat) (x : BForm2) :
    PhysicalCGChannel m n → Q' :=
  fun q => physicalHahnAction m n q.shell
    (sourceShellCoordinates n q.shell x) q.k

/-- Read dependent global data as the active row target on one shell. -/
def shellDataFromGlobal (m n t : Nat) (ht : t ≤ m + n)
    (c : PhysicalCGChannel m n → Q') : Nat → Q' :=
  fun k => if hk : k < shellWidth m n t + 1 then
    c (shellChannelOfIndex m n t k ht (Nat.lt_succ_iff.mp hk))
  else 0

/-- On active rows, extracting global Hahn coordinates and returning to a
shell gives the original physical Hahn action. -/
theorem shellDataFromGlobal_globalHahnCoordinates (m n t : Nat)
    (ht : t ≤ m + n) (x : BForm2) (k : Nat)
    (hk : k < shellWidth m n t + 1) :
    shellDataFromGlobal m n t ht (globalHahnCoordinates m n x) k ≈
      physicalHahnAction m n t (sourceShellCoordinates n t x) k := by
  unfold shellDataFromGlobal
  rw [dif_pos hk]
  unfold globalHahnCoordinates
  rw [shellChannelOfIndex_shell m n t k ht (Nat.lt_succ_iff.mp hk)]
  exact Q'.eqv_refl _

/-- Assemble the inverse shell solver at the source shell of coefficient
`(i,j)`.  Values outside the physical rectangle are set to zero. -/
def globalHahnReconstruct (m n : Nat)
    (c : PhysicalCGChannel m n → Q') : BForm2 :=
  fun i j =>
    if hi : i ≤ m then
      if hj : j ≤ n then
        let t := i + j
        let ht : t ≤ m + n := Nat.add_le_add hi hj
        let a := i - shellLo n t
        allShellHahnSolve m n t ht (shellDataFromGlobal m n t ht c) a
      else 0
    else 0

/-- **Global all-shell source reconstruction.**  The dependent Hahn
coordinates reconstruct every coefficient of the complete physical
`(m+1) x (n+1)` source rectangle. -/
theorem globalHahnReconstruct_coordinates (m n : Nat) (x : BForm2)
    (i j : Nat) (hi : i ≤ m) (hj : j ≤ n) :
    globalHahnReconstruct m n (globalHahnCoordinates m n x) i j ≈ x i j := by
  let t := i + j
  have ht : t ≤ m + n := Nat.add_le_add hi hj
  let a := i - shellLo n t
  let xs := sourceShellCoordinates n t x
  let y := shellDataFromGlobal m n t ht (globalHahnCoordinates m n x)
  have hactive : SourceActive m n t i := by
    unfold SourceActive t
    exact ⟨by omega, hi, by omega⟩
  have hindex := sourceActive_index_complete m n t i hactive
  have ha : a < shellWidth m n t + 1 := by
    exact Nat.lt_succ_iff.mpr hindex.1
  have hsolve : ∀ q, q < shellWidth m n t + 1 →
      allShellHahnSolve m n t ht y q ≈ xs q := by
    apply physicalHahnAction_injective m n t ht
    intro k hk
    have hright := allShellHahnSolve_rightInverse m n t ht y k hk
    refine Q'.eqv_trans _ (y k) _ hright ?_
    exact shellDataFromGlobal_globalHahnCoordinates m n t ht x k hk
  unfold globalHahnReconstruct
  rw [dif_pos hi, dif_pos hj]
  change allShellHahnSolve m n t ht y a ≈ x i j
  refine Q'.eqv_trans _ (xs a) _ (hsolve a ha) ?_
  unfold xs sourceShellCoordinates
  have hleft : shellLo n t + a = i := hindex.2
  rw [hleft]
  have hright : t - i = j := by unfold t; omega
  rw [hright]
  exact Q'.eqv_refl _

end YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction

#print axioms YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction.PhysicalCGChannel.shell_le
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction.shellChannelOfIndex_shell
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction.shellDataFromGlobal_globalHahnCoordinates
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction.globalHahnReconstruct_coordinates
