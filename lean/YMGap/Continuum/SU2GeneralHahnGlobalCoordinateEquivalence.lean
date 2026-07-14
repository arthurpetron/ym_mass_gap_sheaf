/-
# Two-sided dependent global Hahn coordinates

The all-shell source reconstruction already proves that analyzing and then
reconstructing recovers every coefficient in the physical rectangle.  Here
we prove the converse: reconstructing arbitrary dependent channel data and
then applying the exact shell Hahn actions recovers every channel coordinate.
This turns the shell assembly into a constructive two-sided coordinate
equivalence and supplies choice-free single-channel sections.

The coordinates remain the exact Hahn actions.  Identification with raw
transvectants is deliberately deferred to the physical-support projection
bridge required by the off-rectangle leakage fence.
-/

import YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
import YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnAllShellCoordinateBases
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction

local infix:50 " ≈ " => Q'.eqv

private theorem physicalCGChannel_eq_of_fields {m n : Nat}
    (q r : PhysicalCGChannel m n)
    (hk : q.k = r.k) (hs : q.s = r.s) : q = r := by
  cases q with
  | mk qk qkle qs qsle =>
      cases r with
      | mk rk rkle rs rsle =>
          dsimp only at hk hs
          subst rk
          subst rs
          rfl

private theorem globalHahnReconstruct_cell
    (m n t i j a : Nat) (c : PhysicalCGChannel m n → Q')
    (hi : i ≤ m) (hj : j ≤ n) (ht : t ≤ m + n)
    (hsum : i + j = t) (hindex : i - shellLo n t = a) :
    globalHahnReconstruct m n c i j ≈
      allShellHahnSolve m n t ht
        (shellDataFromGlobal m n t ht c) a := by
  unfold globalHahnReconstruct
  rw [dif_pos hi, dif_pos hj]
  subst t
  subst a
  exact Q'.eqv_refl _

private theorem reconstructed_shell_coordinates
    (m n t : Nat) (ht : t ≤ m + n)
    (c : PhysicalCGChannel m n → Q') (a : Nat)
    (ha : a < shellWidth m n t + 1) :
    sourceShellCoordinates n t (globalHahnReconstruct m n c) a ≈
      allShellHahnSolve m n t ht
        (shellDataFromGlobal m n t ht c) a := by
  have hsrc := sourceActive_of_index m n t a ht
    (Nat.lt_succ_iff.mp ha)
  let i := shellLo n t + a
  let j := t - i
  have hi : i ≤ m := hsrc.2.1
  have hj : j ≤ n := hsrc.2.2
  have hit : i ≤ t := hsrc.1
  have hsum : i + j = t := by
    unfold j
    exact Nat.add_sub_of_le hit
  have hindex : i - shellLo n t = a := by
    unfold i
    omega
  unfold sourceShellCoordinates
  change globalHahnReconstruct m n c i j ≈ _
  exact globalHahnReconstruct_cell m n t i j a c
    hi hj ht hsum hindex

/-- **Global dependent-coordinate left inverse.**  Arbitrary physical channel
data survive reconstruction followed by exact Hahn analysis. -/
theorem globalHahnCoordinates_reconstruct (m n : Nat)
    (c : PhysicalCGChannel m n → Q') (q : PhysicalCGChannel m n) :
    globalHahnCoordinates m n (globalHahnReconstruct m n c) q ≈ c q := by
  let t := q.shell
  have ht : t ≤ m + n := q.shell_le
  have hmin := Nat.le_min.mp q.k_le
  have hactive : ChannelActive m n t q.k := by
    unfold ChannelActive t PhysicalCGChannel.shell
    constructor
    · exact hmin.1
    constructor
    · exact hmin.2
    constructor
    · omega
    · simpa only [Nat.add_sub_cancel_right] using q.s_le
  have hk : q.k < shellWidth m n t + 1 :=
    Nat.lt_succ_iff.mpr
      (channelActive_index_complete m n t q.k ht hactive)
  let y := shellDataFromGlobal m n t ht c
  let x := sourceShellCoordinates n t (globalHahnReconstruct m n c)
  have hx : ∀ a, a < shellWidth m n t + 1 →
      x a ≈ allShellHahnSolve m n t ht y a := by
    intro a ha
    exact reconstructed_shell_coordinates m n t ht c a ha
  have hanalysis := physicalHahnAction_congr m n t x
    (allShellHahnSolve m n t ht y) hx q.k
  have hsolve := allShellHahnSolve_rightInverse m n t ht y q.k hk
  have hy : y q.k ≈ c q := by
    unfold y shellDataFromGlobal
    rw [dif_pos hk]
    have hshell := shellChannelOfIndex_shell m n t q.k ht
      (Nat.lt_succ_iff.mp hk)
    have hkfield :
        (shellChannelOfIndex m n t q.k ht
          (Nat.lt_succ_iff.mp hk)).k = q.k := rfl
    have hsfield :
        (shellChannelOfIndex m n t q.k ht
          (Nat.lt_succ_iff.mp hk)).s = q.s := by
      dsimp only [shellChannelOfIndex]
      unfold t PhysicalCGChannel.shell
      omega
    have hqeq : shellChannelOfIndex m n t q.k ht
        (Nat.lt_succ_iff.mp hk) = q := by
      exact physicalCGChannel_eq_of_fields _ _ hkfield hsfield
    rw [hqeq]
    exact Q'.eqv_refl _
  unfold globalHahnCoordinates
  change physicalHahnAction m n t x q.k ≈ c q
  exact Q'.eqv_trans _ _ _ hanalysis
    (Q'.eqv_trans _ _ _ hsolve hy)

/-- Dependent channel data supported on one contraction order. -/
def orderChannelData {m n : Nat} (k : Nat) (v : BForm)
    (q : PhysicalCGChannel m n) : Q' :=
  if q.k = k then v q.s else 0

/-- Choice-free section of one global contraction-order channel. -/
def globalOrderSection (m n k : Nat) (v : BForm) : BForm2 :=
  globalHahnReconstruct m n (orderChannelData k v)

/-- Analysis of the global order section is exactly the requested form on
that order and zero on every other physical contraction order. -/
theorem globalOrderSection_coordinates (m n k : Nat) (v : BForm)
    (q : PhysicalCGChannel m n) :
    globalHahnCoordinates m n (globalOrderSection m n k v) q ≈
      (if q.k = k then v q.s else 0) := by
  exact Q'.eqv_trans _ _ _
    (globalHahnCoordinates_reconstruct m n (orderChannelData k v) q)
    (Q'.eqv_refl _)

end YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence

#print axioms YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence.globalHahnCoordinates_reconstruct
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalCoordinateEquivalence.globalOrderSection_coordinates
