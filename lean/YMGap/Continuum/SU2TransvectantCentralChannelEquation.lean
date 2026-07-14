/-
# Finite right-channel equations on central Hahn shells

A finite linear combination of right-associated trivalent channels is first
packaged as an actual trilinear map.  Its monomial coefficients are the exact
finite channel sum.  On a central `b,c` shell the nested coefficient
factorization turns that sum into a diagonally weighted transpose Hahn action.
This isolates the precise finite system whose solution supplies an all-label
F-row, while retaining a direct `TriMapEqv` certificate interface.
-/

import YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization
import YMGap.Continuum.SU2GeneralHahnCentralCoordinateBases

namespace YMGap.Continuum.SU2TransvectantCentralChannelEquation

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantNestedCoefficientFactorization
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralShellHahnMatrix

local infix:50 " ≈ " => Q'.eqv

/-- The intermediate label corresponding to contraction order `p`. -/
def rightChannelLabel (b c p : Nat) : Nat := b + c - 2 * p

theorem couplingOrder_rightChannelLabel (b c p : Nat)
    (hp : 2 * p ≤ b + c) :
    couplingOrder b c (rightChannelLabel b c p) = p := by
  unfold couplingOrder rightChannelLabel
  omega

/-- An enumerated finite sum of actual right-associated channels. -/
def rightChannelPrefix (a b c d : Nat) :
    Nat → (Nat → Nat) → (Nat → Q') →
      BForm → BForm → BForm → BForm
  | 0, _, _, _, _, _ => zeroF
  | N + 1, col, coeff, x, y, z =>
      addForm
        (scaleForm (coeff 0)
          (triRight a b c d (rightChannelLabel b c (col 0)) x y z))
        (rightChannelPrefix a b c d N
          (fun q => col (q + 1)) (fun q => coeff (q + 1)) x y z)

/-- The packaged channel map has exactly the expected finite coefficient sum,
without any admissibility or shell restriction. -/
theorem rightChannelPrefix_coefficient (a b c d N : Nat)
    (col : Nat → Nat) (coeff : Nat → Q') (i j l s : Nat) :
    rightChannelPrefix a b c d N col coeff (mono i) (mono j) (mono l) s ≈
      finiteDot N coeff (fun q =>
        triRight a b c d (rightChannelLabel b c (col q))
          (mono i) (mono j) (mono l) s) := by
  induction N generalizing col coeff with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [rightChannelPrefix, addForm, scaleForm, finiteDot]
      exact Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (ih (fun q => col (q + 1)) (fun q => coeff (q + 1)))

/-- Any exact family of finite coefficient equations is already a complete
`TriMapEqv` certificate for the packaged right-channel map. -/
theorem triMapEqv_of_finite_right_channel_equations
    (a b c d e N : Nat) (col : Nat → Nat) (coeff : Nat → Q')
    (hcoeff : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 → ∀ s, s < d + 1 →
        triLeft a b c d e (mono i) (mono j) (mono l) s ≈
          finiteDot N coeff (fun q =>
            triRight a b c d (rightChannelLabel b c (col q))
              (mono i) (mono j) (mono l) s)) :
    TriMapEqv a b c d (triLeft a b c d e)
      (rightChannelPrefix a b c d N col coeff) := by
  intro i hi j hj l hl s hs
  exact Q'.eqv_trans _ _ _ (hcoeff i hi j hj l hl s hs)
    (Q'.eqv_symm
      (rightChannelPrefix_coefficient a b c d N col coeff i j l s))

/-- The transpose action of the square central Hahn matrix. -/
def centralHahnTransposeAction (m n t : Nat)
    (x : Nat → Q') (j : Nat) : Q' :=
  finiteDot (m + 1) (fun p => hahnEntry m n t p j) x

/-- The remaining outer binary coefficient after the inner `b,c` channel of
order `p` has been extracted. -/
def rightNestedOuterCoeff (a b c d i t p s : Nat) : Q' :=
  transvect a (rightChannelLabel b c p)
    (couplingOrder a (rightChannelLabel b c p) d)
    (tprod (mono i) (mono (t - p))) s

/-- The complete coefficient target supplied by one left-associated channel. -/
def leftNestedTarget (a b c d e i j l s : Nat) : Q' :=
  hahnEntry a b (i + j) (couplingOrder a b e) i *
    transvect e c (couplingOrder e c d)
      (tprod (mono (i + j - couplingOrder a b e)) (mono l)) s

theorem triLeft_coefficient_eq_leftNestedTarget
    (a b c d e i j l s : Nat)
    (hr : couplingOrder a b e ≤ i + j) :
    triLeft a b c d e (mono i) (mono j) (mono l) s ≈
      leftNestedTarget a b c d e i j l s := by
  exact triLeft_monomial_factorization a b c d e i j l s hr

/-- The actual central right-channel combination, enumerating contraction
orders `0,...,b`. -/
def centralRightChannelMap (a b c d : Nat) (coeff : Nat → Q') :
    BForm → BForm → BForm → BForm :=
  rightChannelPrefix a b c d (b + 1) (fun p => p) coeff

private theorem finiteDot_congr (N : Nat)
    (row row' x x' : Nat → Q')
    (hterm : ∀ p, p < N → row p * x p ≈ row' p * x' p) :
    finiteDot N row x ≈ finiteDot N row' x' := by
  induction N generalizing row row' x x' with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      exact Q'.add_eqv_congr'
        (hterm 0 (by omega))
        (ih (fun p => row (p + 1)) (fun p => row' (p + 1))
          (fun p => x (p + 1)) (fun p => x' (p + 1))
          (fun p hp => hterm (p + 1) (by omega)))

private theorem reorder_nested_term (f h outer : Q') :
    f * (h * outer) ≈ h * (f * outer) := by
  refine Q'.eqv_trans _ ((f * h) * outer) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((h * f) * outer) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  exact Q'.mul_assoc_eqv _ _ _

/-- **Central finite-channel equation.**  On `b ≤ j+l ≤ c` (with
`b ≤ c`), the coefficient of the actual right-channel combination is the
transpose central Hahn action on the explicitly displayed diagonal outer
data `coeff p * rightNestedOuterCoeff ... p`. -/
theorem centralRightChannelMap_coefficient_eq_transposeHahn
    (a b c d i j l s : Nat) (coeff : Nat → Q')
    (hbc : b ≤ c) (hbt : b ≤ j + l) :
    centralRightChannelMap a b c d coeff (mono i) (mono j) (mono l) s ≈
      centralHahnTransposeAction b c (j + l)
        (fun p => coeff p *
          rightNestedOuterCoeff a b c d i (j + l) p s) j := by
  have hsum := rightChannelPrefix_coefficient a b c d (b + 1)
    (fun p => p) coeff i j l s
  refine Q'.eqv_trans _
    (finiteDot (b + 1) coeff (fun p =>
      triRight a b c d (rightChannelLabel b c p)
        (mono i) (mono j) (mono l) s)) _ hsum ?_
  unfold centralHahnTransposeAction
  apply finiteDot_congr
  intro p hp
  have hpb : p ≤ b := by omega
  have hlabel : couplingOrder b c (rightChannelLabel b c p) = p := by
    apply couplingOrder_rightChannelLabel
    omega
  have htri := triRight_monomial_factorization a b c d
    (rightChannelLabel b c p) i j l s (by rw [hlabel]; omega)
  have hfactor :
      triRight a b c d (rightChannelLabel b c p)
          (mono i) (mono j) (mono l) s ≈
        hahnEntry b c (j + l) p j *
          rightNestedOuterCoeff a b c d i (j + l) p s := by
    simpa only [hlabel, rightNestedOuterCoeff] using htri
  refine Q'.eqv_trans _
    (coeff p * (hahnEntry b c (j + l) p j *
      rightNestedOuterCoeff a b c d i (j + l) p s)) _
    (Q'.mul_eqv_congr_left _ _ _ hfactor) ?_
  exact reorder_nested_term _ _ _

/-- Equality on all central `b,c` monomial shells, retaining the full output
window.  This is the exact shellwise part of `TriMapEqv` controlled by the
already invertible central Hahn matrices. -/
def CentralShellTriMapEqv (a b c d : Nat)
    (L R : BForm → BForm → BForm → BForm) : Prop :=
  ∀ i, i < a + 1 → ∀ j, j < b + 1 → ∀ l, l < c + 1 →
    b ≤ j + l → j + l ≤ c →
      FormEqv (d + 1) (L (mono i) (mono j) (mono l))
        (R (mono i) (mono j) (mono l))

/-- Explicit transpose-Hahn data give the central-shell portion of the
trilinear F-move certificate. -/
theorem centralShellTriMapEqv_of_transposeHahn_equations
    (a b c d e : Nat) (coeff : Nat → Q') (hbc : b ≤ c)
    (heq : ∀ i, i < a + 1 → ∀ j, j < b + 1 →
      ∀ l, l < c + 1 → b ≤ j + l → j + l ≤ c →
      ∀ s, s < d + 1 →
        triLeft a b c d e (mono i) (mono j) (mono l) s ≈
          centralHahnTransposeAction b c (j + l)
            (fun p => coeff p *
              rightNestedOuterCoeff a b c d i (j + l) p s) j) :
    CentralShellTriMapEqv a b c d (triLeft a b c d e)
      (centralRightChannelMap a b c d coeff) := by
  intro i hi j hj l hl hbt htc s hs
  exact Q'.eqv_trans _ _ _
    (heq i hi j hj l hl hbt htc s hs)
    (Q'.eqv_symm
      (centralRightChannelMap_coefficient_eq_transposeHahn
        a b c d i j l s coeff hbc hbt))

end YMGap.Continuum.SU2TransvectantCentralChannelEquation

#print axioms YMGap.Continuum.SU2TransvectantCentralChannelEquation.couplingOrder_rightChannelLabel
#print axioms YMGap.Continuum.SU2TransvectantCentralChannelEquation.rightChannelPrefix_coefficient
#print axioms YMGap.Continuum.SU2TransvectantCentralChannelEquation.triMapEqv_of_finite_right_channel_equations
#print axioms YMGap.Continuum.SU2TransvectantCentralChannelEquation.centralRightChannelMap_coefficient_eq_transposeHahn
#print axioms YMGap.Continuum.SU2TransvectantCentralChannelEquation.centralShellTriMapEqv_of_transposeHahn_equations
