/-
# Leakage-free direct-sum basis on every central Hahn shell

The recursive Hahn solver returns source coordinates.  Here those coordinates
are synthesized as an actual finite sum of monomial tensors on the physical
weight shell.  Linearity and the all-order monomial formula identify every
transvectant output form, not merely its distinguished coefficient.  Unit row
data therefore give literal channel basis vectors with zero leakage into every
other active contraction order.
-/

import YMGap.Continuum.SU2GeneralHahnCoordinateEquivalence

namespace YMGap.Continuum.SU2GeneralHahnCentralShellBasis

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnColumnElimination
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnKernelTrivial
open YMGap.Continuum.SU2GeneralHahnRecursiveSolver

local infix:50 " ≈ " => Q'.eqv

/-- Finite synthesis along an arbitrary enumerated list of shell columns.
The zero branch is represented by a literal zero scaling, keeping the
definition choice-free and inside the existing linearity interface. -/
def shellSourcePrefix (t : Nat) :
    Nat → (Nat → Nat) → (Nat → Q') → BForm2
  | 0, _, _ => bscale 0 (shellBasis t 0)
  | N + 1, col, x =>
      badd (bscale (x 0) (shellBasis t (col 0)))
        (shellSourcePrefix t N (fun q => col (q + 1))
          (fun q => x (q + 1)))

private def shellCombineLHS :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  .add (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 3) (.var 2))

private def shellCombineRHS :
    YMGap.Continuum.RingNormaliser.PolyExpr :=
  .mul (.add (.mul (.var 1) (.var 0)) (.var 3)) (.var 2)

private theorem shellCombine_normal :
    YMGap.Continuum.RingNormaliser.normalize shellCombineLHS =
      YMGap.Continuum.RingNormaliser.normalize shellCombineRHS := by
  decide

private theorem shell_combine (x h e tail : Q') :
    x * (h * e) + tail * e ≈ (h * x + tail) * e := by
  let ρ : Nat → Q' := fun i =>
    if i = 0 then x else if i = 1 then h else if i = 2 then e else tail
  have H := YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
    shellCombineLHS shellCombineRHS shellCombine_normal ρ
  simpa [shellCombineLHS, shellCombineRHS,
    YMGap.Continuum.RingNormaliser.eval, ρ] using H

/-- A synthesized shell prefix acts in every contraction order by the exact
finite Hahn row, and its complete output is supported on `mono (t-k)`. -/
theorem shellSourcePrefix_transvect_form (m n t k : Nat) :
    ∀ N : Nat, ∀ col : Nat → Nat, ∀ x : Nat → Q',
      (∀ q, q < N → col q ≤ t) → k ≤ t →
      BFormEqv
        (transvect m n k (shellSourcePrefix t N col x))
        (fun s => finiteDot N (fun q => hahnEntry m n t k (col q)) x *
          mono (t - k) s)
  | 0, col, x, hcol, hk => by
      intro s
      have hscale := transvect_scale m n k 0 (shellBasis t 0) s
      refine Q'.eqv_trans _ (0 * transvect m n k (shellBasis t 0) s) _
        hscale ?_
      refine Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _) ?_
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | N + 1, col, x, hcol, hk => by
      intro s
      have hhead : col 0 ≤ t := hcol 0 (by omega)
      have htail : ∀ q, q < N → col (q + 1) ≤ t := by
        intro q hq
        exact hcol (q + 1) (by omega)
      have hadd := transvect_add m n k
        (bscale (x 0) (shellBasis t (col 0)))
        (shellSourcePrefix t N (fun q => col (q + 1))
          (fun q => x (q + 1))) s
      have hscale := transvect_scale m n k (x 0)
        (shellBasis t (col 0)) s
      have hbasis := shellBasis_transvect_form m n t k (col 0) hhead hk s
      have hrest := shellSourcePrefix_transvect_form m n t k N
        (fun q => col (q + 1)) (fun q => x (q + 1)) htail hk s
      simp only [shellSourcePrefix, finiteDot]
      refine Q'.eqv_trans _
        (transvect m n k (bscale (x 0) (shellBasis t (col 0))) s +
          transvect m n k
            (shellSourcePrefix t N (fun q => col (q + 1))
              (fun q => x (q + 1))) s) _ hadd ?_
      refine Q'.eqv_trans _
        (x 0 * transvect m n k (shellBasis t (col 0)) s +
          finiteDot N
            (fun q => hahnEntry m n t k (col (q + 1)))
            (fun q => x (q + 1)) * mono (t - k) s) _
        (Q'.add_eqv_congr' hscale hrest) ?_
      refine Q'.eqv_trans _
        (x 0 * (hahnEntry m n t k (col 0) * mono (t - k) s) +
          finiteDot N
            (fun q => hahnEntry m n t k (col (q + 1)))
            (fun q => x (q + 1)) * mono (t - k) s) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hbasis)
      · exact shell_combine _ _ _ _

/-- Actual two-form synthesis of arbitrary simultaneous channel data on a
central shell `m ≤ t ≤ n`. -/
def centralShellSynth (m n t : Nat) (hmt : m ≤ t) (htn : t ≤ n)
    (y : Nat → Q') : BForm2 :=
  shellSourcePrefix t (m + 1) (fun q => q)
    (centralHahnSolve m n t hmt htn y)

/-- **Actual transvectant/Hahn bridge.**  The synthesized source reproduces
every requested active contraction channel as a complete output form. -/
theorem centralShellSynth_channels (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (y : Nat → Q')
    (r : Nat) (hr : r < m + 1) :
    BFormEqv (transvect m n r (centralShellSynth m n t hmt htn y))
      (fun s => y r * mono (t - r) s) := by
  intro s
  let x := centralHahnSolve m n t hmt htn y
  have hshell := shellSourcePrefix_transvect_form m n t r (m + 1)
    (fun q => q) x (fun q hq => by
      dsimp
      exact Nat.le_trans (Nat.lt_succ_iff.mp hq) hmt) (by omega) s
  have hrow := centralHahnSolve_rightInverse m n t hmt htn y r hr
  refine Q'.eqv_trans _
    (centralHahnAction m n t x r * mono (t - r) s) _ ?_ ?_
  · simpa only [centralShellSynth, x, centralHahnAction,
      centralHahnMatrix] using hshell
  · exact Q'.mul_eqv_congr_right _ _ _ hrow

/-- Unit data for one contraction channel. -/
def centralChannelUnit (q r : Nat) : Q' := if r = q then 1 else 0

/-- The actual source vector for the `q`-th central-shell channel. -/
def centralShellBasis (m n t : Nat) (hmt : m ≤ t) (htn : t ≤ n)
    (q : Nat) : BForm2 :=
  centralShellSynth m n t hmt htn (centralChannelUnit q)

/-- One theorem records both the target channel and every zero cross-channel:
the central-shell basis is leakage-free across the full direct sum. -/
theorem centralShellBasis_channels (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (q r : Nat)
    (hr : r < m + 1) :
    BFormEqv (transvect m n r (centralShellBasis m n t hmt htn q))
      (fun s => centralChannelUnit q r * mono (t - r) s) :=
  centralShellSynth_channels m n t hmt htn (centralChannelUnit q) r hr

/-- The selected active channel is exactly its shell output monomial. -/
theorem centralShellBasis_target (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (q : Nat)
    (hq : q < m + 1) :
    BFormEqv (transvect m n q (centralShellBasis m n t hmt htn q))
      (mono (t - q)) := by
  intro s
  have h := centralShellBasis_channels m n t hmt htn q q hq s
  refine Q'.eqv_trans _ (1 * mono (t - q) s) _ ?_ ?_
  · simpa only [centralChannelUnit, if_pos] using h
  · exact Q'.one_mul_eqv _

/-- Every other active contraction order vanishes as a complete output form. -/
theorem centralShellBasis_noLeak (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) (q r : Nat)
    (hr : r < m + 1) (hrq : ¬ r = q) :
    BFormEqv (transvect m n r (centralShellBasis m n t hmt htn q)) zeroF := by
  intro s
  have h := centralShellBasis_channels m n t hmt htn q r hr s
  refine Q'.eqv_trans _ (0 * mono (t - r) s) _ ?_ ?_
  · simpa only [centralChannelUnit, if_neg hrq] using h
  · exact Q'.zero_mul_eqv _

end YMGap.Continuum.SU2GeneralHahnCentralShellBasis

#print axioms YMGap.Continuum.SU2GeneralHahnCentralShellBasis.shellSourcePrefix_transvect_form
#print axioms YMGap.Continuum.SU2GeneralHahnCentralShellBasis.centralShellSynth_channels
#print axioms YMGap.Continuum.SU2GeneralHahnCentralShellBasis.centralShellBasis_target
#print axioms YMGap.Continuum.SU2GeneralHahnCentralShellBasis.centralShellBasis_noLeak
