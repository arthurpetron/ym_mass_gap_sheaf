/-
# Core-B structural range recurrence and endpoint-minor decomposition

This file records the exact range-growth identity behind the Core-B cross
products.  Put

  W_s(k,w) = acN w (s+1) (s+k),
  E_s(k,w) = coeffW w (s+1) * coeffW w k.

Then `W_(s+1)(k) = W_s(k+1) + E_s(k)`.  Consequently the pair requested by
the Core-B endpoint comparison,

  A_s = W_s(1) W_s(3),       M_s = W_s(2)^2,

has an exact four-component / three-component recurrence.  Expanding its
endpoint-scaled determinant gives twelve literal two-function minors: one
inherited window minor and eleven boundary or mixed minors.

The decomposition is an identity, but the hoped-for termwise TP2 sign is
false.  At the exact scout point `s=6`, `w=1/4`, `h=wH=1/2`, the pure-boundary
minor `(E_1 E_3, E_2^2)` has the wrong sign.  Thus this recurrence does not by
itself propagate the endpoint inequality via termwise total positivity; any
successful propagation must aggregate cancellations among the twelve minors.

All algebra is constructive `Q'` algebra.  The finite-sum determinant identity
uses only `fsum_mul_fsum`, `fsum_swap`, and the additive congruence lemmas; the
small binomial expansions and the final twelve-term reassociation are checked
by the existing reflective normaliser.
-/

import YMGap.Continuum.CoreBModeFive
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.CoreBStructuralRecurrence

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundF
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The all-`s` range-growth recurrence -/

/-- The range-`(s+1)` window at offset `k`. -/
def modeWindow (w : Q') (s k : Nat) : Q' :=
  acN w (s + 1) (s + k)

/-- The single summand added when the range grows from `s+1` to `s+2`. -/
def boundaryTerm (w : Q') (s k : Nat) : Q' :=
  coeffW w (s + 1) * coeffW w k

/-- The Core-B numerator product `A_s = W_s(1) W_s(3)`. -/
def crossA (w : Q') (s : Nat) : Q' :=
  modeWindow w s 1 * modeWindow w s 3

/-- The Core-B midpoint square `M_s = W_s(2)^2`. -/
def crossM (w : Q') (s : Nat) : Q' :=
  modeWindow w s 2 * modeWindow w s 2

/-- Growing an arbitrary `acN` range appends exactly its last summand. -/
theorem acN_range_succ_eq (w : Q') (n t : Nat) :
    acN w (n + 1) t =
      acN w n t + coeffW w n * coeffW w (t - n) := by
  rfl

/-- **The reusable recurrence:** `W_(s+1)(k) = W_s(k+1) + E_s(k)`. -/
theorem modeWindow_succ_eq (w : Q') (s k : Nat) :
    modeWindow w (s + 1) k = modeWindow w s (k + 1) + boundaryTerm w s k := by
  unfold modeWindow boundaryTerm
  rw [acN_range_succ_eq]
  rw [show s + 1 + k = s + (k + 1) by omega]
  rw [show s + (k + 1) - (s + 1) = k by omega]

/-! ## 2. Four numerator components and three midpoint components -/

/-- The four terms in `(W_s(2)+E_s(1))(W_s(4)+E_s(3))`. -/
def aComponent (w : Q') (s i : Nat) : Q' :=
  match i with
  | 0 => modeWindow w s 2 * modeWindow w s 4
  | 1 => modeWindow w s 2 * boundaryTerm w s 3
  | 2 => boundaryTerm w s 1 * modeWindow w s 4
  | _ => boundaryTerm w s 1 * boundaryTerm w s 3

/-- The three terms in `(W_s(3)+E_s(2))^2`; the middle component includes
both equal cross terms. -/
def mComponent (w : Q') (s j : Nat) : Q' :=
  match j with
  | 0 => modeWindow w s 3 * modeWindow w s 3
  | 1 => modeWindow w s 3 * boundaryTerm w s 2
      + modeWindow w s 3 * boundaryTerm w s 2
  | _ => boundaryTerm w s 2 * boundaryTerm w s 2

private def add3E (a b c : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (.add a b) c

private def add4E (a b c d : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (add3E a b c) d

private def mul22L : RingNormaliser.PolyExpr :=
  .mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))

private def mul22R : RingNormaliser.PolyExpr :=
  add4E (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 3))
    (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3))

private theorem mul22_normal : RingNormaliser.normalize mul22L =
    RingNormaliser.normalize mul22R := by decide

private theorem mul_two_by_two (a b c d : Q') :
    (a + b) * (c + d) ≈ a * c + a * d + b * c + b * d := by
  have hn := RingNormaliser.poly_identity_of_normal_eq mul22L mul22R mul22_normal
    (fun n => match n with | 0 => a | 1 => b | 2 => c | _ => d)
  simpa [RingNormaliser.eval, mul22L, mul22R, add3E, add4E] using hn

private def sq2L : RingNormaliser.PolyExpr :=
  .mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))

private def sq2R : RingNormaliser.PolyExpr :=
  add3E (.mul (.var 0) (.var 0))
    (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
    (.mul (.var 1) (.var 1))

private theorem sq2_normal : RingNormaliser.normalize sq2L =
    RingNormaliser.normalize sq2R := by decide

private theorem sq_two (a b : Q') :
    (a + b) * (a + b) ≈ a * a + (a * b + a * b) + b * b := by
  have hn := RingNormaliser.poly_identity_of_normal_eq sq2L sq2R sq2_normal
    (fun n => if n = 0 then a else b)
  simpa [RingNormaliser.eval, sq2L, sq2R, add3E] using hn

private theorem zero_add_three (a b c : Q') :
    (0 : Q') + a + b + c ≈ a + b + c := by
  have h0 : (0 : Q') + a ≈ a := q_zero_add_eqv a
  have h1 : ((0 : Q') + a) + b ≈ a + b :=
    Q'.add_eqv_congr_right _ _ b h0
  exact Q'.add_eqv_congr_right _ _ c h1

private theorem zero_add_four (a b c d : Q') :
    (0 : Q') + a + b + c + d ≈ a + b + c + d :=
  Q'.add_eqv_congr_right _ _ d (zero_add_three a b c)

/-- The numerator recurrence as a four-term finite sum. -/
theorem crossA_succ_components (w : Q') (s : Nat) :
    crossA w (s + 1) ≈ fsum (aComponent w s) 4 := by
  unfold crossA
  simp only [modeWindow_succ_eq]
  refine Q'.eqv_trans _ _ _
    (mul_two_by_two (modeWindow w s 2) (boundaryTerm w s 1)
      (modeWindow w s 4) (boundaryTerm w s 3)) ?_
  simp only [fsum_succ, fsum_zero, aComponent]
  exact Q'.eqv_symm (zero_add_four _ _ _ _)

/-- The midpoint recurrence as a three-term finite sum. -/
theorem crossM_succ_components (w : Q') (s : Nat) :
    crossM w (s + 1) ≈ fsum (mComponent w s) 3 := by
  unfold crossM
  simp only [modeWindow_succ_eq]
  refine Q'.eqv_trans _ _ _
    (sq_two (modeWindow w s 3) (boundaryTerm w s 2)) ?_
  simp only [fsum_succ, fsum_zero, mComponent]
  exact Q'.eqv_symm (zero_add_three _ _ _)

/-! ## 3. Endpoint determinant as twelve exact mixed minors -/

/-- Oriented determinant `A(w)M(h)-M(w)A(h)`. -/
def determinant (Aw Ah Mw Mh : Q') : Q' :=
  Aw * Mh + -(Mw * Ah)

/-- The endpoint-scaled Core-B determinant at level `s`. -/
def crossDelta (w h : Q') (s : Nat) : Q' :=
  determinant (crossA w s) (crossA h s) (crossM w s) (crossM h s)

/-- The `(i,j)` minor between numerator component `i` and midpoint component
`j`, evaluated in the two coupling variables `w,h`. -/
def mixedMinor (w h : Q') (s i j : Nat) : Q' :=
  determinant (aComponent w s i) (aComponent h s i)
    (mComponent w s j) (mComponent h s j)

/-- All four-by-three component minors. -/
def mixedMinorSum (w h : Q') (s : Nat) : Q' :=
  fsum (fun i => fsum (fun j => mixedMinor w h s i j) 3) 4

private theorem qmn_add (F G : Nat → Nat → Q') (m n : Nat) :
    (fsum (fun i => fsum (F i) n) m + fsum (fun i => fsum (G i) n) m) ≈
      fsum (fun i => fsum (fun j => F i j + G i j) n) m := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (fsum_add (fun i => fsum (F i) n) (fun i => fsum (G i) n) m)) ?_
  exact fsum_eqv_congr _ _
    (fun i => Q'.eqv_symm (fsum_add (F i) (G i) n)) m

private theorem qmn_neg (F : Nat → Nat → Q') (m n : Nat) :
    (-(fsum (fun i => fsum (F i) n) m)) ≈
      fsum (fun i => fsum (fun j => -(F i j)) n) m := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (fsum_neg (fun i => fsum (F i) n) m)) ?_
  exact fsum_eqv_congr _ _
    (fun i => Q'.eqv_symm (fsum_neg (F i) n)) m

/-- Determinant of two finite component sums is the double sum of their
pairwise oriented minors. -/
theorem determinant_fsum (a ah m mh : Nat → Q') (na nm : Nat) :
    determinant (fsum a na) (fsum ah na) (fsum m nm) (fsum mh nm) ≈
      fsum (fun i => fsum (fun j => determinant (a i) (ah i) (m j) (mh j)) nm) na := by
  unfold determinant
  have hAM := fsum_mul_fsum a mh na nm
  have hMA0 := fsum_mul_fsum m ah nm na
  have hMA : (fsum m nm * fsum ah na) ≈
      fsum (fun i => fsum (fun j => m j * ah i) nm) na :=
    Q'.eqv_trans _ _ _ hMA0
      (fsum_swap (fun j i => m j * ah i) nm na)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hAM (Q'.neg_eqv_congr _ _ hMA)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (qmn_neg (fun i j => m j * ah i) na nm)) ?_
  exact qmn_add (fun i j => a i * mh j) (fun i j => -(m j * ah i)) na nm

/-- **Exact determinant recurrence:** the level-`s+1` endpoint determinant is
the sum of the twelve component minors at level `s`. -/
theorem crossDelta_succ_mixedMinorSum (w h : Q') (s : Nat) :
    crossDelta w h (s + 1) ≈ mixedMinorSum w h s := by
  unfold crossDelta mixedMinorSum mixedMinor
  have hAw := crossA_succ_components w s
  have hAh := crossA_succ_components h s
  have hMw := crossM_succ_components w s
  have hMh := crossM_succ_components h s
  refine Q'.eqv_trans _ _ _ ?_
    (determinant_fsum (aComponent w s) (aComponent h s)
      (mComponent w s) (mComponent h s) 4 3)
  unfold determinant
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hAw)
      (Q'.mul_eqv_congr_left _ _ _ hMh))
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hMw)
        (Q'.mul_eqv_congr_left _ _ _ hAh)))

/-! ## 4. Inherited minor plus the eleven-term residual -/

/-- The leading `W_s(2)W_s(4)` versus `W_s(3)^2` minor. -/
def inheritedMinor (w h : Q') (s : Nat) : Q' :=
  mixedMinor w h s 0 0

/-- The eleven remaining boundary or mixed minors, in lexicographic order. -/
def boundaryResidual (w h : Q') (s : Nat) : Q' :=
  mixedMinor w h s 0 1 + mixedMinor w h s 0 2
    + mixedMinor w h s 1 0 + mixedMinor w h s 1 1 + mixedMinor w h s 1 2
    + mixedMinor w h s 2 0 + mixedMinor w h s 2 1 + mixedMinor w h s 2 2
    + mixedMinor w h s 3 0 + mixedMinor w h s 3 1 + mixedMinor w h s 3 2

private def add11E (a b c d e f g h i j k : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.add (.add (.add (.add (.add (.add a b) c) d) e) f) g) h) i) j) k

private def add12E (a b c d e f g h i j k l : RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr :=
  .add (add11E a b c d e f g h i j k) l

private def fsum3E (a b c : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (.add (.add (.const 0) a) b) c

private def split12L : RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.const 0)
    (fsum3E (.var 0) (.var 1) (.var 2)))
    (fsum3E (.var 3) (.var 4) (.var 5)))
    (fsum3E (.var 6) (.var 7) (.var 8)))
    (fsum3E (.var 9) (.var 10) (.var 11))

private def split12R : RingNormaliser.PolyExpr :=
  .add (.var 0)
    (add11E (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6)
      (.var 7) (.var 8) (.var 9) (.var 10) (.var 11))

private theorem split12_normal : RingNormaliser.normalize split12L =
    RingNormaliser.normalize split12R := by decide

private theorem split_twelve
    (a b c d e f g h i j k l : Q') :
    (0 : Q') + ((0 : Q') + a + b + c) + ((0 : Q') + d + e + f)
        + ((0 : Q') + g + h + i) + ((0 : Q') + j + k + l) ≈
      a + (b + c + d + e + f + g + h + i + j + k + l) := by
  have hn := RingNormaliser.poly_identity_of_normal_eq split12L split12R split12_normal
    (fun n => match n with
      | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f
      | 6 => g | 7 => h | 8 => i | 9 => j | 10 => k | _ => l)
  simpa [RingNormaliser.eval, split12L, split12R, add11E, add12E, fsum3E] using hn

/-- The twelve-minor sum splits into one inherited minor and the exact
eleven-minor residual. -/
theorem mixedMinorSum_eq_inherited_add_residual (w h : Q') (s : Nat) :
    mixedMinorSum w h s ≈ inheritedMinor w h s + boundaryResidual w h s := by
  unfold mixedMinorSum inheritedMinor boundaryResidual
  simp only [fsum_succ, fsum_zero]
  exact split_twelve
    (mixedMinor w h s 0 0) (mixedMinor w h s 0 1) (mixedMinor w h s 0 2)
    (mixedMinor w h s 1 0) (mixedMinor w h s 1 1) (mixedMinor w h s 1 2)
    (mixedMinor w h s 2 0) (mixedMinor w h s 2 1) (mixedMinor w h s 2 2)
    (mixedMinor w h s 3 0) (mixedMinor w h s 3 1) (mixedMinor w h s 3 2)

/-- The endpoint determinant recurrence with its inherited term isolated. -/
theorem crossDelta_succ_eq_inherited_add_residual (w h : Q') (s : Nat) :
    crossDelta w h (s + 1) ≈ inheritedMinor w h s + boundaryResidual w h s :=
  Q'.eqv_trans _ _ _ (crossDelta_succ_mixedMinorSum w h s)
    (mixedMinorSum_eq_inherited_add_residual w h s)

/-! ## 5. Exact `s=6` fence against termwise TP2 propagation -/

/-- An exact interior scout point, strictly below `wH`. -/
def wQuarter : Q' := Q'.mkPos 1 4 (by decide)

/-- **TP2 fence.**  The pure-boundary residual minor

`det(E_1 E_3, E_2^2)`

is strictly adverse at `s=6`, `w=1/4`, `h=1/2`.  This is component `(3,2)`,
one of the eleven terms in `boundaryResidual`, so the residual cannot be
proved nonnegative term-by-term in the desired determinant orientation. -/
theorem s6_pure_boundary_minor_negative :
    ¬ ((0 : Q') ≤ mixedMinor wQuarter wH 6 3 2) := by
  set_option maxRecDepth 100000 in
    decide

#print axioms modeWindow_succ_eq
#print axioms crossA_succ_components
#print axioms crossM_succ_components
#print axioms determinant_fsum
#print axioms crossDelta_succ_mixedMinorSum
#print axioms crossDelta_succ_eq_inherited_add_residual
#print axioms s6_pure_boundary_minor_negative

end YMGap.Continuum.CoreBStructuralRecurrence
