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

The decomposition is an identity, but no uniform termwise sign is available.
At the exact scout point `s=6`, `w=1/4`, `h=wH=1/2`, some mixed minors are
positive and some are negative.  Thus propagation requires aggregation rather
than a common-sign TP2 argument.  The residual is also identified exactly as
the one-step difference of a shifted-offset determinant potential.

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

/-- The same numerator product at an arbitrary offset `r`. -/
def offsetA (w : Q') (s r : Nat) : Q' :=
  modeWindow w s r * modeWindow w s (r + 2)

/-- The same midpoint square at an arbitrary offset `r`. -/
def offsetM (w : Q') (s r : Nat) : Q' :=
  modeWindow w s (r + 1) * modeWindow w s (r + 1)

theorem crossA_eq_offsetA (w : Q') (s : Nat) : crossA w s = offsetA w s 1 := by
  rfl

theorem crossM_eq_offsetM (w : Q') (s : Nat) : crossM w s = offsetM w s 1 := by
  rfl

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

/-- Four numerator components for the arbitrary-offset recurrence. -/
def aComponentAt (w : Q') (s r i : Nat) : Q' :=
  match i with
  | 0 => modeWindow w s (r + 1) * modeWindow w s (r + 3)
  | 1 => modeWindow w s (r + 1) * boundaryTerm w s (r + 2)
  | 2 => boundaryTerm w s r * modeWindow w s (r + 3)
  | _ => boundaryTerm w s r * boundaryTerm w s (r + 2)

/-- Three midpoint components for the arbitrary-offset recurrence. -/
def mComponentAt (w : Q') (s r j : Nat) : Q' :=
  match j with
  | 0 => modeWindow w s (r + 2) * modeWindow w s (r + 2)
  | 1 => modeWindow w s (r + 2) * boundaryTerm w s (r + 1)
      + modeWindow w s (r + 2) * boundaryTerm w s (r + 1)
  | _ => boundaryTerm w s (r + 1) * boundaryTerm w s (r + 1)

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

/-- Arbitrary-offset numerator recurrence as four components. -/
theorem offsetA_succ_components (w : Q') (s r : Nat) :
    offsetA w (s + 1) r ≈ fsum (aComponentAt w s r) 4 := by
  unfold offsetA
  simp only [modeWindow_succ_eq]
  rw [show r + 2 + 1 = r + 3 by omega]
  refine Q'.eqv_trans _ _ _
    (mul_two_by_two (modeWindow w s (r + 1)) (boundaryTerm w s r)
      (modeWindow w s (r + 3)) (boundaryTerm w s (r + 2))) ?_
  simp only [fsum_succ, fsum_zero, aComponentAt]
  exact Q'.eqv_symm (zero_add_four _ _ _ _)

/-- Arbitrary-offset midpoint recurrence as three components. -/
theorem offsetM_succ_components (w : Q') (s r : Nat) :
    offsetM w (s + 1) r ≈ fsum (mComponentAt w s r) 3 := by
  unfold offsetM
  simp only [modeWindow_succ_eq]
  rw [show r + 1 + 1 = r + 2 by omega]
  refine Q'.eqv_trans _ _ _
    (sq_two (modeWindow w s (r + 2)) (boundaryTerm w s (r + 1))) ?_
  simp only [fsum_succ, fsum_zero, mComponentAt]
  exact Q'.eqv_symm (zero_add_three _ _ _)

/-! ## 3. Endpoint determinant as twelve exact mixed minors -/

/-- Oriented determinant `A(w)M(h)-M(w)A(h)`. -/
def determinant (Aw Ah Mw Mh : Q') : Q' :=
  Aw * Mh + -(Mw * Ah)

/-- The endpoint-scaled Core-B determinant at level `s`. -/
def crossDelta (w h : Q') (s : Nat) : Q' :=
  determinant (crossA w s) (crossA h s) (crossM w s) (crossM h s)

/-- The endpoint determinant at arbitrary offset `r`. -/
def offsetDelta (w h : Q') (s r : Nat) : Q' :=
  determinant (offsetA w s r) (offsetA h s r) (offsetM w s r) (offsetM h s r)

theorem crossDelta_eq_offsetDelta (w h : Q') (s : Nat) :
    crossDelta w h s = offsetDelta w h s 1 := by
  rfl

/-- The `(i,j)` minor between numerator component `i` and midpoint component
`j`, evaluated in the two coupling variables `w,h`. -/
def mixedMinor (w h : Q') (s i j : Nat) : Q' :=
  determinant (aComponent w s i) (aComponent h s i)
    (mComponent w s j) (mComponent h s j)

/-- All four-by-three component minors. -/
def mixedMinorSum (w h : Q') (s : Nat) : Q' :=
  fsum (fun i => fsum (fun j => mixedMinor w h s i j) 3) 4

/-- Arbitrary-offset component minor. -/
def mixedMinorAt (w h : Q') (s r i j : Nat) : Q' :=
  determinant (aComponentAt w s r i) (aComponentAt h s r i)
    (mComponentAt w s r j) (mComponentAt h s r j)

/-- The four-by-three minor sum at arbitrary offset. -/
def mixedMinorSumAt (w h : Q') (s r : Nat) : Q' :=
  fsum (fun i => fsum (fun j => mixedMinorAt w h s r i j) 3) 4

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

/-- Arbitrary-offset version of the twelve-minor determinant recurrence. -/
theorem offsetDelta_succ_mixedMinorSumAt (w h : Q') (s r : Nat) :
    offsetDelta w h (s + 1) r ≈ mixedMinorSumAt w h s r := by
  unfold offsetDelta mixedMinorSumAt mixedMinorAt
  have hAw := offsetA_succ_components w s r
  have hAh := offsetA_succ_components h s r
  have hMw := offsetM_succ_components w s r
  have hMh := offsetM_succ_components h s r
  refine Q'.eqv_trans _ _ _ ?_
    (determinant_fsum (aComponentAt w s r) (aComponentAt h s r)
      (mComponentAt w s r) (mComponentAt h s r) 4 3)
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

/-- The eleven-term residual at arbitrary offset. -/
def boundaryResidualAt (w h : Q') (s r : Nat) : Q' :=
  mixedMinorAt w h s r 0 1 + mixedMinorAt w h s r 0 2
    + mixedMinorAt w h s r 1 0 + mixedMinorAt w h s r 1 1
    + mixedMinorAt w h s r 1 2 + mixedMinorAt w h s r 2 0
    + mixedMinorAt w h s r 2 1 + mixedMinorAt w h s r 2 2
    + mixedMinorAt w h s r 3 0 + mixedMinorAt w h s r 3 1
    + mixedMinorAt w h s r 3 2

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

/-- Arbitrary-offset split into its first minor and eleven-term residual. -/
theorem mixedMinorSumAt_eq_first_add_residual (w h : Q') (s r : Nat) :
    mixedMinorSumAt w h s r ≈
      mixedMinorAt w h s r 0 0 + boundaryResidualAt w h s r := by
  unfold mixedMinorSumAt boundaryResidualAt
  simp only [fsum_succ, fsum_zero]
  exact split_twelve
    (mixedMinorAt w h s r 0 0) (mixedMinorAt w h s r 0 1)
    (mixedMinorAt w h s r 0 2) (mixedMinorAt w h s r 1 0)
    (mixedMinorAt w h s r 1 1) (mixedMinorAt w h s r 1 2)
    (mixedMinorAt w h s r 2 0) (mixedMinorAt w h s r 2 1)
    (mixedMinorAt w h s r 2 2) (mixedMinorAt w h s r 3 0)
    (mixedMinorAt w h s r 3 1) (mixedMinorAt w h s r 3 2)

/-- The first component minor is exactly the determinant potential at the next
offset. -/
theorem mixedMinorAt_zero_zero_eq_shifted (w h : Q') (s r : Nat) :
    mixedMinorAt w h s r 0 0 = offsetDelta w h s (r + 1) := by
  unfold mixedMinorAt aComponentAt mComponentAt offsetDelta offsetA offsetM
  rw [show r + 3 = r + 1 + 2 by omega]

/-- The endpoint determinant recurrence with its inherited term isolated. -/
theorem crossDelta_succ_eq_inherited_add_residual (w h : Q') (s : Nat) :
    crossDelta w h (s + 1) ≈ inheritedMinor w h s + boundaryResidual w h s :=
  Q'.eqv_trans _ _ _ (crossDelta_succ_mixedMinorSum w h s)
    (mixedMinorSum_eq_inherited_add_residual w h s)

/-- **Shifted-potential recurrence.**  The next range/offset determinant is the
next-offset potential plus the eleven-minor residual. -/
theorem offsetDelta_succ_eq_shifted_add_residual (w h : Q') (s r : Nat) :
    offsetDelta w h (s + 1) r ≈
      offsetDelta w h s (r + 1) + boundaryResidualAt w h s r := by
  refine Q'.eqv_trans _ _ _ (offsetDelta_succ_mixedMinorSumAt w h s r) ?_
  refine Q'.eqv_trans _ _ _ (mixedMinorSumAt_eq_first_add_residual w h s r) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (by rw [mixedMinorAt_zero_zero_eq_shifted]; exact Q'.eqv_refl _)

private def cancelPotentialL : RingNormaliser.PolyExpr :=
  .add (.add (.var 0) (.var 1)) (.neg (.var 0))

private theorem cancelPotential_normal : RingNormaliser.normalize cancelPotentialL =
    RingNormaliser.normalize (.var 1) := by decide

private theorem cancel_potential (a b : Q') : (a + b) + -a ≈ b := by
  have hn := RingNormaliser.poly_identity_of_normal_eq cancelPotentialL (.var 1)
    cancelPotential_normal (fun n => if n = 0 then a else b)
  simpa [RingNormaliser.eval, cancelPotentialL] using hn

/-- **Exact one-step potential difference.**  The eleven-minor residual is
precisely `D_(s+1,r) - D_(s,r+1)` modulo rational equivalence. -/
theorem boundaryResidualAt_eq_potential_difference (w h : Q') (s r : Nat) :
    boundaryResidualAt w h s r ≈
      offsetDelta w h (s + 1) r + -(offsetDelta w h s (r + 1)) := by
  let D := offsetDelta w h (s + 1) r
  let P := offsetDelta w h s (r + 1)
  let R := boundaryResidualAt w h s r
  have hrec : D ≈ P + R := offsetDelta_succ_eq_shifted_add_residual w h s r
  have hsub : D + -P ≈ (P + R) + -P :=
    Q'.add_eqv_congr_right _ _ (-P) hrec
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hsub (cancel_potential P R))

/-- Residuals accumulated along the diagonal path
`(s+n,r) → (s+n-1,r+1) → ⋯ → (s,r+n)`. -/
def cumulativeResidual (w h : Q') (s r : Nat) : Nat → Q'
  | 0 => 0
  | n + 1 => cumulativeResidual w h s (r + 1) n
      + boundaryResidualAt w h (s + n) r

/-- **Finite diagonal telescope.**  Every range shift is exactly a terminal
offset potential plus the cumulative boundary residual along the diagonal. -/
theorem offsetDelta_diagonal_telescope (w h : Q') (s r : Nat) : ∀ n,
    offsetDelta w h (s + n) r ≈
      offsetDelta w h s (r + n) + cumulativeResidual w h s r n
  | 0 => Q'.eqv_symm (q_add_zero_eqv (offsetDelta w h s r))
  | n + 1 => by
      rw [show s + (n + 1) = (s + n) + 1 by omega]
      rw [show r + (n + 1) = (r + 1) + n by omega]
      simp only [cumulativeResidual]
      have hrec := offsetDelta_succ_eq_shifted_add_residual w h (s + n) r
      have ih := offsetDelta_diagonal_telescope w h s (r + 1) n
      refine Q'.eqv_trans _ _ _ hrec ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (boundaryResidualAt w h (s + n) r) ih) ?_
      exact Q'.add_assoc_eqv _ _ _

/-! ## 5. A cancellation pairing and exact `s=6` scout -/

/-- A pairing of the five positive-at-the-scout candidates with five adverse
components, leaving the pure boundary minor as the sixth group. -/
def pairedBoundaryResidual (w h : Q') (s : Nat) : Q' :=
  (mixedMinor w h s 0 1 + mixedMinor w h s 1 0)
    + (mixedMinor w h s 0 2 + mixedMinor w h s 2 0)
    + (mixedMinor w h s 1 1 + mixedMinor w h s 3 0)
    + (mixedMinor w h s 1 2 + mixedMinor w h s 2 1)
    + (mixedMinor w h s 2 2 + mixedMinor w h s 3 1)
    + mixedMinor w h s 3 2

private def add6E (a b c d e f : RingNormaliser.PolyExpr) : RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.add a b) c) d) e) f

private def pair11L : RingNormaliser.PolyExpr :=
  add11E (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)
    (.var 6) (.var 7) (.var 8) (.var 9) (.var 10)

private def pair11R : RingNormaliser.PolyExpr :=
  add6E (.add (.var 0) (.var 2)) (.add (.var 1) (.var 5))
    (.add (.var 3) (.var 8)) (.add (.var 4) (.var 6))
    (.add (.var 7) (.var 9)) (.var 10)

private theorem pair11_normal : RingNormaliser.normalize pair11L =
    RingNormaliser.normalize pair11R := by decide

/-- The pairing is a pure reassociation of the exact eleven-term residual. -/
theorem boundaryResidual_eq_paired (w h : Q') (s : Nat) :
    boundaryResidual w h s ≈ pairedBoundaryResidual w h s := by
  have hn := RingNormaliser.poly_identity_of_normal_eq pair11L pair11R pair11_normal
    (fun n => match n with
      | 0 => mixedMinor w h s 0 1 | 1 => mixedMinor w h s 0 2
      | 2 => mixedMinor w h s 1 0 | 3 => mixedMinor w h s 1 1
      | 4 => mixedMinor w h s 1 2 | 5 => mixedMinor w h s 2 0
      | 6 => mixedMinor w h s 2 1 | 7 => mixedMinor w h s 2 2
      | 8 => mixedMinor w h s 3 0 | 9 => mixedMinor w h s 3 1
      | _ => mixedMinor w h s 3 2)
  simpa [RingNormaliser.eval, pair11L, pair11R, add6E, add11E,
    boundaryResidual, pairedBoundaryResidual] using hn

/-- An exact interior scout point, strictly below `wH`. -/
def wQuarter : Q' := Q'.mkPos 1 4 (by decide)

/-- A second exact interior point used to test whether the scout pairing is
uniform in the coupling. -/
def wThird : Q' := Q'.mkPos 1 3 (by decide)

/-- The pure-boundary residual minor

`det(E_1 E_3, E_2^2)`

is strictly negative at `s=6`, `w=1/4`, `h=1/2`. -/
theorem s6_pure_boundary_minor_negative :
    ¬ ((0 : Q') ≤ mixedMinor wQuarter wH 6 3 2) := by
  set_option maxRecDepth 100000 in
    decide

/-- **Common-sign fence.**  In the endpoint-inequality orientation the desired
sign is nonpositive, but component `(1,2)` is strictly positive at the same
exact scout point. -/
theorem s6_mixed_minor_positive :
    ¬ (mixedMinor wQuarter wH 6 1 2 ≤ (0 : Q')) := by
  set_option maxRecDepth 100000 in
    decide

/-- All six proposed cancellation groups are nonpositive at the exact scout. -/
theorem s6_pairing_certificate :
    (mixedMinor wQuarter wH 6 0 1 + mixedMinor wQuarter wH 6 1 0 ≤ (0 : Q')) ∧
    (mixedMinor wQuarter wH 6 0 2 + mixedMinor wQuarter wH 6 2 0 ≤ (0 : Q')) ∧
    (mixedMinor wQuarter wH 6 1 1 + mixedMinor wQuarter wH 6 3 0 ≤ (0 : Q')) ∧
    (mixedMinor wQuarter wH 6 1 2 + mixedMinor wQuarter wH 6 2 1 ≤ (0 : Q')) ∧
    (mixedMinor wQuarter wH 6 2 2 + mixedMinor wQuarter wH 6 3 1 ≤ (0 : Q')) ∧
    (mixedMinor wQuarter wH 6 3 2 ≤ (0 : Q')) := by
  set_option maxRecDepth 100000 in
    decide

private theorem add_nonpos {a b : Q'} (ha : a ≤ (0 : Q')) (hb : b ≤ (0 : Q')) :
    a + b ≤ (0 : Q') :=
  Q'.le_trans' _ _ _ (Q'.add_le_add ha hb) (by decide)

/-- The paired cancellation proves the full eleven-minor residual nonpositive
at the scout; unlike a direct closed calculation, this records the aggregate
mechanism being tested. -/
theorem s6_boundaryResidual_nonpos :
    boundaryResidual wQuarter wH 6 ≤ (0 : Q') := by
  rcases s6_pairing_certificate with ⟨h1, h2, h3, h4, h5, h6⟩
  have hp : pairedBoundaryResidual wQuarter wH 6 ≤ (0 : Q') :=
    add_nonpos (add_nonpos (add_nonpos (add_nonpos (add_nonpos h1 h2) h3) h4) h5) h6
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (boundaryResidual_eq_paired wQuarter wH 6)) hp

/-- **Pairing fence.**  The six-group pairing is not uniform even at fixed
`s=6`: at `w=1/3`, its third group `(1,1)+(3,0)` is strictly positive.  Thus
the pairing is useful as a cancellation scout at `w=1/4`, but cannot serve as
the all-`w` proof without a different regrouping. -/
theorem s6_pairing_not_uniform :
    ¬ (mixedMinor wThird wH 6 1 1 + mixedMinor wThird wH 6 3 0 ≤ (0 : Q')) := by
  set_option maxRecDepth 100000 in
    decide

#print axioms modeWindow_succ_eq
#print axioms crossA_succ_components
#print axioms crossM_succ_components
#print axioms offsetA_succ_components
#print axioms offsetM_succ_components
#print axioms determinant_fsum
#print axioms crossDelta_succ_mixedMinorSum
#print axioms offsetDelta_succ_mixedMinorSumAt
#print axioms crossDelta_succ_eq_inherited_add_residual
#print axioms offsetDelta_succ_eq_shifted_add_residual
#print axioms boundaryResidualAt_eq_potential_difference
#print axioms offsetDelta_diagonal_telescope
#print axioms boundaryResidual_eq_paired
#print axioms s6_pure_boundary_minor_negative
#print axioms s6_mixed_minor_positive
#print axioms s6_pairing_certificate
#print axioms s6_boundaryResidual_nonpos
#print axioms s6_pairing_not_uniform

end YMGap.Continuum.CoreBStructuralRecurrence
