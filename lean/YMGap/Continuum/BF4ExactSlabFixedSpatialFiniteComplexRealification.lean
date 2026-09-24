/-
# The finite reflected form on the realification of a complex pair

This is the direct sum of two copies of the actual rational finite reflected
form.  Keeping the direct sum explicit prevents the spurious cross terms that
would be introduced by appending the two physical spans.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
  (Span Within Physical scaleSpan within_scale physical_scale within_append physical_append)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] finitePairing

private theorem q_lt_of_not_ge {a b : Q'} (h : ¬ b ≤ a) : a < b := by
  exact Int.not_le.mp h

private theorem add_exchange (a b c d : Q') :
    (a+b)+(c+d) ≈ (a+c)+(b+d) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
    (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem direct_quad (s r a b c d e f : Q') :
    (s*s*a + 2*(s*r)*b + r*r*c) + (s*s*d + 2*(s*r)*e + r*r*f) ≈
      s*s*(a+d) + 2*(s*r)*(b+e) + r*r*(c+f) :=
  poly_identity_of_normal_eq
    (.add
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 3)))
        (.mul (.mul (.var 1) (.var 1)) (.var 4)))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 5))
          (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 6)))
        (.mul (.mul (.var 1) (.var 1)) (.var 7))))
    (.add
      (.add (.mul (.mul (.var 0) (.var 0)) (.add (.var 2) (.var 5)))
        (.mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
          (.add (.var 3) (.var 6))))
      (.mul (.mul (.var 1) (.var 1)) (.add (.var 4) (.var 7))))
    (by decide)
    (fun | 0 => s | 1 => r | 2 => a | 3 => b | 4 => c | 5 => d | 6 => e | _ => f)

private theorem neg_one_twice (a : Q') : (-1) * ((-1) * a) ≈ a :=
  poly_identity_of_normal_eq
    (.mul (.neg (.const 1)) (.mul (.neg (.const 1)) (.var 0)))
    (.var 0) (by decide) (fun _ => a)

private theorem mul_rotate (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => a | 1 => b | _ => c)

/-- Direct sum of two rational pre-inner forms. -/
def directSumPreInnerForm {V W : Type} (F : PreInnerForm V)
    (G : PreInnerForm W) : PreInnerForm (V × W) where
  B x y := F.B x.1 y.1 + G.B x.2 y.2
  nonnegQuad := by
    intro s r x y
    have hF := F.nonnegQuad s r x.1 y.1
    have hG := G.nonnegQuad s r x.2 y.2
    have h := Q'.zero_le_add _ _ hF hG
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (direct_quad s r (F.B x.1 x.1) (F.B x.1 y.1) (F.B y.1 y.1)
        (G.B x.2 x.2) (G.B x.2 y.2) (G.B y.2 y.2)))

/-- The actual finite reflected form, realified as two independent copies. -/
def finiteRealifiedPreInnerForm {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width h stage t : Nat) :
    PreInnerForm
      (guardedSpan width h × guardedSpan width h) :=
  directSumPreInnerForm
    (finitePreInnerForm hw0 hw1 width h stage t)
    (finitePreInnerForm hw0 hw1 width h stage t)

/-- Sharp real Cauchy--Schwarz on the direct-sum carrier.  This is the exact
finite rational inequality used by the phase-aligned complex proof. -/
theorem finiteRealified_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (width h stage t : Nat)
    (x y : guardedSpan width h × guardedSpan width h) :
    let R := finiteRealifiedPreInnerForm hw0 hw1 width h stage t
    (R).B x y * (R).B x y ≤ (R).B x x * (R).B y y := by
  dsimp only
  exact (finiteRealifiedPreInnerForm hw0 hw1 width h stage t).cauchy_schwarz x y

variable {width h : Nat}

def guardedSmul (c : Q') (x : guardedSpan width h) : guardedSpan width h :=
  ⟨scaleSpan c x.val, within_scale c x.property.1, physical_scale c x.property.2⟩

def guardedAdd (x y : guardedSpan width h) : guardedSpan width h :=
  ⟨x.val ++ y.val, within_append x.property.1 y.property.1,
    physical_append x.property.2 y.property.2⟩

def realifiedSmul (c : Q')
    (x : guardedSpan width h × guardedSpan width h) :=
  (guardedSmul c x.1, guardedSmul c x.2)

def realifiedAdd (x y : guardedSpan width h × guardedSpan width h) :=
  (guardedAdd x.1 y.1, guardedAdd x.2 y.2)

/-- Multiplication by `i` on the rational realification. -/
def quarterTurn (x : guardedSpan width h × guardedSpan width h) :=
  (guardedSmul (-1) x.2, x.1)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width h stage t : Nat)

local notation "R" => finiteRealifiedPreInnerForm hw0 hw1 width h stage t

theorem realified_add_right
    (x y z : guardedSpan width h × guardedSpan width h) :
    (R).B x (realifiedAdd y z) ≈ (R).B x y + (R).B x z := by
  dsimp [finiteRealifiedPreInnerForm, directSumPreInnerForm, realifiedAdd,
    guardedAdd, finitePreInnerForm]
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finite_add_right hw0 hw1 width h stage t x.1.val y.1.val z.1.val)
      (finite_add_right hw0 hw1 width h stage t x.2.val y.2.val z.2.val))
    (add_exchange _ _ _ _)

theorem realified_smul_right (c : Q')
    (x y : guardedSpan width h × guardedSpan width h) :
    (R).B x (realifiedSmul c y) ≈ c * (R).B x y := by
  dsimp [finiteRealifiedPreInnerForm, directSumPreInnerForm, realifiedSmul,
    guardedSmul, finitePreInnerForm]
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (finite_smul_right hw0 hw1 width h stage t c x.1.val y.1.val)
      (finite_smul_right hw0 hw1 width h stage t c x.2.val y.2.val))
    (Q'.eqv_symm (Q'.mul_add_eqv c _ _))

theorem realified_symm
    (x y : guardedSpan width h × guardedSpan width h) :
    (R).B x y ≈ (R).B y x := by
  dsimp [finiteRealifiedPreInnerForm, directSumPreInnerForm, finitePreInnerForm]
  exact Q'.add_eqv_congr'
    (finite_symm hw0 hw1 width h stage t x.1.val y.1.val
      x.1.property.1 y.1.property.1 x.1.property.2 y.1.property.2)
    (finite_symm hw0 hw1 width h stage t x.2.val y.2.val
      x.2.property.1 y.2.property.1 x.2.property.2 y.2.property.2)

theorem realified_add_left
    (x y z : guardedSpan width h × guardedSpan width h) :
    (R).B (realifiedAdd x y) z ≈ (R).B x z + (R).B y z := by
  exact Q'.eqv_trans _ _ _ (realified_symm hw0 hw1 width h stage t _ _)
    (Q'.eqv_trans _ _ _ (realified_add_right hw0 hw1 width h stage t _ _ _)
      (Q'.add_eqv_congr'
        (realified_symm hw0 hw1 width h stage t _ _)
        (realified_symm hw0 hw1 width h stage t _ _)))

theorem realified_smul_left (c : Q')
    (x y : guardedSpan width h × guardedSpan width h) :
    (R).B (realifiedSmul c x) y ≈ c * (R).B x y := by
  exact Q'.eqv_trans _ _ _ (realified_symm hw0 hw1 width h stage t _ _)
    (Q'.eqv_trans _ _ _ (realified_smul_right hw0 hw1 width h stage t c _ _)
      (Q'.mul_eqv_congr_left c _ _
        (realified_symm hw0 hw1 width h stage t _ _)))

theorem quarterTurn_orthogonal
    (y : guardedSpan width h × guardedSpan width h) :
    (R).B y (quarterTurn y) ≈ 0 := by
  dsimp [finiteRealifiedPreInnerForm, directSumPreInnerForm, quarterTurn,
    guardedSmul, finitePreInnerForm]
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (finite_smul_right hw0 hw1 width h stage t (-1) y.1.val y.2.val)
    (Q'.eqv_refl _)) ?_
  have hs := finite_symm hw0 hw1 width h stage t y.2.val y.1.val
    y.2.property.1 y.1.property.1 y.2.property.2 y.1.property.2
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hs) ?_
  have hneg : (-1) * finitePairing hw0 hw1 width h stage t y.1.val y.2.val ≈
      -(finitePairing hw0 hw1 width h stage t y.1.val y.2.val) := by
    exact Q'.eqv_trans _ _ _
      (Q'.neg_mul_eqv 1 (finitePairing hw0 hw1 width h stage t y.1.val y.2.val))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hneg)
    (Q'.neg_add_self_eqv _)

theorem quarterTurn_norm
    (y : guardedSpan width h × guardedSpan width h) :
    (R).B (quarterTurn y) (quarterTurn y) ≈ (R).B y y := by
  dsimp [finiteRealifiedPreInnerForm, directSumPreInnerForm, quarterTurn,
    guardedSmul, finitePreInnerForm]
  have h1 := Q'.eqv_trans _ _ _
    (finite_smul_left hw0 hw1 width h stage t (-1)
      y.2.val (scaleSpan (-1) y.2.val))
    (Q'.mul_eqv_congr_left (-1) _ _
      (finite_smul_right hw0 hw1 width h stage t (-1) y.2.val y.2.val))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' h1 (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (neg_one_twice _) (Q'.eqv_refl _))
      (Q'.add_comm_eqv _ _))

/-- The phase-aligned vector uses only rational scalars computed at this same
finite stage. -/
def phaseVector (x y : guardedSpan width h × guardedSpan width h) :=
  realifiedAdd (realifiedSmul ((R).B x y) y)
    (realifiedSmul ((R).B x (quarterTurn y)) (quarterTurn y))

theorem phase_pairing (x y : guardedSpan width h × guardedSpan width h) :
    (R).B x (phaseVector hw0 hw1 width h stage t x y) ≈
      (R).B x y * (R).B x y +
        (R).B x (quarterTurn y) * (R).B x (quarterTurn y) := by
  unfold phaseVector
  exact Q'.eqv_trans _ _ _ (realified_add_right hw0 hw1 width h stage t _ _ _)
    (Q'.add_eqv_congr'
      (realified_smul_right hw0 hw1 width h stage t _ _ _)
      (realified_smul_right hw0 hw1 width h stage t _ _ _))

theorem phase_norm (x y : guardedSpan width h × guardedSpan width h) :
    (R).B (phaseVector hw0 hw1 width h stage t x y)
        (phaseVector hw0 hw1 width h stage t x y) ≈
      ((R).B x y * (R).B x y +
          (R).B x (quarterTurn y) * (R).B x (quarterTurn y)) * (R).B y y := by
  let a := (R).B x y
  let b := (R).B x (quarterTurn y)
  let jy := quarterTurn y
  let ay := realifiedSmul a y
  let bj := realifiedSmul b jy
  have haa : (R).B ay ay ≈ a*a*(R).B y y := by
    exact Q'.eqv_trans _ _ _ (realified_smul_left hw0 hw1 width h stage t a y ay)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _
        (realified_smul_right hw0 hw1 width h stage t a y y))
        (Q'.eqv_symm (Q'.mul_assoc_eqv a a ((R).B y y))))
  have hab : (R).B ay bj ≈ 0 := by
    refine Q'.eqv_trans _ _ _ (realified_smul_left hw0 hw1 width h stage t a y bj) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _
      (realified_smul_right hw0 hw1 width h stage t b y jy)) ?_
    refine Q'.eqv_trans _ ((a*b) * (R).B y jy) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv a b ((R).B y jy))) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a*b) _ _ (quarterTurn_orthogonal hw0 hw1 width h stage t y))
      (QPoly.q_mul_zero (a*b))
  have hbb : (R).B bj bj ≈ b*b*(R).B y y := by
    refine Q'.eqv_trans _ _ _ (realified_smul_left hw0 hw1 width h stage t b jy bj) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left b _ _
      (realified_smul_right hw0 hw1 width h stage t b jy jy)) ?_
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv b b ((R).B jy jy)))
      (Q'.mul_eqv_congr_left (b*b) _ _ (quarterTurn_norm hw0 hw1 width h stage t y))
  unfold phaseVector
  refine Q'.eqv_trans _ _ _ (realified_add_left hw0 hw1 width h stage t ay bj
    (realifiedAdd ay bj)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (realified_add_right hw0 hw1 width h stage t ay ay bj)
    (realified_add_right hw0 hw1 width h stage t bj ay bj)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (Q'.add_eqv_congr' haa hab)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (realified_symm hw0 hw1 width h stage t bj ay) hab)
      hbb)) ?_
  dsimp only [a, b]
  let A := (R).B x y * (R).B x y * (R).B y y
  let C := (R).B x (quarterTurn y) * (R).B x (quarterTurn y) * (R).B y y
  refine Q'.eqv_trans _ (A + C) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (QPoly.q_add_zero_eqv A)
        (QPoly.q_zero_add_eqv C))
      (Q'.eqv_refl _)
  · exact Q'.eqv_symm
      (Q'.add_mul_eqv
        ((R).B x y * (R).B x y)
        ((R).B x (quarterTurn y) * (R).B x (quarterTurn y))
        ((R).B y y))

/-- Sharp complex Cauchy--Schwarz at the actual finite rational reflected
stage.  The imaginary coordinate is pairing with the quarter-turn. -/
theorem finiteComplex_cauchySchwarz
    (x y : guardedSpan width h × guardedSpan width h) :
    (R).B x y * (R).B x y +
        (R).B x (quarterTurn y) * (R).B x (quarterTurn y) ≤
      (R).B x x * (R).B y y := by
  let L := (R).B x y * (R).B x y +
    (R).B x (quarterTurn y) * (R).B x (quarterTurn y)
  by_cases hLnonpos : L ≤ (0 : Q')
  · have hXY : (0 : Q') ≤ (R).B x x * (R).B y y :=
      Q'.mul_nonneg _ _ ((R).self_nonneg x) ((R).self_nonneg y)
    exact Q'.le_trans' _ _ _ hLnonpos hXY
  · have hLpos : (0 : Q') < L := q_lt_of_not_ge hLnonpos
    have hcs := finiteRealified_cauchySchwarz hw0 hw1 width h stage t x
      (phaseVector hw0 hw1 width h stage t x y)
    have hscaled : L*L ≤ L*((R).B x x * (R).B y y) := by
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (phase_pairing hw0 hw1 width h stage t x y))
          (Q'.mul_eqv_congr_left _ _ _
            (phase_pairing hw0 hw1 width h stage t x y))))
        (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left ((R).B x x) _ _
              (phase_norm hw0 hw1 width h stage t x y))
            (by dsimp only [L]; exact mul_rotate _ _ _))))
    exact Q'.le_of_mul_le_mul_left hscaled hLpos


end YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification.directSumPreInnerForm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification.finiteRealifiedPreInnerForm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification.finiteRealified_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFiniteComplexRealification.finiteComplex_cauchySchwarz
