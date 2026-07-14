/-
# Edgewise observable conjugation on the mixed SU(2) pentagon

This file upgrades final-chart observable agreement to an edgewise statement.
Each integral fusion chart is paired with an explicit exact rational inverse.
Observable actions are transported by conjugation along each edge; composition
of chart equivalences is literal composition of those conjugations.  The
kernel-checked mixed pentagon then proves that the long and short edgewise
transports agree on every final state.

This closes conjugation coherence for the existing `(2,2,1,1)` pentagon.
Arbitrary labels and arbitrary overlapping fusion trees remain open.
-/

import YMGap.Continuum.SU2MixedPentagonObservableCoherence

namespace YMGap.Continuum.SU2MixedPentagonEdgeConjugationCoherence

set_option maxHeartbeats 1000000
set_option maxRecDepth 18000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.SU2FourValentMatrixO4Response
open YMGap.Continuum.SU2FourValentFMoveObservableCovariance
open YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted
open YMGap.Continuum.SU2MixedPentagonObservableCoherence

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Semantic standard matrices -/

structure StdMat2 where
  a : Q'
  b : Q'
  c : Q'
  d : Q'

def stdOne : StdMat2 := ⟨1, 0, 0, 1⟩

def stdMul (M N : StdMat2) : StdMat2 :=
  ⟨M.a * N.a + M.b * N.c,
    M.a * N.b + M.b * N.d,
    M.c * N.a + M.d * N.c,
    M.c * N.b + M.d * N.d⟩

def stdApply (M : StdMat2) (x : Q' × Q') : Q' × Q' :=
  (M.a * x.1 + M.b * x.2, M.c * x.1 + M.d * x.2)

def StdMatEq (M N : StdMat2) : Prop :=
  M.a ≈ N.a ∧ M.b ≈ N.b ∧ M.c ≈ N.c ∧ M.d ≈ N.d

theorem stdApply_congr (M : StdMat2) {x y : Q' × Q'}
    (h : VecEq x y) : VecEq (stdApply M x) (stdApply M y) := by
  unfold VecEq stdApply
  exact ⟨QPoly.q_add_congr
      (Q'.mul_eqv_congr_left M.a _ _ h.1)
      (Q'.mul_eqv_congr_left M.b _ _ h.2),
    QPoly.q_add_congr
      (Q'.mul_eqv_congr_left M.c _ _ h.1)
      (Q'.mul_eqv_congr_left M.d _ _ h.2)⟩

theorem stdApply_matEq {M N : StdMat2} (h : StdMatEq M N)
    (x : Q' × Q') : VecEq (stdApply M x) (stdApply N x) := by
  unfold StdMatEq at h
  unfold VecEq stdApply
  exact ⟨QPoly.q_add_congr
      (Q'.mul_eqv_congr_right _ _ x.1 h.1)
      (Q'.mul_eqv_congr_right _ _ x.2 h.2.1),
    QPoly.q_add_congr
      (Q'.mul_eqv_congr_right _ _ x.1 h.2.2.1)
      (Q'.mul_eqv_congr_right _ _ x.2 h.2.2.2)⟩

theorem stdApply_mul (M N : StdMat2) (x : Q' × Q') :
    VecEq (stdApply (stdMul M N) x) (stdApply M (stdApply N x)) := by
  unfold VecEq stdApply stdMul
  constructor <;> ring_qeqv

theorem stdApply_one (x : Q' × Q') : VecEq (stdApply stdOne x) x := by
  unfold VecEq stdApply stdOne
  constructor <;> ring_qeqv

/-! ## Exact chart equivalences and composition -/

structure ChartEquiv2 where
  map : (Q' × Q') → (Q' × Q')
  inv : (Q' × Q') → (Q' × Q')
  map_congr : ∀ {x y}, VecEq x y → VecEq (map x) (map y)
  inv_congr : ∀ {x y}, VecEq x y → VecEq (inv x) (inv y)
  leftInv : ∀ x, VecEq (inv (map x)) x
  rightInv : ∀ x, VecEq (map (inv x)) x

def matrixChart (F Finv : StdMat2)
    (hleft : StdMatEq (stdMul Finv F) stdOne)
    (hright : StdMatEq (stdMul F Finv) stdOne) : ChartEquiv2 where
  map := stdApply F
  inv := stdApply Finv
  map_congr := stdApply_congr F
  inv_congr := stdApply_congr Finv
  leftInv := by
    intro x
    exact vecEq_trans (vecEq_symm (stdApply_mul Finv F x))
      (vecEq_trans (stdApply_matEq hleft x) (stdApply_one x))
  rightInv := by
    intro x
    exact vecEq_trans (vecEq_symm (stdApply_mul F Finv x))
      (vecEq_trans (stdApply_matEq hright x) (stdApply_one x))

def chartThen (C D : ChartEquiv2) : ChartEquiv2 where
  map := fun x => D.map (C.map x)
  inv := fun x => C.inv (D.inv x)
  map_congr := fun h => D.map_congr (C.map_congr h)
  inv_congr := fun h => C.inv_congr (D.inv_congr h)
  leftInv := by
    intro x
    exact vecEq_trans
      (C.inv_congr (D.leftInv (C.map x))) (C.leftInv x)
  rightInv := by
    intro x
    exact vecEq_trans
      (D.map_congr (C.rightInv (D.inv x))) (D.rightInv x)

def sixth : Q' := Q'.mkPos 1 6 (by decide)

def edge01Mat : StdMat2 := ⟨-2, 4, 1, 1⟩
def edge01InvMat : StdMat2 :=
  ⟨-sixth, 4 * sixth, sixth, 2 * sixth⟩

def edge12Mat : StdMat2 := stdOne
def edge12InvMat : StdMat2 := stdOne

def edge23Mat : StdMat2 := ⟨-1, 4, 1, 2⟩
def edge23InvMat : StdMat2 :=
  ⟨(-2) * sixth, 4 * sixth, sixth, sixth⟩

def edge04Mat : StdMat2 := ⟨6, 0, 0, 6⟩
def edge04InvMat : StdMat2 := ⟨sixth, 0, 0, sixth⟩

def edge43Mat : StdMat2 := stdOne
def edge43InvMat : StdMat2 := stdOne

theorem edge01_left : StdMatEq (stdMul edge01InvMat edge01Mat) stdOne := by
  unfold StdMatEq stdMul edge01InvMat edge01Mat stdOne sixth
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge01_right : StdMatEq (stdMul edge01Mat edge01InvMat) stdOne := by
  unfold StdMatEq stdMul edge01InvMat edge01Mat stdOne sixth
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge12_left : StdMatEq (stdMul edge12InvMat edge12Mat) stdOne := by
  unfold StdMatEq stdMul edge12InvMat edge12Mat stdOne
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge12_right : StdMatEq (stdMul edge12Mat edge12InvMat) stdOne := by
  unfold StdMatEq stdMul edge12InvMat edge12Mat stdOne
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge23_left : StdMatEq (stdMul edge23InvMat edge23Mat) stdOne := by
  unfold StdMatEq stdMul edge23InvMat edge23Mat stdOne sixth
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge23_right : StdMatEq (stdMul edge23Mat edge23InvMat) stdOne := by
  unfold StdMatEq stdMul edge23InvMat edge23Mat stdOne sixth
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge04_left : StdMatEq (stdMul edge04InvMat edge04Mat) stdOne := by
  unfold StdMatEq stdMul edge04InvMat edge04Mat stdOne sixth
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge04_right : StdMatEq (stdMul edge04Mat edge04InvMat) stdOne := by
  unfold StdMatEq stdMul edge04InvMat edge04Mat stdOne sixth
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge43_left : StdMatEq (stdMul edge43InvMat edge43Mat) stdOne := by
  unfold StdMatEq stdMul edge43InvMat edge43Mat stdOne
  exact ⟨by decide, by decide, by decide, by decide⟩
theorem edge43_right : StdMatEq (stdMul edge43Mat edge43InvMat) stdOne := by
  unfold StdMatEq stdMul edge43InvMat edge43Mat stdOne
  exact ⟨by decide, by decide, by decide, by decide⟩

def edge01Equiv : ChartEquiv2 :=
  matrixChart edge01Mat edge01InvMat edge01_left edge01_right
def edge12Equiv : ChartEquiv2 :=
  matrixChart edge12Mat edge12InvMat edge12_left edge12_right
def edge23Equiv : ChartEquiv2 :=
  matrixChart edge23Mat edge23InvMat edge23_left edge23_right
def edge04Equiv : ChartEquiv2 :=
  matrixChart edge04Mat edge04InvMat edge04_left edge04_right
def edge43Equiv : ChartEquiv2 :=
  matrixChart edge43Mat edge43InvMat edge43_left edge43_right

def longChartEquiv : ChartEquiv2 :=
  chartThen (chartThen edge01Equiv edge12Equiv) edge23Equiv

def shortChartEquiv : ChartEquiv2 := chartThen edge04Equiv edge43Equiv

theorem longChartEquiv_matches (x : Q' × Q') :
    VecEq (longChartEquiv.map x) (longChart x) := by
  unfold longChartEquiv chartThen edge01Equiv edge12Equiv edge23Equiv
    matrixChart stdApply edge01Mat edge12Mat edge23Mat stdOne
    longChart edge01Chart edge12Chart edge23Chart
  constructor <;> ring_qeqv

theorem shortChartEquiv_matches (x : Q' × Q') :
    VecEq (shortChartEquiv.map x) (shortChart x) := by
  unfold shortChartEquiv chartThen edge04Equiv edge43Equiv matrixChart
    stdApply edge04Mat edge43Mat stdOne shortChart edge04Chart edge43Chart
  constructor <;> ring_qeqv

theorem mixedPentagon_chart_map_coherent (x : Q' × Q') :
    VecEq (longChartEquiv.map x) (shortChartEquiv.map x) :=
  vecEq_trans (longChartEquiv_matches x)
    (vecEq_trans (mixedPentagon_state_eq x)
      (vecEq_symm (shortChartEquiv_matches x)))

/-- Equivalent bijective charts have equivalent inverses constructively. -/
theorem chart_inv_coherent (C D : ChartEquiv2)
    (hmap : ∀ x, VecEq (C.map x) (D.map x)) (x : Q' × Q') :
    VecEq (C.inv x) (D.inv x) := by
  have h₁ := C.inv_congr (vecEq_symm (D.rightInv x))
  have h₂ := C.inv_congr (vecEq_symm (hmap (D.inv x)))
  exact vecEq_trans h₁ (vecEq_trans h₂ (C.leftInv (D.inv x)))

theorem mixedPentagon_chart_inv_coherent (x : Q' × Q') :
    VecEq (longChartEquiv.inv x) (shortChartEquiv.inv x) :=
  chart_inv_coherent longChartEquiv shortChartEquiv
    mixedPentagon_chart_map_coherent x

/-! ## Edgewise conjugation coherence -/

def VecOp := (Q' × Q') → (Q' × Q')

def transportOp (C : ChartEquiv2) (O : VecOp) : VecOp :=
  fun x => C.map (O (C.inv x))

theorem transportOp_then (C D : ChartEquiv2) (O : VecOp)
    (x : Q' × Q') :
    transportOp (chartThen C D) O x =
      transportOp D (transportOp C O) x := rfl

theorem mixedPentagon_transport_coherent (M : IntertwinerMat2)
    (x : Q' × Q') :
    VecEq (transportOp longChartEquiv (matApply M) x)
      (transportOp shortChartEquiv (matApply M) x) := by
  unfold transportOp
  have h₁ := longChartEquiv.map_congr
    (matApply_congr M (mixedPentagon_chart_inv_coherent x))
  exact vecEq_trans h₁
    (mixedPentagon_chart_map_coherent
      (matApply M (shortChartEquiv.inv x)))

/-- The three-edge and two-edge conjugation composites agree pointwise. -/
theorem mixedPentagon_edgewise_conjugation_coherent
    (M : IntertwinerMat2) (x : Q' × Q') :
    VecEq
      (transportOp edge23Equiv
        (transportOp edge12Equiv
          (transportOp edge01Equiv (matApply M))) x)
      (transportOp edge43Equiv
        (transportOp edge04Equiv (matApply M)) x) := by
  change VecEq (transportOp longChartEquiv (matApply M) x)
    (transportOp shortChartEquiv (matApply M) x)
  exact mixedPentagon_transport_coherent M x

end YMGap.Continuum.SU2MixedPentagonEdgeConjugationCoherence

#print axioms YMGap.Continuum.SU2MixedPentagonEdgeConjugationCoherence.edge01Equiv
#print axioms YMGap.Continuum.SU2MixedPentagonEdgeConjugationCoherence.edge23Equiv
#print axioms YMGap.Continuum.SU2MixedPentagonEdgeConjugationCoherence.edge04Equiv
#print axioms YMGap.Continuum.SU2MixedPentagonEdgeConjugationCoherence.mixedPentagon_chart_inv_coherent
#print axioms YMGap.Continuum.SU2MixedPentagonEdgeConjugationCoherence.mixedPentagon_edgewise_conjugation_coherent
