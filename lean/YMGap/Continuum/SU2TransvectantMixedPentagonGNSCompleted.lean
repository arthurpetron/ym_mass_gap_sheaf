/-
# The mixed transvectant pentagon on constructive GNS completions

The exact `(2,2,1,1)` Cayley-transvectant pentagon upstream is a matrix
identity between five physical fusion-path bases.  This file supplies the
independent positive forms and performs the completion descent.

We use denominator-free coefficient charts.  Relative to the physical path
coefficients their diagonal scale factors are

    P0 : (1,1)      P1 : (3,3)      P2 : (6,3)
    P3 : (6,12)     P4 : (6,12).

A harmless common factor `3` clears every channel weight.  The five GNS forms
are therefore

    P0 : diag(288,576)       P1=P2 : diag(24,192)
    P3=P4 : diag(8,16).

In these charts all five edge maps are integral:

    P0 -> P1 : (-2x+4y, x+y)       P1 -> P2 : identity
    P2 -> P3 : (-x+4y, x+2y)
    P0 -> P4 : (6x,6y)             P4 -> P3 : identity.

Every edge is proved to be a dense GNS isometry and is descended through the
Cauchy completion.  The long and short completed routes agree, because both
dense composites are exactly `(6x,6y)`.

Honest scope: this closes one genuinely mixed, non-fundamental pentagon on the
constructive completions.  Uniform all-label Gram formulas and arbitrary-tree
coherence remain the next residual.
-/

import YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted

namespace YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted

set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2SpinOneLabelWiredPentagon
open YMGap.Continuum.SU2TrivalentThetaRecoupling
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted

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
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

/-! ## Five exact path forms -/

private def p0a : GNSData := qWeightGNS 288 (by decide)
private def p0b : GNSData := qWeightGNS 576 (by decide)
private def p1a : GNSData := qWeightGNS 24 (by decide)
private def p1b : GNSData := qWeightGNS 192 (by decide)
private def p3a : GNSData := qWeightGNS 8 (by decide)
private def p3b : GNSData := qWeightGNS 16 (by decide)

abbrev path0GNS : GNSData := gnsProduct p0a p0b
abbrev path1GNS : GNSData := gnsProduct p1a p1b
abbrev path2GNS : GNSData := gnsProduct p1a p1b
abbrev path3GNS : GNSData := gnsProduct p3a p3b
abbrev path4GNS : GNSData := gnsProduct p3a p3b

def basis0 : Q' × Q' := (1, 0)
def basis1 : Q' × Q' := (0, 1)
def tripleBasis0 : Q' × Q' := (3, 0)
def tripleBasis1 : Q' × Q' := (0, 3)

/-- The first two path forms are the independently derived local transvectant
Gram forms, with one common factor `3` and the documented target chart scale. -/
theorem path01_gram_from_transvectants :
    path0GNS.B basis0 basis0 ≈
      3 * triMapInner 2 2 1 1
        (triLeft 2 2 1 1 0) (triLeft 2 2 1 1 0) ∧
    path0GNS.B basis1 basis1 ≈
      3 * triMapInner 2 2 1 1
        (triLeft 2 2 1 1 2) (triLeft 2 2 1 1 2) ∧
    path1GNS.B tripleBasis0 tripleBasis0 ≈
      3 * triMapInner 2 2 1 1
        (triRight 2 2 1 1 1) (triRight 2 2 1 1 1) ∧
    path1GNS.B tripleBasis1 tripleBasis1 ≈
      3 * triMapInner 2 2 1 1
        (triRight 2 2 1 1 3) (triRight 2 2 1 1 3) := by
  decide

/-! ## A reusable heterogeneous completion isometry -/

structure DenseGNSIsometry (D E : GNSData) where
  map : D.V → E.V
  map_veq : ∀ {a b}, D.veq a b → E.veq (map a) (map b)
  map_sub : ∀ a b, E.veq (map (D.sub a b)) (E.sub (map a) (map b))
  norm : ∀ a, E.B (map a) (map a) ≈ D.B a a

namespace DenseGNSIsometry

variable {D E : GNSData} (I : DenseGNSIsometry D E)

theorem distSq_eqv (a b : D.V) :
    E.distSqQ (I.map a) (I.map b) ≈ D.distSqQ a b := by
  refine Q'.eqv_trans _ (E.B (I.map (D.sub a b)) (I.map (D.sub a b))) _ ?_ ?_
  · exact Q'.eqv_symm (E.B_diag_congr (I.map_sub a b))
  · exact I.norm (D.sub a b)

def applyCauchy (x : CauchyGNS D) : CauchyGNS E where
  seq := fun n => I.map (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (I.distSq_eqv (x.seq p) (x.seq q)))
      (x.isCauchy epsilon hepsilon p q hp hq)

theorem applyCauchy_null {x y : CauchyGNS D} (h : CauchyNull D x y) :
    CauchyNull E (I.applyCauchy x) (I.applyCauchy y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h epsilon hepsilon
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (Q'.le_of_eqv (I.distSq_eqv (x.seq n) (y.seq n))) (hN n hn)⟩

def completed : GNSCompletionSpace D → GNSCompletionSpace E :=
  Quotient.lift
    (fun x => Quotient.mk (cauchySetoid E) (I.applyCauchy x))
    (fun _ _ h => Quotient.sound (I.applyCauchy_null h))

theorem completed_embed (a : D.V) :
    I.completed (embedV D a) = embedV E (I.map a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem completed_norm (x : GNSCompletionSpace D) :
    E.cinnerCompl (I.completed x) (I.completed x) = D.cinnerCompl x x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ'
      (E.cInnerSeq (I.applyCauchy u) (I.applyCauchy u) n))
    (bSeq := fun n => CReal.ofQ' (D.cInnerSeq u u n))
    (fun n => PositiveTimeCompression.lifted_eqv (I.norm (u.seq n))) ?_ ?_
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

end DenseGNSIsometry

/-! ## Integral edge charts and their positive forms -/

def edge01Chart (x : Q' × Q') : Q' × Q' :=
  ((-2) * x.1 + 4 * x.2, x.1 + x.2)

def edge12Chart (x : Q' × Q') : Q' × Q' := x

def edge23Chart (x : Q' × Q') : Q' × Q' :=
  ((-1) * x.1 + 4 * x.2, x.1 + 2 * x.2)

def edge04Chart (x : Q' × Q') : Q' × Q' := (6 * x.1, 6 * x.2)

def edge43Chart (x : Q' × Q') : Q' × Q' := x

private def fin2Zero : Fin 2 := ⟨0, by decide⟩
private def fin2One : Fin 2 := ⟨1, by decide⟩
private def oneQuarter : Q' := Q'.mkPos 1 4 (by decide)
private def oneSixth : Q' := Q'.mkPos 1 6 (by decide)
private def oneTwelfth : Q' := Q'.mkPos 1 12 (by decide)

/-- The integral chart entries recover all five physical matrices after the
documented diagonal chart rescalings.  This pins the charts to the upstream
transvectant certificate rather than postulating unrelated maps. -/
theorem edge_charts_match_physical_rows :
    oneThird * (edge01Chart basis0).1 ≈ edge01 fin2Zero fin2Zero ∧
    oneThird * (edge01Chart basis0).2 ≈ edge01 fin2Zero fin2One ∧
    oneThird * (edge01Chart basis1).1 ≈ edge01 fin2One fin2Zero ∧
    oneThird * (edge01Chart basis1).2 ≈ edge01 fin2One fin2One ∧
    oneHalf * (edge12Chart basis0).1 ≈ edge12 fin2Zero fin2Zero ∧
    (edge12Chart basis1).2 ≈ edge12 fin2One fin2One ∧
    (edge23Chart basis0).1 ≈ edge23 fin2Zero fin2Zero ∧
    oneHalf * (edge23Chart basis0).2 ≈ edge23 fin2Zero fin2One ∧
    oneHalf * (edge23Chart basis1).1 ≈ edge23 fin2One fin2Zero ∧
    oneQuarter * (edge23Chart basis1).2 ≈ edge23 fin2One fin2One ∧
    oneSixth * (edge04Chart basis0).1 ≈ edge04 fin2Zero fin2Zero ∧
    oneTwelfth * (edge04Chart basis1).2 ≈ edge04 fin2One fin2One ∧
    (edge43Chart basis0).1 ≈ edge43 fin2Zero fin2Zero ∧
    (edge43Chart basis1).2 ≈ edge43 fin2One fin2One := by
  decide

private def edge01NormL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.add (.mul (.const (-2)) x) (.mul (.const 4) y)
  let q := RingNormaliser.PolyExpr.add x y
  .add (.mul (.const 24) (.mul p p)) (.mul (.const 192) (.mul q q))

private def edge01NormR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  .add (.mul (.const 288) (.mul x x)) (.mul (.const 576) (.mul y y))

private theorem edge01Norm_normal :
    RingNormaliser.normalize edge01NormL = RingNormaliser.normalize edge01NormR := by decide

private theorem edge01_norm_identity (x y : Q') :
    24 * (((-2) * x + 4 * y) * ((-2) * x + 4 * y)) +
        192 * ((x + y) * (x + y)) ≈
      288 * (x * x) + 576 * (y * y) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    edge01NormL edge01NormR edge01Norm_normal (fun | 0 => x | _ => y)
  simpa [edge01NormL, edge01NormR, RingNormaliser.eval] using h

private def edge23NormL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.add (.mul (.const (-1)) x) (.mul (.const 4) y)
  let q := RingNormaliser.PolyExpr.add x (.mul (.const 2) y)
  .add (.mul (.const 8) (.mul p p)) (.mul (.const 16) (.mul q q))

private def edge23NormR : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  .add (.mul (.const 24) (.mul x x)) (.mul (.const 192) (.mul y y))

private theorem edge23Norm_normal :
    RingNormaliser.normalize edge23NormL = RingNormaliser.normalize edge23NormR := by decide

private theorem edge23_norm_identity (x y : Q') :
    8 * (((-1) * x + 4 * y) * ((-1) * x + 4 * y)) +
        16 * ((x + 2 * y) * (x + 2 * y)) ≈
      24 * (x * x) + 192 * (y * y) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    edge23NormL edge23NormR edge23Norm_normal (fun | 0 => x | _ => y)
  simpa [edge23NormL, edge23NormR, RingNormaliser.eval] using h

private def edge04NormL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  .add (.mul (.const 8) (.mul (.mul (.const 6) x) (.mul (.const 6) x)))
    (.mul (.const 16) (.mul (.mul (.const 6) y) (.mul (.const 6) y)))

private theorem edge04Norm_normal :
    RingNormaliser.normalize edge04NormL = RingNormaliser.normalize edge01NormR := by decide

private theorem edge04_norm_identity (x y : Q') :
    8 * ((6 * x) * (6 * x)) + 16 * ((6 * y) * (6 * y)) ≈
      288 * (x * x) + 576 * (y * y) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    edge04NormL edge01NormR edge04Norm_normal (fun | 0 => x | _ => y)
  simpa [edge04NormL, edge01NormR, RingNormaliser.eval] using h

private theorem edge01_map_sub (a b : Q' × Q') :
    path1GNS.veq (edge01Chart (path0GNS.sub a b))
      (path1GNS.sub (edge01Chart a) (edge01Chart b)) := by
  unfold edge01Chart path0GNS path1GNS gnsProduct p0a p0b p1a p1b qWeightGNS GNSData.sub
  constructor <;> ring_qeqv

private theorem edge23_map_sub (a b : Q' × Q') :
    path3GNS.veq (edge23Chart (path2GNS.sub a b))
      (path3GNS.sub (edge23Chart a) (edge23Chart b)) := by
  unfold edge23Chart path2GNS path3GNS gnsProduct p1a p1b p3a p3b qWeightGNS GNSData.sub
  constructor <;> ring_qeqv

private theorem edge04_map_sub (a b : Q' × Q') :
    path4GNS.veq (edge04Chart (path0GNS.sub a b))
      (path4GNS.sub (edge04Chart a) (edge04Chart b)) := by
  unfold edge04Chart path0GNS path4GNS gnsProduct p0a p0b p3a p3b qWeightGNS GNSData.sub
  constructor <;> ring_qeqv

def edge01Iso : DenseGNSIsometry path0GNS path1GNS where
  map := edge01Chart
  map_veq := fun h =>
    ⟨QPoly.q_add_congr (Q'.mul_eqv_congr_left (-2) _ _ h.1)
        (Q'.mul_eqv_congr_left 4 _ _ h.2), QPoly.q_add_congr h.1 h.2⟩
  map_sub := edge01_map_sub
  norm := by
    intro a
    unfold edge01Chart path0GNS path1GNS gnsProduct p0a p0b p1a p1b qWeightGNS
    exact edge01_norm_identity a.1 a.2

def edge12Iso : DenseGNSIsometry path1GNS path2GNS where
  map := edge12Chart
  map_veq := fun h => h
  map_sub := fun a b => by
    unfold edge12Chart
    exact path1GNS.veq_refl _
  norm := fun a => by
    unfold edge12Chart
    exact Q'.eqv_refl _

def edge23Iso : DenseGNSIsometry path2GNS path3GNS where
  map := edge23Chart
  map_veq := fun h =>
    ⟨QPoly.q_add_congr (Q'.mul_eqv_congr_left (-1) _ _ h.1)
        (Q'.mul_eqv_congr_left 4 _ _ h.2),
      QPoly.q_add_congr h.1 (Q'.mul_eqv_congr_left 2 _ _ h.2)⟩
  map_sub := edge23_map_sub
  norm := by
    intro a
    unfold edge23Chart path2GNS path3GNS gnsProduct p1a p1b p3a p3b qWeightGNS
    exact edge23_norm_identity a.1 a.2

def edge04Iso : DenseGNSIsometry path0GNS path4GNS where
  map := edge04Chart
  map_veq := fun h =>
    ⟨Q'.mul_eqv_congr_left 6 _ _ h.1, Q'.mul_eqv_congr_left 6 _ _ h.2⟩
  map_sub := edge04_map_sub
  norm := by
    intro a
    unfold edge04Chart path0GNS path4GNS gnsProduct p0a p0b p3a p3b qWeightGNS
    exact edge04_norm_identity a.1 a.2

def edge43Iso : DenseGNSIsometry path4GNS path3GNS where
  map := edge43Chart
  map_veq := fun h => h
  map_sub := fun a b => by
    unfold edge43Chart
    exact path4GNS.veq_refl _
  norm := fun a => by
    unfold edge43Chart
    exact Q'.eqv_refl _

/-! ## Dense and completed pentagon coherence -/

def longChart (x : Q' × Q') : Q' × Q' :=
  edge23Chart (edge12Chart (edge01Chart x))

def shortChart (x : Q' × Q') : Q' × Q' := edge43Chart (edge04Chart x)

private def pentagonFirstL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let u := RingNormaliser.PolyExpr.add (.mul (.const (-2)) x) (.mul (.const 4) y)
  let v := RingNormaliser.PolyExpr.add x y
  .add (.mul (.const (-1)) u) (.mul (.const 4) v)

private def pentagonFirstR : RingNormaliser.PolyExpr :=
  .mul (.const 6) (.var 0)

private def pentagonSecondL : RingNormaliser.PolyExpr :=
  let x := RingNormaliser.PolyExpr.var 0
  let y := RingNormaliser.PolyExpr.var 1
  let u := RingNormaliser.PolyExpr.add (.mul (.const (-2)) x) (.mul (.const 4) y)
  let v := RingNormaliser.PolyExpr.add x y
  .add u (.mul (.const 2) v)

private def pentagonSecondR : RingNormaliser.PolyExpr :=
  .mul (.const 6) (.var 1)

private theorem pentagonFirst_normal :
    RingNormaliser.normalize pentagonFirstL = RingNormaliser.normalize pentagonFirstR := by decide

private theorem pentagonSecond_normal :
    RingNormaliser.normalize pentagonSecondL = RingNormaliser.normalize pentagonSecondR := by decide

theorem dense_mixed_pentagon (x : Q' × Q') :
    path3GNS.veq (longChart x) (shortChart x) := by
  constructor
  · have h := RingNormaliser.poly_identity_of_normal_eq
      pentagonFirstL pentagonFirstR pentagonFirst_normal
      (fun | 0 => x.1 | _ => x.2)
    simpa [longChart, shortChart, edge01Chart, edge12Chart, edge23Chart,
      edge04Chart, edge43Chart, pentagonFirstL, pentagonFirstR,
      RingNormaliser.eval] using h
  · have h := RingNormaliser.poly_identity_of_normal_eq
      pentagonSecondL pentagonSecondR pentagonSecond_normal
      (fun | 0 => x.1 | _ => x.2)
    simpa [longChart, shortChart, edge01Chart, edge12Chart, edge23Chart,
      edge04Chart, edge43Chart, pentagonSecondL, pentagonSecondR,
      RingNormaliser.eval] using h

def completedLongRoute :
    GNSCompletionSpace path0GNS → GNSCompletionSpace path3GNS :=
  fun x => edge23Iso.completed (edge12Iso.completed (edge01Iso.completed x))

def completedShortRoute :
    GNSCompletionSpace path0GNS → GNSCompletionSpace path3GNS :=
  fun x => edge43Iso.completed (edge04Iso.completed x)

/-- The exact mixed transvectant pentagon survives the constructive GNS
quotients and both Cauchy completions. -/
theorem completed_mixed_pentagon (x : GNSCompletionSpace path0GNS) :
    completedLongRoute x = completedShortRoute x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun n _ => le_of_eqv_le
    (rad_of_veq path3GNS (dense_mixed_pentagon (u.seq n)))
    (Q'.le_of_lt hepsilon)⟩

end YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted

#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.path01_gram_from_transvectants
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.DenseGNSIsometry.completed
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.DenseGNSIsometry.completed_norm
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.edge_charts_match_physical_rows
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.edge01Iso
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.edge23Iso
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.edge04Iso
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.dense_mixed_pentagon
#print axioms YMGap.Continuum.SU2TransvectantMixedPentagonGNSCompleted.completed_mixed_pentagon
