/-
The current `GeometryEnrichedReferenceWeight` interface makes the selected
time action a state-preserving observable automorphism.  It is therefore an
exact isometry of the Wilson form.  If the same action is required to satisfy
`TimeHalfspaceLaw`, reflected symmetry makes the isometry self-adjoint and
reflected positivity makes it positive.

This file proves constructively, before completion, that those requirements
force the selected action to be the identity modulo the Wilson radical.  Thus
adding more exact character modes cannot produce a nontrivial transfer
eigenvalue through this interface: a genuine Euclidean transfer must instead
be a halfspace compression/conditional expectation, rather than the full
state-preserving time automorphism itself.

No numerical input, choice, or classical reasoning is used.  Axiom
dependencies are contained in `{propext, Quot.sound}`.
-/

import YMGap.Continuum.ReferenceWeightTransferConstruction

namespace YMGap.Continuum.PositiveIsometricTimeNoGo

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.ReferenceWeightTransferConstruction
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

/-! ## Constructive rational sign glue -/

/-- A rational which is both nonnegative and whose negative is nonnegative is
zero, stated in the substrate equivalence rather than structural equality. -/
theorem q_eqv_zero_of_nonneg_neg_nonneg (q : Q')
    (hq : (0 : Q') ≤ q) (hn : (0 : Q') ≤ -q) : q ≈ 0 := by
  have hqnum : (0 : Int) ≤ q.num := (Q'.zero_le_iff_num_nonneg q).mp hq
  have hnnum : (0 : Int) ≤ (-q).num := (Q'.zero_le_iff_num_nonneg (-q)).mp hn
  have hnegnum : (0 : Int) ≤ -q.num := by
    exact hnnum
  have hqnonpos : q.num ≤ (0 : Int) := Int.nonpos_of_neg_nonneg hnegnum
  have hqzero : q.num = 0 := Int.le_antisymm hqnonpos hqnum
  unfold Q'.eqv
  rw [hqzero]
  change (0 : Int) = 0 * (q.den : Int)
  simp

/-- Reversing a rational subtraction negates it. -/
theorem q_reverse_sub_eqv_neg_sub (p q : Q') :
    (q + -p) ≈ (-(p + -q)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv q (-p)) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv p (-q))
    (Q'.add_eqv_congr_left (-p) (-(-q)) q (Q'.neg_neg_eqv q)))

/-! ## Positive isometric time is radical-trivial -/

/-- Reflected symmetry followed by full-state isometry says that two time
steps are weakly the identity.  No use of the finite-period field is needed. -/
theorem TimeHalfspaceLaw.timeSquare_pair_eqv
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (a b : A.carrier) :
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map (G.action.hom.map a)) b).eqv
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B a b) := by
  exact Q'.eqv_trans _ _ _
    (L.reflected_symmetric (G.action.hom.map a) b)
    (G.wilsonForm_translation_invariant elin_congr elin_add elin_smul hconj a b)

/-- On the displacement `y = tau a - a`, the reflected form is exactly the
negative of the ordinary squared norm. -/
theorem TimeHalfspaceLaw.reflected_displacement_eqv_neg_norm
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (a : A.carrier) :
    let D := (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
    let y := D.sub (G.action.hom.map a) a
    (D.B (G.action.hom.map y) y).eqv (-(D.B y y)) := by
  let W := G.toWilsonGNSData elin_congr elin_add elin_smul hconj
  let D := W.toGNSData
  let tau := G.action.hom.map
  let y := D.sub (tau a) a
  have hmap : D.veq (tau y) (D.sub (tau (tau a)) (tau a)) := by
    exact G.map_sub (tau a) a
  have eMap : (D.B (tau y) y).eqv
      (D.B (D.sub (tau (tau a)) (tau a)) y) :=
    D.B_congr_left y hmap
  have eExpandShift : (D.B (D.sub (tau (tau a)) (tau a)) y).eqv
      (D.B (tau (tau a)) y + -(D.B (tau a) y)) := by
    refine Q'.eqv_trans _ _ _ (D.B_add_left (tau (tau a)) (D.neg (tau a)) y) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_left (tau a) y)
  have eSquare : (D.B (tau (tau a)) y).eqv (D.B a y) :=
    TimeHalfspaceLaw.timeSquare_pair_eqv L a y
  have eShift : (D.B (tau y) y).eqv
      (D.B a y + -(D.B (tau a) y)) := by
    exact Q'.eqv_trans _ _ _ eMap
      (Q'.eqv_trans _ _ _ eExpandShift
        (Q'.add_eqv_congr' eSquare (Q'.eqv_refl _)))
  have eNorm : (D.B y y).eqv
      (D.B (tau a) y + -(D.B a y)) := by
    refine Q'.eqv_trans _ _ _ (D.B_add_left (tau a) (D.neg a) y) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _) (D.B_neg_left a y)
  have eReverse : (D.B a y + -(D.B (tau a) y)).eqv
      (-(D.B (tau a) y + -(D.B a y))) :=
    q_reverse_sub_eqv_neg_sub (D.B (tau a) y) (D.B a y)
  have eNegNorm : (-(D.B y y)).eqv
      (-(D.B (tau a) y + -(D.B a y))) :=
    Q'.neg_eqv_congr _ _ eNorm
  exact Q'.eqv_trans _ _ _ eShift
    (Q'.eqv_trans _ _ _ eReverse (Q'.eqv_symm eNegNorm))

/-- **Universal no-go.**  Every representative is radical-equivalent to its
selected one-step time translate. -/
theorem TimeHalfspaceLaw.timeShift_rad_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (a : A.carrier) :
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.rad
      (G.action.hom.map a) a := by
  let W := G.toWilsonGNSData elin_congr elin_add elin_smul hconj
  let D := W.toGNSData
  let y := D.sub (G.action.hom.map a) a
  have hpos : (0 : Q') ≤ D.B y y := D.self_nonneg y
  have href : (0 : Q') ≤ D.B (G.action.hom.map y) y := L.reflected_positive y
  have hneg : (0 : Q') ≤ -(D.B y y) :=
    OSReconstructionProgress.le_of_le_eqv href
      (TimeHalfspaceLaw.reflected_displacement_eqv_neg_norm L a)
  exact q_eqv_zero_of_nonneg_neg_nonneg (D.B y y) hpos hneg

/-- The reflected one-step form is consequently just the ordinary norm form. -/
theorem TimeHalfspaceLaw.reflected_form_eqv_norm
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (a : A.carrier) :
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map a) a).eqv
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B a a) := by
  let D := (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
  exact D.B_welldef (TimeHalfspaceLaw.timeShift_rad_identity L a) (D.rad_refl a)

/-! ## Quotient and exact-form consequences -/

/-- The one-step time shift is the identity on each quotient constructor. -/
theorem TimeHalfspaceLaw.quotientTimeShift_qmk_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (a : A.carrier) :
    G.quotientTimeShift elin_congr elin_add elin_smul hconj
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.qmk a) =
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.qmk a := by
  apply Quotient.sound
  exact TimeHalfspaceLaw.timeShift_rad_identity L a

/-- Hence the selected action is the identity on the entire Wilson quotient,
not merely on a chosen character mode. -/
theorem TimeHalfspaceLaw.quotientTimeShift_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj) :
    G.quotientTimeShift elin_congr elin_add elin_smul hconj = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  exact TimeHalfspaceLaw.quotientTimeShift_qmk_identity L a

/-! ## Completion consequence -/

/-- Pointwise radical triviality makes the translated Cauchy representative
null-equivalent to the original representative. -/
theorem TimeHalfspaceLaw.translateCauchy_null_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (x : CauchyGNS
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    CauchyNull
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
      (ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.translateCauchy
        G elin_congr elin_add elin_smul hconj x) x := by
  let D := (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
  intro ε hε
  exact ⟨0, fun n _ => Q'.le_trans' _ 0 ε
    (Q'.le_of_eqv (TimeHalfspaceLaw.timeShift_rad_identity L (x.seq n)))
    (Q'.le_of_lt hε)⟩

/-- The completed shift used by `toTransferExtension` is the identity on the
whole constructive GNS completion. -/
theorem TimeHalfspaceLaw.completedTimeShift_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (x : GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.completedTimeShift
      G elin_congr elin_add elin_smul hconj x = x := by
  refine Quotient.inductionOn x ?_
  intro u
  apply Quotient.sound
  exact TimeHalfspaceLaw.translateCauchy_null_identity L u

/-- Consequently the concrete `TransferExtension` constructed from the law
has identity transfer on every completed vector. -/
theorem TimeHalfspaceLaw.toTransferExtension_T_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (x : GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    L.toTransferExtension.op.T x = x :=
  TimeHalfspaceLaw.completedTimeShift_identity L x

/-- The obstruction is not peculiar to `toTransferExtension`: every supplied
`TransferExtension` has identity action on each embedded representative. -/
theorem TimeHalfspaceLaw.transferExtension_embedV_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (X : G.TransferExtension elin_congr elin_add elin_smul hconj)
    (a : A.carrier) :
    X.op.T (embedV
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData a) =
    embedV (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData a := by
  let D := (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
  calc
    X.op.T (embedV D a) = embedV D (G.action.hom.map a) := X.dense_intertwines a
    _ = embedV D a := by
      apply Quotient.sound
      exact embed_null_of_rad D (TimeHalfspaceLaw.timeShift_rad_identity L a)

/-- Therefore every supplied extension is identity on every vector coming
from the Wilson radical quotient, including every proposed non-vacuum
character quotient vector. -/
theorem TimeHalfspaceLaw.transferExtension_embedQuot_identity
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (X : G.TransferExtension elin_congr elin_add elin_smul hconj)
    (q : (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.QuotSpace) :
    X.op.T (embedQuot
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData q) =
    embedQuot (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData q := by
  refine Quotient.inductionOn q ?_
  intro a
  exact TimeHalfspaceLaw.transferExtension_embedV_identity L X a

/-- In particular, a unit-norm character cannot have reflected form distinct
from one under this interface. -/
theorem TimeHalfspaceLaw.no_unit_reflected_form_distinct_from_one
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (a : A.carrier)
    (hunit : ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B a a).eqv 1)
    (hdistinct : ¬ ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map a) a).eqv 1) : False :=
  hdistinct (Q'.eqv_trans _ _ _ (TimeHalfspaceLaw.reflected_form_eqv_norm L a) hunit)

/-- A quotient vector on which the selected one-step action is nontrivial is
incompatible with `TimeHalfspaceLaw`. -/
theorem TimeHalfspaceLaw.no_nontrivial_quotient_time_vector
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv
        (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (q : (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.QuotSpace)
    (hne : G.quotientTimeShift elin_congr elin_add elin_smul hconj q ≠ q) : False :=
  hne (congrFun (TimeHalfspaceLaw.quotientTimeShift_identity L) q)

end YMGap.Continuum.PositiveIsometricTimeNoGo

#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.q_eqv_zero_of_nonneg_neg_nonneg
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.q_reverse_sub_eqv_neg_sub
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.timeSquare_pair_eqv
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.reflected_displacement_eqv_neg_norm
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.timeShift_rad_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.reflected_form_eqv_norm
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.quotientTimeShift_qmk_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.quotientTimeShift_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.translateCauchy_null_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.completedTimeShift_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.toTransferExtension_T_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.transferExtension_embedV_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.transferExtension_embedQuot_identity
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.no_unit_reflected_form_distinct_from_one
#print axioms YMGap.Continuum.PositiveIsometricTimeNoGo.TimeHalfspaceLaw.no_nontrivial_quotient_time_vector
