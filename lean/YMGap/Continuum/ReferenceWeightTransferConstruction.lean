/-
Construction of the completed transfer from finite-volume time geometry.

A state-preserving observable automorphism is already an exact isometry of the
Wilson form and its radical quotient.  This file carries that isometry through
Cauchy representatives, proves it preserves the null relation, and descends it
to the constructive GNS completion.  The extended map agrees with the previous
quotient time shift on the dense quotient image.

Full-state invariance does not imply transfer positivity.  The concrete plane
model below has one fixed ReferenceWeight and carrier module with two periodic
state-preserving geometries: identity and a sign flip.  The identity satisfies
the reflection/time-halfspace law, while the flip has the exact witness
  B(tau (0,1), (0,1)) = -1,
so it cannot be positive.  This banks the missing premise without weakening or
hiding it.

TimeHalfspaceLaw adds exactly the two representative Osterwalder--Schrader laws
not supplied by static state invariance: reflected symmetry and reflected
positivity.  They pass to the Cauchy completion by constructive limit
uniqueness/order.  Combined with the geometry-derived isometry, they assemble
a genuine TransferOperator and hence the existing TransferExtension.

Every declaration is constructive and has axiom dependencies contained in
{propext, Quot.sound}.  Closed rational facts use kernel decide only.
-/

import YMGap.Continuum.ReferenceWeightTimeGeometry
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.ReferenceWeightTransferConstruction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteVolume
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.WilsonGNS

local infix:50 " ≈ " => Q'.eqv

structure TimeHalfspaceLaw
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))) : Type where
  reflected_symmetric : ∀ a b,
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map a) b).eqv
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      a (G.action.hom.map b))
  reflected_positive : ∀ a, (0 : Q') ≤
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).B
      (G.action.hom.map a) a

theorem GeometryEnrichedReferenceWeight.translation_distSq_eqv
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (a b : A.carrier) :
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.distSqQ
      (G.action.hom.map a) (G.action.hom.map b)).eqv
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.distSqQ
      a b) := by
  let W := G.toWilsonGNSData elin_congr elin_add elin_smul hconj
  have hsub : W.toGNSData.veq
      (G.action.hom.map (W.toGNSData.sub a b))
      (W.toGNSData.sub (G.action.hom.map a) (G.action.hom.map b)) := G.map_sub a b
  refine Q'.eqv_trans _ _ _
    (W.toGNSData.B_diag_congr (W.toGNSData.veq_symm hsub)) ?_
  exact G.wilsonForm_translation_invariant elin_congr elin_add elin_smul hconj
    (W.toGNSData.sub a b) (W.toGNSData.sub a b)

theorem GeometryEnrichedReferenceWeight.quotientTimeShift_qDistSq_isometry
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (p q : (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.QuotSpace) :
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.qDistSq
      (G.quotientTimeShift elin_congr elin_add elin_smul hconj p)
      (G.quotientTimeShift elin_congr elin_add elin_smul hconj q) =
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.qDistSq p q := by
  refine Quotient.inductionOn₂ p q ?_
  intro a b
  apply Quotient.sound
  exact translation_distSq_eqv G elin_congr elin_add elin_smul hconj a b

def GeometryEnrichedReferenceWeight.translateCauchy
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (x : CauchyGNS
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    CauchyGNS (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData where
  seq := fun n => G.action.hom.map (x.seq n)
  modulus := x.modulus
  isCauchy := by
    intro ε hε p q hp hq
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (translation_distSq_eqv G elin_congr elin_add elin_smul hconj
          (x.seq p) (x.seq q)))
      (x.isCauchy ε hε p q hp hq)

theorem GeometryEnrichedReferenceWeight.translateCauchy_null
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    {x y : CauchyGNS
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData}
    (h : CauchyNull
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData x y) :
    CauchyNull
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
      (translateCauchy G elin_congr elin_add elin_smul hconj x)
      (translateCauchy G elin_congr elin_add elin_smul hconj y) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (translation_distSq_eqv G elin_congr elin_add elin_smul hconj
        (x.seq n) (y.seq n)))
    (hN n hn)⟩

def GeometryEnrichedReferenceWeight.completedTimeShift
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))) :
    GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData →
    GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData :=
  Quotient.lift
    (fun x => Quotient.mk
      (cauchySetoid
        (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData)
      (translateCauchy G elin_congr elin_add elin_smul hconj x))
    (fun _ _ h => Quotient.sound
      (translateCauchy_null G elin_congr elin_add elin_smul hconj h))

theorem GeometryEnrichedReferenceWeight.completedTimeShift_embed
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (a : A.carrier) :
    completedTimeShift G elin_congr elin_add elin_smul hconj
      (embedV (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData a) =
    embedV (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
      (G.action.hom.map a) := by
  apply Quotient.sound
  exact cauchyNull_refl _ _

theorem GeometryEnrichedReferenceWeight.completedTimeShift_embedQuot
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (q : (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.QuotSpace) :
    completedTimeShift G elin_congr elin_add elin_smul hconj
      (embedQuot (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData q) =
    embedQuot (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
      (G.quotientTimeShift elin_congr elin_add elin_smul hconj q) := by
  refine Quotient.inductionOn q ?_
  intro a
  exact completedTimeShift_embed G elin_congr elin_add elin_smul hconj a

open YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight

theorem lifted_eqv {a b : Q'} (h : a.eqv b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro ε hε
  exact ⟨0, fun _ _ => ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b ε (Q'.le_of_lt hε)),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a ε (Q'.le_of_lt hε))⟩⟩

theorem GeometryEnrichedReferenceWeight.cinnerRep_time_isometry
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (x y : CauchyGNS
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    CReal.Equiv
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerRep
        (translateCauchy G elin_congr elin_add elin_smul hconj x)
        (translateCauchy G elin_congr elin_add elin_smul hconj y))
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerRep
        x y) := by
  let D := (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ' (D.cInnerSeq
      (translateCauchy G elin_congr elin_add elin_smul hconj x)
      (translateCauchy G elin_congr elin_add elin_smul hconj y) n))
    (bSeq := fun n => CReal.ofQ' (D.cInnerSeq x y n))
    (fun n => lifted_eqv ?_) ?_ ?_
  · exact G.wilsonForm_translation_invariant elin_congr elin_add elin_smul hconj
      (x.seq n) (y.seq n)
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem TimeHalfspaceLaw.cinnerRep_reflected_symmetric
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (x y : CauchyGNS
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    CReal.Equiv
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerRep
        (translateCauchy G elin_congr elin_add elin_smul hconj x) y)
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerRep
        x (translateCauchy G elin_congr elin_add elin_smul hconj y)) := by
  let D := (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ' (D.cInnerSeq
      (translateCauchy G elin_congr elin_add elin_smul hconj x) y n))
    (bSeq := fun n => CReal.ofQ' (D.cInnerSeq x
      (translateCauchy G elin_congr elin_add elin_smul hconj y) n))
    (fun n => lifted_eqv ?_) ?_ ?_
  · exact L.reflected_symmetric (x.seq n) (y.seq n)
  · exact CReal.convergesTo_ofQ'CauchySeq _ _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem GeometryEnrichedReferenceWeight.completedTimeShift_cinner_isometry
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (x y : GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerCompl
      (completedTimeShift G elin_congr elin_add elin_smul hconj x)
      (completedTimeShift G elin_congr elin_add elin_smul hconj y) =
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerCompl
      x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact cinnerRep_time_isometry G elin_congr elin_add elin_smul hconj u v

theorem TimeHalfspaceLaw.completed_selfAdjoint
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (x y : GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerCompl
      (completedTimeShift G elin_congr elin_add elin_smul hconj x) y =
    (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerCompl
      x (completedTimeShift G elin_congr elin_add elin_smul hconj y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro u v
  apply Quotient.sound
  exact L.cinnerRep_reflected_symmetric u v

theorem TimeHalfspaceLaw.completed_positive
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj)
    (x : GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    CReal.RCnonneg
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerCompl
        (completedTimeShift G elin_congr elin_add elin_smul hconj x) x) := by
  refine Quotient.inductionOn x ?_
  intro u
  show CReal.leEv CReal.czero
    ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerRep
      (translateCauchy G elin_congr elin_add elin_smul hconj u) u)
  exact CReal.leEv_ofQ'_of_approx_ge (fun n => L.reflected_positive (u.seq _))

theorem GeometryEnrichedReferenceWeight.completed_contraction
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    (G : GeometryEnrichedReferenceWeight R M)
    (elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b))
    (elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b))
    (elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a))
    (hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a)))
    (x : GNSCompletionSpace
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData) :
    CReal.RCle
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerCompl
        (completedTimeShift G elin_congr elin_add elin_smul hconj x)
        (completedTimeShift G elin_congr elin_add elin_smul hconj x))
      ((G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.cinnerCompl
        x x) := by
  rw [completedTimeShift_cinner_isometry G elin_congr elin_add elin_smul hconj]
  exact CReal.RCle_refl _

def TimeHalfspaceLaw.toTransferExtension
    {A : ObsAlg} {R : ReferenceWeight A} {M : WilsonGNSData.CarrierModule A}
    {G : GeometryEnrichedReferenceWeight R M}
    {elin_congr : ∀ {a b}, M.veq a b → (R.E_Λ a).eqv (R.E_Λ b)}
    {elin_add : ∀ a b, (R.E_Λ (M.add a b)).eqv (R.E_Λ a + R.E_Λ b)}
    {elin_smul : ∀ (s : Q') (a), (R.E_Λ (M.smul s a)).eqv (s * R.E_Λ a)}
    {hconj : ∀ a b,
      (R.E_Λ (A.mul (A.star a) b)).eqv (R.E_Λ (A.mul (A.star b) a))}
    (L : TimeHalfspaceLaw G elin_congr elin_add elin_smul hconj) :
    G.TransferExtension elin_congr elin_add elin_smul hconj where
  op := {
    T := completedTimeShift G elin_congr elin_add elin_smul hconj
    vacuum := embedV
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData
      (G.toWilsonGNSData elin_congr elin_add elin_smul hconj).toGNSData.zero
    selfAdjoint := L.completed_selfAdjoint
    positive := L.completed_positive
    contraction := completed_contraction G elin_congr elin_add elin_smul hconj
  }
  dense_intertwines :=
    completedTimeShift_embed G elin_congr elin_add elin_smul hconj

/-! Counterexample diagnostic. -/

def planeAlg : ObsAlg where
  carrier := Q' × Q'
  one := (1, 0)
  mul := fun a b => (a.1 * b.1 + a.2 * b.2, 0)
  star := fun a => a

def planeI0 : ProbFunctional planeAlg where
  E := fun a => a.1
  normalized := rfl
  positive := fun a => Q'.zero_le_add _ _
    (SumOfSquares.q_mul_self_nonneg a.1)
    (SumOfSquares.q_mul_self_nonneg a.2)

def planeReferenceWeight : ReferenceWeight planeAlg where
  I₀ := planeI0
  w := planeAlg.one
  Z := 1
  Z_eq := rfl
  Z_pos := by decide
  weighted_pos := fun a => Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg a.1)
        (SumOfSquares.q_mul_self_nonneg a.2)))
    (Q'.mul_nonneg _ _ (by decide) (by
      change (0 : Q') ≤ 0
      exact Q'.le_refl' 0))

theorem plane_E_eqv_fst (a : Q' × Q') :
    (planeReferenceWeight.E_Λ a).eqv a.1 := by
  change (((1 : Q') * a.1 + (0 : Q') * a.2) * (1 : Q')).eqv a.1
  refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.one_mul_eqv a.1) (QPoly.q_zero_mul a.2)) ?_
  exact QPoly.q_add_zero_eqv a.1

def planeModule : WilsonGNSData.CarrierModule planeAlg where
  veq := fun a b => a.1.eqv b.1 ∧ a.2.eqv b.2
  veq_refl := fun a => ⟨Q'.eqv_refl a.1, Q'.eqv_refl a.2⟩
  veq_symm := fun h => ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2⟩
  veq_trans := fun h k =>
    ⟨Q'.eqv_trans _ _ _ h.1 k.1, Q'.eqv_trans _ _ _ h.2 k.2⟩
  zero := (0, 0)
  add := fun a b => (a.1 + b.1, a.2 + b.2)
  neg := fun a => (-a.1, -a.2)
  smul := fun s a => (s * a.1, s * a.2)
  add_congr := fun ha hb => ⟨QPoly.q_add_congr ha.1 hb.1, QPoly.q_add_congr ha.2 hb.2⟩
  neg_congr := fun h => ⟨Q'.neg_eqv_congr _ _ h.1, Q'.neg_eqv_congr _ _ h.2⟩
  smul_congr := fun s {_ _} h =>
    ⟨Q'.mul_eqv_congr_left s _ _ h.1, Q'.mul_eqv_congr_left s _ _ h.2⟩
  add_assoc := fun a b c =>
    ⟨Q'.add_assoc_eqv a.1 b.1 c.1, Q'.add_assoc_eqv a.2 b.2 c.2⟩
  add_comm := fun a b => ⟨Q'.add_comm_eqv a.1 b.1, Q'.add_comm_eqv a.2 b.2⟩
  zero_add := fun a => ⟨QPoly.q_zero_add_eqv a.1, QPoly.q_zero_add_eqv a.2⟩
  neg_add := fun a => ⟨Q'.neg_add_self_eqv a.1, Q'.neg_add_self_eqv a.2⟩
  mul_congr := by
    intro a a' b b' ha hb
    refine ⟨QPoly.q_add_congr ?_ ?_, Q'.eqv_refl 0⟩
    · exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha.1)
        (Q'.mul_eqv_congr_left _ _ _ hb.1)
    · exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha.2)
        (Q'.mul_eqv_congr_left _ _ _ hb.2)
  star_congr := fun h => h
  star_add := fun a b => ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  star_smul := fun s a => ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  mul_add_right := by
    intro a b c
    refine ⟨?_, Q'.eqv_symm (QPoly.q_add_zero_eqv 0)⟩
    have h1 := QPoly.q_add_mul a.1 b.1 c.1
    have h2 := QPoly.q_add_mul a.2 b.2 c.2
    refine Q'.eqv_trans _ _ _ (QPoly.q_add_congr h1 h2) ?_
    exact Q'.add_swap_inner (a.1 * c.1) (b.1 * c.1) (a.2 * c.2) (b.2 * c.2)
  smul_mul := by
    intro s a b
    refine ⟨?_, Q'.eqv_symm (Q'.mul_zero_eqv s)⟩
    refine Q'.eqv_trans _ _ _
      (QPoly.q_add_congr (Q'.mul_assoc_eqv s a.1 b.1)
        (Q'.mul_assoc_eqv s a.2 b.2)) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv s (a.1 * b.1) (a.2 * b.2))

def planeFlip (a : Q' × Q') : Q' × Q' := (a.1, -a.2)

theorem q_neg_mul_neg_eq (a b : Q') : (-a) * (-b) = a * b := by
  cases a with
  | mk an ad =>
    cases b with
    | mk bn bd =>
      change Q'.mk ((-an) * (-bn)) ((ad + 1) * (bd + 1) - 1) =
        Q'.mk (an * bn) ((ad + 1) * (bd + 1) - 1)
      congr 1
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem q_neg_neg_eq (a : Q') : -(-a) = a := by
  cases a with
  | mk an ad =>
    change Q'.mk (-(-an)) ad = Q'.mk an ad
    rw [Int.neg_neg]

def planeFlipHom : ObsHom planeAlg planeAlg where
  map := planeFlip
  map_one := rfl
  map_mul := by
    intro a b
    apply Prod.ext
    · change (a.1 * b.1 + a.2 * b.2) =
        (a.1 * b.1 + (-a.2) * (-b.2))
      rw [q_neg_mul_neg_eq]
    · rfl
  map_star := fun _ => rfl

def planeFlipAction : ReferenceTranslationAction planeReferenceWeight where
  hom := planeFlipHom
  weight_fixed := by
    change planeFlip planeAlg.one = planeAlg.one
    rfl
  reference_invariant := fun a => by
    change a.1.eqv a.1
    exact Q'.eqv_refl a.1

def planeIdentityGeometry : GeometryEnrichedReferenceWeight
    planeReferenceWeight planeModule where
  timeExtent := 1
  timeExtent_pos := by decide
  action := identityAction _
  periodic := fun _ => rfl
  map_veq := fun h => h
  map_add := fun _ _ => planeModule.veq_refl _
  map_neg := fun _ => planeModule.veq_refl _
  map_smul := fun _ _ => planeModule.veq_refl _

def planeFlipGeometry : GeometryEnrichedReferenceWeight
    planeReferenceWeight planeModule where
  timeExtent := 2
  timeExtent_pos := by decide
  action := planeFlipAction
  periodic := by
    intro a
    change planeFlip (planeFlip a) = a
    apply Prod.ext
    · rfl
    · exact q_neg_neg_eq a.2
  map_veq := fun {a b} h => by
    change a.1.eqv b.1 ∧ (-a.2).eqv (-b.2)
    exact ⟨h.1, Q'.neg_eqv_congr _ _ h.2⟩
  map_add := fun a b => by
    change (a.1 + b.1).eqv (a.1 + b.1) ∧
      (-(a.2 + b.2)).eqv (-a.2 + -b.2)
    exact ⟨Q'.eqv_refl _, Q'.neg_add_eqv a.2 b.2⟩
  map_neg := fun a => by
    change (-a.1).eqv (-a.1) ∧ (-(-a.2)).eqv (-(-a.2))
    exact ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  map_smul := fun s a => by
    change (s * a.1).eqv (s * a.1) ∧ (-(s * a.2)).eqv (s * (-a.2))
    exact ⟨Q'.eqv_refl _, Q'.eqv_symm (Q'.mul_neg_eqv s a.2)⟩

theorem plane_elin_congr {a b : Q' × Q'} (h : planeModule.veq a b) :
    (planeReferenceWeight.E_Λ a).eqv (planeReferenceWeight.E_Λ b) :=
  Q'.eqv_trans _ _ _ (plane_E_eqv_fst a)
    (Q'.eqv_trans _ _ _ h.1 (Q'.eqv_symm (plane_E_eqv_fst b)))

theorem plane_elin_add (a b : Q' × Q') :
    (planeReferenceWeight.E_Λ (planeModule.add a b)).eqv
      (planeReferenceWeight.E_Λ a + planeReferenceWeight.E_Λ b) :=
  Q'.eqv_trans _ _ _ (plane_E_eqv_fst _)
    (QPoly.q_add_congr (Q'.eqv_symm (plane_E_eqv_fst a))
      (Q'.eqv_symm (plane_E_eqv_fst b)))

theorem plane_elin_smul (s : Q') (a : Q' × Q') :
    (planeReferenceWeight.E_Λ (planeModule.smul s a)).eqv
      (s * planeReferenceWeight.E_Λ a) :=
  Q'.eqv_trans _ _ _ (plane_E_eqv_fst _)
    (Q'.mul_eqv_congr_left s _ _ (Q'.eqv_symm (plane_E_eqv_fst a)))

theorem plane_hconj (a b : Q' × Q') :
    (planeReferenceWeight.E_Λ (planeAlg.mul (planeAlg.star a) b)).eqv
      (planeReferenceWeight.E_Λ (planeAlg.mul (planeAlg.star b) a)) := by
  refine Q'.eqv_trans _ _ _ (plane_E_eqv_fst _) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.mul_comm_eqv a.1 b.1) (Q'.mul_comm_eqv a.2 b.2)) ?_
  exact Q'.eqv_symm (plane_E_eqv_fst _)

def planeIdentityHalfspaceLaw : TimeHalfspaceLaw planeIdentityGeometry
    plane_elin_congr plane_elin_add plane_elin_smul plane_hconj where
  reflected_symmetric := fun _ _ => Q'.eqv_refl _
  reflected_positive := fun a =>
    (planeIdentityGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).E_self_nonneg a

def planeIdentityTransferExtension : planeIdentityGeometry.TransferExtension
    plane_elin_congr plane_elin_add plane_elin_smul plane_hconj :=
  planeIdentityHalfspaceLaw.toTransferExtension

def planeWitness : Q' × Q' := (0, 1)

/-- The counterexample direction has genuine unit norm; it is not a radical
or zero-vector artifact. -/
theorem planeWitness_norm_eqv_one :
    ((planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).B planeWitness planeWitness).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (plane_E_eqv_fst _) ?_
  unfold planeWitness planeAlg
  decide

theorem planeIdentity_flip_action_ne :
    planeIdentityGeometry.action.hom.map ≠ planeFlipGeometry.action.hom.map := by
  intro h
  have hv := congrFun h planeWitness
  have hs := congrArg Prod.snd hv
  change (1 : Q') = -1 at hs
  exact (by decide : ¬ ((1 : Q') = -1)) hs

/-- The nontrivial flip remains an exact isometry of the Wilson distance, so
the obstruction below is specifically positivity rather than continuity or
boundedness. -/
theorem planeFlip_distSq_isometry (a b : Q' × Q') :
    ((planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).toGNSData.distSqQ
      (planeFlipGeometry.action.hom.map a)
      (planeFlipGeometry.action.hom.map b)).eqv
    ((planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).toGNSData.distSqQ a b) :=
  GeometryEnrichedReferenceWeight.translation_distSq_eqv planeFlipGeometry
    plane_elin_congr plane_elin_add plane_elin_smul plane_hconj a b

theorem planeFlip_witness_form_eqv_neg_one :
    ((planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj).B
      (planeFlipGeometry.action.hom.map planeWitness) planeWitness).eqv (-1) := by
  refine Q'.eqv_trans _ _ _ (plane_E_eqv_fst _) ?_
  unfold planeFlipGeometry planeFlipAction planeFlipHom planeWitness planeFlip planeAlg
  change (((0 : Q') * 0) + ((-1 : Q') * 1)).eqv (-1)
  decide

theorem planeFlip_not_reflected_positive :
    ¬ ((0 : Q') ≤
      (planeFlipGeometry.toWilsonGNSData plane_elin_congr plane_elin_add
        plane_elin_smul plane_hconj).B
        (planeFlipGeometry.action.hom.map planeWitness) planeWitness) := by
  intro h
  have hn : (0 : Q') ≤ -1 :=
    OSReconstructionProgress.le_of_le_eqv h planeFlip_witness_form_eqv_neg_one
  exact (by decide : ¬ ((0 : Q') ≤ -1)) hn

theorem planeFlip_no_timeHalfspaceLaw :
    TimeHalfspaceLaw planeFlipGeometry plane_elin_congr plane_elin_add
      plane_elin_smul plane_hconj → False := by
  intro L
  exact planeFlip_not_reflected_positive (L.reflected_positive planeWitness)

end YMGap.Continuum.ReferenceWeightTransferConstruction


#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.TimeHalfspaceLaw
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.translation_distSq_eqv
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.quotientTimeShift_qDistSq_isometry
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.translateCauchy
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.translateCauchy_null
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.completedTimeShift
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.completedTimeShift_embed
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.completedTimeShift_embedQuot
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.lifted_eqv
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.cinnerRep_time_isometry
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.TimeHalfspaceLaw.cinnerRep_reflected_symmetric
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.completedTimeShift_cinner_isometry
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.TimeHalfspaceLaw.completed_selfAdjoint
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.TimeHalfspaceLaw.completed_positive
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.GeometryEnrichedReferenceWeight.completed_contraction
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.TimeHalfspaceLaw.toTransferExtension
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeReferenceWeight
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeModule
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeIdentityGeometry
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeFlipGeometry
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeIdentityHalfspaceLaw
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeIdentityTransferExtension
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeWitness_norm_eqv_one
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeIdentity_flip_action_ne
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeFlip_distSq_isometry
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeFlip_witness_form_eqv_neg_one
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeFlip_not_reflected_positive
#print axioms YMGap.Continuum.ReferenceWeightTransferConstruction.planeFlip_no_timeHalfspaceLaw
