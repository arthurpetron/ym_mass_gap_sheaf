/-
# The original-action reciprocal pairing loss has the actual residual limit

The finite loss is the literal full-action pairing against the in-place
reciprocal approximant. Its scalar Cauchy modulus is computed from the
existing completed-inner-product modulus. Its limit is the squared residual
of the original conditional projection at the same physical link.
This is a limit identity, not a coercive lower bound.
-/

import YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
import YMGap.Continuum.BF4ExactSlabConditionalSweep
import YMGap.Constructive.CRealInnerRegularity

namespace YMGap.Continuum.BF4ExactSlabReciprocalEnergyLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabInPlaceReciprocalConditional
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "A" => inPlaceCauchy hw0 hw1 K extent hK link hl
local notation "L" => finiteLoss hw0 hw1 K extent hK link

/-- The unregularized pairing sequence, retaining its computed inner-product
Cauchy modulus. -/
def pairingStream (p : (F).V) : CReal where
  approx k := (F).B p ((A p).seq k)
  cauchy := by
    let c := (F).cInnerQCauchy (constCauchy F p) (A p)
    exact fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

/-- Pointwise, this is precisely the finite original-action loss. -/
def finiteLossStream (p : (F).V) : CReal :=
  CReal.sub (CReal.ofQ' ((F).B p p)) (pairingStream hw0 hw1 K extent hK link hl p)

/-- An explicit Type-level scalar Cauchy modulus for the finite losses. -/
def finiteLossCauchy (p : (F).V) : CReal.QCauchy (fun k => L p k) :=
  let c := (F).cInnerQCauchy (constCauchy F p) (A p)
  let h := CReal.InnerRegularity.add
    (CReal.InnerRegularity.ofQ' ((F).B p p))
    (CReal.InnerRegularity.neg
      (show CReal.InnerRegularity (pairingStream hw0 hw1 K extent hK link hl p)
        from ⟨c.M, c.bound⟩))
  ⟨h.rate, h.regular⟩

/-- The constructive limit of the literal rational finite-loss stream. -/
def finiteLossReal (p : (F).V) : CReal :=
  CReal.ofQ'CauchySeq (fun k => L p k)
    (finiteLossCauchy hw0 hw1 K extent hK link hl p)

theorem finiteLossReal_converges (p : (F).V) :
    CReal.ConvergesTo (fun k => CReal.ofQ' (L p k))
      (finiteLossReal hw0 hw1 K extent hK link hl p) :=
  CReal.convergesTo_ofQ'CauchySeq _ _

private theorem pairingStream_equiv_cinnerRep (p : (F).V) :
    CReal.Equiv (pairingStream hw0 hw1 K extent hK link hl p)
      ((F).cinnerRep (constCauchy F p) (A p)) := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := fun k => CReal.ofQ' ((F).B p ((A p).seq k)))
    (bSeq := fun k => CReal.ofQ' ((F).cInnerSeq (constCauchy F p) (A p) k))
  · intro k
    exact CReal.Equiv.refl _
  · exact CReal.convergesTo_self _
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

private theorem finiteLossReal_equiv_stream (p : (F).V) :
    CReal.Equiv (finiteLossReal hw0 hw1 K extent hK link hl p)
      (finiteLossStream hw0 hw1 K extent hK link hl p) := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := fun k => CReal.ofQ' (L p k))
    (bSeq := fun k => CReal.ofQ' ((finiteLossStream hw0 hw1 K extent hK link hl p).approx k))
  · intro k
    exact CReal.Equiv.refl _
  · exact finiteLossReal_converges hw0 hw1 K extent hK link hl p
  · exact CReal.convergesTo_self _

/-- The scalar finite-loss limit is the squared residual of the actual
original-action completed conditional projection at this physical link. -/
theorem finiteLoss_limit_eq_residual_norm (p : (F).V) :
    Quotient.mk CReal.crealSetoid
        (finiteLossReal hw0 hw1 K extent hK link hl p) =
      normSq ((projections hw0 hw1 K extent hK).residual ⟨link, hl⟩
        (embedV F p)) := by
  let i : PhysicalLink extent := ⟨link, hl⟩
  let P := projections hw0 hw1 K extent hK
  let x := embedV F p
  let y : GNSCompletionSpace F := Quotient.mk (cauchySetoid F) (A p)
  have hself : (F).cinnerCompl x x =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' ((F).B p p)) :=
    (F).cinnerCompl_embed p p
  have hcross : (F).cinnerCompl x y =
      Quotient.mk CReal.crealSetoid ((F).cinnerRep (constCauchy F p) (A p)) := rfl
  have hop : P.op i x = y := by
    exact (conditionalProjection_embed hw0 hw1 K extent hK link hl p).trans
      (inPlace_limit_eq_conditionalUpdate hw0 hw1 K extent hK link hl p).symm
  have hnorm : normSq (P.op i x) = (F).cinnerCompl x (P.op i x) := by
    exact (P.self_pairing i x).trans ((F).cinnerCompl_comm _ _)
  calc
    Quotient.mk CReal.crealSetoid (finiteLossReal hw0 hw1 K extent hK link hl p)
        = Quotient.mk CReal.crealSetoid
            (finiteLossStream hw0 hw1 K extent hK link hl p) :=
          Quotient.sound (finiteLossReal_equiv_stream hw0 hw1 K extent hK link hl p)
    _ = CReal.RCsub ((F).cinnerCompl x x) ((F).cinnerCompl x y) := by
          rw [hself, hcross, CReal.RCsub_mk]
          exact Quotient.sound (CReal.sub_congr_right
            (pairingStream_equiv_cinnerRep hw0 hw1 K extent hK link hl p))
    _ = normSq (P.residual i x) := by
          rw [← hop, ← hnorm]
          exact (P.single_loss i x).symm

#print axioms pairingStream
#print axioms finiteLossStream
#print axioms finiteLossCauchy
#print axioms finiteLossReal
#print axioms finiteLossReal_converges
#print axioms finiteLoss_limit_eq_residual_norm

end YMGap.Continuum.BF4ExactSlabReciprocalEnergyLimit
