/-
# Fixed-extent heat-cutoff limit of the original Chebyshev covariance bound

The finite original-action inequality has one cutoff-independent Chebyshev
factor. We pass that same inequality to the already-defined CReal covariance
at fixed extent. This does not take a thermodynamic or physical-spacing limit.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovariance
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.BF4ExactSlabSmallNomeCovarianceRate
import YMGap.Continuum.BF4ExactSlabConditionalVariancePositive
import YMGap.Continuum.ContinuousTransferCalculus

namespace YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovariance
open YMGap.Continuum.BF4ExactSlabSmallNomeCovarianceRate
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

/-- The original mixed covariance at the existing heat-cutoff limit has the
same Chebyshev factor and both original diagonal variances. The literal
support and sixteen-layer separation premise are fixed across the cutoff. -/
theorem covariance_sq_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd)
    (extent n : Nat) (support testSupport : List Z4Link)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hpl : LinkLocal extent support p)
    (hql : LinkLocal extent testSupport q)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    let ids := slabPhysicalFaceEdges extent
    let physical := fun (id : Nat) (h : id ∈ ids) => h
    let C := covariance w hw0 hw1 extent ids physical
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (ofQ' (covarianceFactor hd hm n * covarianceFactor hd hm n))
        (CReal.mul (C p p) (C q q))) := by
  dsimp only
  let ids := slabPhysicalFaceEdges extent
  let physical := fun (id : Nat) (h : id ∈ ids) => h
  let f := fun a b : RatPoly => covariance w hw0 hw1 extent ids physical a b
  let v := fun a b : RatPoly => fun stage : Nat =>
    finiteCovariance w hw0 hw1 extent ids physical a b stage
  let factor := covarianceFactor hd hm n * covarianceFactor hd hm n
  have hpq := finite_covariance_converges w hw0 hw1 extent ids physical p q
  have hpp := finite_covariance_converges w hw0 hw1 extent ids physical p p
  have hqq := finite_covariance_converges w hw0 hw1 extent ids physical q q
  have hleft : ConvergesTo
      (fun stage => CReal.mul (ofQ' (v p q stage)) (ofQ' (v p q stage)))
      (CReal.mul (f p q) (f p q)) :=
    convergesTo_mul_general hpq hpq
  have hright : ConvergesTo
      (fun stage => CReal.mul (ofQ' factor)
        (CReal.mul (ofQ' (v p p stage)) (ofQ' (v q q stage))))
      (CReal.mul (ofQ' factor) (CReal.mul (f p p) (f q q))) :=
    CReal.convergesTo_const_mul (ofQ' factor)
      (convergesTo_mul_general hpp hqq)
  change leEv (CReal.mul (f p q) (f p q))
    (CReal.mul (ofQ' factor) (CReal.mul (f p p) (f q q)))
  apply CReal.leEv_of_convergesTo_le hleft hright
  intro stage
  have hfin := finiteCovariance_sq_bound hw0 hw1 hsmall hd hm extent stage n
    support testSupport
    (⟨p, hp⟩ : (fullData hw0 hw1 (headCutoff w + stage) extent
      (Nat.le_add_right _ _)).V)
    (⟨q, hq⟩ : (fullData hw0 hw1 (headCutoff w + stage) extent
      (Nat.le_add_right _ _)).V)
    hpl hql hsep
  change leEv
    (CReal.mul (ofQ' (v p q stage)) (ofQ' (v p q stage)))
    (CReal.mul (ofQ' factor)
      (CReal.mul (ofQ' (v p p stage)) (ofQ' (v q q stage)))) at hfin
  exact hfin

/-- The cutoff-removed diagonal is nonnegative for the same original
normalized action. This uses the finite completed variance pin. -/
theorem covariance_diagonal_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    leEv czero
      (covariance w hw0 hw1 extent (slabPhysicalFaceEdges extent)
        (fun _ hi => hi) p p) := by
  let ids := slabPhysicalFaceEdges extent
  let physical := fun (id : Nat) (h : id ∈ ids) => h
  have hlimit := finite_covariance_converges w hw0 hw1 extent ids physical p p
  apply CReal.leEv_of_convergesTo_le (CReal.convergesTo_const czero) hlimit
  intro stage
  have hfin := BF4ExactSlabConditionalVariancePositive.finiteVariance_nonnegative
    hw0 hw1 extent stage
    (⟨p, hp⟩ : (fullData hw0 hw1 (headCutoff w + stage) extent
      (Nat.le_add_right _ _)).V)
  change leEv czero
    (ofQ' (finiteCovariance w hw0 hw1 extent ids physical p p stage)) at hfin
  exact hfin

/-- The fixed-nome factor is bounded geometrically after removal of the heat
cutoff. This remains a fixed-extent original covariance statement. -/
theorem covariance_sq_geometric_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd)
    (extent n : Nat) (support testSupport : List Z4Link)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hpl : LinkLocal extent support p)
    (hql : LinkLocal extent testSupport q)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    let C := covariance w hw0 hw1 extent (slabPhysicalFaceEdges extent)
      (fun _ hi => hi)
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (ofQ' ((rate hd hm)^n * (rate hd hm)^n))
        (CReal.mul (C p p) (C q q))) := by
  dsimp only
  let C := covariance w hw0 hw1 extent (slabPhysicalFaceEdges extent)
    (fun _ hi => hi)
  have hprod : leEv czero (CReal.mul (C p p) (C q q)) :=
    CReal.mul_nonneg
      (covariance_diagonal_nonnegative hw0 hw1 extent p hp)
      (covariance_diagonal_nonnegative hw0 hw1 extent q hq)
  exact CReal.leEv_trans
    (covariance_sq_bound hw0 hw1 hsmall hd hm extent n
      support testSupport p q hp hq hpl hql hsep)
    (CReal.leEv_scalar_mono
      (covarianceFactor_sq_le_rate_pow_sq hd hm n) hprod)

/-- A data-level degree threshold makes the relative squared covariance
factor at most `epsilon²`; the two variance factors stay original. -/
theorem covariance_sq_epsilon_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hm : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd)
    (extent n : Nat) (support testSupport : List Z4Link)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hpl : LinkLocal extent support p)
    (hql : LinkLocal extent testSupport q)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hn : degreeModulus hd hm epsilon ≤ n) :
    let C := covariance w hw0 hw1 extent (slabPhysicalFaceEdges extent)
      (fun _ hi => hi)
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (ofQ' (epsilon * epsilon))
        (CReal.mul (C p p) (C q q))) := by
  dsimp only
  let C := covariance w hw0 hw1 extent (slabPhysicalFaceEdges extent)
    (fun _ hi => hi)
  have hprod : leEv czero (CReal.mul (C p p) (C q q)) :=
    CReal.mul_nonneg
      (covariance_diagonal_nonnegative hw0 hw1 extent p hp)
      (covariance_diagonal_nonnegative hw0 hw1 extent q hq)
  have hfac : covarianceFactor hd hm n * covarianceFactor hd hm n ≤
      epsilon * epsilon :=
    EigenvalueShiftBound.sq_mono
      (Q'.le_of_lt (covarianceFactor_positive hd hm n))
      (covarianceFactor_le_of_modulus hd hm epsilon hepsilon n hn)
  exact CReal.leEv_trans
    (covariance_sq_bound hw0 hw1 hsmall hd hm extent n
      support testSupport p q hp hq hpl hql hsep)
    (CReal.leEv_scalar_mono hfac hprod)

open BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)

/-- At nome `1/1024`, all smallness and positive-margin premises are discharged.
The remaining premises specify the actual observables and their separation. -/
theorem existingNome_covariance_sq_geometric_bound
    (extent n : Nat) (support testSupport : List Z4Link)
    (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hpl : LinkLocal extent support p)
    (hql : LinkLocal extent testSupport q)
    (hsep : LinksDisjoint (grow extent (16*n) support) testSupport) :
    let C := covariance nome nome_pos nome_lt_one extent (slabPhysicalFaceEdges extent)
      (fun _ hi => hi)
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (ofQ' (existingNomeRate^n * existingNomeRate^n))
        (CReal.mul (C p p) (C q q))) :=
  covariance_sq_geometric_bound nome_pos nome_lt_one
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.1
    BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2
    BF4ExactSlabConditionalGeneratorMargin.existingNome_margin_positive
    extent n support testSupport p q hp hq hpl hql hsep

end YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit

#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit.covariance_sq_bound
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit.covariance_diagonal_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit.covariance_sq_geometric_bound
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit.covariance_sq_epsilon_bound
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeChebyshevCovarianceLimit.existingNome_covariance_sq_geometric_bound
