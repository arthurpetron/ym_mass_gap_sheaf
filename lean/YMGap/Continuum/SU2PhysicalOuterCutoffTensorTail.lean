/-
# Physical degree-thirteen SU(2) outer-cutoff tensor tails

The exact four-dimensional incidence ledger in
`Z4SpinDependentIncidenceProductBound` charges the complete product of link
intertwiner multiplicities by `(spin+1)^12` on each plaquette.  Multiplying by
the heat-kernel dimension factor gives exactly

  tailTerm w 13 spin = (spin+1)^13 w^(C4 spin).

This module instantiates the existing polynomial Casimir tail at degree
thirteen and tensors it over a fixed finite face carrier.  If the retained
cutoff `M` satisfies the two explicit rational hypotheses consumed by
`BondMovingScaledNorm.tail_modulus`, then every later outer cutoff `K` has
one-coordinate shell mass at most `dyad precision`.  The recursive union
envelope depends on the fixed number of faces, but not on `K`.

This is the analytic scalar layer needed before a finite-Fubini comparison
with the actual SU(2) slab new sector.  The physical pointwise domination at
the strong-coupling anchor is re-exported at the end, making explicit that
degree thirteen is not an arbitrary overestimate.

## Axiom gate

Finite `Nat`/`Q'` recursion and already-audited Casimir tails only.  No
`Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.Z4SpinSummedFaceActivityBound

namespace YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail

set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- The facewise polynomial degree forced by four boundary-link incidences
and the cubic local intertwiner bound: `4 * 3 + 1 = 13`. -/
def physicalFacePolynomialDegree : Nat := 13

private theorem add_nonnegative {a b : Q'}
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a + b := by
  have h := Q'.add_le_add ha hb
  rw [Q'.zero_add'] at h
  exact h

private theorem finSum_nonnegative_local (f : Nat → Q')
    (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ M, (0 : Q') ≤ finSum f M
  | 0 => Q'.le_refl' 0
  | M + 1 => Q'.zero_le_add _ _
      (finSum_nonnegative_local f hf M) (hf M)

private theorem finSum_split_local (f : Nat → Q') (N : Nat) :
    ∀ L : Nat,
      finSum f (N + L) ≈
        finSum f N +
          finSum (fun offset => f (N + offset)) L
  | 0 => by
      rw [Nat.add_zero, finSum_zero, Q'.add_zero']
      exact Q'.eqv_refl _
  | L + 1 => by
      have ih := finSum_split_local f N L
      show
        finSum f (N + L) + f (N + L) ≈
          finSum f N +
            (finSum (fun offset => f (N + offset)) L +
              f (N + L))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih)
        (Q'.add_assoc_eqv _ _ _)

/-! ## 1. Degree-thirteen one-coordinate shell and ceiling -/

/-- Inclusive one-face partial mass through spin `K`. -/
def su2PhysicalLabelPartial (w : Q') (K : Nat) : Q' :=
  finSum (tailTerm w physicalFacePolynomialDegree) (K + 1)

/-- One-face mass on spins strictly above `M` and at most `K`. -/
def su2PhysicalOuterShellMass
    (w : Q') (M K : Nat) : Q' :=
  tailWindow w physicalFacePolynomialDegree
    (M + 1) (K - M)

/-- A cutoff-independent one-coordinate ceiling obtained by controlling the
tail after a supplied base cutoff `S` at dyadic precision zero. -/
def su2PhysicalHeatCeiling (w : Q') (S : Nat) : Q' :=
  finSum (tailTerm w physicalFacePolynomialDegree) S + dyad 0

theorem su2PhysicalLabelPartial_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (K : Nat) :
    (0 : Q') ≤ su2PhysicalLabelPartial w K := by
  unfold su2PhysicalLabelPartial
  exact
    finSum_nonnegative_local _
      (tailTerm_nonneg
        (Q'.le_of_lt hw0) physicalFacePolynomialDegree)
      _

theorem su2PhysicalOuterShellMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K : Nat) :
    (0 : Q') ≤ su2PhysicalOuterShellMass w M K := by
  unfold su2PhysicalOuterShellMass tailWindow
  exact
    finSum_nonnegative_local _
      (fun offset =>
        tailTerm_nonneg
          (Q'.le_of_lt hw0)
          physicalFacePolynomialDegree
          (M + 1 + offset))
      _

theorem su2PhysicalHeatCeiling_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (S : Nat) :
    (0 : Q') ≤ su2PhysicalHeatCeiling w S := by
  unfold su2PhysicalHeatCeiling
  exact add_nonnegative
    (finSum_nonnegative_local _
      (tailTerm_nonneg
        (Q'.le_of_lt hw0) physicalFacePolynomialDegree)
      S)
    (dyad_nonneg 0)

/-- The degree-thirteen outer shell is uniformly bounded in every later
outer cutoff.  Both hypotheses are explicit rational inequalities at the
first omitted spin `M+1`. -/
theorem su2PhysicalOuterShellMass_le_dyad
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (precision : Nat) {M K : Nat}
    (hcut :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * (M + 1) + 3) ≤
        HalfPow.half)
    (hhead :
      tailTerm w physicalFacePolynomialDegree (M + 1) ≤
        dyad (precision + 1)) :
    su2PhysicalOuterShellMass w M K ≤
      dyad precision := by
  unfold su2PhysicalOuterShellMass
  exact tail_modulus
    hw0 hw1 physicalFacePolynomialDegree precision
    (M + 1) hcut hhead (K - M)

/-- The base-cutoff hypotheses at precision zero give one ceiling for every
inclusive finite label partial. -/
theorem su2PhysicalLabelPartial_le_heatCeiling
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (S : Nat)
    (hcut :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * S + 3) ≤
        HalfPow.half)
    (hhead :
      tailTerm w physicalFacePolynomialDegree S ≤
        dyad 1) :
    ∀ K,
      su2PhysicalLabelPartial w K ≤
        su2PhysicalHeatCeiling w S := by
  intro K
  by_cases hKS : K + 1 ≤ S
  · have hprefix :
        finSum (tailTerm w physicalFacePolynomialDegree) (K + 1) ≤
          finSum (tailTerm w physicalFacePolynomialDegree) S :=
      RationalTail.finSum_monotone_of_nonneg
        (tailTerm w physicalFacePolynomialDegree)
        (tailTerm_nonneg
          (Q'.le_of_lt hw0) physicalFacePolynomialDegree)
        (K + 1) S hKS
    exact Q'.le_trans' _ _ _ hprefix
      (Q'.add_le_self_of_nonneg _ _ (dyad_nonneg 0))
  · have hSK : S ≤ K + 1 := by omega
    obtain ⟨length, hlength⟩ :=
      Nat.exists_eq_add_of_le hSK
    have htail :
        tailWindow w physicalFacePolynomialDegree S length ≤
          dyad 0 :=
      tail_modulus hw0 hw1 physicalFacePolynomialDegree
        0 S hcut hhead length
    unfold su2PhysicalLabelPartial su2PhysicalHeatCeiling
    rw [hlength]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (finSum_split_local
          (tailTerm w physicalFacePolynomialDegree)
          S length))
      (Q'.add_le_add_left _ _ _ htail)

/-! ## 2. Fixed-dimensional tensor and outside-union envelope -/

def su2PhysicalTensorMass
    (w : Q') (K : Nat) : Nat → Q'
  | 0 => 1
  | dimension + 1 =>
      su2PhysicalLabelPartial w K *
        su2PhysicalTensorMass w K dimension

def su2PhysicalTensorOutsideUnionMass
    (w : Q') (M K : Nat) : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      su2PhysicalOuterShellMass w M K *
          su2PhysicalTensorMass w K dimension +
        su2PhysicalLabelPartial w K *
          su2PhysicalTensorOutsideUnionMass
            w M K dimension

/-- Degree-thirteen outer-cutoff-free tensor envelope. -/
def su2PhysicalTensorTailEnvelope
    (w : Q') (S M precision : Nat) : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      dyad precision *
          su2PhysicalHeatCeiling w S ^ dimension +
        su2PhysicalHeatCeiling w S *
          su2PhysicalTensorTailEnvelope
            w S M precision dimension

theorem su2PhysicalTensorMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (K : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        su2PhysicalTensorMass w K dimension
  | 0 => Q'.zero_le_one
  | dimension + 1 =>
      Q'.mul_nonneg _ _
        (su2PhysicalLabelPartial_nonnegative hw0 K)
        (su2PhysicalTensorMass_nonnegative
          hw0 K dimension)

theorem su2PhysicalTensorOutsideUnionMass_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (M K : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        su2PhysicalTensorOutsideUnionMass
          w M K dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      add_nonnegative
        (Q'.mul_nonneg _ _
          (su2PhysicalOuterShellMass_nonnegative
            hw0 M K)
          (su2PhysicalTensorMass_nonnegative
            hw0 K dimension))
        (Q'.mul_nonneg _ _
          (su2PhysicalLabelPartial_nonnegative hw0 K)
          (su2PhysicalTensorOutsideUnionMass_nonnegative
            hw0 M K dimension))

theorem su2PhysicalTensorTailEnvelope_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (S M precision : Nat) :
    ∀ dimension,
      (0 : Q') ≤
        su2PhysicalTensorTailEnvelope
          w S M precision dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      add_nonnegative
        (Q'.mul_nonneg _ _
          (dyad_nonneg precision)
          (Q'.pow_nonneg _
            (su2PhysicalHeatCeiling_nonnegative hw0 S)
            dimension))
        (Q'.mul_nonneg _ _
          (su2PhysicalHeatCeiling_nonnegative hw0 S)
          (su2PhysicalTensorTailEnvelope_nonnegative
            hw0 S M precision dimension))

theorem su2PhysicalTensorMass_le_ceilingPow
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (S : Nat)
    (hcutBase :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * S + 3) ≤
        HalfPow.half)
    (hheadBase :
      tailTerm w physicalFacePolynomialDegree S ≤
        dyad 1)
    (K : Nat) :
    ∀ dimension,
      su2PhysicalTensorMass w K dimension ≤
        su2PhysicalHeatCeiling w S ^ dimension
  | 0 => Q'.le_refl' 1
  | dimension + 1 => by
      have hpartial :=
        su2PhysicalLabelPartial_le_heatCeiling
          hw0 hw1 S hcutBase hheadBase K
      have htail :=
        su2PhysicalTensorMass_le_ceilingPow
          hw0 hw1 S hcutBase hheadBase K dimension
      have htail0 :=
        su2PhysicalTensorMass_nonnegative
          hw0 K dimension
      have hceiling0 :=
        su2PhysicalHeatCeiling_nonnegative hw0 S
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right
          _ _ _ hpartial htail0)
        (Q'.mul_le_mul_of_nonneg_left
          _ _ _ htail hceiling0)

/-- Main physical-degree outer-cutoff tensor estimate.  Its right-hand side
is independent of the later Peter--Weyl cutoff `K`. -/
theorem su2PhysicalTensorOutsideUnionMass_le_envelope
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (S precision : Nat) {M K : Nat}
    (hcutBase :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * S + 3) ≤
        HalfPow.half)
    (hheadBase :
      tailTerm w physicalFacePolynomialDegree S ≤
        dyad 1)
    (hcutTail :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * (M + 1) + 3) ≤
        HalfPow.half)
    (hheadTail :
      tailTerm w physicalFacePolynomialDegree (M + 1) ≤
        dyad (precision + 1)) :
    ∀ dimension,
      su2PhysicalTensorOutsideUnionMass
          w M K dimension ≤
        su2PhysicalTensorTailEnvelope
          w S M precision dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 => by
      have houter :=
        su2PhysicalOuterShellMass_le_dyad
          hw0 hw1 precision
          (M := M) (K := K)
          hcutTail hheadTail
      have htotal :=
        su2PhysicalTensorMass_le_ceilingPow
          hw0 hw1 S hcutBase hheadBase K dimension
      have hpartial :=
        su2PhysicalLabelPartial_le_heatCeiling
          hw0 hw1 S hcutBase hheadBase K
      have houtside :=
        su2PhysicalTensorOutsideUnionMass_le_envelope
          hw0 hw1 S precision
          (M := M) (K := K)
          hcutBase hheadBase hcutTail hheadTail
          dimension
      have htotal0 :=
        su2PhysicalTensorMass_nonnegative
          hw0 K dimension
      have htail0 := dyad_nonneg precision
      have houtside0 :=
        su2PhysicalTensorOutsideUnionMass_nonnegative
          hw0 M K dimension
      have hceiling0 :=
        su2PhysicalHeatCeiling_nonnegative hw0 S
      have hleft1 :
          su2PhysicalOuterShellMass w M K *
              su2PhysicalTensorMass w K dimension ≤
            dyad precision *
              su2PhysicalTensorMass w K dimension :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ houter htotal0
      have hleft2 :
          dyad precision *
              su2PhysicalTensorMass w K dimension ≤
            dyad precision *
              su2PhysicalHeatCeiling w S ^ dimension :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ htotal htail0
      have hright1 :
          su2PhysicalLabelPartial w K *
              su2PhysicalTensorOutsideUnionMass
                w M K dimension ≤
            su2PhysicalHeatCeiling w S *
              su2PhysicalTensorOutsideUnionMass
                w M K dimension :=
        Q'.mul_le_mul_of_nonneg_right
          _ _ _ hpartial houtside0
      have hright2 :
          su2PhysicalHeatCeiling w S *
              su2PhysicalTensorOutsideUnionMass
                w M K dimension ≤
            su2PhysicalHeatCeiling w S *
              su2PhysicalTensorTailEnvelope
                w S M precision dimension :=
        Q'.mul_le_mul_of_nonneg_left
          _ _ _ houtside hceiling0
      exact Q'.add_le_add
        (Q'.le_trans' _ _ _ hleft1 hleft2)
        (Q'.le_trans' _ _ _ hright1 hright2)

/-- Fixed face-list form ready for the physical finite-Fubini bridge. -/
theorem finiteFaceListSU2OuterUniformTensorBound
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (S precision : Nat) {M K : Nat}
    (faces : List Nat)
    (hcutBase :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * S + 3) ≤
        HalfPow.half)
    (hheadBase :
      tailTerm w physicalFacePolynomialDegree S ≤
        dyad 1)
    (hcutTail :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * (M + 1) + 3) ≤
        HalfPow.half)
    (hheadTail :
      tailTerm w physicalFacePolynomialDegree (M + 1) ≤
        dyad (precision + 1)) :
    su2PhysicalTensorOutsideUnionMass
        w M K faces.length ≤
      su2PhysicalTensorTailEnvelope
        w S M precision faces.length :=
  su2PhysicalTensorOutsideUnionMass_le_envelope
    hw0 hw1 S precision
    hcutBase hheadBase hcutTail hheadTail
    faces.length

/-! ## 3. Link to the actual four-dimensional spin-foam term -/

/-- At the proved strong-coupling anchor, the literal interacting spin-foam
term is pointwise dominated by the product of precisely the same
degree-thirteen one-face weights used above. -/
theorem anchorPhysicalTerm_le_degreeThirteenFaceProduct
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalTerm anchorCoupling K n physical ≤
      eliminateLinks
        (fun edge =>
          tailTerm anchorCoupling
            physicalFacePolynomialDegree
            (physical edge))
        (List.range (plaquetteEdgeCount n)) := by
  simpa [anchorDecoratedFaceProduct,
    anchorDecoratedFaceActivity,
    physicalFacePolynomialDegree] using
      (parametricKPhysicalTerm_anchor_le_decoratedFaceProduct
        hphysical)

#print axioms su2PhysicalOuterShellMass_le_dyad
#print axioms su2PhysicalLabelPartial_le_heatCeiling
#print axioms su2PhysicalTensorMass_le_ceilingPow
#print axioms su2PhysicalTensorOutsideUnionMass_le_envelope
#print axioms finiteFaceListSU2OuterUniformTensorBound
#print axioms anchorPhysicalTerm_le_degreeThirteenFaceProduct

end YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
