/-
# Closedness of literal dyadic plaquette subdivision

The four coplanar children of every coarse plaquette form the ordinary
cellular subdivision of that plaquette.  This module proves that the induced
map on finite mod-two 2-chains commutes with the cellular boundary.  Hence a
duplicate-free coarse support with even face incidence refines to a
duplicate-free fine support with even face incidence.

This is finite cubical geometry only.  It does not construct the mixed
one-, two-, or three-child lifts needed for arbitrary SU(2) coarse spins, and
it makes no measure, continuum, reconstruction, or mass-gap claim.
-/

import YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
import YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel

namespace YMGap.Continuum.Z4DyadicSubdivisionClosure

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4DyadicModTwoCellularKernel
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Coefficient-level cellular subdivision -/

/-- A fine face lies in the literal dyadic subdivision grid when its two
coordinates transverse to the face are even. -/
def dyadicFaceOnSubdivisionGrid : Z4Plaq → Prop
  | ((_, _, c, d), .p01) => c % 2 = 0 ∧ d % 2 = 0
  | ((_, b, _, d), .p02) => b % 2 = 0 ∧ d % 2 = 0
  | ((_, b, c, _), .p03) => b % 2 = 0 ∧ c % 2 = 0
  | ((a, _, _, d), .p12) => a % 2 = 0 ∧ d % 2 = 0
  | ((a, _, c, _), .p13) => a % 2 = 0 ∧ c % 2 = 0
  | ((a, b, _, _), .p23) => a % 2 = 0 ∧ b % 2 = 0

instance dyadicFaceOnSubdivisionGridDecidable (fine : Z4Plaq) :
    Decidable (dyadicFaceOnSubdivisionGrid fine) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := fine
  cases plane <;> simp only [dyadicFaceOnSubdivisionGrid] <;>
    infer_instance

/-- Pull a coarse face coefficient onto all four coplanar dyadic children.
The two coordinates transverse to the face must lie on the even coarse grid;
the two spanning coordinates are free dyadic bits. -/
def dyadicFaceSubdivision
    (coefficient : Z4Plaq → Bool) : Z4Plaq → Bool
  | ((a, b, c, d), .p01) =>
      if c % 2 = 0 ∧ d % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .p01)
      else false
  | ((a, b, c, d), .p02) =>
      if b % 2 = 0 ∧ d % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .p02)
      else false
  | ((a, b, c, d), .p03) =>
      if b % 2 = 0 ∧ c % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .p03)
      else false
  | ((a, b, c, d), .p12) =>
      if a % 2 = 0 ∧ d % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .p12)
      else false
  | ((a, b, c, d), .p13) =>
      if a % 2 = 0 ∧ c % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .p13)
      else false
  | ((a, b, c, d), .p23) =>
      if a % 2 = 0 ∧ b % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .p23)
      else false

theorem dyadicFaceSubdivision_eq_if
    (coefficient : Z4Plaq → Bool) (fine : Z4Plaq) :
    dyadicFaceSubdivision coefficient fine =
      if dyadicFaceOnSubdivisionGrid fine then
        coefficient (dyadicPlaquetteProjection fine)
      else false := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := fine
  cases plane <;> rfl

/-- Subdivision of a coarse link coefficient.  A fine unit link lies over a
coarse link exactly when its three transverse coordinates are even. -/
def dyadicLinkSubdivision
    (coefficient : Z4Link → Bool) : Z4Link → Bool
  | ((a, b, c, d), .x0) =>
      if b % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .x0)
      else false
  | ((a, b, c, d), .x1) =>
      if a % 2 = 0 ∧ c % 2 = 0 ∧ d % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .x1)
      else false
  | ((a, b, c, d), .x2) =>
      if a % 2 = 0 ∧ b % 2 = 0 ∧ d % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .x2)
      else false
  | ((a, b, c, d), .x3) =>
      if a % 2 = 0 ∧ b % 2 = 0 ∧ c % 2 = 0 then
        coefficient ((a / 2, b / 2, c / 2, d / 2), .x3)
      else false

private theorem bool_xor_self_local (bit : Bool) : (bit ^^ bit) = false := by
  cases bit <;> rfl

private theorem odd_half_local (coordinate : Nat) :
    (2 * coordinate + 1) / 2 = coordinate := by
  rw [Nat.mul_add_div (m := 2) (by omega) coordinate 1]
  simp

private theorem twice_half_eq_of_even_local
    {n : Nat} (heven : n % 2 = 0) :
    2 * (n / 2) = n := by
  simpa only [heven, Nat.zero_add] using Nat.mod_add_div n 2

private theorem twice_half_add_one_eq_of_not_even_local
    {n : Nat} (hodd : n % 2 ≠ 0) :
    2 * (n / 2) + 1 = n := by
  have hone : n % 2 = 1 :=
    (Nat.mod_two_eq_zero_or_one n).resolve_left hodd
  simpa only [hone, Nat.add_comm] using Nat.mod_add_div n 2

private theorem decide_toNat_eq_indicator_local
    (proposition : Prop) [Decidable proposition] :
    (decide proposition).toNat = if proposition then 1 else 0 := by
  by_cases h : proposition <;> simp [h]

/-- The one-dimensional cancellation used on each subdivided coarse edge.
At an odd fine coordinate the two adjacent fine faces have the same parent
and cancel.  At an even coordinate they are exactly the forward and backward
coarse faces. -/
private theorem dyadicPairXor_local (value : Nat → Bool) (n : Nat) :
    (value (n / 2) ^^
      (if n = 0 then false else value ((n - 1) / 2))) =
      if n % 2 = 0 then
        value (n / 2) ^^
          (if n / 2 = 0 then false else value (n / 2 - 1))
      else false := by
  by_cases hzero : n = 0
  · subst n
    rfl
  · rw [if_neg hzero]
    by_cases heven : n % 2 = 0
    · rw [if_pos heven]
      have hnTwo : 2 ≤ n := by omega
      have hhalf : n / 2 ≠ 0 := by omega
      have hpred : (n - 1) / 2 = n / 2 - 1 := by omega
      rw [if_neg hhalf]
      rw [hpred]
    · rw [if_neg heven]
      have hhalf : (n - 1) / 2 = n / 2 := by omega
      rw [hhalf]
      exact bool_xor_self_local _

private theorem dyadicIncidentPlanePair_subdivision
    (coefficient : Z4Plaq → Bool) (fineVertex : Z4Vertex)
    (edgeDirection transverse : Dir4) (hne : edgeDirection ≠ transverse) :
    incidentPlanePairCoefficient
        (dyadicFaceSubdivision coefficient)
        fineVertex edgeDirection transverse =
      dyadicLinkSubdivision
        (fun coarseLink =>
          incidentPlanePairCoefficient coefficient coarseLink.1
            edgeDirection transverse)
        (fineVertex, edgeDirection) := by
  obtain ⟨a, b, c, d⟩ := fineVertex
  cases edgeDirection with
  | x0 =>
      cases transverse with
      | x0 => exact False.elim (hne rfl)
      | x1 =>
          by_cases hc : c % 2 = 0
          · by_cases hd : d % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hc, hd] using
                dyadicPairXor_local
                  (fun b' => coefficient
                    ((a / 2, b', c / 2, d / 2), .p01)) b
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hc, hd]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, hc]
      | x2 =>
          by_cases hb : b % 2 = 0
          · by_cases hd : d % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hd] using
                dyadicPairXor_local
                  (fun c' => coefficient
                    ((a / 2, b / 2, c', d / 2), .p02)) c
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hd]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, hb]
      | x3 =>
          by_cases hb : b % 2 = 0
          · by_cases hc : c % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hc] using
                dyadicPairXor_local
                  (fun d' => coefficient
                    ((a / 2, b / 2, c / 2, d'), .p03)) d
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hc]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, hb]
  | x1 =>
      cases transverse with
      | x0 =>
          by_cases hc : c % 2 = 0
          · by_cases hd : d % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hc, hd] using
                dyadicPairXor_local
                  (fun a' => coefficient
                    ((a', b / 2, c / 2, d / 2), .p01)) a
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hc, hd]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, hc]
      | x1 => exact False.elim (hne rfl)
      | x2 =>
          by_cases ha : a % 2 = 0
          · by_cases hd : d % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hd] using
                dyadicPairXor_local
                  (fun c' => coefficient
                    ((a / 2, b / 2, c', d / 2), .p12)) c
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hd]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, ha]
      | x3 =>
          by_cases ha : a % 2 = 0
          · by_cases hc : c % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hc] using
                dyadicPairXor_local
                  (fun d' => coefficient
                    ((a / 2, b / 2, c / 2, d'), .p13)) d
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hc]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, ha]
  | x2 =>
      cases transverse with
      | x0 =>
          by_cases hb : b % 2 = 0
          · by_cases hd : d % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hd] using
                dyadicPairXor_local
                  (fun a' => coefficient
                    ((a', b / 2, c / 2, d / 2), .p02)) a
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hd]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, hb]
      | x1 =>
          by_cases ha : a % 2 = 0
          · by_cases hd : d % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hd] using
                dyadicPairXor_local
                  (fun b' => coefficient
                    ((a / 2, b', c / 2, d / 2), .p12)) b
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hd]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, ha]
      | x2 => exact False.elim (hne rfl)
      | x3 =>
          by_cases ha : a % 2 = 0
          · by_cases hb : b % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hb] using
                dyadicPairXor_local
                  (fun d' => coefficient
                    ((a / 2, b / 2, c / 2, d'), .p23)) d
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hb]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, ha]
  | x3 =>
      cases transverse with
      | x0 =>
          by_cases hb : b % 2 = 0
          · by_cases hc : c % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hc] using
                dyadicPairXor_local
                  (fun a' => coefficient
                    ((a', b / 2, c / 2, d / 2), .p03)) a
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, hb, hc]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, hb]
      | x1 =>
          by_cases ha : a % 2 = 0
          · by_cases hc : c % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hc] using
                dyadicPairXor_local
                  (fun b' => coefficient
                    ((a / 2, b', c / 2, d / 2), .p13)) b
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hc]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, ha]
      | x2 =>
          by_cases ha : a % 2 = 0
          · by_cases hb : b % 2 = 0
            · simpa [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hb] using
                dyadicPairXor_local
                  (fun c' => coefficient
                    ((a / 2, b / 2, c', d / 2), .p23)) c
            · simp [incidentPlanePairCoefficient,
                backwardFaceCoefficient, vertexCoord,
                dyadicFaceSubdivision, dyadicLinkSubdivision,
                subE, planeOf, ha, hb]
          · simp [incidentPlanePairCoefficient,
              backwardFaceCoefficient, vertexCoord,
              dyadicFaceSubdivision, dyadicLinkSubdivision,
              subE, planeOf, ha]
      | x3 => exact False.elim (hne rfl)

private theorem dyadicLinkSubdivision_pointwise_three
    (first second third : Z4Link → Bool) (fineLink : Z4Link) :
    dyadicLinkSubdivision
        (fun link => first link ^^ (second link ^^ third link)) fineLink =
      (dyadicLinkSubdivision first fineLink ^^
        (dyadicLinkSubdivision second fineLink ^^
          dyadicLinkSubdivision third fineLink)) := by
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := fineLink
  cases direction <;> simp only [dyadicLinkSubdivision] <;>
    split <;> simp_all

/-- Cellular boundary commutes with literal four-cell subdivision.  Internal
fine links occur twice and cancel; fine links on the subdivided coarse grid
carry exactly the corresponding coarse boundary coefficient. -/
theorem cellularBoundaryCoefficient_dyadicFaceSubdivision
    (coefficient : Z4Plaq → Bool) (fineLink : Z4Link) :
    cellularBoundaryCoefficient (dyadicFaceSubdivision coefficient) fineLink =
      dyadicLinkSubdivision
        (cellularBoundaryCoefficient coefficient) fineLink := by
  obtain ⟨fineVertex, direction⟩ := fineLink
  cases direction with
  | x0 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_subdivision coefficient fineVertex .x0 .x1
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x0 .x2
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x0 .x3
          (by decide)]
      exact (dyadicLinkSubdivision_pointwise_three
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x0 .x1)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x0 .x2)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x0 .x3)
        (fineVertex, .x0)).symm
  | x1 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_subdivision coefficient fineVertex .x1 .x0
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x1 .x2
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x1 .x3
          (by decide)]
      exact (dyadicLinkSubdivision_pointwise_three
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x1 .x0)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x1 .x2)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x1 .x3)
        (fineVertex, .x1)).symm
  | x2 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_subdivision coefficient fineVertex .x2 .x0
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x2 .x1
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x2 .x3
          (by decide)]
      exact (dyadicLinkSubdivision_pointwise_three
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x2 .x0)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x2 .x1)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x2 .x3)
        (fineVertex, .x2)).symm
  | x3 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_subdivision coefficient fineVertex .x3 .x0
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x3 .x1
          (by decide),
        dyadicIncidentPlanePair_subdivision coefficient fineVertex .x3 .x2
          (by decide)]
      exact (dyadicLinkSubdivision_pointwise_three
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x3 .x0)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x3 .x1)
        (fun link => incidentPlanePairCoefficient coefficient link.1 .x3 .x2)
        (fineVertex, .x3)).symm

/-! ## 2. Identification with the literal finite support -/

theorem dyadicPlaquetteProjection_dyadicCell
    (coarse : Z4Plaq) (index : DyadicCellIndex) :
    dyadicPlaquetteProjection (dyadicCell coarse index) = coarse := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases index <;> cases plane <;>
    simp [dyadicPlaquetteProjection, dyadicVertexProjection,
      dyadicCell, dyadicVertex, addE, dirsOf,
      odd_half_local]

theorem dyadicCell_onSubdivisionGrid
    (coarse : Z4Plaq) (index : DyadicCellIndex) :
    dyadicFaceOnSubdivisionGrid (dyadicCell coarse index) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases index <;> cases plane <;>
    simp [dyadicFaceOnSubdivisionGrid, dyadicCell, dyadicVertex,
      addE, dirsOf]

theorem exists_dyadicCell_of_onSubdivisionGrid
    (fine : Z4Plaq) (hgrid : dyadicFaceOnSubdivisionGrid fine) :
    ∃ index : DyadicCellIndex,
      dyadicCell (dyadicPlaquetteProjection fine) index = fine := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := fine
  cases plane with
  | p01 =>
      simp only [dyadicFaceOnSubdivisionGrid] at hgrid
      rcases hgrid with ⟨hc, hd⟩
      refine ⟨if a % 2 = 0 then
          (if b % 2 = 0 then .origin else .second)
        else (if b % 2 = 0 then .first else .diagonal), ?_⟩
      by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0 <;>
        simp [ha, hb, dyadicPlaquetteProjection, dyadicVertexProjection,
          dyadicCell, dyadicVertex, addE, dirsOf,
          twice_half_eq_of_even_local,
          twice_half_add_one_eq_of_not_even_local, hc, hd]
  | p02 =>
      simp only [dyadicFaceOnSubdivisionGrid] at hgrid
      rcases hgrid with ⟨hb, hd⟩
      refine ⟨if a % 2 = 0 then
          (if c % 2 = 0 then .origin else .second)
        else (if c % 2 = 0 then .first else .diagonal), ?_⟩
      by_cases ha : a % 2 = 0 <;> by_cases hc : c % 2 = 0 <;>
        simp [ha, hc, dyadicPlaquetteProjection, dyadicVertexProjection,
          dyadicCell, dyadicVertex, addE, dirsOf,
          twice_half_eq_of_even_local,
          twice_half_add_one_eq_of_not_even_local, hb, hd]
  | p03 =>
      simp only [dyadicFaceOnSubdivisionGrid] at hgrid
      rcases hgrid with ⟨hb, hc⟩
      refine ⟨if a % 2 = 0 then
          (if d % 2 = 0 then .origin else .second)
        else (if d % 2 = 0 then .first else .diagonal), ?_⟩
      by_cases ha : a % 2 = 0 <;> by_cases hd : d % 2 = 0 <;>
        simp [ha, hd, dyadicPlaquetteProjection, dyadicVertexProjection,
          dyadicCell, dyadicVertex, addE, dirsOf,
          twice_half_eq_of_even_local,
          twice_half_add_one_eq_of_not_even_local, hb, hc]
  | p12 =>
      simp only [dyadicFaceOnSubdivisionGrid] at hgrid
      rcases hgrid with ⟨ha, hd⟩
      refine ⟨if b % 2 = 0 then
          (if c % 2 = 0 then .origin else .second)
        else (if c % 2 = 0 then .first else .diagonal), ?_⟩
      by_cases hb : b % 2 = 0 <;> by_cases hc : c % 2 = 0 <;>
        simp [hb, hc, dyadicPlaquetteProjection, dyadicVertexProjection,
          dyadicCell, dyadicVertex, addE, dirsOf,
          twice_half_eq_of_even_local,
          twice_half_add_one_eq_of_not_even_local, ha, hd]
  | p13 =>
      simp only [dyadicFaceOnSubdivisionGrid] at hgrid
      rcases hgrid with ⟨ha, hc⟩
      refine ⟨if b % 2 = 0 then
          (if d % 2 = 0 then .origin else .second)
        else (if d % 2 = 0 then .first else .diagonal), ?_⟩
      by_cases hb : b % 2 = 0 <;> by_cases hd : d % 2 = 0 <;>
        simp [hb, hd, dyadicPlaquetteProjection, dyadicVertexProjection,
          dyadicCell, dyadicVertex, addE, dirsOf,
          twice_half_eq_of_even_local,
          twice_half_add_one_eq_of_not_even_local, ha, hc]
  | p23 =>
      simp only [dyadicFaceOnSubdivisionGrid] at hgrid
      rcases hgrid with ⟨ha, hb⟩
      refine ⟨if c % 2 = 0 then
          (if d % 2 = 0 then .origin else .second)
        else (if d % 2 = 0 then .first else .diagonal), ?_⟩
      by_cases hc : c % 2 = 0 <;> by_cases hd : d % 2 = 0 <;>
        simp [hc, hd, dyadicPlaquetteProjection, dyadicVertexProjection,
          dyadicCell, dyadicVertex, addE, dirsOf,
          twice_half_eq_of_even_local,
          twice_half_add_one_eq_of_not_even_local, ha, hb]

/-- Membership in the literal flat-mapped four-cell support is exactly the
coordinate condition used by `dyadicFaceSubdivision`. -/
theorem mem_dyadicSupportCells_iff_subdivision
    (support : List Z4Plaq) (fine : Z4Plaq) :
    fine ∈ dyadicSupportCells support ↔
      dyadicFaceOnSubdivisionGrid fine ∧
        dyadicPlaquetteProjection fine ∈ support := by
  rw [mem_dyadicSupportCells_iff]
  constructor
  · rintro ⟨coarse, hcoarse, hcell⟩
    unfold dyadicPlaquetteCells at hcell
    obtain ⟨index, _, hindex⟩ := List.mem_map.mp hcell
    rw [← hindex]
    exact ⟨dyadicCell_onSubdivisionGrid coarse index,
      by simpa only [dyadicPlaquetteProjection_dyadicCell] using hcoarse⟩
  · rintro ⟨hgrid, hcoarse⟩
    obtain ⟨index, hindex⟩ :=
      exists_dyadicCell_of_onSubdivisionGrid fine hgrid
    refine ⟨dyadicPlaquetteProjection fine, hcoarse, ?_⟩
    have hmem :=
      dyadicCell_mem_cells (dyadicPlaquetteProjection fine) index
    rw [hindex] at hmem
    exact hmem

/-- The coefficient-level subdivision is exactly the characteristic
coefficient of the literal flat-mapped four-cell support. -/
theorem dyadicFaceSubdivision_supportCoefficient
    (support : List Z4Plaq) :
    dyadicFaceSubdivision (supportCoefficient support) =
      supportCoefficient (dyadicSupportCells support) := by
  funext fine
  rw [dyadicFaceSubdivision_eq_if]
  by_cases hgrid : dyadicFaceOnSubdivisionGrid fine
  · simp [hgrid, supportCoefficient,
      mem_dyadicSupportCells_iff_subdivision]
  · simp [hgrid, supportCoefficient,
      mem_dyadicSupportCells_iff_subdivision]

/-- Among the four nondegenerate faces in a coarse cellular fibre, literal
coplanar subdivision occupies exactly the all-even-transverse face.  Its
spin is the coarse support indicator and the other three spins vanish. -/
theorem dyadicFacePreimages_dyadicSupportCells_spins
    (support : List Z4Plaq) (coarse : Z4Plaq) :
    (dyadicFacePreimages coarse).map
        (fun fine =>
          (supportCoefficient (dyadicSupportCells support) fine).toNat) =
      [if coarse ∈ support then 1 else 0, 0, 0, 0] := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [dyadicFacePreimages, supportCoefficient,
      mem_dyadicSupportCells_iff_subdivision,
      dyadicFaceOnSubdivisionGrid, dyadicPlaquetteProjection,
      dyadicVertexProjection, odd_half_local,
      decide_toNat_eq_indicator_local]

/-- Packet form of the preceding ordered-fibre computation. -/
theorem dyadicFaceSpinPacket_dyadicSupportCells
    (support : List Z4Plaq) (coarse : Z4Plaq) :
    dyadicFaceSpinPacket
        (fun fine =>
          (supportCoefficient (dyadicSupportCells support) fine).toNat)
        coarse =
      ⟨if coarse ∈ support then 1 else 0, 0, 0, 0⟩ := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases plane <;>
    simp [dyadicFaceSpinPacket, dyadicFacePreimages,
      supportCoefficient, mem_dyadicSupportCells_iff_subdivision,
      dyadicFaceOnSubdivisionGrid, dyadicPlaquetteProjection,
      dyadicVertexProjection, odd_half_local,
      decide_toNat_eq_indicator_local]

/-! ## 3. Closedness preservation -/

/-- A closed coarse mod-two 2-chain has a closed literal dyadic
subdivision. -/
theorem dyadicFaceSubdivision_preserves_modTwoClosed
    (coefficient : Z4Plaq → Bool)
    (hclosed : ModTwoClosed coefficient) :
    ModTwoClosed (dyadicFaceSubdivision coefficient) := by
  intro fineLink
  rw [cellularBoundaryCoefficient_dyadicFaceSubdivision]
  obtain ⟨⟨a, b, c, d⟩, direction⟩ := fineLink
  cases direction <;> simp only [dyadicLinkSubdivision] <;>
    split
  all_goals first | exact hclosed _ | rfl

/-- Literal four-cell refinement preserves the development's geometric
even-incidence condition on every duplicate-free coarse support. -/
theorem dyadicSupportCells_preserves_evenFaceIncidence
    {support : List Z4Plaq} (hnodup : support.Nodup)
    (hclosed : EvenFaceIncidence support) :
    EvenFaceIncidence (dyadicSupportCells support) := by
  have hcoarseModTwo : ModTwoClosed (supportCoefficient support) :=
    (modTwoClosed_supportCoefficient_iff_evenFaceIncidence
      support hnodup).2 hclosed
  have hfineModTwo :
      ModTwoClosed
        (dyadicFaceSubdivision (supportCoefficient support)) :=
    dyadicFaceSubdivision_preserves_modTwoClosed
      (supportCoefficient support) hcoarseModTwo
  rw [dyadicFaceSubdivision_supportCoefficient] at hfineModTwo
  exact (modTwoClosed_supportCoefficient_iff_evenFaceIncidence
    (dyadicSupportCells support)
    (dyadicSupportCells_nodup hnodup)).1 hfineModTwo

/-! ## 4. Corrected-slab containment -/

/-- Each of the four coplanar children of a corrected-slab coarse face lies
in the affine boundary-complete fine slab. -/
theorem dyadicCell_mem_boundaryCompleteFineSlab
    {extent : Nat} {coarse : Z4Plaq}
    (hcoarse : coarse ∈ boundaryCompleteSlabPlaquettes extent)
    (index : DyadicCellIndex) :
    dyadicCell coarse index ∈
      boundaryCompleteSlabPlaquettes (dyadicSlabFineExtent extent) := by
  have hparts :=
    (mem_boundaryCompleteSlabPlaquettes extent coarse).mp hcoarse
  have hboxFine := dyadicCell_mem_double_box hparts.1 index
  have hextent :
      2 * (extent + 1) = dyadicSlabFineExtent extent + 1 := by
    unfold dyadicSlabFineExtent
    omega
  rw [hextent] at hboxFine
  apply (mem_boundaryCompleteSlabPlaquettes
    (dyadicSlabFineExtent extent) _).mpr
  refine ⟨hboxFine, ?_⟩
  have htime := hparts.2
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarse
  cases index <;> cases plane <;>
    simp only [plaquetteTimeAdmissible] at htime <;>
    simp only [plaquetteTimeAdmissible, dyadicSlabFineExtent,
      dyadicCell, dyadicVertex, addE, dirsOf] <;>
    omega

/-- Literal refinement of an arbitrary corrected-slab coarse support stays
inside the corresponding affine fine slab. -/
theorem dyadicSupportCells_subset_boundaryCompleteFineSlab
    {extent : Nat} {support : List Z4Plaq}
    (hsubset : ∀ coarse, coarse ∈ support →
      coarse ∈ boundaryCompleteSlabPlaquettes extent) :
    ∀ fine, fine ∈ dyadicSupportCells support →
      fine ∈ boundaryCompleteSlabPlaquettes
        (dyadicSlabFineExtent extent) := by
  intro fine hfine
  obtain ⟨coarse, hcoarse, hcell⟩ :=
    (mem_dyadicSupportCells_iff support fine).mp hfine
  unfold dyadicPlaquetteCells at hcell
  obtain ⟨index, _, hindex⟩ := List.mem_map.mp hcell
  rw [← hindex]
  exact dyadicCell_mem_boundaryCompleteFineSlab
    (hsubset coarse hcoarse) index

#print axioms cellularBoundaryCoefficient_dyadicFaceSubdivision
#print axioms odd_half_local
#print axioms twice_half_eq_of_even_local
#print axioms twice_half_add_one_eq_of_not_even_local
#print axioms dyadicPlaquetteProjection_dyadicCell
#print axioms dyadicCell_onSubdivisionGrid
#print axioms exists_dyadicCell_of_onSubdivisionGrid
#print axioms mem_dyadicSupportCells_iff_subdivision
#print axioms dyadicFaceSubdivision_supportCoefficient
#print axioms dyadicFacePreimages_dyadicSupportCells_spins
#print axioms dyadicFaceSpinPacket_dyadicSupportCells
#print axioms dyadicFaceSubdivision_preserves_modTwoClosed
#print axioms dyadicSupportCells_preserves_evenFaceIncidence
#print axioms dyadicCell_mem_boundaryCompleteFineSlab
#print axioms dyadicSupportCells_subset_boundaryCompleteFineSlab

end YMGap.Continuum.Z4DyadicSubdivisionClosure
