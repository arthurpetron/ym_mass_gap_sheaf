/-
# Exact 25-tree + 18-cycle integration and five based-cycle Haar marginal

The adapted lower-boundary carrier is ordered as the 25 displayed tree-link
blocks followed by the 23 rooted based-cycle blocks.  This module moves the
five transmitted cycles `{0,4,5,6,10}` to the tail and performs exact
normalized quaternion Haar integration over the other 43 blocks:

* all 25 tree variables; and
* all 18 complementary cycle variables.

The result is a polynomial on precisely the five based-cycle blocks in the
canonical transmitted order.  The theorem here is the exact Fubini/marginal
half of the raw-link-to-cycle bridge.  Transporting a raw 48-link polynomial
to this adapted carrier is the triangular nonlinear substitution whose
elementary constructive left/right Haar law is supplied by
`SU2QuaternionPolynomialHaarTranslation`.

## Axiom gate

Finite lists, an explicit block involution, exact rational sphere moments,
and constructive Fubini only.  No `Classical.*`, `native_decide`, `sorry`,
custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation

namespace YMGap.Continuum.BF4ExactSpatialTreeCycleFiveHaarMarginal

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSpatialTreeGaugeBasedCycles
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal 48 = 25 + 18 + 5 ledger -/

def bf4AdaptedTreeBlockCount : Nat := 25
def bf4AdaptedUnusedCycleBlockCount : Nat := 18
def bf4AdaptedTransmittedBlockCount : Nat := 5
def bf4AdaptedIntegratedBlockCount : Nat := 43
def bf4AdaptedBoundaryBlockCount : Nat := 48

theorem bf4AdaptedBoundaryBlockCount_split :
    bf4AdaptedBoundaryBlockCount =
      bf4AdaptedTreeBlockCount +
        bf4AdaptedUnusedCycleBlockCount +
          bf4AdaptedTransmittedBlockCount := by
  decide

/-- In the adapted carrier, cycle `c` is block `25+c`. -/
def bf4AdaptedTransmittedBlocks : List Nat :=
  bf4TransmittedCycleTable.map fun cycle =>
    bf4AdaptedTreeBlockCount + cycle.val

theorem bf4AdaptedTransmittedBlocks_eq :
    bf4AdaptedTransmittedBlocks = [25, 29, 30, 31, 35] := by
  decide

def bf4AdaptedUnusedCycleBlocks : List Nat :=
  bf4IntegratedCycleTable.map fun cycle =>
    bf4AdaptedTreeBlockCount + cycle.val

theorem bf4AdaptedUnusedCycleBlocks_eq :
    bf4AdaptedUnusedCycleBlocks =
      [26, 27, 28, 32, 33, 34, 36, 37, 38,
       39, 40, 41, 42, 43, 44, 45, 46, 47] := by
  decide

theorem bf4AdaptedUnusedCycleBlocks_length :
    bf4AdaptedUnusedCycleBlocks.length =
      bf4AdaptedUnusedCycleBlockCount := by
  decide

/-! ## 2. Move the five based cycles to the tail -/

def adaptedBasedCycleTailBlockMap (block : Nat) : Nat :=
  if block = 25 then 43
  else if block = 43 then 25
  else if block = 29 then 44
  else if block = 44 then 29
  else if block = 30 then 45
  else if block = 45 then 30
  else if block = 31 then 46
  else if block = 46 then 31
  else if block = 35 then 47
  else if block = 47 then 35
  else block

def adaptedBasedCycleTailBlockInvolution :
    QuaternionBlockInvolution 48 where
  map := adaptedBasedCycleTailBlockMap
  map_lt := by
    intro block hblock
    by_cases h25 : block = 25
    · subst block; decide
    · by_cases h43 : block = 43
      · subst block; decide
      · by_cases h29 : block = 29
        · subst block; decide
        · by_cases h44 : block = 44
          · subst block; decide
          · by_cases h30 : block = 30
            · subst block; decide
            · by_cases h45 : block = 45
              · subst block; decide
              · by_cases h31 : block = 31
                · subst block; decide
                · by_cases h46 : block = 46
                  · subst block; decide
                  · by_cases h35 : block = 35
                    · subst block; decide
                    · by_cases h47 : block = 47
                      · subst block; decide
                      · simpa [adaptedBasedCycleTailBlockMap, h25, h43,
                          h29, h44, h30, h45, h31, h46, h35, h47]
                        using hblock
  involutive := by
    intro block _
    by_cases h25 : block = 25
    · subst block; decide
    · by_cases h43 : block = 43
      · subst block; decide
      · by_cases h29 : block = 29
        · subst block; decide
        · by_cases h44 : block = 44
          · subst block; decide
          · by_cases h30 : block = 30
            · subst block; decide
            · by_cases h45 : block = 45
              · subst block; decide
              · by_cases h31 : block = 31
                · subst block; decide
                · by_cases h46 : block = 46
                  · subst block; decide
                  · by_cases h35 : block = 35
                    · subst block; decide
                    · by_cases h47 : block = 47
                      · subst block; decide
                      · simp [adaptedBasedCycleTailBlockMap, h25, h43,
                          h29, h44, h30, h45, h31, h46, h35, h47]

/-- The five new tail blocks read the transmitted based cycles in order
`{0,4,5,6,10}`. -/
theorem adaptedBasedCycleTailBlockInvolution_tail_order :
    [43, 44, 45, 46, 47].map
        adaptedBasedCycleTailBlockInvolution.map =
      bf4AdaptedTransmittedBlocks := by
  rw [bf4AdaptedTransmittedBlocks_eq]
  decide

/-- The 43 new head blocks read all 25 tree variables and all 18 unused
cycle variables (the displayed order is the order actually integrated). -/
def bf4AdaptedIntegratedSourceOrder : List Nat :=
  (List.range 43).map adaptedBasedCycleTailBlockInvolution.map

theorem bf4AdaptedIntegratedSourceOrder_eq :
    bf4AdaptedIntegratedSourceOrder =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
       10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
       20, 21, 22, 23, 24,
       43, 26, 27, 28, 44, 45, 46,
       32, 33, 34, 47, 36, 37, 38, 39, 40, 41, 42] := by
  decide

theorem bf4AdaptedIntegratedSourceOrder_length :
    bf4AdaptedIntegratedSourceOrder.length =
      bf4AdaptedTreeBlockCount + bf4AdaptedUnusedCycleBlockCount := by
  decide

/-! ## 3. The exact fivefold based-cycle marginal -/

/-- Reindex the five transmitted based cycles to the tail, then integrate
the 25 tree and 18 unused-cycle head blocks. -/
def exactBasedCycleFiveHaarMarginal (polynomial : RatPoly) : RatPoly :=
  partialHaarHeads 43
    (reindexQuaternionPolynomial
      adaptedBasedCycleTailBlockInvolution polynomial)

theorem exactBasedCycleFiveHaarMarginal_supported_five
    (polynomial : RatPoly) :
    SupportedQuaternionBlocks 5
      (exactBasedCycleFiveHaarMarginal polynomial) := by
  unfold exactBasedCycleFiveHaarMarginal
  apply partialHaarHeads_supported 5 43
  simpa using reindexQuaternionPolynomial_supported
    adaptedBasedCycleTailBlockInvolution polynomial

/-- **Exact 25+18 integration theorem.**  For a polynomial in the adapted
48-block tree/based-cycle carrier, its full product Haar integral is the
fivefold Haar integral of the transmitted based-cycle marginal. -/
theorem quaternionHaar_48_eq_basedCycleFiveHaarMarginal
    (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks 48 polynomial) :
    quaternionHaar 48 polynomial ≈
      quaternionHaar 5
        (exactBasedCycleFiveHaarMarginal polynomial) := by
  refine Q'.eqv_trans _
    (quaternionHaar 48
      (reindexQuaternionPolynomial
        adaptedBasedCycleTailBlockInvolution polynomial)) _ ?_ ?_
  · exact Q'.eqv_symm
      (quaternionHaar_reindex
        adaptedBasedCycleTailBlockInvolution polynomial hsupport)
  · exact Q'.eqv_symm (by
      simpa [exactBasedCycleFiveHaarMarginal] using
        quaternionHaar_partialHaarHeads 5 43
          (reindexQuaternionPolynomial
            adaptedBasedCycleTailBlockInvolution polynomial))

/-- The surviving five marginal variables have exactly the rooted based-cycle
index order already identified geometrically. -/
theorem exactBasedCycleFiveHaarMarginal_cycle_order :
    bf4AdaptedTransmittedBlocks.map
        (fun block => block - bf4AdaptedTreeBlockCount) =
      [0, 4, 5, 6, 10] := by
  decide

end YMGap.Continuum.BF4ExactSpatialTreeCycleFiveHaarMarginal

#print axioms YMGap.Continuum.BF4ExactSpatialTreeCycleFiveHaarMarginal.quaternionHaar_48_eq_basedCycleFiveHaarMarginal
