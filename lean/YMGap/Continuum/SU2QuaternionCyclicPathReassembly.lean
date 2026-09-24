/-
# Pairing and reassembly of the actual cyclic degree paths

The computed ragged tree is not replaced by a rectangular index set or an
assumed family of orthogonal projections.  Each valid full path is paired
with its actual product-character kernel; scalar identities can then be
summed over precisely the computed branches.  This is the finite reassembly
needed by the Casimir-square identification, not a scaling estimate.
-/

import YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder

namespace YMGap.Continuum.SU2QuaternionCyclicPathReassembly

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeReassembly
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCharacterPositive
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem sum_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≈ g d) →
    qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | d::ds, h => Q'.add_eqv_congr' (h d List.mem_cons_self)
      (sum_congr f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

/-- Sum a weighted pairing identity over the actual valid ragged paths.
The source tree is identical on the two sides; only test and weight change. -/
theorem leafSum_pairing_congr (tail : Nat) :
    ∀ (m : Nat) (p leftTest rightTest : RatPoly)
      (leftWeight rightWeight : List Nat → Q'),
    (∀ ds, ds.length = m → ValidPath tail p ds →
      leftWeight ds * H (tail+1) (polyMul leftTest (pathPiece tail p ds)) ≈
      rightWeight ds * H (tail+1) (polyMul rightTest (pathPiece tail p ds))) →
    leafSum tail m p leftTest leftWeight ≈ leafSum tail m p rightTest rightWeight
  | 0, _, _, _, _, _, h => h [] rfl True.intro
  | m+1, p, leftTest, rightTest, leftWeight, rightWeight, h =>
      sum_congr _ _ (branchDegrees tail p) (fun d hd =>
        leafSum_pairing_congr tail m (nextPiece tail p d) leftTest rightTest
          (fun ds => leftWeight (d::ds)) (fun ds => rightWeight (d::ds))
          (fun ds hlen hpath => h (d::ds)
            (by simp only [List.length_cons, hlen]) ⟨hd, hpath⟩))

/-- Unweighted complete path reassembly returns the SAME original pairing. -/
theorem full_leafSum_one (tail : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    leafSum tail (tail+1) p test (fun _ => (1 : Q')) ≈
      H (tail+1) (polyMul test p) :=
  Q'.eqv_trans _ _ _ (leafSum_modeFold tail (tail+1) p test _).symm
    (full_modeFold_one_carrier tail p hp test)

/-- Every full path pairing is exactly a doubled-carrier product-character
pairing, with the original source and arbitrary signed test retained. -/
theorem full_path_pairing_kernel (tail : Nat) (p test : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds) :
    H (tail+1) (polyMul test (pathPiece tail p ds)) ≈
      H ((tail+1)+(tail+1)) (polyMul
        (polyMul (characterProduct (tail+1) (pathSlots 0 ds)) p)
        (liftBoundary (tail+1) test)) := by
  have hfold := character_prefix_fold_carrier (tail+1) ds p test
  rw [hlen] at hfold
  exact Q'.eqv_trans _ _ _
    (pathPiece_character_carrier tail ds p hp hpath test).symm
    (Q'.eqv_trans _ _ _ hfold.symm
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (head_pairing (tail+1) (tail+1)
          (polyMul (characterProduct (tail+1) (pathSlots 0 ds)) p) test).symm))

end YMGap.Continuum.SU2QuaternionCyclicPathReassembly

#print axioms YMGap.Continuum.SU2QuaternionCyclicPathReassembly.leafSum_pairing_congr
#print axioms YMGap.Continuum.SU2QuaternionCyclicPathReassembly.full_leafSum_one
#print axioms YMGap.Continuum.SU2QuaternionCyclicPathReassembly.full_path_pairing_kernel
