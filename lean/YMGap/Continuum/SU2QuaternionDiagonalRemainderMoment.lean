/-
# Positive second-moment bound for the exact diagonal remainder

Every valid full-cycle path has a nonnegative pairing with the original
input. Scalar coefficient comparison therefore controls the diagonal
remainder by its SIGNED Casimir-square moment, without absolute leaf costs.
The differential realization of that moment is a separate theorem; this
module does not assert an interacting-variance or scaling estimate.
-/

import YMGap.Continuum.SU2QuaternionExactRemainderForm

namespace YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionExactRemainderForm
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

private theorem sum_le (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≤ g d) →
    qListSum (ids.map f) ≤ qListSum (ids.map g)
  | [], _ => Q'.le_refl' _
  | d::ds, h => Q'.add_le_add (h d List.mem_cons_self)
      (sum_le f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

private theorem sum_congr (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ d, d ∈ ids → f d ≈ g d) →
    qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | d::ds, h => Q'.add_eqv_congr' (h d List.mem_cons_self)
      (sum_congr f g ds (fun k hk => h k (List.mem_cons_of_mem d hk)))

private theorem sum_scale (c : Q') (f : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => c*f d) ≈ c*qListSum (ids.map f)
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | _d::ds => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_scale c f ds))
      (Q'.eqv_symm (Q'.mul_add_eqv c _ _))

private theorem leaf_scale (tail : Nat) : ∀ (m : Nat) (p test : RatPoly)
    (c : Q') (weight : List Nat → Q'),
    leafSum tail m p test (fun ds => c*weight ds) ≈
      c*leafSum tail m p test weight
  | 0, _, _, _, _ => Q'.mul_assoc_eqv _ _ _
  | m+1, p, test, c, weight =>
      Q'.eqv_trans _ _ _
        (sum_congr _ _ (branchDegrees tail p) (fun d _ =>
          leaf_scale tail m (nextPiece tail p d) test c (fun ds => weight (d::ds))))
        (sum_scale c _ (branchDegrees tail p))

private theorem leaf_le_of_paths (tail : Nat) :
    ∀ (m : Nat) (p test : RatPoly) (left right : List Nat → Q'),
      (∀ ds, ds.length = m → ValidPath tail p ds → left ds ≤ right ds) →
      (∀ ds, ds.length = m → ValidPath tail p ds →
        (0 : Q') ≤ quaternionHaar (tail+1) (polyMul test (pathPiece tail p ds))) →
      leafSum tail m p test left ≤ leafSum tail m p test right
  | 0, _, _, _, _, hle, hpos =>
      Q'.mul_le_mul_of_nonneg_right _ _ _ (hle [] rfl True.intro)
        (hpos [] rfl True.intro)
  | m+1, p, test, left, right, hle, hpos => by
      apply sum_le
      intro d hd
      exact leaf_le_of_paths tail m (nextPiece tail p d) test
        (fun ds => left (d::ds)) (fun ds => right (d::ds))
        (fun ds hlen hpath => hle (d::ds)
          (by simp only [List.length_cons, hlen]) ⟨hd,hpath⟩)
        (fun ds hlen hpath => hpos (d::ds)
          (by simp only [List.length_cons, hlen]) ⟨hd,hpath⟩)

/-- Coefficient monotonicity on the ACTUAL full-cycle diagonal path measure.
The coefficients need not themselves be nonnegative. -/
theorem full_leafSum_diagonal_mono (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (left right : List Nat → Q')
    (hle : ∀ ds, ds.length = tail+1 → left ds ≤ right ds) :
    leafSum tail (tail+1) p p left ≤ leafSum tail (tail+1) p p right :=
  leaf_le_of_paths tail (tail+1) p p left right
    (fun ds hlen _ => hle ds hlen)
    (fun ds hlen hpath => full_path_pairing_nonnegative tail p hp ds hlen hpath)

/-- The exact diagonal remainder is quadratically small against a positive
Casimir-square path moment. No absolute mixed-pairing budget appears. -/
theorem pairRemainder_diagonal_le_squareMoment (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    pairRemainder tail w K p p ≤
      (((1 : Q')-w)*((1 : Q')-w))*
        leafSum tail (tail+1) p p (fun ds => totalCasimir ds*totalCasimir ds) :=
  Q'.le_trans' _ _ _
    (full_leafSum_diagonal_mono tail p hp (productRemainder w K)
      (fun ds => (((1 : Q')-w)*((1 : Q')-w))*(totalCasimir ds*totalCasimir ds))
      (fun ds _ => (productRemainder_bounds_of_sufficientCutoff hw0 hw1 hK ds).2))
    (Q'.le_of_eqv (leaf_scale tail (tail+1) p p _ _))

/-- Same inequality for the ORIGINAL heat/Casimir remainder expression. -/
theorem exactRemainderPair_diagonal_le_squareMoment (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    exactRemainderPair tail w K p p ≤
      (((1 : Q')-w)*((1 : Q')-w))*
        leafSum tail (tail+1) p p (fun ds => totalCasimir ds*totalCasimir ds) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (exactRemainderPair_eq_pairRemainder tail w K p p hp))
    (pairRemainder_diagonal_le_squareMoment tail hw0 hw1 K hK p hp)

end YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment

#print axioms YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment.full_leafSum_diagonal_mono
#print axioms YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment.pairRemainder_diagonal_le_squareMoment
#print axioms YMGap.Continuum.SU2QuaternionDiagonalRemainderMoment.exactRemainderPair_diagonal_le_squareMoment
