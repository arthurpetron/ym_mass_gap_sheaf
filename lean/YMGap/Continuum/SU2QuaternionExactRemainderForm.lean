/-
# The exact full-product Taylor remainder as a positive bilinear form

The form below is defined directly from the original product kinetic pairing,
ordinary Haar pairing, and the computed first Casimir coefficient.  The exact
Taylor identity identifies it with `pairRemainder`; diagonal channel
positivity therefore turns the supported polynomial carrier into genuine
`GNSData`, yielding sharp Cauchy--Schwarz without an orthogonality premise.
-/

import YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
import YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
import YMGap.Continuum.SU2QuaternionProductHeatDualForm

namespace YMGap.Continuum.SU2QuaternionExactRemainderForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionProductHeatDualForm

local notation "H" => quaternionHaar
local infix:50 " ≈ " => Q'.eqv

/-- The original product pairing after subtracting its value and restoring its
computed first Casimir coefficient.  The source is the first argument and the
test is the second argument, matching `pairRemainder tail p q`. -/
def exactRemainderPair (tail : Nat) (w : Q') (K : Nat)
    (p q : RatPoly) : Q' :=
  kineticPair (tail+1) w K (List.range (tail+1)) q p +
    -(H (tail+1) (polyMul q p)) +
    ((1 : Q')-w)*pairCasimir tail p q

/-- Exact identification with the computed full-product Taylor remainder. -/
theorem exactRemainderPair_eq_pairRemainder (tail : Nat) (w : Q') (K : Nat)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    exactRemainderPair tail w K p q ≈ pairRemainder tail w K p q := by
  have ht := productPair_taylor tail w K p q hp
  unfold exactRemainderPair kineticPair at *
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' ht (Q'.eqv_refl _)) (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add
        (.add
          (.add
            (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
            (.var 3))
          (.neg (.var 0)))
        (.mul (.var 1) (.var 2)))
      (.var 3) (by decide)
      (fun | 0 => H (tail+1) (polyMul q p)
           | 1 => (1 : Q')-w
           | 2 => pairCasimir tail p q
           | _ => pairRemainder tail w K p q))

private theorem haarPair_congr_left (blocks : Nat) {p p' : RatPoly} (q : RatPoly)
    (h : RatPolyCoeffEqv p p') :
    H blocks (polyMul q p) ≈ H blocks (polyMul q p') :=
  haar_of_coeff (h.mul_left q)

private theorem haarPair_add_left (blocks : Nat) (p q r : RatPoly) :
    H blocks (polyMul r (polyAdd p q)) ≈
      H blocks (polyMul r p) + H blocks (polyMul r q) := by
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_add_right r p q))
    (quaternionHaar_append blocks _ _)

private theorem haarPair_smul_left (blocks : Nat) (c : Q') (p q : RatPoly) :
    H blocks (polyMul q (polySmul c p)) ≈
      c * H blocks (polyMul q p) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right c q p))
    (quaternionHaar_polySmul blocks c _)

private theorem haarPair_symm (blocks : Nat) (p q : RatPoly) :
    H blocks (polyMul q p) ≈ H blocks (polyMul p q) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_comm q p)

private theorem exactRemainderPair_congr_left (tail : Nat) (w : Q') (K : Nat)
    {p p' : RatPoly} (q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hp' : SupportedQuaternionBlocks (tail+1) p')
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (h : RatPolyCoeffEqv p p') :
    exactRemainderPair tail w K p q ≈ exactRemainderPair tail w K p' q := by
  have hk : kineticPair (tail+1) w K (List.range (tail+1)) q p ≈
      kineticPair (tail+1) w K (List.range (tail+1)) q p' :=
    haar_of_coeff ((productMap_congr (tail+1) w K (List.range (tail+1)) h).mul_left q)
  have hc : pairCasimir tail p q ≈ pairCasimir tail p' q :=
    Q'.eqv_trans _ _ _ (pairCasimir_symm tail p q hp hq)
      (Q'.eqv_trans _ _ _ (pairCasimir_congr_right tail q hq h)
        (Q'.eqv_symm (pairCasimir_symm tail p' q hp' hq)))
  unfold exactRemainderPair
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' hk
      (Q'.neg_eqv_congr _ _ (haarPair_congr_left _ q h)))
    (Q'.mul_eqv_congr_left ((1 : Q')-w) _ _ hc)

private theorem exactRemainderPair_symm (tail : Nat) (w : Q') (K : Nat)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    exactRemainderPair tail w K p q ≈ exactRemainderPair tail w K q p := by
  unfold exactRemainderPair
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (kineticPair_symm _ _ _ _ (fun i hi => List.mem_range.mp hi) q p hq hp)
      (Q'.neg_eqv_congr _ _ (haarPair_symm _ p q)))
    (Q'.mul_eqv_congr_left _ _ _ (pairCasimir_symm tail p q hp hq))

private theorem exactRemainderPair_add_left (tail : Nat) (w : Q') (K : Nat)
    (p q r : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (hr : SupportedQuaternionBlocks (tail+1) r) :
    exactRemainderPair tail w K (polyAdd p q) r ≈
      exactRemainderPair tail w K p r + exactRemainderPair tail w K q r := by
  have hpq := supported_add hp hq
  have hk : kineticPair (tail+1) w K (List.range (tail+1)) r (polyAdd p q) ≈
      kineticPair (tail+1) w K (List.range (tail+1)) r p +
        kineticPair (tail+1) w K (List.range (tail+1)) r q := by
    exact Q'.eqv_trans _ _ _
      (kineticPair_symm _ _ _ _ (fun i hi => List.mem_range.mp hi) r
        (polyAdd p q) hr hpq)
      (Q'.eqv_trans _ _ _ (kineticPair_add_left _ _ _ _ p q r)
        (Q'.add_eqv_congr'
          (Q'.eqv_symm (kineticPair_symm _ _ _ _
            (fun i hi => List.mem_range.mp hi) r p hr hp))
          (Q'.eqv_symm (kineticPair_symm _ _ _ _
            (fun i hi => List.mem_range.mp hi) r q hr hq))))
  have hc : pairCasimir tail (polyAdd p q) r ≈
      pairCasimir tail p r + pairCasimir tail q r :=
    Q'.eqv_trans _ _ _ (pairCasimir_symm tail (polyAdd p q) r hpq hr)
      (Q'.eqv_trans _ _ _ (pairCasimir_add_right tail r p q hr)
        (Q'.add_eqv_congr'
          (pairCasimir_symm tail r p hr hp)
          (pairCasimir_symm tail r q hr hq)))
  unfold exactRemainderPair
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hk (Q'.neg_eqv_congr _ _
        (haarPair_add_left _ p q r)))
      (Q'.mul_eqv_congr_left _ _ _ hc))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1))
        (.neg (.add (.var 2) (.var 3))))
        (.mul (.var 4) (.add (.var 5) (.var 6))))
      (.add
        (.add (.add (.var 0) (.neg (.var 2))) (.mul (.var 4) (.var 5)))
        (.add (.add (.var 1) (.neg (.var 3))) (.mul (.var 4) (.var 6))))
      (by decide)
      (fun | 0 => kineticPair (tail+1) w K (List.range (tail+1)) r p
           | 1 => kineticPair (tail+1) w K (List.range (tail+1)) r q
           | 2 => H (tail+1) (polyMul r p)
           | 3 => H (tail+1) (polyMul r q)
           | 4 => (1 : Q')-w
           | 5 => pairCasimir tail p r
           | _ => pairCasimir tail q r))

private theorem exactRemainderPair_smul_left (tail : Nat) (w : Q') (K : Nat)
    (c : Q') (p q : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    exactRemainderPair tail w K (polySmul c p) q ≈
      c * exactRemainderPair tail w K p q := by
  have hcp : SupportedQuaternionBlocks (tail+1) (polySmul c p) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact hp s hs
  have hk : kineticPair (tail+1) w K (List.range (tail+1)) q (polySmul c p) ≈
      c * kineticPair (tail+1) w K (List.range (tail+1)) q p :=
    Q'.eqv_trans _ _ _
      (kineticPair_symm _ _ _ _ (fun i hi => List.mem_range.mp hi) q
        (polySmul c p) hq hcp)
      (Q'.eqv_trans _ _ _ (kineticPair_smul_left _ _ _ _ c p q)
        (Q'.mul_eqv_congr_left c _ _
          (Q'.eqv_symm (kineticPair_symm _ _ _ _
            (fun i hi => List.mem_range.mp hi) q p hq hp))))
  have hc : pairCasimir tail (polySmul c p) q ≈
      c * pairCasimir tail p q :=
    Q'.eqv_trans _ _ _ (pairCasimir_symm tail (polySmul c p) q hcp hq)
      (Q'.eqv_trans _ _ _ (pairCasimir_smul_right tail c q p hq)
        (Q'.mul_eqv_congr_left c _ _ (pairCasimir_symm tail q p hq hp)))
  unfold exactRemainderPair
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hk
        (Q'.neg_eqv_congr _ _ (haarPair_smul_left _ c p q)))
      (Q'.mul_eqv_congr_left _ _ _ hc))
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 3) (.mul (.var 0) (.var 4))))
      (.mul (.var 0)
        (.add (.add (.var 1) (.neg (.var 2))) (.mul (.var 3) (.var 4))))
      (by decide)
      (fun | 0 => c
           | 1 => kineticPair (tail+1) w K (List.range (tail+1)) q p
           | 2 => H (tail+1) (polyMul q p)
           | 3 => (1 : Q')-w
           | _ => pairCasimir tail p q))

/-- Positive symmetric bilinear data for the exact Taylor remainder on the
same supported-polynomial carrier as the product kinetic form. -/
def exactRemainderGNSData (tail : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) : GNSData :=
  { kineticGNSData (tail+1) w hw0 K (List.range (tail+1))
      (fun _ hi => List.mem_range.mp hi) with
    B := fun p q => exactRemainderPair tail w K p.val q.val
    B_congr_left := fun {p p'} q h => exactRemainderPair_congr_left tail w K q.val
      p.property p'.property q.property h
    B_add_left := fun p q r => exactRemainderPair_add_left tail w K
      p.val q.val r.val p.property q.property r.property
    B_smul_left := fun c p q => exactRemainderPair_smul_left tail w K
      c p.val q.val p.property q.property
    B_symm := fun p q => exactRemainderPair_symm tail w K
      p.val q.val p.property q.property
    self_nonneg := fun p => Q'.le_trans' _ _ _
      (pairRemainder_diagonal_nonnegative tail hw0 hw1 K hK p.val p.property)
      (Q'.le_of_eqv (Q'.eqv_symm
        (exactRemainderPair_eq_pairRemainder tail w K
          p.val p.val p.property))) }

/-- Sharp Cauchy--Schwarz for the actual exact Taylor remainder form. -/
theorem exactRemainderPair_cauchySchwarz (tail : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    exactRemainderPair tail w K p q * exactRemainderPair tail w K p q ≤
      exactRemainderPair tail w K p p * exactRemainderPair tail w K q q :=
  (exactRemainderGNSData tail w hw0 hw1 K hK).cauchy_schwarz ⟨p, hp⟩ ⟨q, hq⟩

#print axioms YMGap.Continuum.SU2QuaternionExactRemainderForm.exactRemainderPair
#print axioms YMGap.Continuum.SU2QuaternionExactRemainderForm.exactRemainderPair_eq_pairRemainder
#print axioms YMGap.Continuum.SU2QuaternionExactRemainderForm.exactRemainderGNSData
#print axioms YMGap.Continuum.SU2QuaternionExactRemainderForm.exactRemainderPair_cauchySchwarz

end YMGap.Continuum.SU2QuaternionExactRemainderForm
