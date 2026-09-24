/-
# Exact polarized form of the product-heat source energy

The positive exact Taylor remainder is polarized before any estimate is
taken.  Thus the favorable diagonal terms remain visible, including the
negative square of the actual source `a*f`.
-/

import YMGap.Continuum.SU2QuaternionExactRemainderForm
import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor

namespace YMGap.Continuum.SU2QuaternionExactRemainderEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionExactRemainderForm

local infix:50 " ≈ " => Q'.eqv

/-- The carrier representative of `s*p-q`. -/
def scaledDifference (s : Q') (p q : RatPoly) : RatPoly :=
  polyAdd (polySmul s p) (polySmul (-1) q)

private theorem supported_smul_local {n : Nat} (s : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polySmul s p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

private theorem scaledDifference_supported {n : Nat} (s : Q') {p q : RatPoly}
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q) :
    SupportedQuaternionBlocks n (scaledDifference s p q) :=
  supported_add (supported_smul_local s hp) (supported_smul_local (-1) hq)

/-- Polarization of any positive exact-remainder form. -/
theorem exactRemainderPair_polarization (tail : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (s : Q') (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q) :
    (2*s)*exactRemainderPair tail w K p q ≈
      s*s*exactRemainderPair tail w K p p +
        exactRemainderPair tail w K q q +
        -(exactRemainderPair tail w K (scaledDifference s p q)
          (scaledDifference s p q)) := by
  let D := exactRemainderGNSData tail w hw0 hw1 K hK
  let pv : D.V := ⟨p, hp⟩
  let qv : D.V := ⟨q, hq⟩
  have hd := D.diag_expand s (-1) pv qv
  have hdiag :
      exactRemainderPair tail w K (scaledDifference s p q)
          (scaledDifference s p q) ≈
        ((s*s*exactRemainderPair tail w K p p +
          2*(s*(-1))*exactRemainderPair tail w K p q) +
          (-1)*(-1)*exactRemainderPair tail w K q q) :=
    Q'.eqv_trans _ _ _ hd
      (YMGap.Continuum.GNSQuotient.GNSData.quad_regroup s (-1)
        (exactRemainderPair tail w K p p)
        (exactRemainderPair tail w K p q)
        (exactRemainderPair tail w K q q))
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.var 2))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 3))
        (.neg (.add
          (.add (.mul (.mul (.var 0) (.var 0)) (.var 1))
            (.mul (.mul (.const 2) (.mul (.var 0) (.const (-1)))) (.var 2)))
          (.mul (.mul (.const (-1)) (.const (-1))) (.var 3)))))
      (by decide)
      (fun | 0 => s
           | 1 => exactRemainderPair tail w K p p
           | 2 => exactRemainderPair tail w K p q
           | _ => exactRemainderPair tail w K q q))
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hdiag)))

/-- The remainder retained after polarizing the mixed source term. -/
def polarizedRemainder (tail : Nat) (w : Q') (K : Nat) (s : Q')
    (a f : RatPoly) : Q' :=
  let y := polyMul a (polyMul f f)
  let z := polyMul a f
  s*s*exactRemainderPair tail w K a a +
    exactRemainderPair tail w K y y +
    -(exactRemainderPair tail w K (scaledDifference s a y)
      (scaledDifference s a y)) +
    -((2*s)*exactRemainderPair tail w K z z)

/-- The polarized remainder after dropping only the negative square of
`s*a-a*f^2`; the favorable `a*f` diagonal is retained. -/
def balancedRemainder (tail : Nat) (w : Q') (K : Nat) (s : Q')
    (a f : RatPoly) : Q' :=
  let y := polyMul a (polyMul f f)
  let z := polyMul a f
  s*s*exactRemainderPair tail w K a a +
    exactRemainderPair tail w K y y +
    -((2*s)*exactRemainderPair tail w K z z)

/-- Positivity of the exact remainder drops the first polarized square and
no other favorable term. -/
theorem polarizedRemainder_le_balancedRemainder (tail : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (s : Q') (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    polarizedRemainder tail w K s a f ≤ balancedRemainder tail w K s a f := by
  let y := polyMul a (polyMul f f)
  have hy : SupportedQuaternionBlocks (tail+1) y :=
    supported_polyMul ha (supported_polyMul hf hf)
  have hd := scaledDifference_supported s ha hy
  let D := exactRemainderGNSData tail w hw0 hw1 K hK
  have hnonnegative : (0 : Q') ≤
      exactRemainderPair tail w K (scaledDifference s a y)
        (scaledDifference s a y) :=
    D.self_nonneg ⟨scaledDifference s a y, hd⟩
  have hnegative :
      -(exactRemainderPair tail w K (scaledDifference s a y)
        (scaledDifference s a y)) ≤ 0 := by
    change -(exactRemainderPair tail w K (scaledDifference s a y)
      (scaledDifference s a y)) ≤ -0
    exact Q'.neg_le_neg hnonnegative
  have hregroup : polarizedRemainder tail w K s a f ≈
      balancedRemainder tail w K s a f +
        -(exactRemainderPair tail w K (scaledDifference s a y)
          (scaledDifference s a y)) := by
    unfold polarizedRemainder balancedRemainder
    exact poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.neg (.var 2))) (.neg (.var 3)))
      (.add (.add (.add (.var 0) (.var 1)) (.neg (.var 3))) (.neg (.var 2)))
      (by decide)
      (fun | 0 => s*s*exactRemainderPair tail w K a a
           | 1 => exactRemainderPair tail w K y y
           | 2 => exactRemainderPair tail w K (scaledDifference s a y)
               (scaledDifference s a y)
           | _ => (2*s)*exactRemainderPair tail w K (polyMul a f) (polyMul a f))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _ hnegative)
      (Q'.le_of_eqv (QPoly.q_add_zero_eqv _)))

/-- Exact source-energy identity with the mixed remainder polarized. -/
theorem sourceEnergy_polarized_remainder (tail : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (s : Q') (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    (2*s)*sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≈
      (2*s)*((1 : Q')-w)*weightedAngularEnergy tail a f +
        polarizedRemainder tail w K s a f := by
  let y := polyMul a (polyMul f f)
  let z := polyMul a f
  have hy : SupportedQuaternionBlocks (tail+1) y :=
    supported_polyMul ha (supported_polyMul hf hf)
  have hz : SupportedQuaternionBlocks (tail+1) z := supported_polyMul ha hf
  have ht := sourceEnergy_taylor_angular tail w K a f ha hf
  have hpol := exactRemainderPair_polarization tail w hw0 hw1 K hK s a y ha hy
  have hay := Q'.eqv_symm (exactRemainderPair_eq_pairRemainder tail w K a y ha)
  have hzz := Q'.eqv_symm (exactRemainderPair_eq_pairRemainder tail w K z z hz)
  have hscaled := Q'.mul_eqv_congr_left (2*s) _ _ ht
  exact Q'.eqv_trans _ _ _ hscaled
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (2*s) _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.add_eqv_congr' hay (Q'.neg_eqv_congr _ _ hzz))))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 2) (.var 0))
            (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
              (.add (.var 3) (.neg (.var 4)))))
          (.add
            (.mul (.mul (.mul (.const 2) (.var 0))
              (.add (.const 1) (.neg (.var 1)))) (.var 2))
            (.add (.mul (.mul (.const 2) (.var 0)) (.var 3))
              (.neg (.mul (.mul (.const 2) (.var 0)) (.var 4)))))
          (by decide)
          (fun | 0 => s
               | 1 => w
               | 2 => weightedAngularEnergy tail a f
               | 3 => exactRemainderPair tail w K a y
               | _ => exactRemainderPair tail w K z z))
        (Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (Q'.add_eqv_congr' hpol (Q'.eqv_refl _)))))

end YMGap.Continuum.SU2QuaternionExactRemainderEnergy

#print axioms YMGap.Continuum.SU2QuaternionExactRemainderEnergy.exactRemainderPair_polarization
#print axioms YMGap.Continuum.SU2QuaternionExactRemainderEnergy.polarizedRemainder
#print axioms YMGap.Continuum.SU2QuaternionExactRemainderEnergy.balancedRemainder
#print axioms YMGap.Continuum.SU2QuaternionExactRemainderEnergy.polarizedRemainder_le_balancedRemainder
#print axioms YMGap.Continuum.SU2QuaternionExactRemainderEnergy.sourceEnergy_polarized_remainder
