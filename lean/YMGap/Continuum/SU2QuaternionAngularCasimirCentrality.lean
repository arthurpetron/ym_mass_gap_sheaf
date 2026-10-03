/-
# Centrality of the actual six-plane angular Casimir

The overlapping square commutators cancel in pairs on the ORIGINAL Haar
carrier. Every shared spectator remains arbitrary. Only the actual angular
brackets, linearity and derivative-carrier transport are used. This is a
finite identity, not a heat-flow positivity or conditional variance estimate.
-/

import YMGap.Continuum.SU2QuaternionAngularLieBracket
import YMGap.Continuum.QuaternionHaarLinearAngularEnergy

namespace YMGap.Continuum.SU2QuaternionAngularCasimirCentrality

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionAngularLieBracket

private def squareField (i j : Nat) (p : RatPoly) : RatPoly :=
  angularDerivative i j (angularDerivative i j p)

private theorem reorder_positive {blocks : Nat} (u v z : RatPoly)
    (h : HaarCarrierEqv blocks (polyAdd u (polyNeg v)) z) :
    HaarCarrierEqv blocks u (polyAdd v z) := by
  have hc := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
    (by decide) (fun | 0 => u | _ => v)
  exact (RatPolyCoeffEqv.haarCarrier hc).symm.trans
    ((HaarCarrierEqv.add h (HaarCarrierEqv.refl blocks v)).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_comm z v)))

private theorem reorder_negative {blocks : Nat} (u v z : RatPoly)
    (h : HaarCarrierEqv blocks
      (polyAdd (polyNeg u) (polyNeg (polyNeg v))) z) :
    HaarCarrierEqv blocks u (polyAdd v (polyNeg z)) := by
  have hc := coeffEvalExpr_eqv_of_normalize_eq
    (.neg (.add (.neg (.var 0)) (.neg (.neg (.var 1)))))
    (.add (.var 0) (.neg (.var 1))) (by decide)
    (fun | 0 => u | _ => v)
  exact reorder_positive u v (polyNeg z)
    ((RatPolyCoeffEqv.haarCarrier hc).symm.trans (HaarCarrierEqv.neg h))

/-- The actual same-left overlapping planes, in a cancellation-ready order. -/
theorem same_left_planes_reorder {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks
      (angularDerivative i j (angularDerivative i k p))
      (polyAdd (angularDerivative i k (angularDerivative i j p))
        (polyNeg (angularDerivative j k p))) := by
  have h := overlapping_planes_bracket hb hj hi hk (Ne.symm hij) hjk hik p
  have he : HaarCarrierEqv blocks
      (polyAdd (angularDerivative j i (angularDerivative i k p))
        (polyNeg (angularDerivative i k (angularDerivative j i p))))
      (polyAdd (polyNeg (angularDerivative i j (angularDerivative i k p)))
        (polyNeg (polyNeg (angularDerivative i k (angularDerivative i j p))))) :=
    RatPolyCoeffEqv.haarCarrier
      ((angular_plane_antisymmetry i j _).add
        (RatPolyCoeffEqv.neg
          ((angularDerivative_congr i k (angular_plane_antisymmetry i j p)).trans
            (angularDerivative_neg i k _))))
  exact reorder_negative _ _ _ (he.symm.trans h)

/-- The actual shared-middle overlapping planes, in a cancellation-ready order. -/
theorem shared_middle_planes_reorder {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks
      (angularDerivative i j (angularDerivative j k p))
      (polyAdd (angularDerivative j k (angularDerivative i j p))
        (angularDerivative i k p)) :=
  reorder_positive _ _ _ (overlapping_planes_bracket hb hi hj hk hij hik hjk p)

private theorem paired_squares {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks
      (angularDerivative i j (polyAdd (squareField i k p) (squareField j k p)))
      (polyAdd (squareField i k (angularDerivative i j p))
        (squareField j k (angularDerivative i j p))) := by
  have hy := (same_left_planes_reorder hb hi hj hk hij hik hjk (angularDerivative i k p)).trans
    (HaarCarrierEqv.add
      ((angularDerivative_carrier hb hi hk
          (same_left_planes_reorder hb hi hj hk hij hik hjk p)).trans
        (RatPolyCoeffEqv.haarCarrier
          ((angularDerivative_add i k _ _).trans
            ((RatPolyCoeffEqv.refl _).add (angularDerivative_neg i k _)))))
      (HaarCarrierEqv.refl blocks _))
  have hz := (shared_middle_planes_reorder hb hi hj hk hij hik hjk (angularDerivative j k p)).trans
    (HaarCarrierEqv.add
      ((angularDerivative_carrier hb hj hk
          (shared_middle_planes_reorder hb hi hj hk hij hik hjk p)).trans
        (RatPolyCoeffEqv.haarCarrier (angularDerivative_add j k _ _)))
      (HaarCarrierEqv.refl blocks _))
  have hc := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
      (.add (.add (.var 3) (.var 2)) (.var 1)))
    (.add (.var 0) (.var 3)) (by decide) (fun
      | 0 => squareField i k (angularDerivative i j p)
      | 1 => angularDerivative i k (angularDerivative j k p)
      | 2 => angularDerivative j k (angularDerivative i k p)
      | _ => squareField j k (angularDerivative i j p))
  exact (RatPolyCoeffEqv.haarCarrier (angularDerivative_add i j _ _)).trans
    ((HaarCarrierEqv.add hy hz).trans (RatPolyCoeffEqv.haarCarrier hc))

private theorem square_disjoint (i j k l : Nat)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (squareField k l p))
      (squareField k l (angularDerivative i j p)) :=
  (disjoint_planes_commute i j k l hik hil hjk hjl (angularDerivative k l p)).trans
    (angularDerivative_congr k l (disjoint_planes_commute i j k l hik hil hjk hjl p))

private theorem square_flip (i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (squareField j i p) (squareField i j p) := by
  have h := (angular_plane_antisymmetry i j (angularDerivative j i p)).trans
    (RatPolyCoeffEqv.neg
      ((angularDerivative_congr i j (angular_plane_antisymmetry i j p)).trans
        (angularDerivative_neg i j _)))
  have hc := coeffEvalExpr_eqv_of_normalize_eq
    (.neg (.neg (.var 0))) (.var 0) (by decide)
    (fun _ => squareField i j p)
  exact h.trans hc

private def orderedCasimir (i j k l : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (squareField i j p)
    (polyAdd (squareField k l p)
      (polyAdd (polyAdd (squareField i k p) (squareField j k p))
        (polyAdd (squareField i l p) (squareField j l p))))

private theorem ordered_commutes {blocks i j k l : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (p : RatPoly) :
    HaarCarrierEqv blocks (angularDerivative i j (orderedCasimir i j k l p))
      (orderedCasimir i j k l (angularDerivative i j p)) := by
  have hsum : RatPolyCoeffEqv
      (angularDerivative i j (orderedCasimir i j k l p))
      (polyAdd (angularDerivative i j (squareField i j p))
        (polyAdd (angularDerivative i j (squareField k l p))
          (polyAdd
            (angularDerivative i j (polyAdd (squareField i k p) (squareField j k p)))
            (angularDerivative i j (polyAdd (squareField i l p) (squareField j l p)))))) :=
    (angularDerivative_add i j _ _).trans
    ((RatPolyCoeffEqv.refl _).add
      ((angularDerivative_add i j _ _).trans
        ((RatPolyCoeffEqv.refl _).add (angularDerivative_add i j _ _))))
  exact (RatPolyCoeffEqv.haarCarrier hsum).trans
    (HaarCarrierEqv.add (HaarCarrierEqv.refl blocks _)
      (HaarCarrierEqv.add (RatPolyCoeffEqv.haarCarrier
        (square_disjoint i j k l hik hil hjk hjl p))
        (HaarCarrierEqv.add (paired_squares hb hi hj hk hij hik hjk p)
          (paired_squares hb hi hj hl hij hil hjl p))))

private def planeCode : Nat → Nat → Nat
  | 0, 1 | 1, 0 => 0
  | 0, 2 | 2, 0 => 1
  | 0, 3 | 3, 0 => 2
  | 1, 2 | 2, 1 => 3
  | 1, 3 | 3, 1 => 4
  | 2, 3 | 3, 2 => 5
  | _, _ => 6

private def squareEnvironment (p : RatPoly) : Nat → RatPoly
  | 0 => squareField 0 1 p
  | 1 => squareField 0 2 p
  | 2 => squareField 0 3 p
  | 3 => squareField 1 2 p
  | 4 => squareField 1 3 p
  | _ => squareField 2 3 p

private theorem square_representation {i j : Nat}
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) (p : RatPoly) :
    RatPolyCoeffEqv (squareField i j p) (squareEnvironment p (planeCode i j)) := by
  have hic : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hjc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hic with rfl | rfl | rfl | rfl <;>
    rcases hjc with rfl | rfl | rfl | rfl
  · exact False.elim (hij rfl)
  · exact RatPolyCoeffEqv.refl _
  · exact RatPolyCoeffEqv.refl _
  · exact RatPolyCoeffEqv.refl _
  · exact square_flip 0 1 p
  · exact False.elim (hij rfl)
  · exact RatPolyCoeffEqv.refl _
  · exact RatPolyCoeffEqv.refl _
  · exact square_flip 0 2 p
  · exact square_flip 1 2 p
  · exact False.elim (hij rfl)
  · exact RatPolyCoeffEqv.refl _
  · exact square_flip 0 3 p
  · exact square_flip 1 3 p
  · exact square_flip 2 3 p
  · exact False.elim (hij rfl)

private def orderedExpr (i j k l : Nat) : PolyExpr :=
  .add (.var (planeCode i j))
    (.add (.var (planeCode k l))
      (.add (.add (.var (planeCode i k)) (.var (planeCode j k)))
        (.add (.var (planeCode i l)) (.var (planeCode j l)))))

private def sixExpr : PolyExpr :=
  .add (.var 0) (.add (.var 1) (.add (.var 2)
    (.add (.var 3) (.add (.var 4) (.var 5)))))

private theorem ordered_pin (i j k l : Nat)
    (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (horder : RingNormaliser.normalize (orderedExpr i j k l) =
      RingNormaliser.normalize sixExpr) (p : RatPoly) :
    RatPolyCoeffEqv (orderedCasimir i j k l p) (angularLaplacian p) :=
  ((square_representation hi hj hij p).add
    ((square_representation hk hl hkl p).add
      (((square_representation hi hk hik p).add (square_representation hj hk hjk p)).add
        ((square_representation hi hl hil p).add (square_representation hj hl hjl p))))).trans
    (coeffEvalExpr_eqv_of_normalize_eq (orderedExpr i j k l) sixExpr horder
      (squareEnvironment p))

private theorem concrete_centrality {blocks : Nat} (hb : 0 < blocks)
    (i j k l : Nat)
    (hi : i < 4) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (horder : RingNormaliser.normalize (orderedExpr i j k l) =
      RingNormaliser.normalize sixExpr) (p : RatPoly) :
    HaarCarrierEqv blocks (angularLaplacian (angularDerivative i j p))
      (angularDerivative i j (angularLaplacian p)) :=
  (RatPolyCoeffEqv.haarCarrier
    (ordered_pin i j k l hi hj hk hl hij hik hil hjk hjl hkl horder _)).symm.trans
    ((ordered_commutes hb hi hj hk hl hij hik hil hjk hjl p).symm.trans
      (RatPolyCoeffEqv.haarCarrier (angularDerivative_congr i j
        (ordered_pin i j k l hi hj hk hl hij hik hil hjk hjl hkl horder p))))

private theorem sorted_centrality {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i < j) (p : RatPoly) :
    HaarCarrierEqv blocks (angularLaplacian (angularDerivative i j p))
      (angularDerivative i j (angularLaplacian p)) := by
  have hic : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have hjc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hic with rfl | rfl | rfl | rfl <;>
    rcases hjc with rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬ (0 < 0)) hij)
  · exact concrete_centrality hb 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) p
  · exact concrete_centrality hb 0 2 1 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) p
  · exact concrete_centrality hb 0 3 1 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) p
  · exact False.elim ((by decide : ¬ (1 < 0)) hij)
  · exact False.elim ((by decide : ¬ (1 < 1)) hij)
  · exact concrete_centrality hb 1 2 0 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) p
  · exact concrete_centrality hb 1 3 0 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) p
  · exact False.elim ((by decide : ¬ (2 < 0)) hij)
  · exact False.elim ((by decide : ¬ (2 < 1)) hij)
  · exact False.elim ((by decide : ¬ (2 < 2)) hij)
  · exact concrete_centrality hb 2 3 0 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) p
  · exact False.elim ((by decide : ¬ (3 < 0)) hij)
  · exact False.elim ((by decide : ¬ (3 < 1)) hij)
  · exact False.elim ((by decide : ¬ (3 < 2)) hij)
  · exact False.elim ((by decide : ¬ (3 < 3)) hij)

private theorem laplacian_carrier {blocks : Nat} (hb : 0 < blocks)
    {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks (angularLaplacian p) (angularLaplacian q) := by
  have hs (i j : Nat) (hi : i<4) (hj : j<4) :
      HaarCarrierEqv blocks (squareField i j p) (squareField i j q) :=
    angularDerivative_carrier hb hi hj (angularDerivative_carrier hb hi hj h)
  exact HaarCarrierEqv.add (hs 0 1 (by decide) (by decide))
    (HaarCarrierEqv.add (hs 0 2 (by decide) (by decide))
      (HaarCarrierEqv.add (hs 0 3 (by decide) (by decide))
        (HaarCarrierEqv.add (hs 1 2 (by decide) (by decide))
          (HaarCarrierEqv.add (hs 1 3 (by decide) (by decide))
            (hs 2 3 (by decide) (by decide))))))

private theorem laplacian_neg (p : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polyNeg p)) (polyNeg (angularLaplacian p)) := by
  have h (i j : Nat) : RatPolyCoeffEqv (squareField i j (polyNeg p))
      (polyNeg (squareField i j p)) :=
    (angularDerivative_congr i j (angularDerivative_neg i j p)).trans
      (angularDerivative_neg i j _)
  have hs := (h 0 1).add ((h 0 2).add ((h 0 3).add ((h 1 2).add
    ((h 1 3).add (h 2 3)))))
  have hc := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.neg (.var 0)) (.add (.neg (.var 1)) (.add (.neg (.var 2))
      (.add (.neg (.var 3)) (.add (.neg (.var 4)) (.neg (.var 5)))))))
    (.neg sixExpr) (by decide) (squareEnvironment p)
  exact hs.trans hc

/-- The literal sum of the six original angular squares commutes with every
actual head rotation, under ALL original Haar insertions and shared spectators. -/
theorem angularLaplacian_angularDerivative_carrier {blocks i j : Nat}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (p : RatPoly) :
    HaarCarrierEqv blocks (angularLaplacian (angularDerivative i j p))
      (angularDerivative i j (angularLaplacian p)) := by
  if hij : i=j then
    subst j
    have hz (q : RatPoly) : RatPolyCoeffEqv (angularDerivative i i q) polyZero :=
      RatPolyCoeffEqv.add_neg_smul _
    exact (laplacian_carrier hb (RatPolyCoeffEqv.haarCarrier (hz p))).trans
      ((HaarCarrierEqv.refl blocks polyZero).trans
        (RatPolyCoeffEqv.haarCarrier (hz (angularLaplacian p))).symm)
  else
    if horder : i<j then
      exact sorted_centrality hb hi hj horder p
    else
      have h := sorted_centrality hb hj hi (by omega) p
      exact (laplacian_carrier hb
        (RatPolyCoeffEqv.haarCarrier (angular_plane_antisymmetry j i p))).trans
        ((RatPolyCoeffEqv.haarCarrier (laplacian_neg _)).trans
          ((HaarCarrierEqv.neg h).trans
            (RatPolyCoeffEqv.haarCarrier
              (angular_plane_antisymmetry j i (angularLaplacian p))).symm))

end YMGap.Continuum.SU2QuaternionAngularCasimirCentrality

#print axioms YMGap.Continuum.SU2QuaternionAngularCasimirCentrality.angularLaplacian_angularDerivative_carrier
#print axioms YMGap.Continuum.SU2QuaternionAngularCasimirCentrality.same_left_planes_reorder
#print axioms YMGap.Continuum.SU2QuaternionAngularCasimirCentrality.shared_middle_planes_reorder
