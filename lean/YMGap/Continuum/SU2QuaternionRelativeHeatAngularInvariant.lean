/-
# Simultaneous angular invariance of the actual relative heat prefix

The scalar of x*conj(y) is the four-coordinate dot product. Applying the
same angular rotation to both arguments cancels. The proof uses the original
Haar carrier to respect trailing-zero padding, then the exact character
chain rule and finite heat sum. No cutoff or positivity premise is needed.
-/
import YMGap.Continuum.SU2QuaternionAngularCoordinate
import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry

namespace YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularCoordinate
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCharacterDerivative
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative

def pairedAt (a b u v : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (angularDerivative (4*a+u) (4*a+v) p)
    (angularDerivative (4*b+u) (4*b+v) p)

theorem pairedAt_add (a b u v : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedAt a b u v (polyAdd p q))
      (polyAdd (pairedAt a b u v p) (pairedAt a b u v q)) :=
  ((angularDerivative_add _ _ p q).add (angularDerivative_add _ _ p q)).trans
    (RatPolyCoeffEqv.four_add_swap _ _ _ _)

theorem pairedAt_mul (a b u v : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedAt a b u v (polyMul p q))
      (polyAdd (polyMul (pairedAt a b u v p) q)
        (polyMul p (pairedAt a b u v q))) := by
  refine ((angularDerivative_mul _ _ p q).add
    (angularDerivative_mul _ _ p q)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 4) (.var 1)))
      (.add (.mul (.var 2) (.var 5)) (.mul (.var 4) (.var 3))))
    (.add (.mul (.add (.var 0) (.var 2)) (.var 5))
      (.mul (.var 4) (.add (.var 1) (.var 3)))) (by decide)
    (fun | 0 => angularDerivative (4*a+u) (4*a+v) p
         | 1 => angularDerivative (4*a+u) (4*a+v) q
         | 2 => angularDerivative (4*b+u) (4*b+v) p
         | 3 => angularDerivative (4*b+u) (4*b+v) q
         | 4 => p | _ => q)

private def env (a b : Nat) : Nat → RatPoly
  | 0 => polyVar (4*a) | 1 => polyVar (4*b)
  | 2 => polyVar (4*a+1) | 3 => polyVar (4*b+1)
  | 4 => polyVar (4*a+2) | 5 => polyVar (4*b+2)
  | 6 => polyVar (4*a+3) | _ => polyVar (4*b+3)

private theorem env_even (a b k : Nat) (hk : k < 4) :
    env a b (2*k) = polyVar (4*a+k) := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

private theorem env_odd (a b k : Nat) (hk : k < 4) :
    env a b (2*k+1) = polyVar (4*b+k) := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

private def dotExpr : PolyExpr :=
  .add (.mul (.var 0) (.var 1)) (.add (.mul (.var 2) (.var 3))
    (.add (.mul (.var 4) (.var 5)) (.mul (.var 6) (.var 7))))

private theorem scalar_dot (a b : Nat) :
    RatPolyCoeffEqv (scalarAt a b) (coeffEvalExpr (env a b) dotExpr) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1))
      (.neg (.add (.mul (.var 2) (.neg (.var 3)))
        (.add (.mul (.var 4) (.neg (.var 5))) (.mul (.var 6) (.neg (.var 7)))))))
    dotExpr (by decide) (env a b)

private def planeExpr (u v side k : Nat) : PolyExpr :=
  .add (if v=k then .var (2*u+side) else .const 0)
    (.neg (if u=k then .var (2*v+side) else .const 0))

private theorem plane_eval (a b u v side k : Nat) :
    RatPolyCoeffEqv
      (polyAdd (if v=k then env a b (2*u+side) else polyZero)
        (polySmul (-1) (if u=k then env a b (2*v+side) else polyZero)))
      (coeffEvalExpr (env a b) (planeExpr u v side k)) := by
  have hz : RatPolyCoeffEqv polyZero (coeffEvalExpr (env a b) (.const 0)) :=
    (RatPolyCoeffEqv.zero_smul polyOne).symm
  have hl : RatPolyCoeffEqv (if v=k then env a b (2*u+side) else polyZero)
      (coeffEvalExpr (env a b) (if v=k then .var (2*u+side) else .const 0)) := by
    by_cases h : v=k <;> simp only [h, ↓reduceIte]
    · exact .refl _
    · exact hz
  have hr : RatPolyCoeffEqv (if u=k then env a b (2*v+side) else polyZero)
      (coeffEvalExpr (env a b) (if u=k then .var (2*v+side) else .const 0)) := by
    by_cases h : u=k <;> simp only [h, ↓reduceIte]
    · exact .refl _
    · exact hz
  exact hl.add ((hr.smul (-1)).trans (neg_smul _).symm)

private theorem paired_coordinate_left (blocks a b u v k : Nat)
    (ha : a < blocks) (hab : a ≠ b) (hu : u<4) (hv : v<4) (hk : k<4) :
    HaarCarrierEqv blocks (pairedAt a b u v (polyVar (4*a+k)))
      (coeffEvalExpr (env a b) (planeExpr u v 0 k)) := by
  have hl := angular_coordinate_carrier (i := 4*a+u) (j := 4*a+v)
    (show 4*a+k < 4*blocks by omega)
  have hr := angular_coordinate_carrier (i := 4*b+u) (j := 4*b+v)
    (show 4*a+k < 4*blocks by omega)
  have hvb : 4*b+v ≠ 4*a+k := by intro he; exact hab (by omega)
  have hub : 4*b+u ≠ 4*a+k := by intro he; exact hab (by omega)
  simp only [hvb, hub, ↓reduceIte] at hr
  have hz : HaarCarrierEqv blocks (angularDerivative (4*b+u) (4*b+v)
      (polyVar (4*a+k))) polyZero :=
    hr.trans (RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl polyZero).add (RatPolyCoeffEqv.smul_zero (-1))).trans
        (RatPolyCoeffEqv.add_zero _)))
  have hv' : (4*a+v = 4*a+k) ↔ v=k :=
    ⟨Nat.add_left_cancel, fun h => congrArg (fun x => 4*a+x) h⟩
  have hu' : (4*a+u = 4*a+k) ↔ u=k :=
    ⟨Nat.add_left_cancel, fun h => congrArg (fun x => 4*a+x) h⟩
  have hl' : HaarCarrierEqv blocks (angularDerivative (4*a+u) (4*a+v) (polyVar (4*a+k)))
      (polyAdd (if v=k then polyVar (4*a+u) else polyZero)
        (polySmul (-1) (if u=k then polyVar (4*a+v) else polyZero))) := by
    by_cases h1 : v=k <;> by_cases h2 : u=k
    · simpa only [if_pos h1, if_pos h2, if_pos (hv'.mpr h1), if_pos (hu'.mpr h2)] using hl
    · simpa only [if_pos h1, if_neg h2, if_pos (hv'.mpr h1), if_neg (fun h => h2 (hu'.mp h))] using hl
    · simpa only [if_neg h1, if_pos h2, if_neg (fun h => h1 (hv'.mp h)), if_pos (hu'.mpr h2)] using hl
    · simpa only [if_neg h1, if_neg h2, if_neg (fun h => h1 (hv'.mp h)), if_neg (fun h => h2 (hu'.mp h))] using hl
  have pe := plane_eval a b u v 0 k
  simp only [Nat.add_zero, env_even a b u hu, env_even a b v hv] at pe
  exact (HaarCarrierEqv.add hl' hz).trans
    (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.add_zero _).trans pe))

private theorem paired_coordinate_right (blocks a b u v k : Nat)
    (hb : b < blocks) (hab : a ≠ b) (hu : u<4) (hv : v<4) (hk : k<4) :
    HaarCarrierEqv blocks (pairedAt a b u v (polyVar (4*b+k)))
      (coeffEvalExpr (env a b) (planeExpr u v 1 k)) := by
  have hl := angular_coordinate_carrier (i := 4*a+u) (j := 4*a+v)
    (show 4*b+k < 4*blocks by omega)
  have hr := angular_coordinate_carrier (i := 4*b+u) (j := 4*b+v)
    (show 4*b+k < 4*blocks by omega)
  have hva : 4*a+v ≠ 4*b+k := by intro he; exact hab (by omega)
  have hua : 4*a+u ≠ 4*b+k := by intro he; exact hab (by omega)
  simp only [hva, hua, ↓reduceIte] at hl
  have hz : HaarCarrierEqv blocks (angularDerivative (4*a+u) (4*a+v)
      (polyVar (4*b+k))) polyZero :=
    hl.trans (RatPolyCoeffEqv.haarCarrier
      (((RatPolyCoeffEqv.refl polyZero).add (RatPolyCoeffEqv.smul_zero (-1))).trans
        (RatPolyCoeffEqv.add_zero _)))
  have hv' : (4*b+v = 4*b+k) ↔ v=k :=
    ⟨Nat.add_left_cancel, fun h => congrArg (fun x => 4*b+x) h⟩
  have hu' : (4*b+u = 4*b+k) ↔ u=k :=
    ⟨Nat.add_left_cancel, fun h => congrArg (fun x => 4*b+x) h⟩
  have hr' : HaarCarrierEqv blocks (angularDerivative (4*b+u) (4*b+v) (polyVar (4*b+k)))
      (polyAdd (if v=k then polyVar (4*b+u) else polyZero)
        (polySmul (-1) (if u=k then polyVar (4*b+v) else polyZero))) := by
    by_cases h1 : v=k <;> by_cases h2 : u=k
    · simpa only [if_pos h1, if_pos h2, if_pos (hv'.mpr h1), if_pos (hu'.mpr h2)] using hr
    · simpa only [if_pos h1, if_neg h2, if_pos (hv'.mpr h1), if_neg (fun h => h2 (hu'.mp h))] using hr
    · simpa only [if_neg h1, if_pos h2, if_neg (fun h => h1 (hv'.mp h)), if_pos (hu'.mpr h2)] using hr
    · simpa only [if_neg h1, if_neg h2, if_neg (fun h => h1 (hv'.mp h)), if_neg (fun h => h2 (hu'.mp h))] using hr
  have pe := plane_eval a b u v 1 k
  simp only [env_odd a b u hu, env_odd a b v hv] at pe
  exact (HaarCarrierEqv.add hz hr').trans
    (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.zero_add _).trans pe))

private def termExpr (u v k : Nat) : PolyExpr :=
  .add (.mul (planeExpr u v 0 k) (.var (2*k+1)))
    (.mul (.var (2*k)) (planeExpr u v 1 k))

private def responseExpr (u v : Nat) : PolyExpr :=
  .add (termExpr u v 0) (.add (termExpr u v 1)
    (.add (termExpr u v 2) (termExpr u v 3)))

/-- Simultaneous rotations cancel in the actual relative scalar, at every
pair of distinct supported blocks and every coordinate plane. -/
theorem scalarAt_pairedAngular_carrier_at (blocks a b u v : Nat)
    (ha : a < blocks) (hb : b < blocks) (hab : a ≠ b) (hu : u<4) (hv : v<4) :
    HaarCarrierEqv blocks (pairedAt a b u v (scalarAt a b)) polyZero := by
  have ht (k : Nat) (hk : k<4) : HaarCarrierEqv blocks
      (pairedAt a b u v (polyMul (polyVar (4*a+k)) (polyVar (4*b+k))))
      (coeffEvalExpr (env a b) (termExpr u v k)) := by
    have h := HaarCarrierEqv.add
      (HaarCarrierEqv.mul_right (polyVar (4*b+k))
        (paired_coordinate_left blocks a b u v k ha hab hu hv hk))
      ((paired_coordinate_right blocks a b u v k hb hab hu hv hk).mul_left
        (polyVar (4*a+k)))
    simp only [termExpr, coeffEvalExpr, env_even a b k hk, env_odd a b k hk]
    exact (RatPolyCoeffEqv.haarCarrier (pairedAt_mul a b u v _ _)).trans h
  have hadd (p q : RatPoly) := RatPolyCoeffEqv.haarCarrier
    (blocks := blocks) (pairedAt_add a b u v p q)
  have hdot : HaarCarrierEqv blocks
      (pairedAt a b u v (coeffEvalExpr (env a b) dotExpr))
      (coeffEvalExpr (env a b) (responseExpr u v)) :=
    (hadd _ _).trans (HaarCarrierEqv.add (ht 0 (by decide))
      ((hadd _ _).trans (HaarCarrierEqv.add (ht 1 (by decide))
        ((hadd _ _).trans (HaarCarrierEqv.add (ht 2 (by decide)) (ht 3 (by decide)))))))
  have hzero : RatPolyCoeffEqv (coeffEvalExpr (env a b) (responseExpr u v)) polyZero := by
    have hc : u=0 ∨ u=1 ∨ u=2 ∨ u=3 := by omega
    have hd : v=0 ∨ v=1 ∨ v=2 ∨ v=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      rcases hd with rfl | rfl | rfl | rfl <;>
      exact (coeffEvalExpr_eqv_of_normalize_eq _ (.const 0) (by decide) (env a b)).trans
        (RatPolyCoeffEqv.zero_smul polyOne)
  exact (RatPolyCoeffEqv.haarCarrier
    ((angularDerivative_congr _ _ (scalar_dot a b)).add
      (angularDerivative_congr _ _ (scalar_dot a b)))).trans
      (hdot.trans (RatPolyCoeffEqv.haarCarrier hzero))

/-- The actual finite heat prefix inherits simultaneous rotation invariance
for every rational nome and every cutoff. -/
theorem heatAt_pairedAngular_carrier_at (blocks a b u v : Nat)
    (ha : a < blocks) (hb : b < blocks) (hab : a ≠ b) (hu : u<4) (hv : v<4)
    (w : Q') (K : Nat) :
    HaarCarrierEqv blocks (pairedAt a b u v (heatAt a b w K)) polyZero := by
  have hz := scalarAt_pairedAngular_carrier_at blocks a b u v ha hb hab hu hv
  have hchar (spin : Nat) : HaarCarrierEqv blocks
      (pairedAt a b u v (characterPolynomial (scalarAt a b) spin)) polyZero := by
    have he := ((angularDerivative_character_at (4*a+u) (4*a+v) (scalarAt a b) spin).add
      (angularDerivative_character_at (4*b+u) (4*b+v) (scalarAt a b) spin)).trans
        (RatPolyCoeffEqv.mul_add_right _ _ _).symm
    exact (RatPolyCoeffEqv.haarCarrier he).trans
      ((hz.mul_left _).trans (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_zero_right _)))
  have hsmul (c : Q') (p : RatPoly) : RatPolyCoeffEqv
      (pairedAt a b u v (polySmul c p)) (polySmul c (pairedAt a b u v p)) :=
    ((angularDerivative_smul _ _ c p).add (angularDerivative_smul _ _ c p)).trans
      (RatPolyCoeffEqv.smul_add c _ _).symm
  unfold heatAt
  induction List.range (K+1) with
  | nil => exact HaarCarrierEqv.refl _ _
  | cons spin spins ih =>
      exact (RatPolyCoeffEqv.haarCarrier (pairedAt_add a b u v _ _)).trans
        ((HaarCarrierEqv.add
          ((RatPolyCoeffEqv.haarCarrier (hsmul _ _)).trans
            ((HaarCarrierEqv.smul _ (hchar spin)).trans
              (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.smul_zero _)))) ih).trans
                (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _)))

#print axioms pairedAt_add
#print axioms pairedAt_mul

end YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant

#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant.scalarAt_pairedAngular_carrier_at
#print axioms YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant.heatAt_pairedAngular_carrier_at
