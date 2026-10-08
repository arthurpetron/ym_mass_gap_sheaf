/-
# Three paired Hessian directions are the six-plane trace

The mixed gradient identity is the finite bilinear polarization of the
decomposable coordinate-wedge square identity. Arbitrary-insertion Haar IBP
then identifies the second traces. No sphere relation, inverse, or sign of
the Hessian is assumed. The reciprocal consumer keeps the literal derivative
of its certified weight; the three-direction leading curvature cost is not
replaced by six times that cost. This is not a scaling or OS estimate.
-/
import YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign
import YMGap.Continuum.SU2QuaternionPairedFrameAt

namespace YMGap.Continuum.QuaternionHaarPairedHessianTrace
set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.SU2QuaternionPairedFrameAt
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarFiniteReciprocalHessianSign
local infix:50 " ≈ " => Q'.eqv

private def wedgeExpr (offset i j : Nat) : PolyExpr :=
  .add (.mul (.var i) (.var (offset+j)))
    (.neg (.mul (.var j) (.var (offset+i))))
private def plusExpr (offset : Nat) (i : Nat) : PolyExpr :=
  match i with
  | 0 => .add (wedgeExpr offset 0 1) (wedgeExpr offset 2 3)
  | 1 => .add (wedgeExpr offset 0 2) (.neg (wedgeExpr offset 1 3))
  | _ => .add (wedgeExpr offset 0 3) (wedgeExpr offset 1 2)
private def sixExpr (f : Nat → Nat → PolyExpr) : PolyExpr :=
  .add (f 0 1) (.add (f 0 2) (.add (f 0 3)
    (.add (f 1 2) (.add (f 1 3) (f 2 3)))))
private def pairedWedge (x d : Nat → RatPoly) (i : Fin 3) : RatPoly :=
  match i.val with
  | 0 => polyAdd (wedgeEntry x d 0 1) (wedgeEntry x d 2 3)
  | 1 => polyAdd (wedgeEntry x d 0 2) (polyNeg (wedgeEntry x d 1 3))
  | _ => polyAdd (wedgeEntry x d 0 3) (wedgeEntry x d 1 2)
private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega
private theorem field_pin (s i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative (4*s+i) (4*s+j) p)
      (wedgeEntry (fun k => polyVar (4*s+k))
        (fun k => ratDerivative (4*s+k) p) i j) :=
  (RatPolyCoeffEqv.refl _).add (neg_smul _).symm
private theorem paired_wedge_pin (s : Nat) (p : RatPoly) (i : Fin 3) :
    RatPolyCoeffEqv (pairedDerivativeAt s i p)
      (pairedWedge (fun k => polyVar (4*s+k))
        (fun k => ratDerivative (4*s+k) p) i) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact (field_pin s 0 1 p).add (field_pin s 2 3 p)
  · exact (field_pin s 0 2 p).add (RatPolyCoeffEqv.neg (field_pin s 1 3 p))
  · exact (field_pin s 0 3 p).add (field_pin s 1 2 p)
private theorem three_congr {f g : Fin 3 → RatPoly}
    (h : ∀ i, RatPolyCoeffEqv (f i) (g i)) :
    RatPolyCoeffEqv (threeSum f) (threeSum g) :=
  (h 0).add ((h 1).add (h 2))
private theorem six_congr {f g : Nat → Nat → RatPoly}
    (h : ∀ i j, RatPolyCoeffEqv (f i j) (g i j)) :
    RatPolyCoeffEqv (six f) (six g) :=
  (h 0 1).add ((h 0 2).add ((h 0 3).add ((h 1 2).add ((h 1 3).add (h 2 3)))))

/-- Bilinear polarization, at raw coefficient strength and any block. -/
theorem paired_gradient_mixed_pin (s : Nat) (r A : RatPoly) :
    RatPolyCoeffEqv
      (threeSum (fun i => polyMul (pairedDerivativeAt s i r) (pairedDerivativeAt s i A)))
      (six (fun i j => polyMul (angularDerivative (4*s+i) (4*s+j) r)
        (angularDerivative (4*s+i) (4*s+j) A))) := by
  let x := fun k => polyVar (4*s+k)
  let d := fun k => ratDerivative (4*s+k) r
  let e := fun k => ratDerivative (4*s+k) A
  have hp := three_congr (fun i => (paired_wedge_pin s r i).mul (paired_wedge_pin s A i))
  have hs := six_congr (fun i j => (field_pin s i j r).mul (field_pin s i j A))
  have hm : RatPolyCoeffEqv
      (threeSum (fun i => polyMul (pairedWedge x d i) (pairedWedge x e i)))
      (six (fun i j => polyMul (wedgeEntry x d i j) (wedgeEntry x e i j))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (plusExpr 4 0) (plusExpr 8 0))
        (.add (.mul (plusExpr 4 1) (plusExpr 8 1))
          (.mul (plusExpr 4 2) (plusExpr 8 2))))
      (sixExpr (fun i j => .mul (wedgeExpr 4 i j) (wedgeExpr 8 i j)))
      (by decide) (fun
        | 0 => x 0
        | 1 => x 1
        | 2 => x 2
        | 3 => x 3
        | 4 => d 0
        | 5 => d 1
        | 6 => d 2
        | 7 => d 3
        | 8 => e 0
        | 9 => e 1
        | 10 => e 2
        | _ => e 3)
  exact hp.trans (hm.trans hs.symm)

theorem paired_gradient_square_pin (s : Nat) (A : RatPoly) :
    RatPolyCoeffEqv (threeSum (fun i => polyMul (pairedDerivativeAt s i A) (pairedDerivativeAt s i A)))
      (six (fun i j => polyMul (angularDerivative (4*s+i) (4*s+j) A)
        (angularDerivative (4*s+i) (4*s+j) A))) :=
  paired_gradient_mixed_pin s A A

private theorem haar_add (n : Nat) (r p q : RatPoly) :
    quaternionHaar n (polyMul r (polyAdd p q)) ≈
      quaternionHaar n (polyMul r p)+quaternionHaar n (polyMul r q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right r p q))
    (quaternionHaar_append n _ _)
private theorem haar_neg (n : Nat) (r p : RatPoly) :
    quaternionHaar n (polyMul r (polyNeg p)) ≈ -quaternionHaar n (polyMul r p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((neg_smul p).mul_left r))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (-1) r p)
      (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))
private theorem haar_three (n : Nat) (r : RatPoly) (f : Fin 3 → RatPoly) :
    quaternionHaar n (polyMul r (threeSum f)) ≈
      quaternionHaar n (polyMul r (f 0))+
        (quaternionHaar n (polyMul r (f 1))+quaternionHaar n (polyMul r (f 2))) :=
  Q'.eqv_trans _ _ _ (haar_add n r _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (haar_add n r _ _))
private theorem pair_sum (n : Nat) (r p a b c d : RatPoly)
    (ha : quaternionHaar n (polyMul r a) ≈ -quaternionHaar n (polyMul p c))
    (hb : quaternionHaar n (polyMul r b) ≈ -quaternionHaar n (polyMul p d)) :
    quaternionHaar n (polyMul r (polyAdd a b)) ≈
      -quaternionHaar n (polyMul p (polyAdd c d)) :=
  Q'.eqv_trans _ _ _ (haar_add n r a b)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha hb)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_add_eqv _ _))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (haar_add n p c d)))))
private theorem paired_pair {n s : Nat} (hs : s<n) (i : Fin 3) (r p : RatPoly) :
    quaternionHaar n (polyMul r (pairedDerivativeAt s i p)) ≈
      -quaternionHaar n (polyMul p (pairedDerivativeAt s i r)) := by
  have h (a b : Nat) (ha : a<4) (hb : b<4) :=
    Q'.eqv_trans _ _ _ (angular_pair_at hs ha hb r p)
      (Q'.neg_eqv_congr _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ p)))
  rcases direction_cases i with rfl | rfl | rfl
  · exact pair_sum n r p _ _ _ _ (h 0 1 (by decide) (by decide)) (h 2 3 (by decide) (by decide))
  · have hn : quaternionHaar n (polyMul r (polyNeg (angularDerivative (4*s+1) (4*s+3) p))) ≈
        -quaternionHaar n (polyMul p (polyNeg (angularDerivative (4*s+1) (4*s+3) r))) :=
      Q'.eqv_trans _ _ _ (haar_neg n r _)
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (h 1 3 (by decide) (by decide)))
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (haar_neg n p _))))
    exact pair_sum n r p _ _ _ _ (h 0 2 (by decide) (by decide)) hn
  · exact pair_sum n r p _ _ _ _ (h 0 3 (by decide) (by decide)) (h 1 2 (by decide) (by decide))
private theorem three_neg (a b c : Q') :
    -a+(-b+ -c) ≈ -(a+(b+c)) :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm (Q'.neg_add_eqv b c)))
    (Q'.eqv_symm (Q'.neg_add_eqv a (b+c)))
private theorem six_neg (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

/-- Trace equality under EVERY original Haar insertion; no support premise. -/
theorem paired_second_trace_carrier {n s : Nat} (hs : s<n) (A : RatPoly) :
    HaarCarrierEqv n (threeSum (fun i => pairedDerivativeAt s i (pairedDerivativeAt s i A)))
      (six (fun i j => angularDerivative (4*s+i) (4*s+j) (angularDerivative (4*s+i) (4*s+j) A))) := by
  intro r
  let pA : Fin 3 → RatPoly := fun i => pairedDerivativeAt s i A
  let pR : Fin 3 → RatPoly := fun i => pairedDerivativeAt s i r
  let dA : Nat → Nat → RatPoly := fun i j => angularDerivative (4*s+i) (4*s+j) A
  let dR : Nat → Nat → RatPoly := fun i j => angularDerivative (4*s+i) (4*s+j) r
  let pairedGrad : Fin 3 → RatPoly := fun i => polyMul (pA i) (pR i)
  let sixGrad : Nat → Nat → RatPoly := fun i j => polyMul (dA i j) (dR i j)
  let pairedTrace : Fin 3 → RatPoly := fun i => pairedDerivativeAt s i (pA i)
  let sixTrace : Nat → Nat → RatPoly := fun i j => angularDerivative (4*s+i) (4*s+j) (dA i j)
  let moments : Nat → Nat → Q' := fun i j => quaternionHaar n (polyMul polyOne (sixGrad i j))
  have hi (i : Fin 3) : quaternionHaar n (polyMul r (pairedTrace i)) ≈
      -quaternionHaar n (polyMul polyOne (pairedGrad i)) :=
    Q'.eqv_trans _ _ _ (paired_pair hs i r (pA i))
      (Q'.neg_eqv_congr _ _ (haar_of_coeff (blocks := n)
        (RatPolyCoeffEqv.one_mul (pairedGrad i)).symm))
  have hpaired : quaternionHaar n (polyMul r (threeSum pairedTrace)) ≈
      -quaternionHaar n (polyMul polyOne (threeSum pairedGrad)) :=
    Q'.eqv_trans _ _ _ (haar_three n r pairedTrace)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hi 0)
      (Q'.add_eqv_congr' (hi 1) (hi 2)))
      (Q'.eqv_trans _ _ _ (three_neg _ _ _)
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (haar_three n polyOne pairedGrad)))))
  have hmix : quaternionHaar n (polyMul polyOne (threeSum pairedGrad)) ≈
      quaternionHaar n (polyMul polyOne (six sixGrad)) :=
    haar_of_coeff (blocks := n) ((paired_gradient_mixed_pin s A r).mul_left polyOne)
  have hplane (i j : Nat) (hi : i<4) (hj : j<4) :
      quaternionHaar n (polyMul r (sixTrace i j)) ≈ -(moments i j) :=
    Q'.eqv_trans _ _ _ (angular_pair_at hs hi hj r (dA i j))
      (Q'.neg_eqv_congr _ _ (haar_of_coeff (blocks := n)
        ((RatPolyCoeffEqv.one_mul (sixGrad i j)).trans
          (RatPolyCoeffEqv.mul_comm (dA i j) (dR i j))).symm))
  have hplanes : sixValue (fun i j => quaternionHaar n (polyMul r (sixTrace i j))) ≈
      sixValue (fun i j => -(moments i j)) := sixValue_congr _ _ hplane
  have hneg : sixValue (fun i j => -(moments i j)) ≈
      -quaternionHaar n (polyMul polyOne (six sixGrad)) :=
    Q'.eqv_trans _ _ _ (six_neg moments)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (haar_six n polyOne sixGrad)))
  have hsix : quaternionHaar n (polyMul r (six sixTrace)) ≈
      -quaternionHaar n (polyMul polyOne (six sixGrad)) :=
    Q'.eqv_trans _ _ _ (haar_six n r sixTrace) (Q'.eqv_trans _ _ _ hplanes hneg)
  exact Q'.eqv_trans _ _ _ hpaired (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hmix)
    (Q'.eqv_symm hsix))

/-- The entire signed Hessian trace, not either term separately. Multiplying
this carrier equality by any literal weight preserves it. -/
theorem paired_hessian_trace_carrier {n s : Nat} (hs : s<n) (A : RatPoly) :
    HaarCarrierEqv n
      (polyAdd (polyMul A (threeSum (fun i => pairedDerivativeAt s i (pairedDerivativeAt s i A))))
        (polyNeg (threeSum (fun i => polyMul (pairedDerivativeAt s i A) (pairedDerivativeAt s i A)))))
      (polyAdd (polyMul A (six (fun i j => angularDerivative (4*s+i) (4*s+j)
          (angularDerivative (4*s+i) (4*s+j) A))))
        (polyNeg (six (fun i j => polyMul (angularDerivative (4*s+i) (4*s+j) A)
          (angularDerivative (4*s+i) (4*s+j) A))))) :=
  HaarCarrierEqv.add (HaarCarrierEqv.mul_left A (paired_second_trace_carrier hs A))
    (HaarCarrierEqv.neg (RatPolyCoeffEqv.haarCarrier (paired_gradient_square_pin s A)))

private def planeSlot (i j : Nat) : Nat :=
  if i=0 then j-1 else if i=1 then j+1 else 5
private theorem six_trace_distribution (A : RatPoly) (f g : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (polyAdd (polyMul A (six f)) (polyNeg (six g)))
      (six (fun i j => polyAdd (polyMul A (f i j)) (polyNeg (g i j)))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 12) (sixExpr (fun i j => .var (planeSlot i j))))
      (.neg (sixExpr (fun i j => .var (6+planeSlot i j)))))
    (sixExpr (fun i j => .add (.mul (.var 12) (.var (planeSlot i j)))
      (.neg (.var (6+planeSlot i j)))))
    (by decide) (fun
      | 0 => f 0 1
      | 1 => f 0 2
      | 2 => f 0 3
      | 3 => f 1 2
      | 4 => f 1 3
      | 5 => f 2 3
      | 6 => g 0 1
      | 7 => g 0 2
      | 8 => g 0 3
      | 9 => g 1 2
      | 10 => g 1 3
      | 11 => g 2 3
      | _ => A)

/-- Actual successor reciprocal: only its produced favorable correction is
discarded. The SAME certified weight and all six literal signed derivatives
of that weight remain. This is the three-direction Hessian trace consumer,
not a bound on its noise or interaction correction. -/
theorem finite_reciprocal_paired_hessian_ibp_le {blocks block : Nat}
    (hb : block<blocks) {F A : RatPoly} {upper : Q'} (hupper : (0 : Q')<upper)
    (hA : SupportedQuaternionBlocks blocks A) (PF : Certificate blocks F)
    (U : Certificate blocks (polyAdd (cap upper) (polyNeg A))) (k : Nat) :
    let G := reciprocal A upper hupper (k+1)
    quaternionHaar blocks (polyMul (polyMul F (polyMul G G))
      (polyAdd (polyMul A (threeSum (fun i => pairedDerivativeAt block i (pairedDerivativeAt block i A))))
        (polyNeg (threeSum (fun i => polyMul (pairedDerivativeAt block i A) (pairedDerivativeAt block i A)))))) ≤
      -sixValue (fun i j => quaternionHaar blocks
        (polyMul (polyMul (polyMul A (polyMul G G))
          (angularDerivative (4*block+i) (4*block+j) A))
          (angularDerivative (4*block+i) (4*block+j) F))) := by
  dsimp only
  let G := reciprocal A upper hupper (k+1)
  let W := polyMul F (polyMul G G)
  let dA : Nat → Nat → RatPoly := fun i j => angularDerivative (4*block+i) (4*block+j) A
  let ddA : Nat → Nat → RatPoly := fun i j => angularDerivative (4*block+i) (4*block+j) (dA i j)
  let squares : Nat → Nat → RatPoly := fun i j => polyMul (dA i j) (dA i j)
  let curvature : Nat → Nat → RatPoly := fun i j => polyAdd (polyMul A (ddA i j)) (polyNeg (squares i j))
  let correction : Nat → Nat → Q' := fun i j => quaternionHaar blocks
    (polyMul (polyMul (polyMul A (polyMul G G)) (dA i j))
      (angularDerivative (4*block+i) (4*block+j) F))
  have hdist : quaternionHaar blocks (polyMul W
      (polyAdd (polyMul A (six ddA)) (polyNeg (six squares)))) ≈
      quaternionHaar blocks (polyMul W (six curvature)) :=
    haar_of_coeff (blocks := blocks) ((six_trace_distribution A ddA squares).mul_left W)
  have hsum : sixValue (fun i j => quaternionHaar blocks (polyMul W (curvature i j))) ≤
      sixValue (fun i j => -(correction i j)) :=
    sixValue_mono _ _ (fun i j hi hj => finite_reciprocal_hessian_ibp_le hb hi hj hupper hA PF U k)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (paired_hessian_trace_carrier hb A W))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_six blocks W curvature))
        (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (six_neg correction)))))

end YMGap.Continuum.QuaternionHaarPairedHessianTrace
#print axioms YMGap.Continuum.QuaternionHaarPairedHessianTrace.paired_gradient_mixed_pin
#print axioms YMGap.Continuum.QuaternionHaarPairedHessianTrace.paired_gradient_square_pin
#print axioms YMGap.Continuum.QuaternionHaarPairedHessianTrace.paired_second_trace_carrier
#print axioms YMGap.Continuum.QuaternionHaarPairedHessianTrace.paired_hessian_trace_carrier
#print axioms YMGap.Continuum.QuaternionHaarPairedHessianTrace.finite_reciprocal_paired_hessian_ibp_le
