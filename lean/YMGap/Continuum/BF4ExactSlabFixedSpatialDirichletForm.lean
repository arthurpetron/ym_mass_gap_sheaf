/-
# Exact positive edge energy for the ORIGINAL spatially weighted transfer

For the literal T=K V, retain the complete edge density
K(x,y)V(x)V(y)g(x)g(y). Twice the difference between its marginal
quadratic form and its mixed pairing is its integral against (f(x)-f(y))².
The identity needs only source support. Actual certificates for K, V and g
make this energy nonnegative at the existing late-cutoff threshold.

No reciprocal, square root, eigenvector, stationary law or strict estimate
is supplied or assumed. The diagonal weight is V*g*Tg, not V or V². A
uniform lower fraction of its centered variance remains a separate estimate.
The original finite terminal messages are consumers, not new hypotheses.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder (kineticCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] weightedMass kineticWeight spatialWeight baseLinks

/-- One original kinetic layer and exactly one spatial factor at each end. -/
def edgeDensity (w : Q') (K width : Nat) (g : RatPoly) : RatPoly :=
  polyMul (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) g))
    (liftBoundary (N width) (polyMul (spatialWeight w K width) g))

def jump (width : Nat) (f : RatPoly) : RatPoly :=
  polyAdd f (polyNeg (liftBoundary (N width) f))

/-- The actual edge marginal and mixed transfer pairing, without division. -/
def energy (w : Q') (K width : Nat) (g f : RatPoly) : Q' :=
  weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) (polyMul f f)) +
    -(weightedMass w K width
      (polyMul (polyMul g f) (transferStep w K width (polyMul g f))))

private theorem support_pair {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks (blocks+blocks) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem edgeDensity_supported (w : Q') (K width : Nat) {g : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g) :
    SupportedQuaternionBlocks (N width+N width) (edgeDensity w K width g) :=
  supported_polyMul
    (supported_polyMul (kineticWeight_supported w K width)
      (support_pair (supported_polyMul (spatialWeight_supported w K width) hg)))
    (lift_supported (supported_polyMul (spatialWeight_supported w K width) hg) (N width))

theorem jump_supported (width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width+N width) (jump width f) :=
  supported_add (support_pair hf) (support_neg (lift_supported hf (N width)))

private theorem pair_algebra (k v g f lv lg h : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul (polyMul k (polyMul v g)) (polyMul lv lg)) (polyMul f h))
      (polyMul (polyMul k (polyMul v (polyMul g f))) (polyMul lv (polyMul lg h))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 4) (.var 5)))
      (.mul (.var 3) (.var 6)))
    (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.var 4) (.mul (.var 5) (.var 6)))) (by decide)
    (fun | 0 => k | 1 => v | 2 => g | 3 => f | 4 => lv | 5 => lg | _ => h)

private theorem lower_algebra (k v g u p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul (polyMul k (polyMul v g)) u) p)
      (polyMul (polyMul k (polyMul v (polyMul g p))) u) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.var 4))
    (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 4)))) (.var 3))
    (by decide) (fun | 0 => k | 1 => v | 2 => g | 3 => u | _ => p)

private theorem upper_algebra (a v g p : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a (polyMul v g)) p)
      (polyMul a (polyMul v (polyMul g p))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
    (by decide) (fun | 0 => a | 1 => v | 2 => g | _ => p)

private theorem output_pairing (w : Q') (K width : Nat) (f h : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) f))
        (liftBoundary (N width) (polyMul (spatialWeight w K width) h))) ≈
      weightedMass w K width (polyMul h (transferStep w K width f)) := by
  unfold weightedMass
  exact Q'.eqv_trans _ _ _
    (step_pairing (N width) (N width) (kineticWeight w K width)
      (spatialWeight w K width) f (polyMul (spatialWeight w K width) h))
    (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans
      (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) h (transferStep w K width f))))

/-- Arbitrary signed lower/upper insertions retain both copies of g and V. -/
theorem edge_pairing (w : Q') (K width : Nat) (g f h : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g) (polyMul f (liftBoundary (N width) h))) ≈
      weightedMass w K width
        (polyMul (polyMul g h) (transferStep w K width (polyMul g f))) := by
  have hp : RatPolyCoeffEqv
      (polyMul (edgeDensity w K width g) (polyMul f (liftBoundary (N width) h)))
      (polyMul (polyMul (kineticWeight w K width)
        (polyMul (spatialWeight w K width) (polyMul g f)))
        (liftBoundary (N width) (polyMul (spatialWeight w K width) (polyMul g h)))) := by
    simpa only [edgeDensity, lift_product] using pair_algebra
      (kineticWeight w K width) (spatialWeight w K width) g f
      (liftBoundary (N width) (spatialWeight w K width))
      (liftBoundary (N width) g) (liftBoundary (N width) h)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp) (output_pairing w K width _ _)

private theorem lower_pairing (w : Q') (K width : Nat) (g p : RatPoly) :
    quaternionHaar (N width+N width) (polyMul (edgeDensity w K width g) p) ≈
      weightedMass w K width (polyMul g (transferStep w K width (polyMul g p))) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (lower_algebra (kineticWeight w K width) (spatialWeight w K width)
      g (liftBoundary (N width) (polyMul (spatialWeight w K width) g)) p))
    (output_pairing w K width _ _)

private theorem upper_pairing (w : Q') (K width : Nat) (g p : RatPoly) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g) (liftBoundary (N width) p)) ≈
      weightedMass w K width (polyMul (polyMul g p) (transferStep w K width g)) := by
  have hp : RatPolyCoeffEqv
      (polyMul (edgeDensity w K width g) (liftBoundary (N width) p))
      (polyMul (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) g))
        (liftBoundary (N width) (polyMul (spatialWeight w K width) (polyMul g p)))) := by
    simpa only [edgeDensity, lift_product] using upper_algebra
      (polyMul (kineticWeight w K width) (polyMul (spatialWeight w K width) g))
      (liftBoundary (N width) (spatialWeight w K width))
      (liftBoundary (N width) g) (liftBoundary (N width) p)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp) (output_pairing w K width _ _)

private theorem product_reorder (a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a b) c) (polyMul (polyMul a c) b) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => a | 1 => b | _ => c)

/-- The two edge diagonals are twice the SAME original temporal marginal.
This is an identity, not a change to the endpoint weight or an invariant law. -/
theorem edge_diagonal_identity (w : Q') (K width : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g)
        (polyAdd (polyMul f f)
          (polyMul (liftBoundary (N width) f) (liftBoundary (N width) f)))) ≈
      (2 : Q') * weightedMass w K width
        (polyMul (polyMul g (transferStep w K width g)) (polyMul f f)) := by
  let d := weightedMass w K width
    (polyMul (polyMul g (transferStep w K width g)) (polyMul f f))
  have hd : weightedMass w K width
      (polyMul (polyMul g (polyMul f f)) (transferStep w K width g)) ≈ d :=
    weightedMass_congr w K width (product_reorder g (polyMul f f) (transferStep w K width g))
  have hl : quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g) (polyMul f f)) ≈ d :=
    Q'.eqv_trans _ _ _ (lower_pairing w K width g (polyMul f f))
      (Q'.eqv_trans _ _ _
        (transferStep_weighted_symmetric w K width (supported_polyMul hg (supported_polyMul hf hf)) hg) hd)
  have hr : quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g)
        (polyMul (liftBoundary (N width) f) (liftBoundary (N width) f))) ≈ d := by
    rw [← lift_product]
    exact Q'.eqv_trans _ _ _ (upper_pairing w K width g (polyMul f f)) hd
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hl hr)
        (poly_identity_of_normal_eq (.add (.var 0) (.var 0))
          (.mul (.const 2) (.var 0)) (by decide) (fun _ => d))))

private theorem square_difference (e a b : RatPoly) :
    RatPolyCoeffEqv (polyMul e (polyMul (polyAdd a (polyNeg b)) (polyAdd a (polyNeg b))))
      (polyAdd (polyMul e (polyMul a a))
        (polyAdd (polyNeg (polyMul e (polyMul a b)))
          (polyAdd (polyNeg (polyMul e (polyMul a b))) (polyMul e (polyMul b b))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.add (.var 1) (.neg (.var 2))) (.add (.var 1) (.neg (.var 2)))))
    (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
      (.add (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
        (.add (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
          (.mul (.var 0) (.mul (.var 2) (.var 2))))))
    (by decide) (fun | 0 => e | 1 => a | _ => b)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem haar_expansion (blocks : Nat) (e a b : RatPoly) :
    quaternionHaar blocks (polyMul e (polyMul (polyAdd a (polyNeg b)) (polyAdd a (polyNeg b)))) ≈
      quaternionHaar blocks (polyMul e (polyMul a a)) +
        (-(quaternionHaar blocks (polyMul e (polyMul a b))) +
          (-(quaternionHaar blocks (polyMul e (polyMul a b))) +
            quaternionHaar blocks (polyMul e (polyMul b b)))) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (square_difference e a b))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
          (Q'.add_eqv_congr' (haar_neg blocks _)
            (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
              (Q'.add_eqv_congr' (haar_neg blocks _) (Q'.eqv_refl _)))))))

private theorem twice_difference (a b : Q') : a + (-b + (-b+a)) ≈ (2 : Q')*(a + -b) :=
  poly_identity_of_normal_eq
    (.add (.var 0) (.add (.neg (.var 1)) (.add (.neg (.var 1)) (.var 0))))
    (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))) (by decide)
    (fun | 0 => a | _ => b)

/-- Exact division-free edge identity for the same original K/V transfer. -/
theorem energy_identity (w : Q') (K width : Nat) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) :
    (2 : Q') * energy w K width g f ≈
      quaternionHaar (N width+N width)
        (polyMul (edgeDensity w K width g) (polyMul (jump width f) (jump width f))) := by
  let d := weightedMass w K width
    (polyMul (polyMul g (transferStep w K width g)) (polyMul f f))
  let c := weightedMass w K width
    (polyMul (polyMul g f) (transferStep w K width (polyMul g f)))
  have hd : weightedMass w K width
      (polyMul (polyMul g (polyMul f f)) (transferStep w K width g)) ≈ d :=
    weightedMass_congr w K width (product_reorder g (polyMul f f) (transferStep w K width g))
  have hl : quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g) (polyMul f f)) ≈ d :=
    Q'.eqv_trans _ _ _ (lower_pairing w K width g (polyMul f f))
      (Q'.eqv_trans _ _ _
        (transferStep_weighted_symmetric w K width (supported_polyMul hg (supported_polyMul hf hf)) hg) hd)
  have hr : quaternionHaar (N width+N width)
      (polyMul (edgeDensity w K width g)
        (polyMul (liftBoundary (N width) f) (liftBoundary (N width) f))) ≈ d := by
    rw [← lift_product]
    exact Q'.eqv_trans _ _ _ (upper_pairing w K width g (polyMul f f)) hd
  have hc := edge_pairing w K width g f f
  have he := Q'.eqv_trans _ _ _
    (haar_expansion (N width+N width) (edgeDensity w K width g) f (liftBoundary (N width) f))
    (Q'.add_eqv_congr' hl (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hc)
      (Q'.add_eqv_congr' (Q'.neg_eqv_congr _ _ hc) hr)))
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ he (twice_difference d c))

/-- Positivity retains the whole original heat product and the supplied
message certificate on both actual endpoint carriers. -/
def edgeCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g) (G : Certificate (N width) g) :
    Certificate (N width+N width) (edgeDensity w K width g) :=
  let VG := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul G
  ((kineticCertificate hw0 hw1 K width hK).mul
    (certificate_extend (N width) (supported_polyMul (spatialWeight_supported w K width) hg) VG)).mul
    (lift_certificate (N width) VG)

theorem energy_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {g f : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (G : Certificate (N width) g) :
    (0 : Q') ≤ energy w K width g f := by
  have hn := ((edgeCertificate hw0 hw1 K width hK hg G).mul
    (Certificate.square (jump width f) (jump_supported width hf))).haar_nonnegative
  have hi := energy_identity w K width hg hf
  have htwo : (2 : Q')*(0 : Q') ≤ (2 : Q')*energy w K width g f :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _))
      (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (Q'.eqv_symm hi)))
  exact Q'.le_of_mul_le_mul_left htwo (by decide)

end YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.edgeDensity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.jump
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.edgeDensity_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.jump_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.edge_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.edge_diagonal_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.energy_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.edgeCertificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm.energy_nonnegative
