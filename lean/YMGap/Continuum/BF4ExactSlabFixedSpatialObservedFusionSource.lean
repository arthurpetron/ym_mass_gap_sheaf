/-
# Fusion with a signed observed-window source retained

An earlier observed window is generally a signed message f, not the
unobserved terminal g. The relative certificates a*g plus or minus f
multiply the signed fusion edge without assuming independence or positivity
of f. All other spatial factors and the original kinetic map are retained.
The exact fusion identity centers against T f, NOT against T g. Therefore
its connected consumer must retain the additional c_1*D(T f,T g) term.
No signed bulk estimate or temporal decay is proved here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFusionBoundary
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder (kineticCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket (initialWindowBracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceRemainder
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (supported_smul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step partialHaarHeads_congr)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration (partialHaarHeads_certificate)
open YMGap.Continuum.SU2QuaternionHeatFusionResidual
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight activeBlocks terminalMessage observedMessage

/-- The full retained action times a possibly signed observed source. -/
def retainedMessage (w : Q') (K width : Nat) (face : Z4Plaq) (f probe : RatPoly) : RatPoly :=
  productMap (N width) w K (activeBlocks width)
    (polyMul (polyMul (remainingSpatialWeight w K width face) f) probe)

theorem retainedMessage_supported (w : Q') (K width : Nat) (face : Z4Plaq)
    {f p : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hp : SupportedQuaternionBlocks (N width) p) :
    SupportedQuaternionBlocks (N width) (retainedMessage w K width face f p) :=
  productMap_supported _ w K _ (activeBlocks_lt width)
    (supported_polyMul (supported_polyMul (remainingSpatialWeight_supported w K width face) hf) hp)

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private def halve {blocks : Nat} {p q : RatPoly}
    (h : RatPolyCoeffEqv (polyAdd p p) q) (Q : Certificate blocks q) : Certificate blocks p := by
  have he : RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p :=
    (RatPolyCoeffEqv.smul_add _ _ _).trans ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide) p).trans (RatPolyCoeffEqv.one_smul p)))
  exact .ofCoeff he.symm (.smul HalfPow.half HalfPow.half_nonneg (.ofCoeff h Q))

-- The two-cell identity uses shared variables, with no sign assumed of p or q.
private def signed_product {blocks : Nat} {A B p q : RatPoly}
    (P : Certificate blocks (polyAdd A p)) (Q : Certificate blocks (polyAdd A (polyNeg p)))
    (R : Certificate blocks (polyAdd B q)) (S : Certificate blocks (polyAdd B (polyNeg q))) :
    Certificate blocks (polyAdd (polyMul A B) (polyMul p q)) ×
      Certificate blocks (polyAdd (polyMul A B) (polyNeg (polyMul p q))) := by
  let env : Nat → RatPoly := fun | 0 => A | 1 => B | 2 => p | _ => q
  let pos : PolyExpr := .add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))
  let neg : PolyExpr := .add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))
  exact ⟨halve (coeffEvalExpr_eqv_of_normalize_eq (.add pos pos)
    (.add (.mul (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (.mul (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3)))))
    (by decide) env) (P.mul R |>.add (Q.mul S)),
    halve (coeffEvalExpr_eqv_of_normalize_eq (.add neg neg)
    (.add (.mul (.add (.var 0) (.var 2)) (.add (.var 1) (.neg (.var 3))))
      (.mul (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.var 3))))
    (by decide) env) (P.mul S |>.add (Q.mul R))⟩

private def kinetic_certificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) p) (P : Certificate (N width) p) :
    Certificate (N width) (productMap (N width) w K (activeBlocks width) p) := by
  change Certificate (N width) (kernelMap (N width) (polynomialProduct _ (activeBlocks width)) p)
  rw [← kineticWeight_eq_indexedProduct]
  exact partialHaarHeads_certificate (N width) (N width)
    ((kineticCertificate hw0 hw1 K width hK).mul (certificate_extend (N width) hp P))

private theorem product_neg (R f : RatPoly) :
    RatPolyCoeffEqv (polyMul R (polyNeg f)) (polyNeg (polyMul R f)) :=
  coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.neg (.var 1)))
    (.neg (.mul (.var 0) (.var 1))) (by decide) (fun i => if i = 0 then R else f)

private theorem map_neg (w : Q') (K width : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (productMap (N width) w K (activeBlocks width) (polyNeg p))
      (polyNeg (productMap (N width) w K (activeBlocks width) p)) :=
  (productMap_congr _ w K _ (smul_neg p).symm).trans
    ((kernelMap_smul _ _ (-1) p).trans (smul_neg _))

private theorem weighted_cap (g : RatPoly) (a d : Q') :
    RatPolyCoeffEqv (polyMul (polySmul a g) (cap d)) (polySmul (a*d) g) :=
  (RatPolyCoeffEqv.polyMul_smul_left a g _).trans
    ((((RatPolyCoeffEqv.mul_comm g (cap d)).trans (cap_mul_left d g)).smul a).trans
      (RatPolyCoeffEqv.smul_assoc a d g))

/-- Two concrete comparison certificates for a signed retained source.
The reference remains the erased message of the ORIGINAL terminal g_n. -/
def retainedMessage_comparison {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    {f e : RatPoly} {a d : Q'} (hf : SupportedQuaternionBlocks (N width) f)
    (P : Certificate (N width) (polyAdd (polySmul a (terminalMessage w K width n)) f))
    (Q : Certificate (N width) (polyAdd (polySmul a (terminalMessage w K width n)) (polyNeg f)))
    (I : Interval (N width) e d) :
    Certificate (N width) (polyAdd (polySmul (a*d) (erasedMessage w K width n face))
      (retainedMessage w K width face f e)) ×
    Certificate (N width) (polyAdd (polySmul (a*d) (erasedMessage w K width n face))
      (polyNeg (retainedMessage w K width face f e))) := by
  let g := terminalMessage w K width n
  let R := remainingSpatialWeight w K width face
  let s := polyMul R g
  let t := polyMul (polyMul R f) e
  have hs := supported_polyMul (remainingSpatialWeight_supported w K width face)
    (terminalMessage_supported w K width n)
  have ht := supported_polyMul (supported_polyMul (remainingSpatialWeight_supported w K width face) hf) I.support
  let C := signed_product P Q I.lower I.upper
  have hc : RatPolyCoeffEqv (polyMul R (polyMul (polySmul a g) (cap d))) (polySmul (a*d) s) :=
    ((weighted_cap g a d).mul_left R).trans (RatPolyCoeffEqv.polyMul_smul_right (a*d) R g)
  have he : RatPolyCoeffEqv (polyMul R (polyMul f e)) t := (RatPolyCoeffEqv.mul_assoc R f e).symm
  have hp : Certificate (N width) (polyAdd (polySmul (a*d) s) t) :=
    .ofCoeff ((RatPolyCoeffEqv.mul_add_right _ _ _).trans (hc.add he)).symm
      ((remainingSpatialWeight_certificate hw0 hw1 K width hK face).mul C.1)
  have hq : Certificate (N width) (polyAdd (polySmul (a*d) s) (polyNeg t)) :=
    .ofCoeff ((RatPolyCoeffEqv.mul_add_right _ _ _).trans
      (hc.add ((product_neg R _).trans (RatPolyCoeffEqv.neg he)))).symm
      ((remainingSpatialWeight_certificate hw0 hw1 K width hK face).mul C.2)
  have ep := (productMap_add (N width) w K (activeBlocks width) (polySmul (a*d) s) t).trans
    ((kernelMap_smul _ _ (a*d) s).add (.refl _))
  have eq := (productMap_add (N width) w K (activeBlocks width) (polySmul (a*d) s) (polyNeg t)).trans
    ((kernelMap_smul _ _ (a*d) s).add (map_neg w K width t))
  exact ⟨.ofCoeff ep.symm (kinetic_certificate hw0 hw1 K width hK
      (supported_add (supported_smul hs (a*d)) ht) hp),
    .ofCoeff eq.symm (kinetic_certificate hw0 hw1 K width hK
      (supported_add (supported_smul hs (a*d)) (support_neg ht)) hq)⟩

/-- The signed-source comparisons are supplied by the actual earlier window,
not added as an unsolved hypothesis about its transmitted message. -/
def observedMessage_comparison {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L : Nat)
    {p : RatPoly} {a : Q'} (I : Interval ((L+1)*(N width)) p a) :
    Certificate (N width) (polyAdd (polySmul a (terminalMessage w K width (m+L)))
      (observedMessage w K width m L p)) ×
    Certificate (N width) (polyAdd (polySmul a (terminalMessage w K width (m+L)))
      (polyNeg (observedMessage w K width m L p))) := by
  let B := initialWindowBracket hw0 hw1 K width hK m L I
  have hl := B.lowerCertificate
  have hu := B.upperCertificate
  exact ⟨.ofCoeff ((RatPolyCoeffEqv.add_comm _ _).trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_coefficient
        (Q'.eqv_symm (Q'.neg_neg_eqv a)) _))) hl,
    .ofCoeff ((RatPolyCoeffEqv.refl _).add (smul_neg _).symm) hu⟩

private theorem probe_pin (w : Q') (K width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (f p : RatPoly) :
    RatPolyCoeffEqv (transferStep w K width (polyMul f p))
      (retainedMessage w K width face f (polyMul (heatPrefix w K (plaquette width face).scalar) p)) := by
  have ht : transferStep w K width (polyMul f p) =
      productMap (N width) w K (activeBlocks width) (polyMul (spatialWeight w K width) (polyMul f p)) := by
    unfold transferStep step productMap kernelMap
    rw [kineticWeight_eq_indexedProduct]
    rfl
  rw [ht]
  exact productMap_congr _ w K _ (((spatialWeight_split w K width face hf).mul_right _).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) (by decide)
      (fun | 0 => heatPrefix w K (plaquette width face).scalar
           | 1 => remainingSpatialWeight w K width face | 2 => f | _ => p)))

private theorem retained_add (w : Q') (K width : Nat) (face : Z4Plaq) (f p q : RatPoly) :
    RatPolyCoeffEqv (retainedMessage w K width face f (polyAdd p q))
      (polyAdd (retainedMessage w K width face f p) (retainedMessage w K width face f q)) :=
  (productMap_congr _ w K _ (RatPolyCoeffEqv.mul_add_right _ p q)).trans (productMap_add _ w K _ _ _)

private theorem retained_smul (w : Q') (K width : Nat) (face : Z4Plaq) (f : RatPoly) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (retainedMessage w K width face f (polySmul c p))
      (polySmul c (retainedMessage w K width face f p)) :=
  (productMap_congr _ w K _ (RatPolyCoeffEqv.polyMul_smul_right c _ p)).trans (kernelMap_smul _ _ c _)

/-- Fusion for an arbitrary signed source. Crucially, the subtractive
message is T f; it is not the unobserved reference T g. -/
theorem signedSource_fusion (w : Q') (K width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (f : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (transferStep w K width (polyMul f (characterPolynomial (plaquette width face).scalar 1)))
        (polySmul (-coeffW w 1) (transferStep w K width f)))
      (polyAdd (retainedMessage w K width face f (bulkResidual w K (plaquette width face).scalar))
        (retainedMessage w K width face f (boundaryResidual w K (plaquette width face).scalar))) := by
  let H := heatPrefix w K (plaquette width face).scalar
  let chi := characterPolynomial (plaquette width face).scalar 1
  let c := coeffW w 1
  have hi : RatPolyCoeffEqv (transferStep w K width f) (retainedMessage w K width face f H) :=
    (partialHaarHeads_congr (N width)
      (((RatPolyCoeffEqv.mul_one f).symm.mul_left (spatialWeight w K width)).mul_left
        (kineticWeight w K width))).trans
      ((probe_pin w K width face hf f polyOne).trans
        (productMap_congr _ w K _ ((RatPolyCoeffEqv.mul_one H).mul_left _)))
  have hc : RatPolyCoeffEqv (polySmul (-c) H) (polyNeg (polyMul (cap c) H)) :=
    ((RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 c)
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv c)))) H).trans
      (RatPolyCoeffEqv.smul_assoc (-1) c H).symm).trans
      ((smul_neg _).trans (RatPolyCoeffEqv.neg (cap_mul_left c H).symm))
  have he : RatPolyCoeffEqv (polyAdd (polyMul H chi) (polySmul (-c) H))
      (polyAdd (bulkResidual w K (plaquette width face).scalar)
        (boundaryResidual w K (plaquette width face).scalar)) := by
    have hcenter := coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 0))))
      (.mul (.add (.var 1) (.neg (.var 2))) (.var 0)) (by decide)
      (fun | 0 => H | 1 => chi | _ => cap c)
    exact ((RatPolyCoeffEqv.refl _).add hc).trans (hcenter.trans (heat_fusion_residual w K _))
  exact ((probe_pin w K width face hf f chi).add (hi.smul (-c))).trans
    (((RatPolyCoeffEqv.refl _).add (retained_smul w K width face f (-c) H).symm).trans
      ((retained_add w K width face f _ _).symm.trans
        ((productMap_congr _ w K _ (he.mul_left _)).trans (retained_add w K width face f _ _))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource.retainedMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource.retainedMessage_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource.retainedMessage_comparison
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource.observedMessage_comparison
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialObservedFusionSource.signedSource_fusion
