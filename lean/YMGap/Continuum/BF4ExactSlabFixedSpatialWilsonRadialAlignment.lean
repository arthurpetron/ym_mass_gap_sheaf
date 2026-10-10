/-
# Original Wilson radial alignment and sharp reweighted fourth moments

Every weight, source, unit, support, active-link and cutoff guard is produced
on the original slab. The bound is E <= 6(1-w)L^2 H[W(4-f^2)] + 3L^4 B,
where B is the already proved original one-link fourth budget times oddMass.
The radial mass is a raw trace deficit, not the interacting centered variance.
No survival, moving-family, physical scaling or Clay conclusion follows here.
-/

import YMGap.Continuum.SU2QuaternionProductHeatRadialAlignment
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialAlignment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialIncrement
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionHeatQuarticBound (quarticBudget)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarChordalDifference (norm_difference_conj)
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.QuaternionHaarWordQuadratic
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarFamilySquare
open YMGap.Continuum.QuaternionHaarWordComponents (component component_difference)
open YMGap.Continuum.SU2QuaternionProductHeatRadialAlignment

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage oddMass edgeDensity energy

private def imagSquare (p : PolyQuaternion) : RatPoly :=
  polyAdd (square p.iPart) (polyAdd (square p.jPart) (square p.kPart))

private def radial (p : PolyQuaternion) : RatPoly := polySmul 4 (imagSquare p)

private def rawRadial (p : PolyQuaternion) : RatPoly :=
  polyAdd (cap 4) (polyNeg (square (characterPolynomial p.scalar 1)))

private def radial_certificate {n : Nat} {p : PolyQuaternion} (hp : Supported n p) :
    Certificate n (radial p) :=
  ((Certificate.square p.iPart hp.iPart).add
    ((Certificate.square p.jPart hp.jPart).add (Certificate.square p.kPart hp.kPart))).smul 4 (by decide)

private theorem radial_pin {n : Nat} {p : PolyQuaternion}
    (hu : HaarCarrierEqv n (polyQuaternionNorm p) polyOne) :
    HaarCarrierEqv n (rawRadial p) (radial p) := by
  have hf : RatPolyCoeffEqv (square (characterPolynomial p.scalar 1))
      (polySmul 4 (square p.scalar)) := by
    have h := coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.const 4) (.mul (.var 0) (.var 0))) (by decide) (fun _ => p.scalar)
    exact (((cap_mul_left 2 p.scalar).mul (cap_mul_left 2 p.scalar)).symm.trans h).trans
      (cap_mul_left 4 (square p.scalar))
  have hr : RatPolyCoeffEqv
      (polyAdd (polySmul 4 (polyQuaternionNorm p)) (polyNeg (polySmul 4 (square p.scalar))))
      (radial p) := by
    exact (((cap_mul_left 4 (polyQuaternionNorm p)).symm.add
      (RatPolyCoeffEqv.neg (cap_mul_left 4 (square p.scalar)).symm)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.const 4) (.add (.mul (.var 0) (.var 0))
          (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))))
          (.neg (.mul (.const 4) (.mul (.var 0) (.var 0)))))
        (.mul (.const 4) (.add (.mul (.var 1) (.var 1))
          (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (by decide) (fun | 0 => p.scalar | 1 => p.iPart | 2 => p.jPart | _ => p.kPart))).trans
      (cap_mul_left 4 (imagSquare p))
  have hs : HaarCarrierEqv n (polySmul 4 (polyQuaternionNorm p)) (cap 4) :=
    ((RatPolyCoeffEqv.haarCarrier (cap_mul_left 4 (polyQuaternionNorm p))).symm.trans
      (hu.mul_left (cap 4))).trans
      (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_one (cap 4)))
  have hp := HaarCarrierEqv.add hs (HaarCarrierEqv.refl n (polyNeg (polySmul 4 (square p.scalar))))
  exact (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hf))).trans
    (hp.symm.trans (RatPolyCoeffEqv.haarCarrier hr))

private theorem component_supported {n : Nat} {p : PolyQuaternion} (hp : Supported n p) (j : Nat) :
    SupportedQuaternionBlocks n (component j p) := by
  match j with
  | 0 => exact hp.scalar | 1 => exact hp.iPart | 2 => exact hp.jPart | _+3 => exact hp.kPart

private theorem source_supported (width : Nat) (loop : SourceLoop width) :
    Supported (N width) (sourceWord width loop.edges) :=
  let h := sourceWord_supported width loop.edges
  ⟨h.scalar, h.iPart, h.jPart, h.kPart⟩

private theorem upper_word_lift (width : Nat) (loop : SourceLoop width) :
    PaddedQuaternionCoeffEqv (N width+N width)
      (liftQuaternion (N width) (sourceWord width loop.edges))
      (wordWith (upperOriented width) loop.edges) := by
  exact wordWith_lift (N width+N width) (N width)
    (orientedLink width) (upperOriented width) loop.edges (by
      intro e he
      unfold orientedLink link upperOriented
      rw [if_pos (loop.physical e he)]
      split
      · rw [liftQuaternion_conj, liftQuaternion_coordinateVariable]
        exact .refl _ _
      · rw [liftQuaternion_coordinateVariable]
        exact .refl _ _)

private theorem upper_component_lift (width : Nat) (loop : SourceLoop width) (j : Nat) :
    PaddedPolynomialCoeffEqv (N width+N width)
      (liftBoundary (N width) (component j (sourceWord width loop.edges)))
      (component j (wordWith (upperOriented width) loop.edges)) := by
  have h := upper_word_lift width loop
  match j with
  | 0 => exact h.scalar | 1 => exact h.iPart | 2 => exact h.jPart | _+3 => exact h.kPart

private def linkChordal (width : Nat) (e : OrientedBF4Link) : RatPoly :=
  polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e))

private theorem link_chordal_pin {width : Nat} {e : OrientedBF4Link}
    (he : e.link ∈ baseLinks width) :
    RatPolyCoeffEqv (linkChordal width e) (chordal (N width) ((baseLinks width).idxOf e.link)) := by
  unfold linkChordal orientedLink link upperOriented
  rw [if_pos he]
  split
  · exact norm_difference_conj _ _
  · exact RatPolyCoeffEqv.refl _

private theorem edgeWeight_pin (w : Q') (K width depth : Nat) :
    edgeWeight (N width) w (K+1) (activeBlocks width)
        (polyMul (spatialWeight w (K+1) width) (terminalMessage w (K+1) width depth)) =
      edgeDensity w (K+1) width (terminalMessage w (K+1) width depth) := by
  unfold edgeWeight edgeDensity productHeat
  rw [kineticWeight_eq_indexedProduct]

private theorem original_endpoint_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width depth : Nat) (hK : sufficientCutoff w ≤ K+1) (hhead : headCutoff w ≤ K+1)
    (loop : SourceLoop width) (e : OrientedBF4Link) (he : e ∈ loop.edges)
    (hactive : (baseLinks width).idxOf e.link ∈ activeBlocks width) (j : Nat) :
    let W := edgeDensity w (K+1) width (terminalMessage w (K+1) width depth)
    let p := sourceWord width loop.edges
    let q := wordWith (upperOriented width) loop.edges
    2*moment (N width+N width) W (polyMul (linkChordal width e) (square (component j p))) ≤
      (2*(6*(1-w)))*moment (N width+N width) W (square (component j p)) +
        moment (N width+N width) W
          (polyMul (linkChordal width e) (square (component j (difference p q)))) := by
  let W := edgeDensity w (K+1) width (terminalMessage w (K+1) width depth)
  let p := sourceWord width loop.edges
  let q := wordWith (upperOriented width) loop.edges
  let D := linkChordal width e
  let d := chordal (N width) ((baseLinks width).idxOf e.link)
  let u := component j p
  have hu := component_supported (source_supported width loop) j
  have hp := word_supported (orientedLink width) loop.edges
    (fun f hf => lower_supported (loop.physical f hf))
  have hq := word_supported (upperOriented width) loop.edges
    (fun f hf => upper_supported (loop.physical f hf))
  have hw := edgeDensity_supported w (K+1) width (terminalMessage_supported w (K+1) width depth)
  have hD := support_norm (difference_supported (lower_supported (loop.physical e he))
    (upper_supported (loop.physical e he)))
  have hd : SupportedQuaternionBlocks (N width+N width) d :=
    support_norm (difference_supported
      (Supported.coordinate (by have := List.idxOf_lt_length_of_mem (loop.physical e he); omega))
      (Supported.coordinate (by have := List.idxOf_lt_length_of_mem (loop.physical e he); omega)))
  have h := product_endpoint_square_bound (N width) (Q'.le_of_lt hw0) hw1 K hK
    (activeBlocks width) (activeBlocks_lt width) _ hactive
    (supported_polyMul (spatialWeight_supported w (K+1) width)
      (terminalMessage_supported w (K+1) width depth)) hu
    (by
      rw [edgeWeight_pin]
      exact edgeCertificate hw0 hw1 (K+1) width hhead
        (terminalMessage_supported w (K+1) width depth)
        (terminalMessage_certificate hw0 hw1 (K+1) width hhead depth))
  rw [edgeWeight_pin] at h
  have hdp := link_chordal_pin (loop.physical e he)
  have hl := haar_of_coeff (blocks := N width+N width) ((hdp.mul_right (square u)).mul_left W)
  have hdelta : PaddedPolynomialCoeffEqv (N width+N width)
      (polyAdd u (polyNeg (liftBoundary (N width) u))) (component j (difference p q)) := by
    rw [component_difference]
    exact (PaddedPolynomialCoeffEqv.refl _ _).add (padded_neg (upper_component_lift width loop j))
  have hreplace : PaddedPolynomialCoeffEqv (N width+N width)
      (polyMul d (square (polyAdd u (polyNeg (liftBoundary (N width) u)))))
      (polyMul D (square (component j (difference p q)))) :=
    (PaddedPolynomialCoeffEqv.of_coeff hdp.symm).mul (hdelta.mul hdelta)
  have hr := hreplace.haar_insert
    (supported_polyMul hd (supported_polyMul
      (supported_add (support_lower hu) (support_neg (lift_supported hu (N width))))
      (supported_add (support_lower hu) (support_neg (lift_supported hu (N width))))))
    (supported_polyMul hD (supported_polyMul
      (component_supported (difference_supported hp hq) j)
      (component_supported (difference_supported hp hq) j))) W hw
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left 2 _ _ hl))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ hr)))

private theorem imag_moment_pin (n : Nat) (W : RatPoly) (p : PolyQuaternion) :
    moment n W (imagSquare p) ≈ moment n W (square p.iPart)+
      (moment n W (square p.jPart)+moment n W (square p.kPart)) :=
  Q'.eqv_trans _ _ _ (haar_weighted_add n W _ _)
    (Q'.add_eqv_congr_left _ _ _ (haar_weighted_add n W _ _))

private theorem radial_moment_pin (n : Nat) (W : RatPoly) (p : PolyQuaternion) :
    moment n W (radial p) ≈ 4*(moment n W (square p.iPart)+
      (moment n W (square p.jPart)+moment n W (square p.kPart))) :=
  Q'.eqv_trans _ _ _ (weighted_scale n W _ 4)
    (Q'.mul_eqv_congr_left 4 _ _ (imag_moment_pin n W p))

private theorem moment_reweight (n : Nat) (W D p : RatPoly) :
    moment n (polyMul W D) p ≈ moment n W (polyMul D p) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_assoc W D p)

/-- SAME raw trace radial mass. Its normalization is 4 minus the raw second
moment, rather than the OWN centered variance. -/
def radialMass (w : Q') (K width depth : Nat) (loop : SourceLoop width) : Q' :=
  moment (N width+N width) (edgeDensity w K width (terminalMessage w K width depth))
    (rawRadial (sourceWord width loop.edges))

private theorem original_link_radial_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width depth : Nat) (hK : sufficientCutoff w ≤ K+1) (hhead : headCutoff w ≤ K+1)
    (loop : SourceLoop width) (e : OrientedBF4Link) (he : e ∈ loop.edges)
    (hactive : (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    let W := edgeDensity w (K+1) width (terminalMessage w (K+1) width depth)
    let p := sourceWord width loop.edges
    moment (N width+N width) W (polyMul (linkChordal width e) (radial p)) ≤
      (6*(1-w))*moment (N width+N width) W (radial p) +
        2*moment (N width+N width) W (polyMul (linkChordal width e) (wordChordal width loop)) := by
  let n := N width+N width
  let W := edgeDensity w (K+1) width (terminalMessage w (K+1) width depth)
  let D := linkChordal width e
  let p := sourceWord width loop.edges
  let q := wordWith (upperOriented width) loop.edges
  let z := difference p q
  let c := 6*(1-w)
  let a (j : Nat) := moment n W (polyMul D (square (component j p)))
  let b (j : Nat) := moment n W (square (component j p))
  let d (j : Nat) := moment n W (polyMul D (square (component j z)))
  have hs := Q'.add_le_add
    (original_endpoint_bound hw0 hw1 K width depth hK hhead loop e he hactive 1)
    (Q'.add_le_add (original_endpoint_bound hw0 hw1 K width depth hK hhead loop e he hactive 2)
      (original_endpoint_bound hw0 hw1 K width depth hK hhead loop e he hactive 3))
  have hl : 2*(a 1+(a 2+a 3)) ≈ 2*a 1+(2*a 2+2*a 3) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.var 0) (.add (.var 1) (.var 2))))
      (.add (.mul (.const 2) (.var 0)) (.add (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 2))))
      (by decide) (fun | 0 => a 1 | 1 => a 2 | _ => a 3)
  have hr : (2*c)*b 1+d 1+((2*c)*b 2+d 2+((2*c)*b 3+d 3)) ≈
      2*c*(b 1+(b 2+b 3))+(d 1+(d 2+d 3)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 4))
        (.add (.add (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.var 5))
          (.add (.mul (.mul (.const 2) (.var 0)) (.var 3)) (.var 6))))
      (.add (.mul (.mul (.const 2) (.var 0)) (.add (.var 1) (.add (.var 2) (.var 3))))
        (.add (.var 4) (.add (.var 5) (.var 6)))) (by decide)
      (fun | 0 => c | 1 => b 1 | 2 => b 2 | 3 => b 3 | 4 => d 1 | 5 => d 2 | _ => d 3)
  have hsum := Q'.mul_le_mul_of_nonneg_left _ _ 2
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hl) (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))) (by decide)
  have hp := word_supported (orientedLink width) loop.edges (fun f hf => lower_supported (loop.physical f hf))
  have hq := word_supported (upperOriented width) loop.edges (fun f hf => upper_supported (loop.physical f hf))
  have hz := difference_supported hp hq
  have R := edgeCertificate hw0 hw1 (K+1) width hhead (terminalMessage_supported w (K+1) width depth)
    (terminalMessage_certificate hw0 hw1 (K+1) width hhead depth)
  have RD := R.mul (normCertificate (difference_supported
    (lower_supported (loop.physical e he)) (upper_supported (loop.physical e he))))
  have C : Certificate n (polyAdd (polyQuaternionNorm z) (polyNeg (imagSquare z))) :=
    Certificate.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3)))))
        (.neg (.add (.mul (.var 1) (.var 1)) (.add (.mul (.var 2) (.var 2)) (.mul (.var 3) (.var 3))))))
      (.mul (.var 0) (.var 0)) (by decide)
      (fun | 0 => z.scalar | 1 => z.iPart | 2 => z.jPart | _ => z.kPart))
      (Certificate.square z.scalar hz.scalar)
  have hleft : moment n W (polyMul D (radial p)) ≈ 2*(2*(a 1+(a 2+a 3))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (moment_reweight n W D (radial p)))
      (Q'.eqv_trans _ _ _ (radial_moment_pin n (polyMul W D) p)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _
          (Q'.add_eqv_congr' (moment_reweight n W D (square p.iPart))
            (Q'.add_eqv_congr' (moment_reweight n W D (square p.jPart))
              (moment_reweight n W D (square p.kPart)))))
        (poly_identity_of_normal_eq (.mul (.const 4) (.var 0))
          (.mul (.const 2) (.mul (.const 2) (.var 0))) (by decide)
          (fun _ => a 1+(a 2+a 3)))))
  have hright : 2*(2*c*(b 1+(b 2+b 3))+(d 1+(d 2+d 3))) ≈
      c*(4*(b 1+(b 2+b 3)))+2*(d 1+(d 2+d 3)) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2)))
      (.add (.mul (.var 0) (.mul (.const 4) (.var 1))) (.mul (.const 2) (.var 2)))
      (by decide) (fun | 0 => c | 1 => b 1+(b 2+b 3) | _ => d 1+(d 2+d 3))
  have hdpin : d 1+(d 2+d 3) ≈ moment n (polyMul W D) (imagSquare z) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_symm (moment_reweight n W D (square z.iPart)))
        (Q'.add_eqv_congr' (Q'.eqv_symm (moment_reweight n W D (square z.jPart)))
          (Q'.eqv_symm (moment_reweight n W D (square z.kPart)))))
      (Q'.eqv_symm (imag_moment_pin n (polyMul W D) z))
  have hdfull := Q'.le_trans' _ _ _ (Q'.le_of_eqv hdpin)
    (Q'.le_trans' _ _ _ (weighted_order RD C) (Q'.le_of_eqv (moment_reweight n W D (polyQuaternionNorm z))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
        (Q'.add_le_add
          (Q'.le_of_eqv (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm (radial_moment_pin n W p))))
          (Q'.mul_le_mul_of_nonneg_left _ _ 2 hdfull (by decide)))))

/-- Literal occurrence-count squared, with repeats and the empty word kept. -/
def pathSquared {width : Nat} (loop : SourceLoop width) : Q' :=
  Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length

/-- The original one-link fourth budget, retaining its SAME odd partition. -/
def fourthBudget (w : Q') (S K width depth : Nat) : Q' :=
  quarticBudget w S * oddMass w K width depth

/-- The mixed radial and word-fourth estimates are both produced on the
actual original density. Reweighted vector Cauchy gives L^4, not 16 L^4. -/
theorem original_radial_moment_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S K width depth : Nat) (hS : 1 ≤ S) (hquartic : S+3 ≤ K+1)
    (hhead : headCutoff w ≤ K+1) (halign : sufficientCutoff w ≤ K+1)
    (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide)) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    mixedRadialMoment w (K+1) width depth loop ≤
        (6*(1-w))*pathSquared loop*radialMass w (K+1) width depth loop +
          2*(pathSquared loop*pathSquared loop)*fourthBudget w S (K+1) width depth ∧
      moment (N width+N width)
          (edgeDensity w (K+1) width (terminalMessage w (K+1) width depth))
          (square (wordChordal width loop)) ≤
        (pathSquared loop*pathSquared loop)*fourthBudget w S (K+1) width depth := by
  let n := N width+N width
  let W := edgeDensity w (K+1) width (terminalMessage w (K+1) width depth)
  let p := sourceWord width loop.edges
  let q := wordWith (upperOriented width) loop.edges
  let r := wordChordal width loop
  let A := radial p
  let c := 6*(1-w)
  let P := pathSquared loop
  let B := fourthBudget w S (K+1) width depth
  have hp := word_supported (orientedLink width) loop.edges
    (fun e he => lower_supported (loop.physical e he))
  have hqword := word_supported (upperOriented width) loop.edges
    (fun e he => upper_supported (loop.physical e he))
  have hpu := word_unit (orientedLink width) loop.edges
    (fun e he => lower_unit (loop.physical e he))
  have R := edgeCertificate hw0 hw1 (K+1) width hhead
    (terminalMessage_supported w (K+1) width depth)
    (terminalMessage_certificate hw0 hw1 (K+1) width hhead depth)
  have hD (e : OrientedBF4Link) (he : e ∈ loop.edges) :
      Supported n (difference (orientedLink width e) (upperOriented width e)) :=
    difference_supported (lower_supported (loop.physical e he)) (upper_supported (loop.physical e he))
  have hfourth (e : OrientedBF4Link) (he : e ∈ loop.edges) :
      moment n W (square (linkChordal width e)) ≤ B :=
    selected_quartic_bound hw0 hw1 S (K+1) width depth hS hquartic hhead hhalf hq e
      (loop.physical e he) (hactive e he)
  have hpair (e f : OrientedBF4Link) (he : e ∈ loop.edges) (hf : f ∈ loop.edges) :
      moment n W (polyMul (linkChordal width e) (linkChordal width f)) ≤ B :=
    mixed_square_bound R (support_norm (hD e he)) (support_norm (hD f hf)) B
      (hfourth e he) (hfourth f hf)
  have hDword (e : OrientedBF4Link) (he : e ∈ loop.edges) :
      moment n W (polyMul (linkChordal width e) r) ≤ P*B := by
    have h := word_norm_quadratic_bound (R.mul (normCertificate (hD e he)))
      (orientedLink width) (upperOriented width) loop.edges
      (fun f hf => lower_supported (loop.physical f hf))
      (fun f hf => upper_supported (loop.physical f hf))
      (fun f hf => lower_unit (loop.physical f hf))
      (fun f hf => upper_unit (loop.physical f hf)) B (by
        intro f hf
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (moment_reweight n W (linkChordal width e) (linkChordal width f))) (hpair e f he hf))
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (moment_reweight n W (linkChordal width e) r)) h
  have hfourthWord : moment n W (square r) ≤ (P*P)*B := by
    have h := word_norm_quadratic_bound (R.mul (normCertificate (difference_supported hp hqword)))
      (orientedLink width) (upperOriented width) loop.edges
      (fun e he => lower_supported (loop.physical e he))
      (fun e he => upper_supported (loop.physical e he))
      (fun e he => lower_unit (loop.physical e he))
      (fun e he => upper_unit (loop.physical e he)) (P*B) (by
        intro e he
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _ (moment_reweight n W r (linkChordal width e))
            (haar_of_coeff ((RatPolyCoeffEqv.mul_comm r (linkChordal width e)).mul_left W))))
          (hDword e he))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (moment_reweight n W r r))
      (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (Q'.mul_assoc_eqv P P B)))
  have hmixed : moment n W (polyMul A r) ≤
      P*(c*moment n W A+2*(P*B)) := by
    have h := word_norm_quadratic_bound (R.mul (radial_certificate hp))
      (orientedLink width) (upperOriented width) loop.edges
      (fun e he => lower_supported (loop.physical e he))
      (fun e he => upper_supported (loop.physical e he))
      (fun e he => lower_unit (loop.physical e he))
      (fun e he => upper_unit (loop.physical e he)) (c*moment n W A+2*(P*B)) (by
        intro e he
        have hlink := original_link_radial_bound hw0 hw1 K width depth halign hhead
          loop e he (hactive e he)
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _ (moment_reweight n W A (linkChordal width e))
            (haar_of_coeff ((RatPolyCoeffEqv.mul_comm A (linkChordal width e)).mul_left W))))
          (Q'.le_trans' _ _ _ hlink
            (Q'.add_le_add_left _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 (hDword e he) (by decide)))))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (moment_reweight n W A r)) h
  have hmass : radialMass w (K+1) width depth loop ≈ moment n W A :=
    haar_of_carrier ((radial_pin hpu).mul_left W)
  have hraw : mixedRadialMoment w (K+1) width depth loop ≈ moment n W (polyMul A r) :=
    Q'.eqv_trans _ _ _
      (haar_of_carrier (((radial_pin hpu).mul_left r).mul_left W))
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm r A).mul_left W))
  have hright : P*(c*moment n W A+2*(P*B)) ≈
      c*P*radialMass w (K+1) width depth loop+2*(P*P)*B :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left P _ _ (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left c _ _ (Q'.eqv_symm hmass))))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.const 2) (.mul (.var 0) (.var 3)))))
        (.add (.mul (.mul (.var 1) (.var 0)) (.var 2))
          (.mul (.mul (.const 2) (.mul (.var 0) (.var 0))) (.var 3))) (by decide)
        (fun | 0 => P | 1 => c | 2 => radialMass w (K+1) width depth loop | _ => B))
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hraw)
    (Q'.le_trans' _ _ _ hmixed (Q'.le_of_eqv hright)), hfourthWord⟩

/-- Original energy payment by the raw radial deficit and actual quartic
budget. Every finite onset guard is explicit; no variance premise is added. -/
theorem wilson_energy_radial_alignment_cleared {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S K width depth : Nat) (hS : 1 ≤ S) (hquartic : S+3 ≤ K+1)
    (hhead : headCutoff w ≤ K+1) (halign : sufficientCutoff w ≤ K+1)
    (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide)) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    energy w (K+1) width (terminalMessage w (K+1) width depth)
        (sourceCharacter width loop.edges 1) ≤
      (6*(1-w))*pathSquared loop*radialMass w (K+1) width depth loop +
        3*(pathSquared loop*pathSquared loop)*fourthBudget w S (K+1) width depth := by
  have h := original_radial_moment_bounds hw0 hw1 S K width depth hS hquartic hhead halign
    hhalf hq loop hactive
  have henergy := Q'.le_trans' _ _ _
    (wilson_energy_radial_cleared hw0 hw1 (K+1) width hhead depth loop)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (radial_moment_split w (K+1) width depth loop))
      (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ 2 h.1 (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ 2 h.2 (by decide))))
  have he :
      2*((6*(1-w))*pathSquared loop*radialMass w (K+1) width depth loop+
        2*(pathSquared loop*pathSquared loop)*fourthBudget w S (K+1) width depth)+
      2*((pathSquared loop*pathSquared loop)*fourthBudget w S (K+1) width depth) ≈
      2*((6*(1-w))*pathSquared loop*radialMass w (K+1) width depth loop+
        3*(pathSquared loop*pathSquared loop)*fourthBudget w S (K+1) width depth) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2))))
        (.mul (.const 2) (.mul (.var 1) (.var 2))))
      (.mul (.const 2) (.add (.var 0) (.mul (.mul (.const 3) (.var 1)) (.var 2)))) (by decide)
      (fun | 0 => (6*(1-w))*pathSquared loop*radialMass w (K+1) width depth loop
           | 1 => pathSquared loop*pathSquared loop
           | _ => fourthBudget w S (K+1) width depth)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ henergy (Q'.le_of_eqv he)) (by decide : (0 : Q') < 2)

#print axioms radialMass
#print axioms pathSquared
#print axioms fourthBudget
#print axioms original_radial_moment_bounds
#print axioms wilson_energy_radial_alignment_cleared

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRadialAlignment
