/-
# One output-block Casimir of an actual full cyclic path

Each literal character slot carries its own Casimir.  The product-character
kernel is first differentiated on its corresponding upper endpoint, then
the original source is inserted and the lower endpoints are integrated.
This is a per-block eigenpin; the full-Casimir sum alone does not imply it.
-/

import YMGap.Continuum.SU2QuaternionCyclicPathCasimir

namespace YMGap.Continuum.SU2QuaternionCyclicPathBlockCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionCharacterProductPositive
open YMGap.Continuum.SU2QuaternionCharacterProductCasimir
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionCharacterCasimirLocality
open YMGap.Continuum.SU2QuaternionCharacterEndpointSymmetry
open YMGap.Continuum.SU2QuaternionSelectedCharacterCasimir
open YMGap.Continuum.SU2QuaternionCasimirHeadIntegration
open YMGap.Continuum.SU2QuaternionCyclicCharacterPositive
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir
open YMGap.Continuum.QuaternionHaarAngularCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem tailProduct_independent (n origin : Nat) : ∀ (ds : List Nat)
    (start : Nat), origin < start → start + ds.length ≤ n →
    QuaternionBlockIndependent (n+origin)
      (characterProduct n (pathSlots start ds))
  | [], _, _, _ => quaternionBlockIndependent_polyOne _
  | d::ds, start, hlt, hbound => by
      simp only [List.length_cons] at hbound
      change QuaternionBlockIndependent (n+origin)
        (polyMul (normalizedCharacterAt start (n+start) d)
          (characterProduct n (pathSlots (start+1) ds)))
      apply quaternionBlockIndependent_polyMul
      · apply normalizedCharacterAt_independent
        · omega
        · omega
      · exact tailProduct_independent n origin ds (start+1) (by omega) (by omega)

private theorem casimir_value (d : Nat) :
    Q'.ofNat (d*(d+2)) ≈ Q'.ofNat d * (Q'.ofNat d + 2) :=
  Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv d (d+2))
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv d 2)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))))

/-- The upper endpoint of the `j`th actual character is an eigenblock even
in the full product; every other character is independent of that block. -/
theorem characterProduct_one_upperLaplacian (n start : Nat) :
    ∀ (ds : List Nat) (j : Nat), start + ds.length ≤ n → j < ds.length →
      HaarCarrierEqv (n+n)
        (blockAngularLaplacian (n+start+j)
          (characterProduct n (pathSlots start ds)))
        (polySmul (-(Q'.ofNat ((ds.getD j 0)*((ds.getD j 0)+2))))
          (characterProduct n (pathSlots start ds)))
  | [], _, _, hj => by contradiction
  | d::ds, 0, hbound, _ => by
      let f := normalizedCharacterAt start (n+start) d
      let r := characterProduct n (pathSlots (start+1) ds)
      have hs : start < n := by
        simp only [List.length_cons] at hbound
        omega
      have hrind : QuaternionBlockIndependent (n+start) r :=
        tailProduct_independent n start ds (start+1) (by omega) (by
          simp only [List.length_cons] at hbound
          omega)
      have hu : n+start < n+n := by omega
      have hne : start ≠ n+start := by omega
      have heigen := normalizedCharacterAt_blockAngularLaplacian_right
        (blocks := n+n) (by omega) ⟨start, by omega⟩
        ⟨n+start, hu⟩ hne d
      have heigen' : HaarCarrierEqv (n+n)
          (blockAngularLaplacian (n+start) f)
          (polySmul (-(Q'.ofNat (d*(d+2)))) f) :=
        heigen.trans (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.smul_coefficient
            (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (casimir_value d))) f))
      change HaarCarrierEqv (n+n)
        (blockAngularLaplacian (n+start) (polyMul f r))
        (polySmul (-(Q'.ofNat (d*(d+2)))) (polyMul f r))
      exact (RatPolyCoeffEqv.haarCarrier
        (blockAngularLaplacian_mul_independent (n+start) f r hrind)).trans
        ((HaarCarrierEqv.mul_right r heigen').trans
          (RatPolyCoeffEqv.haarCarrier
            (RatPolyCoeffEqv.polyMul_smul_left _ f r)))
  | d::ds, j+1, hbound, hj => by
      let f := normalizedCharacterAt start (n+start) d
      let r := characterProduct n (pathSlots (start+1) ds)
      let b := n + start + (j+1)
      have hfind : QuaternionBlockIndependent b f :=
        normalizedCharacterAt_independent (by omega) (by omega) d
      have htail : start+1+ds.length ≤ n := by
        simp only [List.length_cons] at hbound
        omega
      have hjtail : j < ds.length := by
        simp only [List.length_cons] at hj
        omega
      have hrec := characterProduct_one_upperLaplacian n (start+1) ds j htail hjtail
      have hb : b < n+n := by omega
      have hcomm : HaarCarrierEqv (n+n)
          (blockAngularLaplacian b (polyMul f r))
          (blockAngularLaplacian b (polyMul r f)) :=
        blockAngularLaplacian_carrier hb
          (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.mul_comm f r))
      have hpull : HaarCarrierEqv (n+n)
          (blockAngularLaplacian b (polyMul f r))
          (polyMul f (blockAngularLaplacian b r)) :=
        hcomm.trans ((RatPolyCoeffEqv.haarCarrier
          (blockAngularLaplacian_mul_independent b r f hfind)).trans
            (RatPolyCoeffEqv.haarCarrier
              (RatPolyCoeffEqv.mul_comm (blockAngularLaplacian b r) f)))
      change HaarCarrierEqv (n+n)
        (blockAngularLaplacian b (polyMul f r))
        (polySmul (-(Q'.ofNat ((ds.getD j 0)*((ds.getD j 0)+2))))
          (polyMul f r))
      have hrec' : HaarCarrierEqv (n+n)
          (blockAngularLaplacian b r)
          (polySmul (-(Q'.ofNat ((ds.getD j 0)*((ds.getD j 0)+2)))) r) := by
        simpa only [b, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec
      exact hpull.trans ((HaarCarrierEqv.mul_left f hrec').trans
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.polyMul_smul_right _ f r)))

/-- The same literal character product has its selected *positive* Casimir
eigenvalue, with no sum over the other upper endpoints. -/
theorem characterProduct_one_upperCasimir (n : Nat) (ds : List Nat)
    (hlen : ds.length = n) (s : Nat) (hs : s < n) :
    HaarCarrierEqv (n+n)
      (activeCasimirPolynomial [n+s] (characterProduct n (pathSlots 0 ds)))
      (polySmul (Q'.ofNat ((ds.getD s 0)*((ds.getD s 0)+2)))
        (characterProduct n (pathSlots 0 ds))) := by
  let kernel := characterProduct n (pathSlots 0 ds)
  let c := Q'.ofNat ((ds.getD s 0)*((ds.getD s 0)+2))
  have hlap : HaarCarrierEqv (n+n)
      (blockAngularLaplacian (n+s) kernel) (polySmul (-c) kernel) := by
    simpa only [Nat.zero_add, hlen] using
      characterProduct_one_upperLaplacian n 0 ds s (by omega) (by omega)
  have hneg : HaarCarrierEqv (n+n)
      (polyNeg (blockAngularLaplacian (n+s) kernel))
      (polySmul c kernel) :=
    (HaarCarrierEqv.neg hlap).trans
      (RatPolyCoeffEqv.haarCarrier
        ((QuaternionHaarAngularCarrier.neg_smul _).trans
          ((RatPolyCoeffEqv.smul_assoc (-1) (-c) kernel).trans
            (RatPolyCoeffEqv.smul_coefficient
              (poly_identity_of_normal_eq
                (.mul (.const (-1)) (.neg (.var 0))) (.var 0)
                (by decide) (fun _ => c)) kernel))))
  change HaarCarrierEqv (n+n)
    (polyAdd (polyNeg (blockAngularLaplacian (n+s) kernel)) polyZero)
    (polySmul c kernel)
  exact (RatPolyCoeffEqv.haarCarrier
    (RatPolyCoeffEqv.add_zero (polyNeg (blockAngularLaplacian (n+s) kernel)))).trans hneg

/-- Each full valid path is an eigenvector on *each* original output block.
Its eigenvalue is the degree of that slot, not the sum over all slots. -/
theorem full_path_blockCasimir_carrier (tail : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds)
    (s : Nat) (hs : s < tail+1) :
    HaarCarrierEqv (tail+1)
      (activeCasimirPolynomial [s] (pathPiece tail p ds))
      (polySmul (Q'.ofNat ((ds.getD s 0)*((ds.getD s 0)+2)))
        (pathPiece tail p ds)) := by
  let n := tail+1
  let kernel := characterProduct n (pathSlots 0 ds)
  let c := Q'.ofNat ((ds.getD s 0)*((ds.getD s 0)+2))
  have hbase : HaarCarrierEqv n
      (partialHaarHeads n (polyMul kernel p)) (pathPiece tail p ds) := by
    have hf := character_prefix_fold_carrier n ds p
    rw [hlen] at hf
    exact hf.trans (pathPiece_character_carrier tail ds p hp hpath)
  have hcomm := activeCasimirPolynomial_partialHaarHeads n [s] (polyMul kernel p)
  have hkernel := characterProduct_one_upperCasimir n ds hlen s (by omega)
  have hpind : QuaternionBlockIndependent (n+s) p :=
    supported_upper_independent hp s
  have hpull := activeCasimirPolynomial_mul_independent [n+s] kernel p
    (fun block hb => by
      simp only [List.mem_singleton] at hb
      subst block
      exact hpind)
  have hupper : HaarCarrierEqv (n+n)
      (activeCasimirPolynomial [n+s] (polyMul kernel p))
      (polySmul c (polyMul kernel p)) :=
    (RatPolyCoeffEqv.haarCarrier hpull).trans
      ((HaarCarrierEqv.mul_right p hkernel).trans
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.polyMul_smul_left c kernel p)))
  have hintegrated := partialHaarHeads_carrier (tailBlocks := n)
    (headBlocks := n) hupper
  have hscaled : HaarCarrierEqv n
      (partialHaarHeads n (polySmul c (polyMul kernel p)))
      (polySmul c (partialHaarHeads n (polyMul kernel p))) :=
    RatPolyCoeffEqv.haarCarrier
      (partialHaarHeads_smul n c (polyMul kernel p))
  exact (activeCasimirPolynomial_carrier [s]
      (fun i hi => by
        simp only [List.mem_singleton] at hi
        subst i
        exact hs) hbase.symm).trans
    ((RatPolyCoeffEqv.haarCarrier hcomm).trans
      (hintegrated.trans (hscaled.trans
        (HaarCarrierEqv.smul c hbase))))

end YMGap.Continuum.SU2QuaternionCyclicPathBlockCasimir

#print axioms YMGap.Continuum.SU2QuaternionCyclicPathBlockCasimir.characterProduct_one_upperLaplacian
#print axioms YMGap.Continuum.SU2QuaternionCyclicPathBlockCasimir.characterProduct_one_upperCasimir
#print axioms YMGap.Continuum.SU2QuaternionCyclicPathBlockCasimir.full_path_blockCasimir_carrier
