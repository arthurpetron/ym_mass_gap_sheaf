/-
# A non-null normalized original boundary code at every odd extent

The constant insertion has zero exposed degree at every crossing face.
Consequently the ORIGINAL full interface paired with one stabilizes already
at cutoff zero and has Haar value one. At anchor zero both heat-dressed
boundary polynomials are also one. The same trivial-representation boundary
code therefore has norm one in every original finite and cutoff-limit form.

This is normalization of a specified boundary CODE. No stationarity under
physical time, inter-slab compatibility, strict gap or continuum vacuum is
asserted. All identities keep the original heat coefficients and Haar carrier.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS

namespace YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSelectedFaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceSelection
open YMGap.Continuum.BF4ExactSlabAllExtentInterfaceCutoffLimit
open YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabAllExtentAnchoredCutoffLimit
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionExposedHeatCutoffSelection
open YMGap.Continuum.SU2QuaternionFourBlockSelection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem headDegreeBound_zero : ∀ p : RatPoly,
    HasQuaternionBlockDegree 0 0 p → headDegreeBound p = 0
  | [], _ => rfl
  | t :: p, h => by
    rw [headDegreeBound, h t List.mem_cons_self,
      headDegreeBound_zero p (fun s hs => h s (List.mem_cons_of_mem t hs))]
    rfl

theorem selectedFaceBound_one {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) : selectedFaceBound hf polyOne = 0 :=
  headDegreeBound_zero _ (chain_degree (faceExposure hf).steps
    (Nat.lt_trans (by decide : 0 < 3) (face_carrier_four_blocks hf)) (hasQuaternionBlockDegree_one _))

private theorem map_max_zero {A : Type} (f : A → Nat) : ∀ xs : List A,
    (∀ x, x ∈ xs → f x = 0) → (xs.map f).foldr Nat.max 0 = 0
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, List.foldr_cons, h x List.mem_cons_self,
      map_max_zero f xs (fun y hy => h y (List.mem_cons_of_mem x hy))]
    rfl

theorem interfaceBound_one (half : Nat) : interfaceBound half polyOne = 0 :=
  map_max_zero _ _ (fun face _ => selectedFaceBound_one (fixedFaces_physical face.property).1)

private theorem supported_one (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

theorem weightedFacePolynomial_vacuum (w : Q') (K extent id : Nat) :
    RatPolyCoeffEqv (weightedFacePolynomial w K extent zeroEdgeLabelling id) polyOne := by
  unfold weightedFacePolynomial
  simp only [zeroEdgeLabelling, coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero, characterPolynomial]
  exact RatPolyCoeffEqv.one_smul _

theorem vacuum_polynomialProduct (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polynomialProduct (weightedFacePolynomial w K extent zeroEdgeLabelling) ids) polyOne
  | [] => RatPolyCoeffEqv.refl _
  | id :: ids => ((weightedFacePolynomial_vacuum w K extent id).mul
      (vacuum_polynomialProduct w K extent ids)).trans (RatPolyCoeffEqv.one_mul _)

theorem interfaceHeatInsertion_cutoff_zero (w : Q') (half : Nat) :
    RatPolyCoeffEqv (interfaceHeatInsertion w 0 half) polyOne := by
  unfold interfaceHeatInsertion centralBoundaryChannels
  rw [boundedEdgeLabellings_zero]
  change RatPolyCoeffEqv (polyAdd (interfaceLabelPolynomial w 0 half zeroEdgeLabelling) polyZero) polyOne
  exact (RatPolyCoeffEqv.add_zero _).trans (vacuum_polynomialProduct w 0 _ _)

private theorem haar_one (half : Nat) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length polyOne ≈ 1 := by
  have h := exactCorrectedSlabHaarCoefficient_vacuum (centralExtent half)
  unfold exactCorrectedSlabHaarCoefficient at h
  rw [exactCorrectedSlabSpinNetworkIntegrand_vacuum] at h
  exact h

/-- All original crossing heat factors are retained; only their nonzero modes cancel. -/
theorem interfacePairing_one (w : Q') (K half : Nat) : interfacePairing w K half polyOne ≈ 1 := by
  have h := interfacePairing_stable w K half polyOne (supported_one _)
    (by rw [interfaceBound_one]; exact Nat.zero_le K)
  rw [interfaceBound_one] at h
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
    (((interfaceHeatInsertion_cutoff_zero w half).mul_left polyOne).trans (RatPolyCoeffEqv.one_mul _)))
    (haar_one half))

theorem lowerObservable_cutoff_zero (w : Q') (half : Nat) :
    RatPolyCoeffEqv (lowerObservable w 0 half (fun _ => 1)) polyOne := by
  unfold lowerObservable centralHalfStates
  rw [boundedEdgeLabellings_zero]
  change RatPolyCoeffEqv (polyAdd (polySmul 1 (lowerPolynomial w 0 half zeroEdgeLabelling)) polyZero) polyOne
  exact ((RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul _)).trans
    (vacuum_polynomialProduct w 0 _ _)

theorem upperObservable_cutoff_zero (w : Q') (half : Nat) :
    RatPolyCoeffEqv (upperObservable w 0 half (fun _ => 1)) polyOne := by
  unfold upperObservable centralHalfStates
  rw [boundedEdgeLabellings_zero]
  change RatPolyCoeffEqv (polyAdd (polySmul 1 (upperPolynomial w 0 half zeroEdgeLabelling)) polyZero) polyOne
  exact ((RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul _)).trans
    (vacuum_polynomialProduct w 0 _ _)

/-- Trivial-representation boundary code with its literal zero-cutoff witness. -/
def vacuumCode (half : Nat) : BoundaryObservable half :=
  BoundaryObservable.ofCoefficients half 0 (fun _ => 1)

theorem vacuumCode_finite_norm (w : Q') (K half : Nat) :
    finiteForm w K (vacuumCode half) (vacuumCode half) ≈ 1 := by
  have h := exact_bilinear_anchored w (Nat.zero_le K) half (fun _ => 1) (fun _ => 1)
  have hp := (lowerObservable_cutoff_zero w half).mul
    ((upperObservable_cutoff_zero w half).mul_left (interfaceHeatInsertion w K half))
  have hr := hp.trans ((RatPolyCoeffEqv.mul_one _).mul_left polyOne)
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _ hr) (interfacePairing_one w K half))

theorem vacuumCode_limit_norm (w : Q') (half : Nat) :
    limitForm w (vacuumCode half) (vacuumCode half) ≈ 1 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (finiteForm_stable w
    (formModulus w (vacuumCode half) (vacuumCode half)) (vacuumCode half) (vacuumCode half) (Nat.le_refl _)))
    (vacuumCode_finite_norm w _ half)

end YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.selectedFaceBound_one
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.interfaceBound_one
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.weightedFacePolynomial_vacuum
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.vacuum_polynomialProduct
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.interfaceHeatInsertion_cutoff_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.interfacePairing_one
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.lowerObservable_cutoff_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.upperObservable_cutoff_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.vacuumCode
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.vacuumCode_finite_norm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization.vacuumCode_limit_norm
