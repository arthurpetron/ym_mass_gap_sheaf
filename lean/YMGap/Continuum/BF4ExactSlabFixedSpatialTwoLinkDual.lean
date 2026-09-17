/-
# Two-link control on the original slab and its signed message determinant

For distinct active i,j, retain every other heat factor and both copies of
a=V*T^n1. The four-cell inequality yields
 h (H[a di f ri]+H[a dj f rj])^2
   <= energy(T^n1,f) (H[a di ri^2]+H[a dj rj^2]+2h H[a dij ri rj]).
The twice-erased cross pairing is signed, not declared small or zero.

For the already constructed tests ri=t*qi*Gi, rj=t*qj*Gj in the actual
marginal nu=a*t, it splits exactly into the corrected ordinary pairing
and the determinant remainder Delta_ij=t*dij-di*dj. This identifies the
action-dependent term a collective bound must control. No spatial locality
of the terminal message, complete decomposition, or global gap is asserted.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity energy energy_identity energy_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
open YMGap.Continuum.BF4ExactSlabFixedSpatialDualDirichlet (erasedPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialErasedMessageInverse (reciprocal)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.SU2QuaternionWeightedProductTwoLinkDual
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks kineticWeight

/-- Remove exactly the two chosen factors, retaining the entire V*T^n1 source. -/
def twiceErasedMessage (w : Q') (K width n i j : Nat) : RatPoly :=
  productMap (N width) w K (eraseIndex j (eraseIndex i (activeBlocks width)))
    (polyMul (spatialWeight w K width) (terminalMessage w K width n))

theorem twiceErasedMessage_supported (w : Q') (K width n i j : Nat) :
    SupportedQuaternionBlocks (N width) (twiceErasedMessage w K width n i j) :=
  productMap_supported (N width) w K _
    (fun k hk => activeBlocks_lt width k (mem_of_mem_erase i (mem_of_mem_erase j hk)))
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))

/-- The cross marginal uses the same full endpoint and two-factor erasure. -/
def crossPair (w : Q') (K width n i j : Nat) (r s : RatPoly) : Q' :=
  quaternionHaar (N width) (polyMul
    (polyMul (polyMul (spatialWeight w K width) (terminalMessage w K width n))
      (twiceErasedMessage w K width n i j)) (polyMul r s))

/-- The original temporal energy controls TWO centered dual tests with no
independent estimate or absolute value substituted for their signed cross term. -/
theorem terminal_two_link_dual_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i j : Nat) (hi : i ∈ activeBlocks width) (hj : j ∈ activeBlocks width) (hne : i ≠ j)
    {f r s : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hr : SupportedQuaternionBlocks (N width) r) (hs : SupportedQuaternionBlocks (N width) s)
    (hc : RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) r)) polyZero)
    (hd : RatPolyCoeffEqv (project j (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) s)) polyZero) :
    let L := erasedPair w K width n i f r + erasedPair w K width n j f s
    headFloor w*(L*L) ≤ energy w K width (terminalMessage w K width n) f *
      (erasedPair w K width n i r r + erasedPair w K width n j s s +
        ((2 : Q')*headFloor w)*crossPair w K width n i j r s) := by
  let g := terminalMessage w K width n
  let a := polyMul (spatialWeight w K width) g
  let ids := eraseIndex j (eraseIndex i (activeBlocks width))
  have hpi := select_perm i hi
  have hj' : j ∈ eraseIndex i (activeBlocks width) :=
    (List.mem_cons.mp (hpi.mem_iff.mp hj)).resolve_left (Ne.symm hne)
  have hpj := select_perm j hj'
  have hp : (activeBlocks width).Perm (i::j::ids) := hpi.trans (List.Perm.cons i hpj)
  have hni : i ∉ ids := fun h =>
    not_mem_erase i (activeBlocks_nodup width) (mem_of_mem_erase j h)
  have hnj : j ∉ ids :=
    not_mem_erase j (List.nodup_cons.mp (hpi.nodup_iff.mp (activeBlocks_nodup width))).2
  have hqj : (eraseIndex j (activeBlocks width)).Perm (i::ids) :=
    List.Perm.cons_inv ((select_perm j hj).symm.trans (hp.trans (List.Perm.swap j i ids)))
  have ha := supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)
  let C := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)
  have h := two_link_dual_bound (N width) hw0 hw1 K hK i j ids
    (activeBlocks_lt width i hi) (activeBlocks_lt width j hj) hne hni hnj
    (fun k hk => activeBlocks_lt width k (mem_of_mem_erase i (mem_of_mem_erase j hk)))
    ha hf hr hs C hc hd
  have pinI (x y : RatPoly) :
      SU2QuaternionWeightedProductDualEnergy.marginalPair (N width) w K (j::ids) a x y ≈
      erasedPair w K width n i x y := marginalPair_perm (N width) w K hpj.symm a x y
  have pinJ (x y : RatPoly) :
      SU2QuaternionWeightedProductDualEnergy.marginalPair (N width) w K (i::ids) a x y ≈
      erasedPair w K width n j x y := marginalPair_perm (N width) w K hqj.symm a x y
  have he : RatPolyCoeffEqv (edgeWeight (N width) w K (i::j::ids) a) (edgeDensity w K width g) := by
    unfold edgeWeight edgeDensity
    rw [kineticWeight_eq_indexedProduct]
    exact ((polynomialProduct_perm _ hp).symm.mul_right _).mul_right _
  have henergy : weightedPair (N width+N width) (edgeWeight (N width) w K (i::j::ids) a)
      (jump (N width) f) (jump (N width) f) ≈ (2 : Q')*energy w K width g f :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (he.mul_left _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_symm (energy_identity w K width (terminalMessage_supported w K width n) hf)))
  have hL := Q'.add_eqv_congr' (pinI f r) (pinJ f s)
  have hR := Q'.add_eqv_congr' (Q'.add_eqv_congr' (pinI r r) (pinJ s s))
    (Q'.eqv_refl (((2 : Q')*headFloor w)*crossPair w K width n i j r s))
  have hl := Q'.mul_eqv_congr_left ((2 : Q')*headFloor w) _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hL) (Q'.mul_eqv_congr_left _ _ _ hL))
  have hb := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ henergy) (Q'.mul_eqv_congr_left _ _ _ hR))))
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))))
    (show (0 : Q') < (2 : Q') by decide)

/-- The actual unnormalized two-message determinant. No sign is imposed. -/
def messageDeterminant (w : Q') (K width n i j : Nat) : RatPoly :=
  polyAdd
    (polyMul (terminalMessage w K width (n+1)) (twiceErasedMessage w K width n i j))
    (polyNeg (polyMul (conditionalMessage w K width n i) (conditionalMessage w K width n j)))

theorem messageDeterminant_supported (w : Q') (K width n i j : Nat) :
    SupportedQuaternionBlocks (N width) (messageDeterminant w K width n i j) := by
  apply supported_add
  · exact supported_polyMul (terminalMessage_supported w K width (n+1))
      (twiceErasedMessage_supported w K width n i j)
  · intro term ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    exact supported_polyMul (conditionalMessage_supported w K width n i)
      (conditionalMessage_supported w K width n j) s hs

section ActualTests

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n i j : Nat)

/-- The ordinary actual-marginal pairing, with the constructed d_i*G_i corrections. -/
def correctedCross (q r : RatPoly) (k l : Nat) : Q' :=
  quaternionHaar (N width) (polyMul (marginalWeight w K width n)
    (polyMul (polyMul q r)
      (polyMul
        (polyMul (conditionalMessage w K width n i) (reciprocal hw0 hw1 K width hK n i k))
        (polyMul (conditionalMessage w K width n j) (reciprocal hw0 hw1 K width hK n j l)))))

/-- The signed action-dependent remainder; neither absolute value nor spatial
decay is built into this definition. -/
def determinantCross (q r : RatPoly) (k l : Nat) : Q' :=
  quaternionHaar (N width) (polyMul (marginalWeight w K width n)
    (polyMul (messageDeterminant w K width n i j)
      (polyMul (polyMul q r)
        (polyMul (reciprocal hw0 hw1 K width hK n i k) (reciprocal hw0 hw1 K width hK n j l)))))

/-- Exact signed cross pin for the ACTUAL polynomial tests. No reciprocal
limit, centering, independent-terminal-factor or determinant bound is assumed. -/
theorem dualTest_cross_pin (q r : RatPoly) (k l : Nat) :
    crossPair w K width n i j
      (dualTest hw0 hw1 K width hK n i q k) (dualTest hw0 hw1 K width hK n j r l) ≈
    correctedCross hw0 hw1 K width hK n i j q r k l +
      determinantCross hw0 hw1 K width hK n i j q r k l :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 4)) (.mul (.mul (.mul (.var 1) (.var 5)) (.var 7)) (.mul (.mul (.var 1) (.var 6)) (.var 8))))
    (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 5) (.var 6)) (.mul (.mul (.var 2) (.var 7)) (.mul (.var 3) (.var 8))))) (.mul (.mul (.var 0) (.var 1)) (.mul (.add (.mul (.var 1) (.var 4)) (.neg (.mul (.var 2) (.var 3)))) (.mul (.mul (.var 5) (.var 6)) (.mul (.var 7) (.var 8)))))) (by decide) (fun
      | 0 => polyMul (spatialWeight w K width) (terminalMessage w K width n)
      | 1 => terminalMessage w K width (n+1)
      | 2 => conditionalMessage w K width n i
      | 3 => conditionalMessage w K width n j
      | 4 => twiceErasedMessage w K width n i j
      | 5 => q | 6 => r
      | 7 => reciprocal hw0 hw1 K width hK n i k
      | _ => reciprocal hw0 hw1 K width hK n j l)))
    (quaternionHaar_append _ _ _)

/-- Physical two-test estimate with local norms already paid by the one-U
budget. The only cross correction is displayed on the same actual marginal.
It is still an approximate dual pairing, not a collective global gap. -/
theorem actual_signed_two_link_bound
    (hi : i ∈ activeBlocks width) (hj : j ∈ activeBlocks width) (hne : i ≠ j)
    {f q r : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hq : SupportedQuaternionBlocks (N width) q) (hr : SupportedQuaternionBlocks (N width) r)
    (hc : RatPolyCoeffEqv (project i (polyMul (marginalWeight w K width n) q)) polyZero)
    (hd : RatPolyCoeffEqv (project j (polyMul (marginalWeight w K width n) r)) polyZero)
    (k l : Nat) :
    let L := erasedPair w K width n i f (dualTest hw0 hw1 K width hK n i q k) +
      erasedPair w K width n j f (dualTest hw0 hw1 K width hK n j r l)
    headFloor w*(L*L) ≤ energy w K width (terminalMessage w K width n) f *
      (prefixCap w * (marginalPair w K width n q q + marginalPair w K width n r r) +
        ((2 : Q')*headFloor w)*
          (correctedCross hw0 hw1 K width hK n i j q r k l +
            determinantCross hw0 hw1 K width hK n i j q r k l)) := by
  have h := terminal_two_link_dual_energy hw0 hw1 K width hK n i j hi hj hne hf
    (dualTest_supported hw0 hw1 K width hK n i hq k)
    (dualTest_supported hw0 hw1 K width hK n j hr l)
    (dualTest_centered hw0 hw1 K width hK n i hi hc k)
    (dualTest_centered hw0 hw1 K width hK n j hj hd l)
  have hn := Q'.add_le_add
    (dualTest_norm_bound hw0 hw1 K width hK n i hi hq k)
    (dualTest_norm_bound hw0 hw1 K width hK n j hj hr l)
  have hnorm := Q'.le_trans' _ _ _ hn (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))
  have hcross := Q'.mul_eqv_congr_left ((2 : Q')*headFloor w) _ _
    (dualTest_cross_pin hw0 hw1 K width hK n i j q r k l)
  exact Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.add_le_add hnorm (Q'.le_of_eqv hcross))
    (energy_nonnegative hw0 hw1 K width hK
      (terminalMessage_supported w K width n) hf
      (terminalMessage_certificate hw0 hw1 K width hK n)))

end ActualTests

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.twiceErasedMessage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.twiceErasedMessage_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.crossPair
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.terminal_two_link_dual_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.messageDeterminant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.messageDeterminant_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.correctedCross
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.determinantCross
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.dualTest_cross_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual.actual_signed_two_link_bound
