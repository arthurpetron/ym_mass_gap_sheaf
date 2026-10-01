/-
# The same spectator mass in weighted channels and original heat moments

A source independent of every block outside the passive list has constant
projected Gram channels: each channel is independent of every original block.
Finite Haar factorization therefore gives one common nonnegative channel mass.
For passive-independent insertions the ORIGINAL full-heat source moment has
exactly the same mass. No bare/heat retention inequality is assumed.

Positive source order also orders original square-inserted moments. This is
not an order on signed channel polynomials and does not replace the original
heat-paired moment by a bare square. All zero-mass cases are retained.
-/

import YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight
import YMGap.Continuum.SU2QuaternionProductHeatBandResponse
import YMGap.Continuum.SU2QuaternionProductHeatGramLocality
import YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
import YMGap.Continuum.SU2QuaternionHaarFamilyCertificate

namespace YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyCertificate
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramLocality
open YMGap.Continuum.SU2QuaternionProductHeatBandResponse
open YMGap.Continuum.SU2QuaternionDisjointBlockHaarFactorization
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The existing passive channels, without renormalizing their weights. -/
def channelSquare (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a e : RatPoly) : Q' :=
  channelSum (productChannels n w K ids) (fun c =>
    H n (polyMul (polyMul (channelSource ids a c) (channelSource ids a c)) e))

/-- Explicit common mass. It is not postulated to be a bare spectator norm. -/
def channelMass (n : Nat) (w : Q') (K : Nat) (ids : List Nat) (a : RatPoly) : Q' :=
  channelSum (productChannels n w K ids) (fun c =>
    H n (polyMul (channelSource ids a c) (channelSource ids a c)))

theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

theorem channelSum_smul (value : RatPoly → Q') (a : Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a * value c) ≈ a * channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => c.1 | 1 => a | _ => value c.2))
        (channelSum_smul value a cs))
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

private theorem sum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) →
      (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (hv c List.mem_cons_self))
      (sum_nonnegative value cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => hv d (List.mem_cons_of_mem c hd)))

theorem channelSource_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {a : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (c : GramChannel)
    (hc : c ∈ productChannels n w K ids) :
    SupportedQuaternionBlocks n (channelSource ids a c.2) :=
  familyProject_supported ids
    (supported_polyMul ha (productChannels_supported n w K ids hids c hc))

/-- A spectator source's projected channels omit EVERY in-range block.
The two cases use locality outside the list and actual integration inside it. -/
theorem spectator_channel_independent (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (a : RatPoly)
    (ha : ∀ i, i < n → i ∉ ids → QuaternionBlockIndependent i a)
    (c : GramChannel) (hc : c ∈ productChannels n w K ids) :
    ∀ i, i < n → QuaternionBlockIndependent i (channelSource ids a c.2) := by
  intro i hi
  by_cases hm : i ∈ ids
  · exact channelSource_independent ids a c.2 i hm
  · exact familyProject_preserves_independent ids
      (quaternionBlockIndependent_polyMul (ha i hi hm)
        (productChannels_independent n w K ids i hm c hc))

/-- Original finite Haar factorization for an all-block-independent factor.
Signed and zero coefficients are allowed in both polynomials. -/
theorem all_independent_haar_factor {n : Nat} {a e : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (he : SupportedQuaternionBlocks n e)
    (hind : ∀ i, i < n → QuaternionBlockIndependent i a) :
    H n (polyMul a e) ≈ H n a * H n e := by
  apply haar_product ha he
  intro s hs t ht i hi
  apply Or.inl
  intro component hcomponent
  have hz := exponentAt_clearQuaternionBlock_self s.1 i component hcomponent
  rw [hind i hi s hs] at hz
  exact hz

/-- Exact weighted factorization. No sign, heat-floor or insertion-independence
premise is needed: the spectator channels are already constant on all blocks. -/
theorem channelSquare_factor (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (a e : RatPoly)
    (ha : SupportedQuaternionBlocks n a) (he : SupportedQuaternionBlocks n e)
    (hind : ∀ i, i < n → i ∉ ids → QuaternionBlockIndependent i a) :
    channelSquare n w K ids a e ≈ channelMass n w K ids a * H n e := by
  have hterm := channelSum_congr
    (fun c => H n (polyMul (polyMul (channelSource ids a c) (channelSource ids a c)) e))
    (fun c => H n e * H n (polyMul (channelSource ids a c) (channelSource ids a c)))
    (productChannels n w K ids) (by
      intro c hc
      have hb := channelSource_supported n w K ids hids ha c hc
      have hi := spectator_channel_independent n w K ids a hind c hc
      exact Q'.eqv_trans _ _ _
        (all_independent_haar_factor (supported_polyMul hb hb) he
          (fun i hi' => quaternionBlockIndependent_polyMul (hi i hi') (hi i hi')))
        (Q'.mul_comm_eqv _ _))
  exact Q'.eqv_trans _ _ _ hterm
    (Q'.eqv_trans _ _ _ (channelSum_smul _ (H n e) _)
      (Q'.mul_comm_eqv _ _))

theorem channelMass_nonnegative (n : Nat) {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    (0 : Q') ≤ channelMass n w K ids a :=
  sum_nonnegative _ _ (productChannels_nonnegative n hw K ids)
    (fun c hc => (Certificate.square _
      (channelSource_supported n w K ids hids ha c hc)).haar_nonnegative)

/-- Fubini projects the insertion, not the original source or heat kernel.
This permits a whole certified angular weight without assuming syntactic
independence of its zero-coefficient derivative terms. -/
theorem channelSquare_project_weight (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) (a e : RatPoly) :
    channelSquare n w K ids a e ≈
      channelSquare n w K ids a (familyProject ids e) :=
  channelSum_congr _ _ _ (fun c _ =>
    quaternionHaar_polyMul_eq_after_integratingBlocks n ids
      (polyMul (channelSource ids a c.2) (channelSource ids a c.2)) e hids
      (fun i hi => quaternionBlockIndependent_polyMul
        (channelSource_independent ids a c.2 i hi)
        (channelSource_independent ids a c.2 i hi)))

/-- The original full heat on an all-independent source gives the SAME
factor as its Haar square. The assertion is tested Haar equality, not an
identity on arbitrary polynomials omitted from a product-map list. -/
theorem all_independent_sourceMoment (n : Nat) (w : Q') (K : Nat)
    (a e : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (he : SupportedQuaternionBlocks n e)
    (hind : ∀ i, i < n → QuaternionBlockIndependent i a) :
    sourceMoment n w K (List.range n) a e ≈ H n (polyMul a a) * H n e := by
  have hd : SupportedHaarEqv n
      (productMap n w K (List.range n) a) (cap (H n a)) := by
    have hdrop := productMap_drop_independent_prefix n w K [] (List.range n)
      (by simpa only [List.append_nil] using CayleyParentInj.range_nodup n)
      (by intro i hi; exact List.mem_range.mp (by simpa only [List.append_nil] using hi))
      a ha (fun i hi => hind i (List.mem_range.mp hi))
    have hdrop' : SupportedHaarEqv n
        (productMap n w K (List.range n) a) (productMap n w K [] a) := by
      simpa only [List.append_nil] using hdrop
    exact hdrop'.trans
      (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier (productMap_nil n w K a ha)))
  have hstart := hd (polyMul a e) (supported_polyMul ha he)
  have hcap : H n (polyMul (polyMul a e) (cap (H n a))) ≈
      H n a * H n (polyMul a e) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left _ _)))
      (quaternionHaar_polySmul n _ _)
  have hpair := all_independent_haar_factor ha he hind
  have hsquare := all_independent_haar_factor ha ha hind
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hcap
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hpair)
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
          (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hsquare)))))

/-- The common mass is also the ORIGINAL full-heat source moment's factor.
Insertion independence is essential here; arbitrary insertions depending on
the passive source cannot be factored through that source's original density. -/
theorem spectator_sourceMoment_factor (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hactive : ∀ i, i ∈ active → i < n)
    (hpassive : ∀ i, i ∈ passive → i < n)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive++active).Perm (List.range n)) (a e : RatPoly)
    (ha : SupportedQuaternionBlocks n a) (he : SupportedQuaternionBlocks n e)
    (haind : ∀ i, i < n → i ∉ passive → QuaternionBlockIndependent i a)
    (heind : ∀ i, i ∈ passive → QuaternionBlockIndependent i e) :
    sourceMoment n w K (List.range n) a e ≈ channelMass n w K passive a * H n e := by
  have hc := sourceMoment_projected_channels n w K active passive hactive hpassive
    hnot hcover a e ha he heind
  have ht := channelSum_congr
    (fun c => sourceMoment n w K (List.range n) (channelSource passive a c) e)
    (fun c => H n e * H n (polyMul (channelSource passive a c) (channelSource passive a c)))
    (productChannels n w K passive) (by
    intro c hmem
    exact Q'.eqv_trans _ _ _
      (all_independent_sourceMoment n w K (channelSource passive a c.2) e
        (channelSource_supported n w K passive hpassive ha c hmem) he
        (spectator_channel_independent n w K passive a haind c hmem))
      (Q'.mul_comm_eqv _ _))
  exact Q'.eqv_trans _ _ _ hc
    (Q'.eqv_trans _ _ _ ht
      (Q'.eqv_trans _ _ _ (channelSum_smul _ (H n e) _)
        (Q'.mul_comm_eqv _ _)))

/-- Exact source-scalar square law for the original heat-paired moment. -/
theorem sourceMoment_smul (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a e : RatPoly) (c : Q') :
    sourceMoment n w K ids (polySmul c a) e ≈
      (c*c)*sourceMoment n w K ids a e := by
  have hmap := productMap_smul n w K ids c a
  have hshape : RatPolyCoeffEqv
      (polyMul (polyMul (polySmul c a) e)
        (productMap n w K ids (polySmul c a)))
      (polySmul (c*c) (polyMul (polyMul a e) (productMap n w K ids a))) :=
    ((RatPolyCoeffEqv.refl _).mul hmap).trans
      (((RatPolyCoeffEqv.polyMul_smul_left c a e).mul (.refl _)).trans
        ((RatPolyCoeffEqv.polyMul_smul_left c _ _).trans
          (((RatPolyCoeffEqv.polyMul_smul_right c _ _).smul c).trans
            (RatPolyCoeffEqv.smul_assoc c c _))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hshape) (quaternionHaar_polySmul n _ _)

/-- Positive source order compares ORIGINAL full heat-paired square moments.
The square can depend on every block. No variance or source is inverted. -/
theorem sourceMoment_square_mono {n : Nat} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (p q f : RatPoly) (hp : SupportedQuaternionBlocks n p)
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f)
    (P : Certificate n p) (Q : Certificate n q)
    (D : Certificate n (polyAdd q (polyNeg p))) :
    sourceMoment n w K ids p (polyMul f f) ≤
      sourceMoment n w K ids q (polyMul f f) := by
  have U : Certificate n (polyAdd (polySmul 1 q) (polyNeg p)) :=
    .ofCoeff ((RatPolyCoeffEqv.one_smul q).add (.refl _)) D
  have C := sourceProductUpper hw0 hw1 K hK ids hids hp hq P Q
    (by decide : (0 : Q') ≤ 1) U
  have C' : Certificate n (polyAdd (polyMul q (productMap n w K ids q))
      (polyNeg (polyMul p (productMap n w K ids p)))) :=
    .ofCoeff (((RatPolyCoeffEqv.smul_coefficient (by decide : (1:Q')*1 ≈ 1) _).trans
      (RatPolyCoeffEqv.one_smul _)).symm.add (.refl _)) C
  have ho := square_moment_order C' hf
  have pin (a : RatPoly) :
      sourceMoment n w K ids a (polyMul f f) ≈
        H n (polyMul (polyMul a (productMap n w K ids a)) (polyMul f f)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => a | 1 => polyMul f f | _ => productMap n w K ids a))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (pin p))
    (Q'.le_trans' _ _ _ ho (Q'.ge_of_eqv (pin q)))

#print axioms channelSquare
#print axioms channelMass
#print axioms channelSum_congr
#print axioms channelSum_smul
#print axioms channelSource_supported
#print axioms spectator_channel_independent
#print axioms all_independent_haar_factor
#print axioms channelSquare_factor
#print axioms channelMass_nonnegative
#print axioms channelSquare_project_weight
#print axioms all_independent_sourceMoment
#print axioms spectator_sourceMoment_factor
#print axioms sourceMoment_smul
#print axioms sourceMoment_square_mono

end YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
