/-
# Third Casimir moment contraction through the actual passive channels

Each projected channel is independent of the passive blocks. Its FULL
Casimir is therefore the active Casimir, which commutes through that same
channel. Apply the already proved first-Casimir channel contraction to the
active Casimir of the original source. The resulting coefficient is one.

This is a channel-sum estimate, not a replacement of an arbitrary source's
full cubic moment by an active moment. No interacting variance, numerical
scaling rate or continuum consequence is asserted.
-/

import YMGap.Continuum.SU2QuaternionCyclicCasimirCube
import YMGap.Continuum.SU2QuaternionChannelAngularContraction
import YMGap.Continuum.SU2QuaternionLiteralCasimirPairing

namespace YMGap.Continuum.SU2QuaternionPassiveChannelCasimirCube

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramLocality
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicCasimirBilinear
open YMGap.Continuum.SU2QuaternionCyclicCasimirCube
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The SAME literal third moment, on the displayed active block list. -/
def activeThirdMoment (n : Nat) (active : List Nat) (p : RatPoly) : Q' :=
  let Cp := activeCasimirPolynomial active p
  H n (polyMul Cp (activeCasimirPolynomial active Cp))

private theorem blockLaplacian_congr (block : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (blockAngularLaplacian block p) (blockAngularLaplacian block q) := by
  have hd (i j : Nat) : RatPolyCoeffEqv
      (blockAngularDerivative block i j (blockAngularDerivative block i j p))
      (blockAngularDerivative block i j (blockAngularDerivative block i j q)) :=
    angularDerivative_congr (4*block+i) (4*block+j)
      (angularDerivative_congr (4*block+i) (4*block+j) h)
  refine (blockAngularLaplacian_eq_six block p).trans ?_
  refine RatPolyCoeffEqv.trans ?_ (blockAngularLaplacian_eq_six block q).symm
  unfold six
  exact (hd 0 1).add ((hd 0 2).add ((hd 0 3).add
    ((hd 1 2).add ((hd 1 3).add (hd 2 3)))))

private theorem activeCasimir_congr : ∀ active : List Nat, ∀ {p q : RatPoly},
    RatPolyCoeffEqv p q →
    RatPolyCoeffEqv (activeCasimirPolynomial active p) (activeCasimirPolynomial active q)
  | [], _, _, _ => RatPolyCoeffEqv.refl polyZero
  | block::active, p, q, h => by
      change RatPolyCoeffEqv
        (polyAdd (polyNeg (blockAngularLaplacian block p)) (activeCasimirPolynomial active p))
        (polyAdd (polyNeg (blockAngularLaplacian block q)) (activeCasimirPolynomial active q))
      exact (RatPolyCoeffEqv.neg (blockLaplacian_congr block h)).add
        (activeCasimir_congr active h)

/-- Coefficient transport preserves BOTH full derivatives in the third moment. -/
theorem thirdMoment_congr (tail : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    thirdMoment tail p ≈ thirdMoment tail q := by
  let active := List.range (tail+1)
  have hc := activeCasimir_congr active h
  exact haar_of_coeff (RatPolyCoeffEqv.mul hc (activeCasimir_congr active hc))

theorem activeThirdMoment_congr (n : Nat) (active : List Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : activeThirdMoment n active p ≈ activeThirdMoment n active q := by
  have hc := activeCasimir_congr active h
  exact haar_of_coeff (RatPolyCoeffEqv.mul hc (activeCasimir_congr active hc))

private theorem blockAngularSquare_nonnegative (n block : Nat) (hb : block < n)
    (p : RatPoly) (hp : SupportedQuaternionBlocks n p) :
    (0 : Q') ≤ H n (blockAngularSquare block p) := by
  have C (i j : Nat) (hi : i < 4) (hj : j < 4) :
      Certificate n (polyMul (blockAngularDerivative block i j p)
        (blockAngularDerivative block i j p)) :=
    Certificate.square _ (angularDerivative_supported_at (by omega) (by omega) hp)
  have B : Certificate n (blockAngularSquare block p) := by
    unfold blockAngularSquare six
    exact (C 0 1 (by decide) (by decide)).add
      ((C 0 2 (by decide) (by decide)).add
        ((C 0 3 (by decide) (by decide)).add
          ((C 1 2 (by decide) (by decide)).add
            ((C 1 3 (by decide) (by decide)).add (C 2 3 (by decide) (by decide))))))
  exact B.haar_nonnegative

private theorem angularListSum_nonnegative (n : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) : ∀ active : List Nat,
    (∀ i, i ∈ active → i < n) → (0 : Q') ≤ angularListSum n active p
  | [], _ => Q'.le_refl' 0
  | block::active, ha => Q'.zero_le_add _ _
      (blockAngularSquare_nonnegative n block (ha block List.mem_cons_self) p hp)
      (angularListSum_nonnegative n p hp active
        (fun i hi => ha i (List.mem_cons_of_mem block hi)))

/-- Positivity of this actual active third moment follows from angular squares. -/
theorem activeThirdMoment_nonnegative (n : Nat) (active : List Nat)
    (ha : ∀ i, i ∈ active → i < n) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) : (0 : Q') ≤ activeThirdMoment n active p :=
  Q'.le_trans' _ _ _
    (angularListSum_nonnegative n (activeCasimirPolynomial active p)
      (activeCasimirPolynomial_supported active ha hp) active ha)
    (Q'.ge_of_eqv (haar_activeCasimir_self n active ha (activeCasimirPolynomial active p)))

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) → channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- Exact insertion pullback through the actual passive channel. No support,
positivity or heat assumption is needed for this coefficient identity. -/
theorem channelSource_mul_pullback (passive : List Nat) (q r c : RatPoly)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i r) :
    RatPolyCoeffEqv (channelSource passive (polyMul q r) c)
      (polyMul (channelSource passive q c) r) :=
  (familyProject_congr passive (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => q | 1 => r | _ => c))).trans
    ((familyProject_mul_of_independent passive r (polyMul q c) hind).trans
      (RatPolyCoeffEqv.mul_comm _ _))

/-- The complete channel sum of FULL third moments contracts to the SAME
original active third moment with coefficient one. -/
theorem channelSource_thirdMoment_le_activeThirdMoment (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat)
    (passive active : List Nat) (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      thirdMoment tail (channelSource passive q c)) ≤ activeThirdMoment (tail+1) active q := by
  let cs := productChannels (tail+1) w K passive
  let Cq := activeCasimirPolynomial active q
  have hCq : SupportedQuaternionBlocks (tail+1) Cq :=
    activeCasimirPolynomial_supported active hactive hq
  have hdisjoint : ∀ i, i ∈ active → i ∉ passive := fun i hi hp => hnot i hp hi
  have hsource (c : GramChannel) (hc : c ∈ cs) :
      SupportedQuaternionBlocks (tail+1) (channelSource passive q c.2) :=
    familyProject_supported passive (supported_polyMul hq
      (productChannels_supported (tail+1) w K passive hpassive c hc))
  have hCsource (c : GramChannel) (hc : c ∈ cs) :
      SupportedQuaternionBlocks (tail+1) (channelSource passive Cq c.2) :=
    familyProject_supported passive (supported_polyMul hCq
      (productChannels_supported (tail+1) w K passive hpassive c hc))
  have hcomm (c : GramChannel) (hc : c ∈ cs) :
      RatPolyCoeffEqv
        (activeCasimirPolynomial (List.range (tail+1)) (channelSource passive q c.2))
        (channelSource passive Cq c.2) :=
    (activeCasimirPolynomial_range_eq_active (tail+1) passive active hcover
      (channelSource passive q c.2)
      (fun i hi => channelSource_independent passive q c.2 i hi)).trans
      (activeCasimir_channelSource passive active hdisjoint q c.2
        (fun i hi => productChannels_independent (tail+1) w K passive i (hdisjoint i hi) c hc))
  have he : channelSum cs (fun c => thirdMoment tail (channelSource passive q c)) ≈
      channelSum cs (fun c => pairCasimir tail (channelSource passive Cq c)
        (channelSource passive Cq c)) := by
    apply channelSum_congr
    intro c hc
    let Cp := activeCasimirPolynomial (List.range (tail+1)) (channelSource passive q c.2)
    have hCp : SupportedQuaternionBlocks (tail+1) Cp :=
      activeCasimirPolynomial_supported (List.range (tail+1))
        (fun i hi => List.mem_range.mp hi) (hsource c hc)
    exact Q'.eqv_trans _ _ _ (pairCasimir_eq_literal tail Cp Cp hCp hCp).symm
      (Q'.eqv_trans _ _ _ (pairCasimir_congr_right tail Cp hCp (hcomm c hc))
        (Q'.eqv_trans _ _ _ (pairCasimir_symm tail Cp (channelSource passive Cq c.2)
          hCp (hCsource c hc))
          (pairCasimir_congr_right tail (channelSource passive Cq c.2)
            (hCsource c hc) (hcomm c hc))))
  have htail : tail+1-1 = tail := by omega
  have hbound : channelSum cs (fun c => pairCasimir tail (channelSource passive Cq c)
      (channelSource passive Cq c)) ≤ angularListSum (tail+1) active Cq := by
    simpa only [htail] using pairCasimir_channel_le_active (tail+1) (by omega)
      hw0 hw1 K passive active hnd hpassive hactive hdisjoint hcover Cq hCq
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ hbound
      (Q'.ge_of_eqv (haar_activeCasimir_self (tail+1) active hactive Cq)))

/-- A passive-independent insertion remains inside EVERY channel source and
both full derivatives. The RHS differentiates the actual original `q*r`. -/
theorem channelSource_mul_thirdMoment_le_activeThirdMoment (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat)
    (passive active : List Nat) (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < tail+1)
    (hactive : ∀ i, i ∈ active → i < tail+1)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (hcover : (passive ++ active).Perm (List.range (tail+1)))
    (q r : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hr : SupportedQuaternionBlocks (tail+1) r)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i r) :
    channelSum (productChannels (tail+1) w K passive) (fun c =>
      thirdMoment tail (polyMul (channelSource passive q c) r)) ≤
      activeThirdMoment (tail+1) active (polyMul q r) := by
  let cs := productChannels (tail+1) w K passive
  have he : channelSum cs (fun c => thirdMoment tail (channelSource passive (polyMul q r) c)) ≈
      channelSum cs (fun c => thirdMoment tail (polyMul (channelSource passive q c) r)) :=
    channelSum_congr _ _ cs (fun c _ =>
      thirdMoment_congr tail (channelSource_mul_pullback passive q r c.2 hind))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (channelSource_thirdMoment_le_activeThirdMoment tail hw0 hw1 K passive active hnd
      hpassive hactive hnot hcover (polyMul q r) (supported_polyMul hq hr))

#print axioms activeThirdMoment
#print axioms thirdMoment_congr
#print axioms activeThirdMoment_congr
#print axioms activeThirdMoment_nonnegative
#print axioms channelSource_mul_pullback
#print axioms channelSource_thirdMoment_le_activeThirdMoment
#print axioms channelSource_mul_thirdMoment_le_activeThirdMoment

end YMGap.Continuum.SU2QuaternionPassiveChannelCasimirCube
