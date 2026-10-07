/-
# An initial ORIGINAL local energy bound survives every filtering step

The literal positive symmetric transfer is T=K V. A constructed terminal
envelope l*a <= T a <= U*a keeps BOTH endpoints under iteration. A bound
E(a,psi) <= d*ell[a*(T a)*psi^2] therefore supplies a fixed source Rayleigh
floor rho=(1-d)*l, which positive operator algebra propagates to T^t(a*psi).
The resulting cleared original cost is at most (d+eta)*Z1*ell[b^2], with
no time accumulation, polynomial inverse, source-norm inverse, degree
restriction, stationary eigenpin, or discarded action covariance.

This transports a supplied INITIAL local energy coefficient; it does not
construct a scaling-small d or eta, a surviving continuum excitation, an
all-vector changing-action comparison, or a physical/continuum/Clay gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceRayleighPersistence
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalEnergyTransport

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass weightedMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (Bracket)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (clearedRayleighCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceRayleighPersistence
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit (boundaryDrift)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks weightedMass terminalMessage transferStep terminalComparison

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

private def transfer_bracket {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) (B : Bracket width f g) :
    Bracket width (transferStep w K width f) (transferStep w K width g) where
  lower := B.lower
  upper := B.upper
  lowerCertificate := Certificate.ofCoeff
    ((transferStep_add w K width _ _).trans
      ((RatPolyCoeffEqv.refl _).add (transferStep_smul w K width _ _))).symm
    (transferStep_certificate hw0 hw1 K width hK
      (supported_add hf (support_smul hg _)) B.lowerCertificate)
  upperCertificate := Certificate.ofCoeff
    ((transferStep_add w K width _ _).trans
      ((transferStep_smul w K width _ _).add (transferStep_smul w K width _ _))).symm
    (transferStep_certificate hw0 hw1 K width hK
      (supported_add (support_smul hg _) (support_smul hf _)) B.upperCertificate)

private def reindex {width : Nat} {f g f' g' : RatPoly}
    (hf : f = f') (hg : g = g') (B : Bracket width f g) : Bracket width f' g' := by
  cases hf
  cases hg
  exact B

private theorem reindex_lower {width : Nat} {f g f' g' : RatPoly}
    (hf : f = f') (hg : g = g') (B : Bracket width f g) :
    (reindex hf hg B).lower = B.lower := by
  cases hf
  cases hg
  rfl

private theorem reindex_upper {width : Nat} {f g f' g' : RatPoly}
    (hf : f = f') (hg : g = g') (B : Bracket width f g) :
    (reindex hf hg B).upper = B.upper := by
  cases hf
  cases hg
  rfl

attribute [local irreducible] reindex

/-- Constructed fixed endpoints for every later actual terminal quotient.
Unlike refreshing the bracket, this preserves the INITIAL l and U. -/
def terminalFixedEnvelope {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) :
    (t : Nat) → Bracket width
      (transferStep w K width (terminalMessage w K width (s+1+t)))
      (terminalMessage w K width (s+1+t))
  | 0 => by
      let B := terminalComparison hw0 hw1 K width hK s 1 0
      exact reindex (terminalMessage_next w K width (s+1)).symm rfl B
  | t+1 => by
      let B := terminalFixedEnvelope hw0 hw1 K width hK s t
      let C := transfer_bracket hw0 hw1 K width hK
        (transferStep_supported w K width (terminalMessage_supported w K width (s+1+t)))
        (terminalMessage_supported w K width (s+1+t)) B
      have hg : transferStep w K width (terminalMessage w K width (s+1+t)) =
          terminalMessage w K width (s+1+(t+1)) := by
        simpa only [Nat.add_assoc] using terminalMessage_next w K width (s+1+t)
      exact reindex (congrArg (transferStep w K width) hg) hg C

private theorem fixed_lower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) : ∀ t,
    (terminalFixedEnvelope hw0 hw1 K width hK s t).lower =
      (terminalComparison hw0 hw1 K width hK s 1 0).lower
  | 0 => reindex_lower _ _ _
  | t+1 => (reindex_lower _ _ _).trans (fixed_lower hw0 hw1 K width hK s t)

private theorem fixed_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (s : Nat) : ∀ t,
    (terminalFixedEnvelope hw0 hw1 K width hK s t).upper =
      (terminalComparison hw0 hw1 K width hK s 1 0).upper
  | 0 => reindex_upper _ _ _
  | t+1 => (reindex_upper _ _ _).trans (fixed_upper hw0 hw1 K width hK s t)

private theorem bracket_mass {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {f g : RatPoly}
    (B : Bracket width f g) :
    B.lower*weightedMass w K width g ≤ weightedMass w K width f ∧
      weightedMass w K width f ≤ B.upper*weightedMass w K width g := by
  have hl := weightedMass_nonnegative hw0 hw1 K width hK B.lowerCertificate
  have hu := weightedMass_nonnegative hw0 hw1 K width hK B.upperCertificate
  have hp : weightedMass w K width (polyAdd f (polySmul (-B.lower) g)) ≈
      weightedMass w K width f + -(B.lower*weightedMass w K width g) :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (weightedMass_smul w K width _ _) (Q'.neg_mul_eqv _ _)))
  have hq : weightedMass w K width (polyAdd (polySmul B.upper g) (polySmul (-1) f)) ≈
      B.upper*weightedMass w K width g + -(weightedMass w K width f) :=
    Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' (weightedMass_smul w K width _ _)
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width _ _)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))
  exact ⟨Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hl (Q'.le_of_eqv hp)),
    Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hu (Q'.le_of_eqv hq))⟩

private theorem moment_reorder (a b f : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a (polyMul f f)) b)
      (polyMul (polyMul a b) (polyMul f f)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
    (by decide) (fun | 0 => a | 1 => b | _ => f)

private theorem local_floor (l d M C B : Q')
    (hd : d ≤ 1) (hlower : l*B ≤ M) (he : M + -C ≤ d*M) :
    ((1-d)*l)*B ≤ C := by
  have hf : (1-d)*M ≤ C := Q'.le_of_sub_nonneg
    (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le he) (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.add (.var 1) (.neg (.var 2)))))
        (.add (.var 2) (.neg (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))))
        (by decide) (fun | 0 => d | 1 => M | _ => C))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv (1-d) l B))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (1-d) hlower
      (Q'.sub_nonneg_of_le hd)) hf)

private theorem cost_from_envelope (l U d eta Z P B R : Q')
    (hZ : (0 : Q') ≤ Z) (hB : (0 : Q') ≤ B)
    (hd : (0 : Q') ≤ d) (heta : (0 : Q') ≤ eta)
    (hlP : l*Z ≤ P) (hPU : P ≤ U*Z) (hwidth : U-l ≤ eta*l)
    (hfloor : ((1-d)*l)*B ≤ R) :
    P*B + -(Z*R) ≤ (d+eta)*(P*B) := by
  let rho := (1-d)*l
  have hraw := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_right _ _ B hPU hB)
    (Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg_left _ _ Z hfloor hZ))
  have hpin : (U*Z)*B + -(Z*(rho*B)) ≈ (U-rho)*(Z*B) :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.var 1) (.mul (.var 3) (.var 2)))))
      (.mul (.add (.var 0) (.neg (.var 3))) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => U | 1 => Z | 2 => B | _ => rho)
  have hwidth' : U-rho ≤ (d+eta)*l := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))))
      (.add (.add (.var 0) (.neg (.var 2))) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => U | 1 => d | _ => l)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (d*l) hwidth)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (.mul (.add (.var 1) (.var 0)) (.var 2))
        (by decide) (fun | 0 => eta | 1 => d | _ => l))))
  have hlast : ((d+eta)*l)*(Z*B) ≤ (d+eta)*(P*B) := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ (d+eta)
      (Q'.mul_le_mul_of_nonneg_right _ _ B hlP hB) (Q'.zero_le_add _ _ hd heta)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => d+eta | 1 => l | 2 => Z | _ => B))) h
  exact Q'.le_trans' _ _ _ hraw (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ (Z*B) hwidth'
      (Q'.mul_nonneg _ _ hZ hB)) hlast))

/-- A local INITIAL original energy fraction controls the complete outgoing
cleared cost for every filter length, including zero transmitted norms.
The initial source, its center if any, and the original action stay fixed. -/
theorem original_block_cost_le_initial_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (s t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) {d : Q'}
    (hd0 : (0 : Q') ≤ d) (hd1 : d ≤ 1)
    (hlocal : energy w K width (terminalMessage w K width (s+1)) psi ≤
      d*weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width (s+1))
          (transferStep w K width (terminalMessage w K width (s+1)))) (polyMul psi psi))) :
    let A := terminalMessage w K width (s+1+t)
    let b := originalBlockTransfer w K width t
      (polyMul (terminalMessage w K width (s+1)) psi)
    clearedRayleighCost w K width A b ≤
      (d+comparisonEta hw0 hw1 width s)*
        (weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let a := terminalMessage w K width (s+1)
  let c := polyMul a psi
  let A := terminalMessage w K width (s+1+t)
  let b := originalBlockTransfer w K width t c
  let J := terminalFixedEnvelope hw0 hw1 K width hK s 0
  let l := (terminalComparison hw0 hw1 K width hK s 1 0).lower
  let U := (terminalComparison hw0 hw1 K width hK s 1 0).upper
  let rho := (1-d)*l
  have ha := terminalMessage_supported w K width (s+1)
  have hc : SupportedQuaternionBlocks (N width) c := supported_polyMul ha hp
  have hl : (0 : Q') < l := terminalComparison_lower_positive hw0 hw1 K width hK s 1 0
  have hM := (bracket_mass hw0 hw1 K width hK
    (multiplyBracket J ((terminalMessage_certificate hw0 hw1 K width hK (s+1)).mul
      (Certificate.square psi hp)))).1
  change J.lower*weightedMass w K width (polyMul (polyMul a (polyMul psi psi)) a) ≤
    weightedMass w K width
      (polyMul (polyMul a (polyMul psi psi)) (transferStep w K width a)) at hM
  rw [show J.lower = l from fixed_lower hw0 hw1 K width hK s 0] at hM
  have hMpin := weightedMass_congr w K width (moment_reorder a (transferStep w K width a) psi)
  have hBpin : weightedMass w K width (polyMul (polyMul a (polyMul psi psi)) a) ≈
      weightedMass w K width (polyMul c c) :=
    weightedMass_congr w K width (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 0))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => a | _ => psi))
  have hlower := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_eqv_congr_left l _ _ hBpin))
    (Q'.le_trans' _ _ _ hM (Q'.le_of_eqv hMpin))
  have hsource : rho*weightedMass w K width (polyMul c c) ≤
      weightedMass w K width (polyMul c (transferStep w K width c)) :=
    local_floor _ _ _ _ _ hd1 hlower hlocal
  have hrho : (0 : Q') ≤ rho :=
    Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hd1) (Q'.le_of_lt hl)
  have hfloor := sourceRayleigh_floor_persists hw0 hw1 K width hK hc hrho hsource t
  have hb := sourceRayleigh_supported w K width t hc
  let F := terminalFixedEnvelope hw0 hw1 K width hK s t
  have hbounds := bracket_mass hw0 hw1 K width hK
    (multiplyBracket F (terminalMessage_certificate hw0 hw1 K width hK (s+1+t)))
  rw [show (multiplyBracket F (terminalMessage_certificate hw0 hw1 K width hK (s+1+t))).lower = l
      from fixed_lower hw0 hw1 K width hK s t,
    show (multiplyBracket F (terminalMessage_certificate hw0 hw1 K width hK (s+1+t))).upper = U
      from fixed_upper hw0 hw1 K width hK s t] at hbounds
  exact cost_from_envelope l U d (comparisonEta hw0 hw1 width s) _ _ _ _
    (Q'.le_of_lt (terminalPair_positive hw0 hw1 K width hK (s+1+t) (s+1+t)))
    (weightedMass_nonnegative hw0 hw1 K width hK (Certificate.square b hb))
    hd0 (comparisonEta_nonnegative hw0 hw1 width s) hbounds.1 hbounds.2
    (terminalComparison_relative_width hw0 hw1 K width hK s 1 0) hfloor

private theorem energy_from_cost (D E F Q c epsilon gamma : Q')
    (hcost : D ≤ c*Q) (herror : Q'.abs (D + -(E+F)) ≤ epsilon*Q)
    (hdrift : Q'.abs F ≤ gamma*Q) : E ≤ ((c+epsilon)+gamma)*Q := by
  have he := Q'.le_trans' _ _ _ (Q'.neg_le_abs (D + -(E+F))) herror
  have hf := Q'.le_trans' _ _ _ (Q'.neg_le_abs F) hdrift
  have h := Q'.add_le_add (Q'.add_le_add hcost he) hf
  have hleft : (D + -(D + -(E+F))) + -F ≈ E :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.add (.var 0)
        (.neg (.add (.var 1) (.var 2)))))) (.neg (.var 2))) (.var 1)
      (by decide) (fun | 0 => D | 1 => E | _ => F)
  have hright : (c*Q+epsilon*Q)+gamma*Q ≈ ((c+epsilon)+gamma)*Q :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 3)))
        (.mul (.var 2) (.var 3)))
      (.mul (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
      (by decide) (fun | 0 => c | 1 => epsilon | 2 => gamma | _ => Q)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

/-- The transported local estimate reaches the GENUINE original energy of
the finite conditional ratio, using the already constructed reconstruction
onset and the literal signed drift. No conditional derivative/noise ceiling
is inserted. The two finite terminal errors remain explicit. -/
theorem original_block_ratio_energy_le_initial_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat)
    (hK : headCutoff w ≤ K) (s t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) {d : Q'}
    (hd0 : (0 : Q') ≤ d) (hd1 : d ≤ 1)
    (hlocal : energy w K width (terminalMessage w K width (s+1)) psi ≤
      d*weightedMass w K width
        (polyMul (polyMul (terminalMessage w K width (s+1))
          (transferStep w K width (terminalMessage w K width (s+1)))) (polyMul psi psi)))
    {epsilon : Q'} (he : (0 : Q') < epsilon) (k : Nat)
    (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k) :
    let A := terminalMessage w K width (s+1+t)
    let b := originalBlockTransfer w K width t
      (polyMul (terminalMessage w K width (s+1)) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK (s+1) t psi k
    weightedMass w K width (polyMul A A)*energy w K width A phi ≤
      (((d+comparisonEta hw0 hw1 width s)+epsilon)+
        comparisonEta hw0 hw1 width (s+t))*
        (weightedMass w K width (polyMul A (transferStep w K width A))*
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let A := terminalMessage w K width (s+1+t)
  let b := originalBlockTransfer w K width t
    (polyMul (terminalMessage w K width (s+1)) psi)
  let phi := blockConditionalRatio hw0 hw1 K width hK (s+1) t psi k
  let Q := weightedMass w K width (polyMul A (transferStep w K width A))*
    weightedMass w K width (polyMul b b)
  have hdepth : 1 ≤ s+1+t := by omega
  have herr := blockConditionalRatio_energy_error_relative_tolerance hw0 hw1
    K width hK (s+1) t hdepth hp epsilon he k hk
  have hd := blockConditionalRatio_boundaryDrift_abs_le hw0 hw1
    K width hK (s+1) t hdepth hp k
  have hindex : s+1+t-1 = s+t := by omega
  rw [hindex] at hd
  have hd' : Q'.abs (boundaryDrift w K width A phi) ≤
      comparisonEta hw0 hw1 width (s+t)*Q :=
    Q'.le_trans' _ _ _ hd (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
  exact energy_from_cost _ _ _ Q (d+comparisonEta hw0 hw1 width s)
    epsilon (comparisonEta hw0 hw1 width (s+t))
    (original_block_cost_le_initial_energy hw0 hw1 K width hK s t hp hd0 hd1 hlocal)
    herr hd'

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalEnergyTransport

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalEnergyTransport.terminalFixedEnvelope
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalEnergyTransport.original_block_cost_le_initial_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalEnergyTransport.original_block_ratio_energy_le_initial_energy
