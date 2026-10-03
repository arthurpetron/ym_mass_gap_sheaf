/-
# An original OWN-centered Young-cost budget at every terminal depth

For A=Tg_n, psi=F-OWNc_n and b=T(g_n psi), the endpoint cost is
Q=ell((A psi)^2), while S=ell(b^2) and E=ell(A^2) is the SAME even partition.
The already constructed cap16 certificate for the OWN-centered fundamental
square gives Q<=16E, without terminal-amplitude powers or a density inverse.
The actual full-action Young square then proves S/4<=G whenever S>=32a^2E.
That last original S/E lower bound remains an explicit unpaid input; no
gain floor, terminal overlap, changing-family estimate or survival is claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
import YMGap.Continuum.QuaternionHaarRelativePredictionFloor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
  (centeredMessage commutatorGain ownCenteredBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_middle_pin)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarWordDifference (weighted_order weighted_scale)
open YMGap.Continuum.QuaternionHaarRelativePredictionFloor (weighted_square_young)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage transferStep spatialWeight weightedMass
  sourceCharacter ownMean centeredMessage commutatorGain evenPartition

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (loop : SourceLoop width)

/-- The original endpoint A*(F-OWNc_n), not an independent surrogate. -/
def ownGainEndpoint : RatPoly :=
  polyMul (transferStep w K width (terminalMessage w K width n))
    (shifted (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop))

def ownGainSquare : Q' :=
  let b := centeredMessage w K width n (sourceCharacter width loop.edges 1)
    (ownMean hw0 hw1 K width hK n loop)
  weightedMass w K width (polyMul b b)

def ownGainYoungCost : Q' :=
  let u := ownGainEndpoint hw0 hw1 K width hK n loop
  weightedMass w K width (polyMul u u)

private theorem endpoint_supported :
    SupportedQuaternionBlocks (N width) (ownGainEndpoint hw0 hw1 K width hK n loop) :=
  supported_polyMul (transferStep_supported w K width (terminalMessage_supported w K width n))
    (shifted_supported (sourceCharacter_supported width loop.edges 1)
      (ownMean hw0 hw1 K width hK n loop))

private theorem message_supported :
    SupportedQuaternionBlocks (N width)
      (centeredMessage w K width n (sourceCharacter width loop.edges 1)
        (ownMean hw0 hw1 K width hK n loop)) := by
  unfold centeredMessage
  exact transferStep_supported w K width
    (supported_polyMul (terminalMessage_supported w K width n)
      (shifted_supported (sourceCharacter_supported width loop.edges 1)
        (ownMean hw0 hw1 K width hK n loop)))

private theorem capped_endpoint_square {blocks : Nat} {V A psi : RatPoly} {c : Q'}
    (PV : Certificate blocks V) (PA : Certificate blocks A)
    (Ppsi : SquareBound blocks psi c) :
    H blocks (polyMul V (polyMul (polyMul A psi) (polyMul A psi))) ≤
      c*H blocks (polyMul V (polyMul A A)) := by
  let R := polyMul V (polyMul A A)
  have h := weighted_order (PV.mul (PA.mul PA)) Ppsi.certificate
  have hl : RatPolyCoeffEqv (polyMul R (polyMul psi psi))
      (polyMul V (polyMul (polyMul A psi) (polyMul A psi))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => V | 1 => A | _ => psi)
  have hr : H blocks (polyMul R (cap c)) ≈ c*H blocks R :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks)
      ((RatPolyCoeffEqv.mul_comm R (cap c)).trans (cap_mul_left c R)))
      (YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul blocks c R)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (blocks := blocks) hl))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

/-- Q<=16E uses the SAME actual OWN center and full action, at every depth.
E is the even partition, not the original finite odd variance denominator. -/
theorem ownGainYoungCost_le_sixteen_evenPartition :
    ownGainYoungCost hw0 hw1 K width hK n loop ≤ 16*evenPartition w K width n := by
  let A := transferStep w K width (terminalMessage w K width n)
  have PA : Certificate (N width) A := by
    dsimp only [A]
    rw [terminalMessage_next]
    exact terminalMessage_certificate hw0 hw1 K width hK (n+1)
  have hbound := capped_endpoint_square
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK) PA
    (ownCenteredBound hw0 hw1 K width hK n loop)
  have he := evenPartition_middle_pin w K width n
  unfold ownGainYoungCost ownGainEndpoint weightedMass
  unfold weightedMass at he
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
    (Q'.mul_eqv_congr_left 16 _ _ (Q'.eqv_symm he)))

attribute [local irreducible] ownGainEndpoint ownGainSquare ownGainYoungCost

private theorem young_collect (s q j g a : Q') (h : 2*a*j ≤ (a*a)*q+s)
    (hg : g ≈ s+(-a)*j) : s-(a*a)*q ≤ 2*g := by
  have he : ((a*a)*q+s)-(2*a*j) ≈ 2*(s+(-a)*j)-(s-(a*a)*q) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 4) (.var 4)) (.var 1)) (.var 0))
        (.neg (.mul (.mul (.const 2) (.var 4)) (.var 2))))
      (.add (.mul (.const 2) (.add (.var 0) (.mul (.neg (.var 4)) (.var 2))))
        (.neg (.add (.var 0) (.neg (.mul (.mul (.var 4) (.var 4)) (.var 1))))))
      (by decide) (fun | 0 => s | 1 => q | 2 => j | _ => a)
  have ht := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hg)) (Q'.eqv_refl (-(s-(a*a)*q)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le h)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he ht)))

/-- Original full-action Young's square, with arbitrary signed reference a. -/
theorem own_gain_young_lower (a : Q') :
    ownGainSquare hw0 hw1 K width hK n loop -
        (a*a)*ownGainYoungCost hw0 hw1 K width hK n loop ≤
      2*commutatorGain w K width n (sourceCharacter width loop.edges 1)
        (ownMean hw0 hw1 K width hK n loop) a := by
  let V := spatialWeight w K width
  let b := centeredMessage w K width n (sourceCharacter width loop.edges 1)
    (ownMean hw0 hw1 K width hK n loop)
  let u := ownGainEndpoint hw0 hw1 K width hK n loop
  let s := H (N width) (polyMul V (polyMul b b))
  let q := H (N width) (polyMul V (polyMul u u))
  let j := H (N width) (polyMul V (polyMul u b))
  have hy : 2*a*j ≤ (a*a)*q+s := weighted_square_young
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK)
    (endpoint_supported hw0 hw1 K width hK n loop)
    (message_supported hw0 hw1 K width hK n loop) a
  have hp : RatPolyCoeffEqv (polyMul b (polyAdd b (polySmul (-a) u)))
      (polyAdd (polyMul b b) (polySmul (-a) (polyMul u b))) :=
    (RatPolyCoeffEqv.mul_add_right b b _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-a) b u).trans
          ((RatPolyCoeffEqv.mul_comm b u).smul (-a))))
  have hu : RatPolyCoeffEqv
      (polyMul (transferStep w K width (terminalMessage w K width n))
        (shifted (sourceCharacter width loop.edges 1) (ownMean hw0 hw1 K width hK n loop))) u := by
    dsimp only [u]
    unfold ownGainEndpoint
    exact RatPolyCoeffEqv.refl _
  have hgain := (RatPolyCoeffEqv.refl b).mul
    ((RatPolyCoeffEqv.refl b).add (hu.smul (-a)))
  have hg : commutatorGain w K width n (sourceCharacter width loop.edges 1)
      (ownMean hw0 hw1 K width hK n loop) a ≈ s+(-a)*j := by
    unfold commutatorGain weightedMass
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N width) (hgain.mul_left V))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N width) (hp.mul_left V))
        (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) V _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl s) (weighted_scale (N width) V (polyMul u b) (-a)))))
  have h := young_collect s q j
    (commutatorGain w K width n (sourceCharacter width loop.edges 1)
      (ownMean hw0 hw1 K width hK n loop) a) a hy hg
  unfold ownGainSquare ownGainYoungCost weightedMass
  exact h

/-- The only unpaid input is a genuine original S/E floor. The cost side
is constructed above; no gain inequality is assumed. No sign of a is needed. -/
theorem own_gain_relative_lower (a : Q')
    (hS : 32*(a*a)*evenPartition w K width n ≤ ownGainSquare hw0 hw1 K width hK n loop) :
    (Q'.mkPos 1 4 (by decide))*ownGainSquare hw0 hw1 K width hK n loop ≤
      commutatorGain w K width n (sourceCharacter width loop.edges 1)
        (ownMean hw0 hw1 K width hK n loop) a := by
  let S := ownGainSquare hw0 hw1 K width hK n loop
  let Q := ownGainYoungCost hw0 hw1 K width hK n loop
  let E := evenPartition w K width n
  let G := commutatorGain w K width n (sourceCharacter width loop.edges 1)
    (ownMean hw0 hw1 K width hK n loop) a
  have hscale : (a*a)*(16*E) ≈ HalfPow.half*(32*(a*a)*E) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.const 16) (.var 1)))
      (.mul (.const 16) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => a | _ => E))
      (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.var 2) (.mul (.mul (.const 32) (.mul (.var 0) (.var 0))) (.var 1)))
          (.mul (.mul (.var 2) (.const 32)) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
          (by decide) (fun | 0 => a | 1 => E | _ => HalfPow.half))
        (Q'.mul_eqv_congr_right _ _ _ (by decide : HalfPow.half*32 ≈ (16 : Q')))))
  have hQ : (a*a)*Q ≤ HalfPow.half*S :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (a*a)
      (ownGainYoungCost_le_sixteen_evenPartition hw0 hw1 K width hK n loop)
      (SumOfSquares.q_mul_self_nonneg a))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscale)
        (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hS HalfPow.half_nonneg))
  have hidentity : HalfPow.half*S ≈ S+ -(HalfPow.half*S) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq (.var 0)
        (.add (.add (.var 0) (.var 0)) (.neg (.var 0)))
        (by decide) (fun _ => HalfPow.half*S))
      (Q'.add_eqv_congr' (ExpNeg.two_halves S) (Q'.eqv_refl _))
  have hhalf : HalfPow.half*S ≤ 2*G :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentity)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left S _ _ (Q'.neg_le_neg hQ))
        (own_gain_young_lower hw0 hw1 K width hK n loop a))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hhalf HalfPow.half_nonneg
  have hl : HalfPow.half*(HalfPow.half*S) ≈ (Q'.mkPos 1 4 (by decide))*S :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ S (by decide : HalfPow.half*HalfPow.half ≈ Q'.mkPos 1 4 (by decide)))
  have hr : HalfPow.half*(2*G) ≈ G :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ G (by decide : HalfPow.half*2 ≈ (1 : Q')))
        (Q'.one_mul_eqv G))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hr))

end YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget.ownGainEndpoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget.ownGainSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget.ownGainYoungCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget.ownGainYoungCost_le_sixteen_evenPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget.own_gain_young_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget.own_gain_relative_lower
