/-
# Explicit one-star parity on the original weighted slice

Every supported polynomial is the sum of its explicit even and odd parts
under ONE full spatial vertex-center sign. The parts are orthogonal for the
original finite marginal V*g_n*g_(n+1). The existing six-factor temporal
energy bound applies to the constructed odd part, not to the even remainder.

No all-stars decomposition, gauge-invariant-sector bound, limiting spectral
gap, or continuum statement is asserted. All finite action factors remain.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStar
open YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarEnergy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionWeightedProductBlockErasure (haar_product_zero_of_sign)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_add)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

def evenPart (width : Nat) (v : Z4Vertex) (f : RatPoly) : RatPoly :=
  polySmul HalfPow.half (polyAdd f (starSign width v f))

def oddPart (width : Nat) (v : Z4Vertex) (f : RatPoly) : RatPoly :=
  polySmul HalfPow.half (polyAdd f (polyNeg (starSign width v f)))

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

theorem evenPart_supported (width : Nat) (v : Z4Vertex) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (evenPart width v f) :=
  support_smul (supported_add hf (starSign_supported width v hf)) _

theorem oddPart_supported (width : Nat) (v : Z4Vertex) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (oddPart width v f) :=
  support_smul (supported_add hf (support_neg (starSign_supported width v hf))) _

/-- Exact finite polynomial decomposition, before any quotient or integration. -/
theorem decomposition (width : Nat) (v : Z4Vertex) (f : RatPoly) :
    RatPolyCoeffEqv (polyAdd (evenPart width v f) (oddPart width v f)) f := by
  have h : RatPolyCoeffEqv
      (polyAdd (polyAdd f (starSign width v f)) (polyAdd f (polyNeg (starSign width v f))))
      (polyAdd f f) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.neg (.var 1))))
      (.add (.var 0) (.var 0)) (by decide) (fun | 0 => f | _ => starSign width v f)
  exact (RatPolyCoeffEqv.smul_add HalfPow.half _ _).symm.trans
    ((h.smul HalfPow.half).trans ((RatPolyCoeffEqv.smul_add HalfPow.half f f).trans
      ((RatPolyCoeffEqv.add_smul_same HalfPow.half HalfPow.half f).trans
        ((RatPolyCoeffEqv.smul_coefficient (by decide : HalfPow.half+HalfPow.half ≈ 1) f).trans
          (RatPolyCoeffEqv.one_smul f)))))

theorem evenPart_even (width : Nat) (v : Z4Vertex) (f : RatPoly) :
    RatPolyCoeffEqv (starSign width v (evenPart width v f)) (evenPart width v f) := by
  have h := starSign_smul width v HalfPow.half (polyAdd f (starSign width v f))
  rw [starSign_add] at h
  exact h.trans ((((RatPolyCoeffEqv.refl (starSign width v f)).add
    (starSign_involutive width v f)).trans (RatPolyCoeffEqv.add_comm _ _)).smul HalfPow.half)

private theorem starSign_neg (width : Nat) (v : Z4Vertex) (f : RatPoly) :
    starSign width v (polyNeg f) = polyNeg (starSign width v f) :=
  signSelectedPolynomial_neg _ _ f

private theorem smul_neg (c : Q') : ∀ p : RatPoly,
    RatPolyCoeffEqv (polySmul c (polyNeg p)) (polyNeg (polySmul c p))
  | [] => .refl []
  | t :: rest => by
      intro weight
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_neg_eqv c t.2))
        (smul_neg c rest weight)

theorem oddPart_odd (width : Nat) (v : Z4Vertex) (f : RatPoly) :
    RatPolyCoeffEqv (starSign width v (oddPart width v f)) (polyNeg (oddPart width v f)) := by
  have h := starSign_smul width v HalfPow.half (polyAdd f (polyNeg (starSign width v f)))
  rw [starSign_add, starSign_neg] at h
  have hs : RatPolyCoeffEqv (polyAdd (starSign width v f) (polyNeg f))
      (polyNeg (polyAdd f (polyNeg (starSign width v f)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 1) (.neg (.var 0))) (.neg (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => f | _ => starSign width v f)
  exact h.trans ((((RatPolyCoeffEqv.refl (starSign width v f)).add
    (RatPolyCoeffEqv.neg (starSign_involutive width v f))).smul HalfPow.half).trans
      ((hs.smul HalfPow.half).trans (smul_neg HalfPow.half _)))

private theorem marginal_invariant (w : Q') (K width : Nat) (v : Z4Vertex) (n : Nat) :
    RatPolyCoeffEqv (starSign width v (marginalWeight w K width n))
      (marginalWeight w K width n) :=
  (starSign_mul width v _ _).trans
    ((endpointWeight_starSign w K width v n).mul (terminalMessage_starSign w K width v (n+1)))

/-- Orthogonality is on the original V*g_n*g_(n+1) marginal. -/
theorem parts_orthogonal (w : Q') (K width : Nat) (v : Z4Vertex) (n : Nat) (f : RatPoly) :
    marginalPair w K width n (evenPart width v f) (oddPart width v f) ≈ 0 := by
  let e := evenPart width v f
  let o := oddPart width v f
  let nu := marginalWeight w K width n
  have hb : RatPolyCoeffEqv (starSign width v (polyMul nu e)) (polyMul nu e) :=
    (starSign_mul width v _ _).trans
      ((marginal_invariant w K width v n).mul (evenPart_even width v f))
  have hz := haar_product_zero_of_sign (N width) (coordinateSelector width v)
    o (polyMul nu e) (oddPart_odd width v f) hb
  exact Q'.eqv_trans _ _ _ (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => nu | 1 => e | _ => o))) hz

/-- Pythagoras preserves the actual finite marginal and signed cross terms. -/
theorem marginal_norm_split (w : Q') (K width : Nat) (v : Z4Vertex) (n : Nat) (f : RatPoly) :
    marginalPair w K width n f f ≈
      marginalPair w K width n (evenPart width v f) (evenPart width v f) +
      marginalPair w K width n (oddPart width v f) (oddPart width v f) := by
  let e := evenPart width v f
  let o := oddPart width v f
  let nu := marginalWeight w K width n
  have hd := decomposition width v f
  have hs : RatPolyCoeffEqv (polyMul f f)
      (polyAdd (polyAdd (polyMul e e) (polyMul o o))
        (polyAdd (polyMul e o) (polyMul e o))) :=
    (hd.mul hd).symm.trans (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => e | _ => o))
  have hz := parts_orthogonal w K width v n f
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hs.mul_left nu))
    (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) nu _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (haar_weighted_add (N width) nu _ _)
        (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) nu _ _) (Q'.add_eqv_congr' hz hz)))
        (poly_identity_of_normal_eq (.add (.var 0) (.add (.const 0) (.const 0)))
          (.var 0) (by decide) (fun _ => _))))

/-- The previously proved charged-sector estimate now applies to a constructed
part of every supported input. No estimate is supplied for its even part. -/
theorem oddPart_six_energy_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (v : Z4Vertex) (depth : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    (headFloor w)^6 *
        weightedMass w K width (polyMul
          (polyMul (terminalMessage w K width depth) (terminalMessage w K width (depth+1)))
          (polyMul (oddPart width v f) (oddPart width v f))) ≤
      (prefixCap w)^6 * energy w K width (terminalMessage w K width depth) (oddPart width v f) :=
  terminal_starOdd_six_energy_floor hw0 hw1 K width hK v depth
    (oddPart_supported width v hf) (oddPart_odd width v f)

end YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.evenPart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.oddPart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.evenPart_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.oddPart_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.decomposition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.evenPart_even
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.oddPart_odd
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.parts_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.marginal_norm_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialVertexStarParity.oddPart_six_energy_floor
