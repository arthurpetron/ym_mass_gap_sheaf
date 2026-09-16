/-
# Constructive completion of a bounded ordinary-Haar polynomial map

A dense map preserving subtraction and satisfying a rational squared-norm
bound acts termwise on the existing GNS Cauchy representatives. Its explicit
input tolerance is epsilon * invSucc ((C*C).num.toNat). The old rational
budget lemma proves the Cauchy and null-descent estimates; no choice of
representatives, new completion carrier, reciprocal, or diagonal is needed.

The completed map agrees exactly with the dense map and retains its C*C
norm and distance bounds. The polynomial adapter uses the actual ordinary
quaternion-Haar form, with constant weight one. It does not assert cutoff
convergence, positivity or symmetry of an operator, stationarity, an OS
identification, or a spectral gap.
-/

import YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.SU2QuaternionHaarBoundedCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-- Dense algebraic data and the supplied finite norm estimate. The completion
and its estimates are constructed below, not fields of this input. -/
structure BoundedMap (D : GNSData) (C : Q') where
  toFun : D.V → D.V
  nonnegative : (0 : Q') ≤ C
  map_sub : ∀ x y, D.veq (toFun (D.sub x y)) (D.sub (toFun x) (toFun y))
  norm_bound : ∀ x, D.B (toFun x) (toFun x) ≤ (C*C)*D.B x x

/-- A concrete rational tolerance, defined even when C is zero. -/
def tolerance (C epsilon : Q') : Q' := epsilon * Q'.invSucc (C*C).num.toNat

theorem tolerance_positive (C epsilon : Q') (he : (0 : Q') < epsilon) :
    (0 : Q') < tolerance C epsilon := Q'.mul_pos he (Q'.invSucc_pos _)

namespace BoundedMap

variable {D : GNSData} {C : Q'} (T : BoundedMap D C)

include T in
theorem square_nonnegative : (0 : Q') ≤ C*C :=
  Q'.mul_nonneg _ _ T.nonnegative T.nonnegative

theorem distance_bound (x y : D.V) :
    D.distSqQ (T.toFun x) (T.toFun y) ≤ (C*C)*D.distSqQ x y :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (D.B_diag_congr (T.map_sub x y)))
    (T.norm_bound (D.sub x y))

private theorem tolerance_bound (epsilon : Q') (he : (0 : Q') < epsilon)
    (x y : D.V) (h : D.distSqQ x y ≤ tolerance C epsilon) :
    D.distSqQ (T.toFun x) (T.toFun y) ≤ epsilon :=
  Q'.le_trans' _ _ _ (T.distance_bound x y)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h T.square_nonnegative)
      (ExpNeg.mul_le_of_mul_invSucc_toNat (C*C) epsilon
        T.square_nonnegative (Q'.le_of_lt he)))

/-- Termwise action with the explicit inherited input modulus. -/
def mapCauchy (X : CauchyGNS D) : CauchyGNS D where
  seq n := T.toFun (X.seq n)
  modulus epsilon := X.modulus (tolerance C epsilon)
  isCauchy := fun epsilon he p q hp hq => T.tolerance_bound epsilon he _ _
    (X.isCauchy _ (tolerance_positive C epsilon he) p q hp hq)

theorem mapCauchy_modulus (X : CauchyGNS D) (epsilon : Q') :
    (T.mapCauchy X).modulus epsilon = X.modulus (tolerance C epsilon) := rfl

/-- The same explicit tolerance transports null equivalence. -/
theorem mapCauchy_null {X Y : CauchyGNS D} (h : CauchyNull D X Y) :
    CauchyNull D (T.mapCauchy X) (T.mapCauchy Y) := by
  intro epsilon he
  obtain ⟨n, hn⟩ := h (tolerance C epsilon) (tolerance_positive C epsilon he)
  exact ⟨n, fun k hk => T.tolerance_bound epsilon he _ _ (hn k hk)⟩

/-- Actual map on the already constructed GNS completion. -/
def completionMap : GNSCompletionSpace D → GNSCompletionSpace D :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid D) (T.mapCauchy X))
    (fun _ _ h => Quotient.sound (T.mapCauchy_null h))

theorem completionMap_mk (X : CauchyGNS D) :
    T.completionMap (Quotient.mk (cauchySetoid D) X) =
      Quotient.mk (cauchySetoid D) (T.mapCauchy X) := rfl

/-- No rescaling changes the dense map: its embedding pin is exact. -/
theorem completionMap_embed (x : D.V) :
    T.completionMap (embedV D x) = embedV D (T.toFun x) := rfl

/-- The SAME rational squared-norm constant passes to all completed vectors. -/
theorem completionMap_norm_bound (x : GNSCompletionSpace D) :
    CReal.RCle (D.cinnerCompl (T.completionMap x) (T.completionMap x))
      (CReal.RCscale (C*C) (D.cinnerCompl x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  change CReal.leEv (D.cinnerRep (T.mapCauchy X) (T.mapCauchy X))
    (CReal.mul (CReal.ofQ' (C*C)) (D.cinnerRep X X))
  exact CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_ofQ'CauchySeq _ (D.cInnerQCauchy (T.mapCauchy X) (T.mapCauchy X)))
    (CReal.convergesTo_const_mul (CReal.ofQ' (C*C))
      (CReal.convergesTo_ofQ'CauchySeq _ (D.cInnerQCauchy X X)))
    (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (T.norm_bound (X.seq n))
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))

/-- The sharp Lipschitz estimate also holds between arbitrary completion points. -/
theorem completionMap_distance_bound (x y : GNSCompletionSpace D) :
    CReal.RCle
      (D.cinnerCompl (D.cSub (T.completionMap x) (T.completionMap y))
        (D.cSub (T.completionMap x) (T.completionMap y)))
      (CReal.RCscale (C*C) (D.cinnerCompl (D.cSub x y) (D.cSub x y))) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  change CReal.leEv
    (CReal.ofQ'CauchySeq _ (D.distSqSeqCauchy (T.mapCauchy X) (T.mapCauchy Y)))
    (CReal.mul (CReal.ofQ' (C*C)) (CReal.ofQ'CauchySeq _ (D.distSqSeqCauchy X Y)))
  exact CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy (T.mapCauchy X) (T.mapCauchy Y)))
    (CReal.convergesTo_const_mul (CReal.ofQ' (C*C))
      (CReal.convergesTo_ofQ'CauchySeq _ (D.distSqSeqCauchy X Y)))
    (fun n => CReal.leEv_of_le (fun k => Q'.le_trans' _ _ _ (T.distance_bound (X.seq n) (Y.seq n))
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.invSucc_pos k)))))

end BoundedMap

/-- Ordinary product-quaternion Haar GNS, not a reflected OS form. -/
def haarData (blocks : Nat) : GNSData :=
  weightedGNSData blocks polyOne (Certificate.one blocks)

theorem haarData_pair (blocks : Nat) (p q : (haarData blocks).V) :
    (haarData blocks).B p q ≈ quaternionHaar blocks (polyMul p.val q.val) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_one _)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') :
    SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- Convert a supported algebraic polynomial map and its actual Haar square
estimate into the constructive completion consumer. Additivity and scalar
compatibility are coefficient-sensitive; no quotient compatibility is assumed. -/
def ofPolynomial (blocks : Nat) (T : RatPoly → RatPoly) (C : Q') (hC : (0 : Q') ≤ C)
    (hsupport : ∀ {p}, SupportedQuaternionBlocks blocks p → SupportedQuaternionBlocks blocks (T p))
    (hadd : ∀ p q, SupportedQuaternionBlocks blocks p → SupportedQuaternionBlocks blocks q →
      RatPolyCoeffEqv (T (polyAdd p q)) (polyAdd (T p) (T q)))
    (hsmul : ∀ c p, SupportedQuaternionBlocks blocks p →
      RatPolyCoeffEqv (T (polySmul c p)) (polySmul c (T p)))
    (hnorm : ∀ p, SupportedQuaternionBlocks blocks p →
      quaternionHaar blocks (polyMul (T p) (T p)) ≤ (C*C)*quaternionHaar blocks (polyMul p p)) :
    BoundedMap (haarData blocks) C where
  toFun p := ⟨T p.val, hsupport p.property⟩
  nonnegative := hC
  map_sub := by
    intro p q
    change RatPolyCoeffEqv (T (polyAdd p.val (polySmul (-1) q.val)))
      (polyAdd (T p.val) (polySmul (-1) (T q.val)))
    exact (hadd p.val (polySmul (-1) q.val) p.property (support_smul q.property (-1))).trans
      ((RatPolyCoeffEqv.refl (T p.val)).add (hsmul (-1) q.val q.property))
  norm_bound := by
    intro p
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (haarData_pair blocks ⟨T p.val, hsupport p.property⟩ ⟨T p.val, hsupport p.property⟩))
      (Q'.le_trans' _ _ _ (hnorm p.val p.property)
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (haarData_pair blocks p p)))))

end YMGap.Continuum.SU2QuaternionHaarBoundedCompletion

#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.tolerance_positive
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.distance_bound
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.mapCauchy
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.mapCauchy_modulus
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.mapCauchy_null
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.completionMap
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.completionMap_mk
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.completionMap_embed
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.completionMap_norm_bound
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.BoundedMap.completionMap_distance_bound
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.haarData
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.haarData_pair
#print axioms YMGap.Continuum.SU2QuaternionHaarBoundedCompletion.ofPolynomial
