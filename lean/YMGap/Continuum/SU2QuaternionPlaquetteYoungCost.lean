/-
# Exact Young cost of one fundamental plaquette

This consumes the actual fundamental and square product-heat images only at
the supported insertions required by the three-moment formula.  It does not
upgrade supported-Haar equivalence to polynomial equality.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
import YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments

namespace YMGap.Continuum.SU2QuaternionPlaquetteYoungCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOrientedWordSelection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPlaquette
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Channel form of the exact one-ended cost.  Here `a` is the actual source;
no independence, pointwise bound, or interacting-law comparison is assumed. -/
theorem singleEndedCost_plaquette_channels
    (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (a b c d : Nat) (ids rest : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (hp : ids.Perm (a::b::c::d::rest))
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    let f := characterPolynomial (word a b c d false false true true).scalar 1
    let chi2 := characterPolynomial (word a b c d false false true true).scalar 2
    singleEndedCost n w K ids q f ≈
      H n (polyMul (polyMul q q) (polyMul f f)) +
      ((H n (polyMul (polyMul q q) polyOne) +
          qpow w 32 * H n (polyMul (polyMul q q) chi2)) +
        -((2 : Q') * (qpow w 12 *
          H n (polyMul (polyMul (polyMul q q) f) f)))) := by
  dsimp only
  let f := characterPolynomial (word a b c d false false true true).scalar 1
  let chi2 := characterPolynomial (word a b c d false false true true).scalar 2
  have hf : SupportedQuaternionBlocks n f :=
    word_supported (hids a (hp.mem_iff.mpr (by simp)))
      (hids b (hp.mem_iff.mpr (by simp)))
      (hids c (hp.mem_iff.mpr (by simp)))
      (hids d (hp.mem_iff.mpr (by simp))) false false true true 1
  have hq2 : SupportedQuaternionBlocks n (polyMul q q) := supported_polyMul hq hq
  have hq2f : SupportedQuaternionBlocks n (polyMul (polyMul q q) f) :=
    supported_polyMul hq2 hf
  have hm := singleEndedCost_eq_moments n w K ids hn hids hq hf
  have hsquare := productMap_plaquetteSquare_of_perm n w K hK
    a b c d ids rest hn hids hp
  have hfund := productMap_plaquette_of_perm n w K (by omega)
    a b c d ids rest hn hids hp
  have hsecond0 := hsquare (polyMul q q) hq2
  have hsecond1 : H n (polyMul (polyMul q q)
      (polyAdd polyOne (polySmul (qpow w 32) chi2))) ≈
      H n (polyMul (polyMul q q) polyOne) +
        qpow w 32 * H n (polyMul (polyMul q q) chi2) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right n (polyMul q q)
      polyOne (polySmul (qpow w 32) chi2))
      (Q'.add_eqv_congr_left _ _ _
        (quaternionHaar_polyMul_smul_right n (qpow w 32) (polyMul q q) chi2))
  have hsecond := Q'.eqv_trans _ _ _ hsecond0 hsecond1
  have hthird := Q'.eqv_trans _ _ _
    (hfund (polyMul (polyMul q q) f) hq2f)
    (quaternionHaar_polyMul_smul_right n (qpow w 12)
      (polyMul (polyMul q q) f) f)
  exact Q'.eqv_trans _ _ _ hm
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr'
        hsecond
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left 2 _ _ hthird))))

/-- Collected two-moment form of the same exact cost.  In particular, the
only source quantities left are its Haar square and its square weighted by
the original fundamental plaquette square. -/
theorem singleEndedCost_plaquette_collected
    (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (a b c d : Nat) (ids rest : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (hp : ids.Perm (a::b::c::d::rest))
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    let f := characterPolynomial (word a b c d false false true true).scalar 1
    singleEndedCost n w K ids q f ≈
      ((1 : Q') - qpow w 32) * H n (polyMul (polyMul q q) polyOne) +
      ((1 : Q') + qpow w 32 - (2 : Q') * qpow w 12) *
        H n (polyMul (polyMul q q) (polyMul f f)) := by
  dsimp only
  let p := (word a b c d false false true true).scalar
  let f := characterPolynomial p 1
  let chi2 := characterPolynomial p 2
  let A := H n (polyMul (polyMul q q) polyOne)
  let F := H n (polyMul (polyMul q q) (polyMul f f))
  have hcenter : RatPolyCoeffEqv chi2
      (polyAdd (polyMul f f) (polySmul (-1) polyOne)) := by
    have hpad0 : RatPolyCoeffEqv chi2
        (polyAdd (polyAdd polyOne chi2) (polyMul (cap (-1)) polyOne)) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (.var 0) (.add (.add (.var 1) (.var 0))
          (.mul (.const (-1)) (.var 1))) (by decide)
        (fun | 0 => chi2 | _ => polyOne)
    have hpad : RatPolyCoeffEqv chi2
        (polyAdd (polyAdd polyOne chi2) (polySmul (-1) polyOne)) :=
      hpad0.trans ((RatPolyCoeffEqv.refl _).add (cap_mul_left (-1) polyOne))
    exact hpad.trans
      ((first_character_square p).symm.add
        (RatPolyCoeffEqv.refl (polySmul (-1) polyOne)))
  have hnegative :
      H n (polyMul (polyMul q q) (polySmul (-1) polyOne)) ≈ -A := by
    exact Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_smul_right n (-1) (polyMul q q) polyOne)
      (poly_identity_of_normal_eq
        (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => A))
  have hchi : H n (polyMul (polyMul q q) chi2) ≈ F + -A := by
    exact Q'.eqv_trans _ _ _
      (haar_of_coeff ((RatPolyCoeffEqv.refl (polyMul q q)).mul hcenter))
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_add_right n (polyMul q q)
          (polyMul f f) (polySmul (-1) polyOne))
        (Q'.add_eqv_congr_left _ _ _ hnegative))
  have hchannels := singleEndedCost_plaquette_channels n w K hK
    a b c d ids rest hn hids hp q hq
  have hassoc :
      H n (polyMul (polyMul (polyMul q q) f) f) ≈ F :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc (polyMul q q) f f)
  have hlast :
      -((2 : Q') * (qpow w 12 *
        H n (polyMul (polyMul (polyMul q q) f) f))) ≈
      -((2 : Q') * (qpow w 12 * F)) :=
    Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _
      (Q'.mul_eqv_congr_left (qpow w 12) _ _ hassoc))
  exact Q'.eqv_trans _ _ _ hchannels
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left F _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr_left A _ _
            (Q'.mul_eqv_congr_left (qpow w 32) _ _ hchi))
          hlast))
      (poly_identity_of_normal_eq
        (.add (.var 1)
          (.add
            (.add (.var 0) (.mul (.var 2) (.add (.var 1) (.neg (.var 0)))))
            (.neg (.mul (.const 2) (.mul (.var 3) (.var 1))))))
        (.add
          (.mul (.add (.const 1) (.neg (.var 2))) (.var 0))
          (.mul
            (.add (.add (.const 1) (.var 2))
              (.neg (.mul (.const 2) (.var 3)))) (.var 1)))
        (by decide)
        (fun | 0 => A | 1 => F | 2 => qpow w 32 | _ => qpow w 12)))

/-- The source-Young identity with the plaquette channel cost made explicit.
The favorable source-increment term is retained exactly. -/
theorem four_mul_sourceEnergy_add_increment_eq_plaquette_channels
    (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (a b c d : Nat) (ids rest : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (hp : ids.Perm (a::b::c::d::rest))
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    let f := characterPolynomial (word a b c d false false true true).scalar 1
    let chi2 := characterPolynomial (word a b c d false false true true).scalar 2
    (4 : Q') * sourceEnergy n w K ids q f + sourceIncrementCost n w K ids q f ≈
      (2 : Q') *
        (H n (polyMul (polyMul q q) (polyMul f f)) +
        ((H n (polyMul (polyMul q q) polyOne) +
            qpow w 32 * H n (polyMul (polyMul q q) chi2)) +
          -((2 : Q') * (qpow w 12 *
            H n (polyMul (polyMul (polyMul q q) f) f))))) := by
  dsimp only
  let f := characterPolynomial (word a b c d false false true true).scalar 1
  have hf : SupportedQuaternionBlocks n f :=
    word_supported (hids a (hp.mem_iff.mpr (by simp)))
      (hids b (hp.mem_iff.mpr (by simp)))
      (hids c (hp.mem_iff.mpr (by simp)))
      (hids d (hp.mem_iff.mpr (by simp))) false false true true 1
  exact Q'.eqv_trans _ _ _
    (four_mul_sourceEnergy_add_increment_eq_two_singleEnded
      n w K ids hids hq hf)
    (Q'.mul_eqv_congr_left 2 _ _
      (singleEndedCost_plaquette_channels n w K hK
        a b c d ids rest hn hids hp q hq))

/-- Collected `4E + D = 2J`, retaining the favorable increment correction. -/
theorem four_mul_sourceEnergy_add_increment_eq_plaquette_collected
    (n : Nat) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (a b c d : Nat) (ids rest : List Nat) (hn : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) (hp : ids.Perm (a::b::c::d::rest))
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    let f := characterPolynomial (word a b c d false false true true).scalar 1
    (4 : Q') * sourceEnergy n w K ids q f + sourceIncrementCost n w K ids q f ≈
      (2 : Q') *
        (((1 : Q') - qpow w 32) * H n (polyMul (polyMul q q) polyOne) +
        ((1 : Q') + qpow w 32 - (2 : Q') * qpow w 12) *
          H n (polyMul (polyMul q q) (polyMul f f))) := by
  dsimp only
  let f := characterPolynomial (word a b c d false false true true).scalar 1
  have hf : SupportedQuaternionBlocks n f :=
    word_supported (hids a (hp.mem_iff.mpr (by simp)))
      (hids b (hp.mem_iff.mpr (by simp)))
      (hids c (hp.mem_iff.mpr (by simp)))
      (hids d (hp.mem_iff.mpr (by simp))) false false true true 1
  exact Q'.eqv_trans _ _ _
    (four_mul_sourceEnergy_add_increment_eq_two_singleEnded
      n w K ids hids hq hf)
    (Q'.mul_eqv_congr_left 2 _ _
      (singleEndedCost_plaquette_collected n w K hK
        a b c d ids rest hn hids hp q hq))

end YMGap.Continuum.SU2QuaternionPlaquetteYoungCost

#print axioms YMGap.Continuum.SU2QuaternionPlaquetteYoungCost.singleEndedCost_plaquette_channels
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteYoungCost.singleEndedCost_plaquette_collected
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteYoungCost.four_mul_sourceEnergy_add_increment_eq_plaquette_channels
#print axioms YMGap.Continuum.SU2QuaternionPlaquetteYoungCost.four_mul_sourceEnergy_add_increment_eq_plaquette_collected
