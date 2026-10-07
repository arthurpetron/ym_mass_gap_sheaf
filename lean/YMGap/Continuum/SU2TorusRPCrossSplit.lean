/-
# Torus RP assembly (d3g): the split crossing plaquette is a sum of Θ-symmetric squares

A crossing plaquette with base on the cut has the word `U₁ · P · U₂* · P'*`, where `U₁` and `U₂` are crossing
temporal links, `P` is the positive-half spatial link and `P' = Θ(P)`. After splitting each crossing link as
`Uᵢ = (Θ Bᵢ)* · Bᵢ`, with `Bᵢ` in the positive half and `Θ Bᵢ` its shift, the word is
  `W = ((sB₁* B₁) P) ((sB₂* B₂)* sP*)`.
* `cross_split_word`: `Re W ≅ dot (sY) Y` with `Y = (B₁ P) B₂*` and `sY = (sB₁ sP) sB₂*` (no `decide`; only
  associativity, `conj_mul`, `conj_conj`, cyclicity of `Re`, and symmetry of `dot`).
* `rpk_cross_split`: with `sX = shQ a X`, `T_K(Re W)` is an RPK whenever `Y` is supported on the positive half.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: carrying out the split on the concrete torus integrand and
the final instantiation).
-/

import YMGap.Continuum.SU2TorusRPAssembly

namespace YMGap.Continuum.SU2TorusRPCrossSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open PolyQuaternion (mul conj)
open YMGap.Continuum.SU2TorusRPWord (dot conj_mul conj_conj scalar_comm scalar_mul_conj qassoc qmul qrefl qtrans qsymm)
open YMGap.Continuum.SU2TorusRPKernel (shQ shQ_mul shQ_conj SupQ rpk_TK)
open YMGap.Continuum.SU2TorusRPCore (RPK)
open YMGap.Continuum.SU2WilsonCharacterPower (wilsonPoly)
open YMGap.Continuum.SU2WilsonActivity (wilsonA)

local infix:50 " ≅ " => RatPolyCoeffEqv
local infix:50 " ≅q " => PolyQuaternionCoeffEqv

theorem dot_comm (X Y : PolyQuaternion) : dot X Y ≅ dot Y X :=
  RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_comm _ _) (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_comm _ _)
    (RatPolyCoeffEqv.add (RatPolyCoeffEqv.mul_comm _ _) (RatPolyCoeffEqv.mul_comm _ _)))

theorem cross_split_word (B1 P B2 sB1 sP sB2 : PolyQuaternion) :
    (mul (mul (mul (conj sB1) B1) P) (mul (conj (mul (conj sB2) B2)) (conj sP))).scalar ≅
      dot (mul (mul sB1 sP) (conj sB2)) (mul (mul B1 P) (conj B2)) := by
  -- conj(sB₂* B₂) ≅ B₂* sB₂
  have h1 : conj (mul (conj sB2) B2) ≅q mul (conj B2) sB2 :=
    qtrans (conj_mul _ _) (qmul (qrefl _) (conj_conj sB2))
  -- W ≅ sB₁* · R
  have h2 : mul (mul (mul (conj sB1) B1) P) (mul (conj (mul (conj sB2) B2)) (conj sP)) ≅q
      mul (conj sB1) (mul (mul B1 P) (mul (mul (conj B2) sB2) (conj sP))) :=
    qtrans (qmul (qassoc _ _ _) (qmul h1 (qrefl _))) (qassoc _ _ _)
  -- R · sB₁* ≅ Y · Z
  have h3 : mul (mul (mul B1 P) (mul (mul (conj B2) sB2) (conj sP))) (conj sB1) ≅q
      mul (mul (mul B1 P) (conj B2)) (mul (mul sB2 (conj sP)) (conj sB1)) :=
    qtrans (qmul (qtrans (qmul (qrefl _) (qassoc _ _ _)) (qsymm (qassoc _ _ _))) (qrefl _)) (qassoc _ _ _)
  -- Z ≅ conj(sY)
  have h4 : mul (mul sB2 (conj sP)) (conj sB1) ≅q conj (mul (mul sB1 sP) (conj sB2)) := by
    refine qsymm (qtrans (conj_mul _ _) ?_)
    refine qtrans (qmul (conj_conj sB2) (conj_mul _ _)) (qsymm (qassoc _ _ _))
  refine (h2.scalar).trans ((scalar_comm _ _).trans ?_)
  refine (h3.scalar).trans ?_
  refine ((qmul (qrefl _) h4).scalar).trans ?_
  exact (scalar_mul_conj _ _).trans (dot_comm _ _)

/-- The split crossing plaquette weight `T_K` is an RPK. -/
theorem rpk_cross_split {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (B1 P B2 : PolyQuaternion)
    (hY : SupQ a (mul (mul B1 P) (conj B2))) :
    RPK a (wilsonPoly
      (mul (mul (mul (conj (shQ a B1)) B1) P) (mul (conj (mul (conj (shQ a B2)) B2)) (conj (shQ a P)))).scalar
      (wilsonA β) K) := by
  refine rpk_TK hβ K _ _ hY ?_
  have h := cross_split_word B1 P B2 (shQ a B1) (shQ a P) (shQ a B2)
  rw [shQ_mul, shQ_mul, shQ_conj]
  exact h

end YMGap.Continuum.SU2TorusRPCrossSplit

#print axioms YMGap.Continuum.SU2TorusRPCrossSplit.cross_split_word
#print axioms YMGap.Continuum.SU2TorusRPCrossSplit.rpk_cross_split
