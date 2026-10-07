/-
# Torus RP (d4h): crossing words at the second cut (right split)

At the cut `t = M` the crossing temporal links are split on the right, `Uᵢ = Bᵢ·(ΘBᵢ)*`, and the positive spatial
link `P` sits in the LAST slot of the plaquette word:
  `W = ((B₁ sB₁*) sP) ((B₂ sB₂*)* P*)`.
`cross_word_M`: `Re W ≅ dot (sY) Y` with `Y = (B₂* P*) B₁`, `sY = (sB₂* sP*) sB₁`; `rpk_cross_M` gives RPK of its
`T_K` under `SupQ a Y`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSplitChain

namespace YMGap.Continuum.SU2TorusRPCrossM

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
open YMGap.Continuum.SU2TorusRPCrossSplit (dot_comm)

local infix:50 " ≅ " => RatPolyCoeffEqv
local infix:50 " ≅q " => PolyQuaternionCoeffEqv

theorem cross_word_M (B1 P B2 S1 sP S2 : PolyQuaternion) :
    (mul (mul (mul B1 (conj S1)) sP) (mul (conj (mul B2 (conj S2))) (conj P))).scalar ≅
      dot (mul (mul (conj S2) (conj sP)) S1) (mul (mul (conj B2) (conj P)) B1) := by
  have h1 : conj (mul B2 (conj S2)) ≅q mul S2 (conj B2) :=
    qtrans (conj_mul _ _) (qmul (conj_conj S2) (qrefl _))
  -- W ≅ B1 · (Z · (cB2·cP)), Z = (cS1·sP)·S2
  have h2 : mul (mul (mul B1 (conj S1)) sP) (mul (conj (mul B2 (conj S2))) (conj P)) ≅q
      mul B1 (mul (mul (mul (conj S1) sP) S2) (mul (conj B2) (conj P))) := by
    refine qtrans (qmul (qrefl _) (qmul h1 (qrefl _))) ?_
    refine qtrans (qassoc _ _ _) (qtrans (qassoc _ _ _) (qmul (qrefl _) ?_))
    refine qsymm (qtrans (qassoc _ _ _) (qtrans (qassoc _ _ _) (qmul (qrefl _) (qmul (qrefl _) ?_))))
    exact qsymm (qassoc _ _ _)
  have hZ : mul (mul (conj S1) sP) S2 ≅q conj (mul (mul (conj S2) (conj sP)) S1) := by
    refine qsymm (qtrans (conj_mul _ _) (qtrans (qmul (qrefl _) (qtrans (conj_mul _ _)
      (qmul (conj_conj _) (conj_conj _)))) (qsymm (qassoc _ _ _))))
  refine (h2.scalar).trans ((scalar_comm _ _).trans ?_)
  refine ((qassoc (mul (mul (conj S1) sP) S2) (mul (conj B2) (conj P)) B1).scalar).trans ?_
  refine ((qmul hZ (qrefl (mul (mul (conj B2) (conj P)) B1))).scalar).trans ?_
  exact (scalar_comm _ _).trans ((scalar_mul_conj _ _).trans (dot_comm _ _))

theorem rpk_cross_M {a : Nat} {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (B1 P B2 : PolyQuaternion)
    (hY : SupQ a (mul (mul (conj B2) (conj P)) B1)) :
    RPK a (wilsonPoly
      (mul (mul (mul B1 (conj (shQ a B1))) (shQ a P)) (mul (conj (mul B2 (conj (shQ a B2)))) (conj P))).scalar
      (wilsonA β) K) := by
  refine rpk_TK hβ K _ _ hY ?_
  have h := cross_word_M B1 P B2 (shQ a B1) (shQ a P) (shQ a B2)
  rw [shQ_mul, shQ_mul, shQ_conj, shQ_conj]
  exact h

end YMGap.Continuum.SU2TorusRPCrossM

#print axioms YMGap.Continuum.SU2TorusRPCrossM.cross_word_M
#print axioms YMGap.Continuum.SU2TorusRPCrossM.rpk_cross_M
