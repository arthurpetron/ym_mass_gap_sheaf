/-
# Torus RP (d6c): end-to-end reduction for the split torus integrand

`torus_rp_master`: on `a + a` blocks, for the actual `Π_ps T_K` times an observable part `X = ΘF·F` fixed by the
split chain, positivity `0 ≤ ∫ X · Π_ps T_K` follows from
* an admissible split chain (`ChainOK`), support and index bounds;
* the factorisation `Π_ps T_K[split] ≈PE (Wp·ΘWp)·Π_cs G` (from `torus_factor`, `pe_lift`, `imgTK_eq_TK`);
* RPK of each `Ctw`-twisted crossing factor (from `rpk_match0/M`).
The geometric facts above (layout, index lists of crossing plaquettes) are hypotheses here.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (hypotheses not yet instantiated from the torus geometry).
-/

import YMGap.Continuum.SU2TorusRPCrossMatch

namespace YMGap.Continuum.SU2TorusRPMaster

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE pe_trans pe_refl pe_haar pe_mulL pe_mulR)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPSplitChain (chImg ChainOK chain_coord)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx imgTK subst_prod)
open YMGap.Continuum.SU2TorusRPCore (Sup RPK)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPCrossC (Ctw)

theorem torus_rp_master {a : Nat} (hb : 0 < a + a - 1) (ha : a + a - 1 + 1 = a + a)
    (o : SelectedMultiplierOrientation) (st : SelectedTranslationStep (a + a - 1))
    (r : List (SelectedTranslationStep (a + a - 1))) (hch : ChainOK o (st :: r))
    (links : List Z4Link) (N : Nat) (β : Q') (K : Nat) (ps : List Z4Plaq)
    (σ : QuaternionBlockInvolution (a + a)) (hσ : ∀ k, k < a → σ.map k = k + a) (Tb : Nat → Bool)
    (F Wp : RatPoly) (hF : Sup a F) (hWp : Sup a Wp)
    {α : Type} (G : α → RatPoly) (cs : List α) (hG : ∀ c ∈ cs, RPK a (Ctw a Tb (G c)))
    (X : RatPoly)
    (hX : X = polyMul (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) (reindexQuaternionPolynomial σ F)) F)
    (hXfix : PE (a + a - 1 + 1) (applySelectedTranslationSteps hb (st :: r) X) X)
    (hsup : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks (a + a - 1 + 1)
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)))
    (hps : ∀ p ∈ ps, ∀ b ∈ plaqIdx links N p, b < a + a - 1 + 1)
    (hfac : PE (a + a) (prodPoly (imgTK links N β K (chImg o (st :: r))) ps)
      (polyMul (polyMul Wp (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) (reindexQuaternionPolynomial σ Wp)))
        (cs.foldr (fun c Y => polyMul (G c) Y) polyOne))) :
    (0 : Q') ≤ quaternionHaar (a + a)
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)) := by
  have hS := YMGap.Continuum.SU2TorusRPStepSub.steps_ringSub hb (st :: r)
  have hsub := subst_prod (n := a + a - 1 + 1) links N β K hS _ (chain_coord o hb st r hch) ps hps
  have hpe : PE (a + a - 1 + 1) (applySelectedTranslationSteps hb (st :: r)
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)))
      (polyMul X (prodPoly (imgTK links N β K (chImg o (st :: r))) ps)) :=
    pe_trans _ (hS.mul _ _) (YMGap.Continuum.SU2TorusRPSubst.pe_mul2 _ hXfix hsub)
  have hinv := YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.applySelectedTranslationSteps_haar hb
    (st :: r) _ hsup
  have h1 := YMGap.Continuum.SU2TorusRPCompOn.haar_step _ hinv hpe
  rw [ha] at h1
  have h2 := pe_haar (a + a) (pe_mulL (a + a) X hfac)
  have h3 := YMGap.Continuum.SU2TorusRPSplitRP.torus_rp_split σ hσ Tb F Wp hF hWp G cs hG
  rw [← hX] at h3
  exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ h1 h2)))

end YMGap.Continuum.SU2TorusRPMaster

#print axioms YMGap.Continuum.SU2TorusRPMaster.torus_rp_master
