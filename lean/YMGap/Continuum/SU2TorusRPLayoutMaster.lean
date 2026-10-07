/-
# Torus RP (d9g): `torus_rp_master` instantiated on the concrete layout

`torus_rp_layout`: on the layout `L = P ++ C ++ Θ P` (`a = |P| + |C|`, `N = 2M`) with the concrete split chain
`layChain`, the selector `layT` and the half swap, positivity `0 ≤ ∫ X · ∏_ps T_K` holds for `X = Θ_H F · F`, given
* `C` nodup and nonempty, containing every in-box crossing link; `P` in the box, containing every in-box `pos` link;
* `ps ~ pos ++ mir pos ++ cross`, `pos` in-box `pos` plaquettes, `cross` in-box crossing plaquettes;
* still as hypotheses: the chain fixes `X` (`hXfix`), support of the integrand (`hsup`), the plaquette index bound
  (`hps`) and `Sup a (∏_pos T_K)` (`hWp`).
The geometric inputs of the master (ChainOK, hfac, per-crossing RPK, hσ) are discharged here.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (hXfix, hsup, hps, hWp, the choice of P, C, and the integrand bridge).
-/

import YMGap.Continuum.SU2TorusRPMaster
import YMGap.Continuum.SU2TorusRPLayoutFactor

namespace YMGap.Continuum.SU2TorusRPLayoutMaster

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2HaarAlgebra (PE)
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2TorusRPSplitChain (chImg ChainOK)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx imgTK)
open YMGap.Continuum.SU2TorusRPCore (Sup RPK)
open YMGap.Continuum.SU2TorusRPHaar (conjSel)
open YMGap.Continuum.SU2TorusRPCrossC (Ctw)
open YMGap.Continuum.SU2TorusRPGeom (reflLink linkSide plaqSide Side)
open YMGap.Continuum.SU2TorusRPLayoutChain (layChain)
open YMGap.Continuum.SU2TorusRPLayoutT (layT)
open YMGap.Continuum.SU2TorusRPThetaProd (mir)
open YMGap.Continuum.SU2TorusRPHalfSwap (halfSwap)

/-- `torus_rp_master` for an arbitrary nonempty chain list. -/
theorem master_list {a : Nat} (hb : 0 < a + a - 1) (ha : a + a - 1 + 1 = a + a)
    (o : SelectedMultiplierOrientation) (l : List (SelectedTranslationStep (a + a - 1))) (hne : l ≠ [])
    (hch : ChainOK o l)
    (links : List Z4Link) (N : Nat) (β : Q') (K : Nat) (ps : List Z4Plaq)
    (σ : QuaternionBlockInvolution (a + a)) (hσ : ∀ k, k < a → σ.map k = k + a) (Tb : Nat → Bool)
    (F Wp : RatPoly) (hF : Sup a F) (hWp : Sup a Wp)
    {α : Type} (G : α → RatPoly) (cs : List α) (hG : ∀ c ∈ cs, RPK a (Ctw a Tb (G c)))
    (X : RatPoly)
    (hX : X = polyMul (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) (reindexQuaternionPolynomial σ F)) F)
    (hXfix : PE (a + a - 1 + 1) (applySelectedTranslationSteps hb l X) X)
    (hsup : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks (a + a - 1 + 1)
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)))
    (hps : ∀ p ∈ ps, ∀ b ∈ plaqIdx links N p, b < a + a - 1 + 1)
    (hfac : PE (a + a) (prodPoly (imgTK links N β K (chImg o l)) ps)
      (polyMul (polyMul Wp (signSelectedPolynomial (4 * (a + a)) (conjSel Tb) (reindexQuaternionPolynomial σ Wp)))
        (cs.foldr (fun c Y => polyMul (G c) Y) polyOne))) :
    (0 : Q') ≤ quaternionHaar (a + a)
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)) := by
  cases l with
  | nil => exact absurd rfl hne
  | cons st r =>
    exact YMGap.Continuum.SU2TorusRPMaster.torus_rp_master hb ha o st r hch links N β K ps σ hσ Tb F Wp hF hWp
      G cs hG X hX hXfix hsup hps hfac

variable {M : Nat} (hM : 1 ≤ M) (P C : List Z4Link) (hnd : (P ++ C ++ P.map (reflLink M)).Nodup)
  (hC : C.Nodup)
  (hCcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .cross → ℓ ∈ C)
  (hPcov : ∀ ℓ : Z4Link, InBox (2 * M) ℓ.1 → linkSide M ℓ = .pos → ℓ ∈ P)
  (hPbox : ∀ x ∈ P, InBox (2 * M) x.1)

theorem a_pos (hCne : C ≠ []) : 1 ≤ P.length + C.length := by
  cases C with
  | nil => exact absurd rfl hCne
  | cons c C => simp only [List.length_cons]; omega

include hM hC hCcov hPcov hPbox in
theorem torus_rp_layout {β : Q'} (hβ : (0 : Q') ≤ β) (K : Nat) (ps pos cross : List Z4Plaq)
    (hperm : ps.Perm (pos ++ pos.map (mir M) ++ cross))
    (hposP : ∀ p ∈ pos, InBox (2 * M) p.1 ∧ plaqSide M p = .pos)
    (hcross : ∀ q ∈ cross, InBox (2 * M) q.1 ∧ plaqSide M q = .cross) (hCne : C ≠ [])
    (hb : 0 < (P.length + C.length) + (P.length + C.length) - 1)
    (F : RatPoly) (hF : Sup (P.length + C.length) F)
    (hWp : Sup (P.length + C.length)
      (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) pos))
    (X : RatPoly)
    (hX : X = polyMul (signSelectedPolynomial (4 * ((P.length + C.length) + (P.length + C.length)))
      (conjSel (layT (P ++ C ++ P.map (reflLink M))))
      (reindexQuaternionPolynomial (halfSwap (P.length + C.length)) F)) F)
    (hXfix : PE ((P.length + C.length) + (P.length + C.length) - 1 + 1)
      (applySelectedTranslationSteps hb (layChain M P C hnd (a_pos P C hCne)) X) X)
    (hsup : YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks
      ((P.length + C.length) + (P.length + C.length) - 1 + 1)
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps)))
    (hps : ∀ p ∈ ps, ∀ b ∈ plaqIdx (P ++ C ++ P.map (reflLink M)) (2 * M) p,
      b < (P.length + C.length) + (P.length + C.length) - 1 + 1) :
    (0 : Q') ≤ quaternionHaar ((P.length + C.length) + (P.length + C.length))
      (polyMul X (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK (P ++ C ++ P.map (reflLink M)) (2 * M) β K) ps)) := by
  have ha := a_pos P C hCne
  have hfac := YMGap.Continuum.SU2TorusRPLayoutFactor.lay_factor hM P C hnd ha hPcov hPbox β K ps pos cross hperm hposP
  rw [YMGap.Continuum.SU2TorusRPSplitFactor.prodPoly_eq_foldr
    (imgTK (P ++ C ++ P.map (reflLink M)) (2 * M) β K (chImg .direct (layChain M P C hnd ha))) cross] at hfac
  refine master_list hb (by omega) .direct _ ?_ (YMGap.Continuum.SU2TorusRPLayoutChain.layChain_ok M P C hnd ha hC)
    _ _ β K ps (halfSwap _) (YMGap.Continuum.SU2TorusRPHalfSwap.halfSwap_low _) _ F _ hF hWp _ cross
    (fun q hq => YMGap.Continuum.SU2TorusRPCrossPlaq.rpk_cross_plaq hM P C hnd ha hCcov hPcov hPbox hβ K hC
      q.1 q.2 (hcross q hq).1 (hcross q hq).2) X hX hXfix hsup hps hfac
  cases C with
  | nil => exact absurd rfl hCne
  | cons c C => intro h; cases h

end YMGap.Continuum.SU2TorusRPLayoutMaster

#print axioms YMGap.Continuum.SU2TorusRPLayoutMaster.master_list
#print axioms YMGap.Continuum.SU2TorusRPLayoutMaster.torus_rp_layout
