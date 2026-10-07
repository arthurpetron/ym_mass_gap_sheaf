/-
# Torus RP (d4f): simultaneous crossing split by a chain of shears

For a list of left shears of one orientation with pairwise distinct selected blocks and multipliers that are never selected,
the chain maps `U_s ↦ M_m·U_s` (`M_m = U_m` direct, `U_m*` inverse) for each step `(s, m)` and fixes all other coordinates (`chain_coord`).
With `split_prod_haar` this splits ALL crossing links of the actual torus `Π T_K` at once (`split_chain`).

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN.**
-/

import YMGap.Continuum.SU2TorusRPSplitStep
import YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix

namespace YMGap.Continuum.SU2TorusRPSplitChain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2HaarL1Activity (prodPoly)
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2TorusRPSubst (RingSub QPE qsub qpe_trans qpe_mul qpe_conj qmul_sub qconj_sub)
open YMGap.Continuum.SU2TorusRPStepCoord (idR id_coord qpe_of_coeff)
open YMGap.Continuum.SU2TorusRPSplitTK (plaqIdx imgTK split_prod_haar)
open YMGap.Continuum.SU2QuaternionInverseTranslationCoordinates (coordinateImage)
open PolyQuaternion (mul conj)

local notation "cv" => PolyQuaternion.coordinateVariable
local notation "Sup" => YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini.SupportedQuaternionBlocks

variable {tailBlocks : Nat}

/-- Multiplier quaternion for an orientation. -/
def multQ (o : SelectedMultiplierOrientation) (m : Nat) : PolyQuaternion :=
  match o with
  | .direct => cv m
  | .inverse => conj (cv m)

/-- Left (`M·U`) or right (`U·M`) multiplication. -/
def sideMul (sd : SelectedTranslationSide) (Mq U : PolyQuaternion) : PolyQuaternion :=
  match sd with
  | .left => mul Mq U
  | .right => mul U Mq

/-- Coordinate image of a split chain. -/
def chImg (o : SelectedMultiplierOrientation) : List (SelectedTranslationStep tailBlocks) → Nat → PolyQuaternion
  | [], b => cv b
  | st :: r, b => if b = st.selected then sideMul st.side (multQ o st.multiplier) (cv b) else chImg o r b

/-- Admissible split chain. -/
structure ChainOK (o : SelectedMultiplierOrientation) (steps : List (SelectedTranslationStep tailBlocks)) : Prop where
  orient : ∀ st ∈ steps, st.multiplierOrientation = o
  distinct : steps.Pairwise fun x y => x.selected ≠ y.selected
  fresh : ∀ st ∈ steps, ∀ st' ∈ steps, st.multiplier ≠ st'.selected

theorem chainOK_tail {o : SelectedMultiplierOrientation} {st : SelectedTranslationStep tailBlocks} {r : List (SelectedTranslationStep tailBlocks)}
    (h : ChainOK o (st :: r)) : ChainOK o r :=
  ⟨fun x hx => h.orient x (List.mem_cons_of_mem _ hx),
   (List.pairwise_cons.mp h.distinct).2,
   fun x hx y hy => h.fresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)⟩

theorem chain_padded (o : SelectedMultiplierOrientation) (hb : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks)), ChainOK o steps →
    ∀ b, b < tailBlocks + 1 →
    PaddedQuaternionCoeffEqv (tailBlocks + 1) (applySelectedTranslationStepsQuaternion hb steps (cv b)) (chImg o steps b)
  | [], _, b, _ => PaddedQuaternionCoeffEqv.refl _ _
  | st :: r, h, b, hbl => by
      have hr := chainOK_tail h
      have happ : applySelectedTranslationStepsQuaternion hb (st :: r) (cv b) =
          applySelectedTranslationStepsQuaternion hb r (applySelectedTranslationStepsQuaternion hb [st] (cv b)) :=
        applySteps_append hb [st] r (cv b)
      rw [happ]
      have h1 := applyStep_coordinate hb st b hbl
      refine (PaddedQuaternionCoeffEqv.applySteps hb r h1).trans ?_
      unfold chImg coordinateImage
      by_cases hs : b = st.selected
      · rw [if_pos hs, if_pos hs, h.orient st (List.mem_cons_self ..)]
        have hm : PaddedQuaternionCoeffEqv (tailBlocks + 1)
            (applySelectedTranslationStepsQuaternion hb r (multQ o st.multiplier)) (multQ o st.multiplier) := by
          have hfix := applySteps_fixed_coordinate hb r _ st.multiplier_lt
            (fun y hy => h.fresh st (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy))
          cases o
          · exact hfix
          · exact (applySteps_conj hb r _).trans (PaddedQuaternionCoeffEqv.conj hfix)
        have hu : PaddedQuaternionCoeffEqv (tailBlocks + 1)
            (applySelectedTranslationStepsQuaternion hb r (cv st.selected)) (cv b) := by
          rw [hs]
          exact applySteps_fixed_coordinate hb r _ st.selected_lt
            (fun y hy => (List.pairwise_cons.mp h.distinct).1 y hy)
        have hmul := applySteps_mul hb r
        cases hsd : st.side <;> cases o <;> simp only [sideMul, multQ] at hm ⊢
        · exact (hmul _ _).trans (PaddedQuaternionCoeffEqv.mul hm hu)
        · exact (hmul _ _).trans (PaddedQuaternionCoeffEqv.mul hm hu)
        · exact (hmul _ _).trans (PaddedQuaternionCoeffEqv.mul hu hm)
        · exact (hmul _ _).trans (PaddedQuaternionCoeffEqv.mul hu hm)
      · rw [if_neg hs, if_neg hs]
        exact chain_padded o hb r hr b hbl

theorem steps_supported_ne (hb : 0 < tailBlocks) (st : SelectedTranslationStep tailBlocks)
    (r : List (SelectedTranslationStep tailBlocks)) (p : RatPoly) :
    Sup (tailBlocks + 1) (applySelectedTranslationSteps hb (st :: r) p) :=
  YMGap.Continuum.SU2TorusRPStepSub.steps_supported hb r _ (applySelectedTranslationStep_supported hb st p)

theorem idR_sup (n : Nat) (p : RatPoly) : Sup n (idR n p) := fun t ht =>
  Nat.le_of_eq (YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients.reindex_term_length _ p t ht)

theorem pe_idR (n : Nat) (p : RatPoly) (hp : Sup n p) : YMGap.Continuum.SU2HaarAlgebra.PE n p (idR n p) :=
  YMGap.Continuum.SU2TorusRPStepSub.prefix_pe n
    (YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.prefix_symm
      (identityReindexQuaternionPolynomial_prefix n p)) hp (idR_sup n p)

theorem chImg_idR (o : SelectedMultiplierOrientation) (hR : RingSub (tailBlocks + 1) (idR (tailBlocks + 1))) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks)) (b : Nat), b < tailBlocks + 1 →
    QPE (tailBlocks + 1) (qsub (idR (tailBlocks + 1)) (chImg o steps b)) (chImg o steps b)
  | [], b, hbl => id_coord _ b hbl
  | st :: r, b, hbl => by
      unfold chImg
      by_cases hs : b = st.selected
      · rw [if_pos hs]
        have hm : QPE (tailBlocks + 1) (qsub (idR (tailBlocks + 1)) (multQ o st.multiplier)) (multQ o st.multiplier) := by
          cases o
          · exact id_coord _ _ st.multiplier_lt
          · exact qpe_trans (qconj_sub hR _) (qpe_conj (id_coord _ _ st.multiplier_lt))
        cases st.side
        · exact qpe_trans (qmul_sub hR _ _) (qpe_mul hm (id_coord _ _ hbl))
        · exact qpe_trans (qmul_sub hR _ _) (qpe_mul (id_coord _ _ hbl) hm)
      · rw [if_neg hs]; exact chImg_idR o hR r b hbl

theorem chain_coord (o : SelectedMultiplierOrientation) (hb : 0 < tailBlocks) (st : SelectedTranslationStep tailBlocks)
    (r : List (SelectedTranslationStep tailBlocks)) (h : ChainOK o (st :: r)) (b : Nat) (hbl : b < tailBlocks + 1) :
    QPE (tailBlocks + 1) (qsub (applySelectedTranslationSteps hb (st :: r)) (cv b)) (chImg o (st :: r) b) := by
  have hp := chain_padded o hb (st :: r) h b hbl
  have hR := YMGap.Continuum.SU2TorusRPReindex.reindex_ringSub (identityQuaternionBlockInvolution (tailBlocks + 1))
  have e : qsub (applySelectedTranslationSteps hb (st :: r)) (cv b) =
      applySelectedTranslationStepsQuaternion hb (st :: r) (cv b) := rfl
  rw [e]
  refine qpe_trans (r := qsub (idR (tailBlocks + 1)) (applySelectedTranslationStepsQuaternion hb (st :: r) (cv b)))
    ⟨pe_idR _ _ (steps_supported_ne hb st r _), pe_idR _ _ (steps_supported_ne hb st r _),
    pe_idR _ _ (steps_supported_ne hb st r _), pe_idR _ _ (steps_supported_ne hb st r _)⟩
    (qpe_trans (qpe_of_coeff _ hp) (chImg_idR o hR _ b hbl))

/-- **Simultaneous concrete crossing split** of the actual torus `Π T_K`. -/
theorem split_chain (o : SelectedMultiplierOrientation) (hb : 0 < tailBlocks) (st : SelectedTranslationStep tailBlocks)
    (r : List (SelectedTranslationStep tailBlocks)) (h : ChainOK o (st :: r))
    (links : List Z4Link) (N : Nat) (β : Q') (K : Nat) (ps : List Z4Plaq)
    (hsup : Sup (tailBlocks + 1) (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps))
    (hps : ∀ p ∈ ps, ∀ b ∈ plaqIdx links N p, b < tailBlocks + 1) :
    (quaternionHaar (tailBlocks + 1) (prodPoly (YMGap.Continuum.SU2WilsonPolymerIdentity.TK links N β K) ps)).eqv
      (quaternionHaar (tailBlocks + 1) (prodPoly (imgTK links N β K (chImg o (st :: r))) ps)) :=
  split_prod_haar links N β K (YMGap.Continuum.SU2TorusRPStepSub.steps_ringSub hb (st :: r)) ps
    (YMGap.Continuum.SU2QuaternionAllDegreeHaarTranslationChain.applySelectedTranslationSteps_haar hb _ _ hsup)
    _ (chain_coord o hb st r h) hps

end YMGap.Continuum.SU2TorusRPSplitChain

#print axioms YMGap.Continuum.SU2TorusRPSplitChain.chain_coord
#print axioms YMGap.Continuum.SU2TorusRPSplitChain.split_chain
