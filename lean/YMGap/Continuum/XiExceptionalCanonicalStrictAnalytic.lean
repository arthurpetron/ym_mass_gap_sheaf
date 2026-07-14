/-
# Analytic factorization of the construction-valid canonical carrier

The strict canonical gate requires every attachment parent to have appeared
earlier in the ordered build.  Removing only tree/background compatibility
still factors the resulting duplicate-free finite carrier into its strict
tree majorant and two copies of `XiR`.
-/

import YMGap.Continuum.XiExceptionalCanonicalStrictCarrier

namespace YMGap.Continuum.XiExceptionalCanonicalStrictAnalytic

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentCarrier
open YMGap.Continuum.XiExceptionalCanonicalRootAttachmentEnumeration
open YMGap.Continuum.XiExceptionalCanonicalStrictCarrier

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def strictCanonicalRootAttachmentTreeMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label)
    (rootAttachmentTreeCodes Gamma.length Gamma.length)

def strictRelaxedRootAttachmentCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) : Q' :=
  (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label code.tree *
    admissibleFamilyWeight w qP label
      (selectByBits Gamma code.background)) *
    admissibleFamilyWeight w qP label
      (selectByBits Gamma code.external)

def strictRelaxedRootAttachmentCarrierMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum
    (strictRelaxedRootAttachmentCarrierCodeWeight
      w Gamma qP b1 b2 label)
    (rootAttachmentCarrierCodes Gamma.length Gamma.length)

theorem strictRootAttachmentTreeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentTreeCode Gamma.length) :
    (0 : Q') ≤ strictRootAttachmentTreeWeight
      w Gamma qP b1 b2 label code := by
  unfold strictRootAttachmentTreeWeight
  split
  · unfold rootAttachmentActivity
    exact familyActivity_nonneg hw _ label
  · exact Q'.le_refl' _

theorem strictRelaxedRootAttachmentCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) :
    (0 : Q') ≤ strictRelaxedRootAttachmentCarrierCodeWeight
      w Gamma qP b1 b2 label code := by
  unfold strictRelaxedRootAttachmentCarrierCodeWeight
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (strictRootAttachmentTreeWeight_nonnegative hw
        Gamma qP b1 b2 label code.tree)
      (admissibleFamilyWeight_nonnegative hw qP label
        (selectByBits Gamma code.background)))
    (admissibleFamilyWeight_nonnegative hw qP label
      (selectByBits Gamma code.external))

theorem strictRootAttachmentCarrierCodeWeight_le_relaxed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : RootAttachmentCarrierCode Gamma.length) :
    strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label code ≤
      strictRelaxedRootAttachmentCarrierCodeWeight
        w Gamma qP b1 b2 label code := by
  unfold strictRootAttachmentCarrierCodeWeight
  split
  next hvalid =>
    have hgate :
        ((selectByBits Gamma code.background).all qP &&
          familyCompatibleB (selectByBits Gamma code.background)) = true := by
      unfold rootAttachmentBackgroundValidB at hvalid
      dsimp only at hvalid
      cases hq : (selectByBits Gamma code.background).all qP <;>
        cases hc : familyCompatibleB
          (selectByBits Gamma code.background) <;> simp_all
    unfold strictRelaxedRootAttachmentCarrierCodeWeight
      admissibleFamilyWeight
    simp only [hgate, if_true]
    exact Q'.le_refl' _
  next _ =>
    exact strictRelaxedRootAttachmentCarrierCodeWeight_nonnegative hw
      Gamma qP b1 b2 label code

private theorem qListSum_le_pointwise (f g : a → Q') :
    ∀ xs : List a, (∀ x, x ∈ xs → f x ≤ g x) →
      qListSum f xs ≤ qListSum g xs
  | [], _ => Q'.le_refl' 0
  | x :: xs, h => by
      apply Q'.add_le_add
      · exact h x List.mem_cons_self
      · exact qListSum_le_pointwise f g xs
          (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem strictRootAttachmentCarrierMajorant_le_relaxed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (strictRootAttachmentCarrierCodeWeight w Gamma qP b1 b2 label)
        (rootAttachmentCarrierCodes Gamma.length Gamma.length) ≤
      strictRelaxedRootAttachmentCarrierMajorant
        w Gamma qP b1 b2 label := by
  apply qListSum_le_pointwise
  intro code _
  exact strictRootAttachmentCarrierCodeWeight_le_relaxed hw
    Gamma qP b1 b2 label code

theorem strictRelaxedRootAttachmentCarrierMajorant_eqv
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    strictRelaxedRootAttachmentCarrierMajorant w Gamma qP b1 b2 label ≈
      (strictCanonicalRootAttachmentTreeMajorant
          w Gamma qP b1 b2 label * XiR w qP Gamma label) *
        XiR w qP Gamma label := by
  have hcodes : rootAttachmentCarrierCodes Gamma.length Gamma.length =
      (rootAttachmentTreeCodes Gamma.length Gamma.length).flatMap
        (fun tree => (bitVectors Gamma.length).flatMap (fun background =>
          (bitVectors Gamma.length).map (fun external =>
            RootAttachmentCarrierCode.mk tree background external))) := by
    unfold rootAttachmentCarrierCodes maskPairs
    simp only [List.map_flatMap, List.map_map]
    rfl
  unfold strictRelaxedRootAttachmentCarrierMajorant
  rw [hcodes]
  refine Q'.eqv_trans _ _ _
    (qListSum_flatMap
      (strictRelaxedRootAttachmentCarrierCodeWeight
        w Gamma qP b1 b2 label)
      (fun tree => (bitVectors Gamma.length).flatMap (fun background =>
        (bitVectors Gamma.length).map (fun external =>
          RootAttachmentCarrierCode.mk tree background external)))
      (rootAttachmentTreeCodes Gamma.length Gamma.length)) ?_
  have hexternal : ∀ tree background,
      qListSum
          (strictRelaxedRootAttachmentCarrierCodeWeight
            w Gamma qP b1 b2 label)
          ((bitVectors Gamma.length).map (fun external =>
            RootAttachmentCarrierCode.mk tree background external)) ≈
        (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label tree *
          admissibleFamilyWeight w qP label
            (selectByBits Gamma background)) * XiR w qP Gamma label := by
    intro tree background
    rw [qListSum_map]
    unfold strictRelaxedRootAttachmentCarrierCodeWeight
    refine Q'.eqv_trans _ _ _
      (qListSum_const_mul
        (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label tree *
          admissibleFamilyWeight w qP label
            (selectByBits Gamma background))
        (fun external => admissibleFamilyWeight w qP label
          (selectByBits Gamma external))
        (bitVectors Gamma.length)) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (admissibleFamilyWeight_bitVectors_eqv_XiR
        w qP Gamma label)
  have hbackground : ∀ tree,
      qListSum
          (strictRelaxedRootAttachmentCarrierCodeWeight
            w Gamma qP b1 b2 label)
          ((bitVectors Gamma.length).flatMap (fun background =>
            (bitVectors Gamma.length).map (fun external =>
              RootAttachmentCarrierCode.mk tree background external))) ≈
        (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label tree *
          XiR w qP Gamma label) * XiR w qP Gamma label := by
    intro tree
    refine Q'.eqv_trans _ _ _
      (qListSum_flatMap
        (strictRelaxedRootAttachmentCarrierCodeWeight
          w Gamma qP b1 b2 label)
        (fun background => (bitVectors Gamma.length).map (fun external =>
          RootAttachmentCarrierCode.mk tree background external))
        (bitVectors Gamma.length)) ?_
    refine Q'.eqv_trans _ _ _
      (qListSum_eqv_congr _ _ (bitVectors Gamma.length)
        (fun background _ => hexternal tree background)) ?_
    refine Q'.eqv_trans _ _ _
      (qListSum_mul_const
        (fun background =>
          strictRootAttachmentTreeWeight w Gamma qP b1 b2 label tree *
            admissibleFamilyWeight w qP label
              (selectByBits Gamma background))
        (XiR w qP Gamma label) (bitVectors Gamma.length)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (qListSum_const_mul
          (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label tree)
          (fun background => admissibleFamilyWeight w qP label
            (selectByBits Gamma background))
          (bitVectors Gamma.length))
        (Q'.mul_eqv_congr_left _ _ _
          (admissibleFamilyWeight_bitVectors_eqv_XiR
            w qP Gamma label)))
  refine Q'.eqv_trans _ _ _
    (qListSum_eqv_congr _ _
      (rootAttachmentTreeCodes Gamma.length Gamma.length)
      (fun tree _ => hbackground tree)) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_mul_const
      (fun tree => strictRootAttachmentTreeWeight
        w Gamma qP b1 b2 label tree * XiR w qP Gamma label)
      (XiR w qP Gamma label)
      (rootAttachmentTreeCodes Gamma.length Gamma.length)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _
      (qListSum_mul_const
        (strictRootAttachmentTreeWeight w Gamma qP b1 b2 label)
        (XiR w qP Gamma label)
        (rootAttachmentTreeCodes Gamma.length Gamma.length))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_refl _)))

/-! The strict gate preserves the already-closed two-occurrence fence. -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def p : TL.Plaquette := (0, 0)
private def q : TL.Plaquette := (1, 0)
private def X : Polymer TL := [p]
private def Y : Polymer TL := [p, q]
private def Gamma2 : List (Polymer TL) := [X, Y]
private def qAll : Polymer TL → Bool := fun _ => true
private def bX : Polymer TL → Bool := fun Z => decide (Z = X)
private def bY : Polymer TL → Bool := fun Z => decide (Z = Y)
private def labelOne : TL.Plaquette → Rep := fun _ => 1
private def half : Q' := Q'.mkPos 1 2 (by decide)

set_option maxRecDepth 10000 in
theorem strict_canonical_tree_majorant_eqv_one_over_64 :
    strictCanonicalRootAttachmentTreeMajorant
        half Gamma2 qAll bX bY labelOne ≈
      Q'.mkPos 1 64 (by decide) := by
  decide

set_option maxRecDepth 10000 in
theorem strict_canonical_tree_majorant_le_chain_on_raw_fence :
    strictCanonicalRootAttachmentTreeMajorant
        half Gamma2 qAll bX bY labelOne ≤
      connectingChainMajorant half qAll bX bY Gamma2 labelOne := by
  decide

#print axioms strictRootAttachmentTreeWeight_nonnegative
#print axioms strictRootAttachmentCarrierCodeWeight_le_relaxed
#print axioms strictRootAttachmentCarrierMajorant_le_relaxed
#print axioms strictRelaxedRootAttachmentCarrierMajorant_eqv
#print axioms strict_canonical_tree_majorant_eqv_one_over_64
#print axioms strict_canonical_tree_majorant_le_chain_on_raw_fence

end YMGap.Continuum.XiExceptionalCanonicalStrictAnalytic
