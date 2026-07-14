/-
# Analytic envelope for the exceptional occurrence-tree carrier

The injective allocator lands in a finite tree/background/external code
space.  This module removes only the tree--background compatibility gate,
replacing the background factor by its ordinary admissible-family weight.
The resulting finite sum factorizes exactly as one occurrence-tree majorant
times two copies of `XiR`.
-/

import YMGap.Continuum.XiExceptionalSourceTreeFiber

namespace YMGap.Continuum.XiExceptionalSourceTreeAnalytic

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiExceptionalOccurrenceTreeCodes
open YMGap.Continuum.XiExceptionalOccurrenceTreeWeight
open YMGap.Continuum.XiExceptionalOccurrenceTreeMajorant
open YMGap.Continuum.XiExceptionalSourceTreeCarrier
open YMGap.Continuum.XiExceptionalSourceTreeFiber

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

def relaxedOccurrenceTreeCarrierCodeWeight (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : OccTreeCarrierCode Gamma.length) : Q' :=
  (occurrenceTreeCodeWeight w Gamma qP b1 b2 label code.tree *
    admissibleFamilyWeight w qP label
      (selectByBits Gamma code.background)) *
    admissibleFamilyWeight w qP label
      (selectByBits Gamma code.external)

def relaxedOccurrenceTreeCarrierMajorant (w : Q')
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) : Q' :=
  qListSum
    (relaxedOccurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
    (occurrenceTreeCarrierCodes Gamma)

theorem relaxedOccurrenceTreeCarrierCodeWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : OccTreeCarrierCode Gamma.length) :
    (0 : Q') ≤ relaxedOccurrenceTreeCarrierCodeWeight
      w Gamma qP b1 b2 label code := by
  unfold relaxedOccurrenceTreeCarrierCodeWeight
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (occurrenceTreeCodeWeight_nonnegative hw Gamma qP b1 b2 label
        code.tree)
      (admissibleFamilyWeight_nonnegative hw qP label
        (selectByBits Gamma code.background)))
    (admissibleFamilyWeight_nonnegative hw qP label
      (selectByBits Gamma code.external))

theorem occurrenceTreeCarrierCodeWeight_le_relaxed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep)
    (code : OccTreeCarrierCode Gamma.length) :
    occurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label code ≤
      relaxedOccurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label
        code := by
  unfold occurrenceTreeCarrierCodeWeight
  split
  next hvalid =>
    have hgate :
        ((selectByBits Gamma code.background).all qP &&
          familyCompatibleB (selectByBits Gamma code.background)) = true := by
      unfold treeBackgroundValidB at hvalid
      dsimp only at hvalid
      cases hq : (selectByBits Gamma code.background).all qP <;>
        cases hc : familyCompatibleB
          (selectByBits Gamma code.background) <;> simp_all
    unfold relaxedOccurrenceTreeCarrierCodeWeight admissibleFamilyWeight
    simp only [hgate, if_true]
    exact Q'.le_refl' _
  next _ =>
    exact relaxedOccurrenceTreeCarrierCodeWeight_nonnegative hw
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

theorem occurrenceTreeCarrierMajorant_le_relaxed
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    occurrenceTreeCarrierMajorant w Gamma qP b1 b2 label ≤
      relaxedOccurrenceTreeCarrierMajorant w Gamma qP b1 b2 label := by
  apply qListSum_le_pointwise
  intro code _
  exact occurrenceTreeCarrierCodeWeight_le_relaxed hw
    Gamma qP b1 b2 label code

theorem relaxedOccurrenceTreeCarrierMajorant_eqv
    (w : Q') (Gamma : List (Polymer L))
    (qP b1 b2 : Polymer L → Bool) (label : L.Plaquette → Rep) :
    relaxedOccurrenceTreeCarrierMajorant w Gamma qP b1 b2 label ≈
      (occurrenceTreeMajorant w Gamma qP b1 b2 label Gamma.length *
        XiR w qP Gamma label) * XiR w qP Gamma label := by
  unfold relaxedOccurrenceTreeCarrierMajorant occurrenceTreeCarrierCodes
  refine Q'.eqv_trans _ _ _
    (qListSum_flatMap
      (relaxedOccurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
      (fun tree => (bitVectors Gamma.length).flatMap (fun background =>
        (bitVectors Gamma.length).map (fun external =>
          OccTreeCarrierCode.mk tree background external)))
      (occurrenceTreeCodesUpTo Gamma.length Gamma.length)) ?_
  have hexternal : ∀ tree background,
      qListSum
          (relaxedOccurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
          ((bitVectors Gamma.length).map (fun external =>
            OccTreeCarrierCode.mk tree background external)) ≈
        (occurrenceTreeCodeWeight w Gamma qP b1 b2 label tree *
          admissibleFamilyWeight w qP label
            (selectByBits Gamma background)) * XiR w qP Gamma label := by
    intro tree background
    rw [qListSum_map]
    unfold relaxedOccurrenceTreeCarrierCodeWeight
    refine Q'.eqv_trans _ _ _
      (qListSum_const_mul
        (occurrenceTreeCodeWeight w Gamma qP b1 b2 label tree *
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
          (relaxedOccurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
          ((bitVectors Gamma.length).flatMap (fun background =>
            (bitVectors Gamma.length).map (fun external =>
              OccTreeCarrierCode.mk tree background external))) ≈
        (occurrenceTreeCodeWeight w Gamma qP b1 b2 label tree *
          XiR w qP Gamma label) * XiR w qP Gamma label := by
    intro tree
    refine Q'.eqv_trans _ _ _
      (qListSum_flatMap
        (relaxedOccurrenceTreeCarrierCodeWeight w Gamma qP b1 b2 label)
        (fun background => (bitVectors Gamma.length).map (fun external =>
          OccTreeCarrierCode.mk tree background external))
        (bitVectors Gamma.length)) ?_
    refine Q'.eqv_trans _ _ _
      (qListSum_eqv_congr _ _ (bitVectors Gamma.length)
        (fun background _ => hexternal tree background)) ?_
    refine Q'.eqv_trans _ _ _
      (qListSum_mul_const
        (fun background =>
          occurrenceTreeCodeWeight w Gamma qP b1 b2 label tree *
            admissibleFamilyWeight w qP label
              (selectByBits Gamma background))
        (XiR w qP Gamma label) (bitVectors Gamma.length)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (qListSum_const_mul
          (occurrenceTreeCodeWeight w Gamma qP b1 b2 label tree)
          (fun background => admissibleFamilyWeight w qP label
            (selectByBits Gamma background))
          (bitVectors Gamma.length))
        (Q'.mul_eqv_congr_left _ _ _
          (admissibleFamilyWeight_bitVectors_eqv_XiR
            w qP Gamma label)))
  refine Q'.eqv_trans _ _ _
    (qListSum_eqv_congr _ _
      (occurrenceTreeCodesUpTo Gamma.length Gamma.length)
      (fun tree _ => hbackground tree)) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_mul_const
      (fun tree => occurrenceTreeCodeWeight w Gamma qP b1 b2 label tree *
        XiR w qP Gamma label)
      (XiR w qP Gamma label)
      (occurrenceTreeCodesUpTo Gamma.length Gamma.length)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_trans _ _ _
      (qListSum_mul_const
        (occurrenceTreeCodeWeight w Gamma qP b1 b2 label)
        (XiR w qP Gamma label)
        (occurrenceTreeCodesUpTo Gamma.length Gamma.length))
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_refl _)))

theorem routedExternalIncompatibleSource_treeAnalytic_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        (routedExternalIncompatibleSource Gamma qP b1 b2) ≤
      (occurrenceTreeMajorant w Gamma qP b1 b2 label Gamma.length *
        XiR w qP Gamma label) * XiR w qP Gamma label := by
  exact Q'.le_trans' _ _ _
    (routedExternalIncompatibleSource_treeCarrier_bound hw
      Gamma qP b1 b2 label)
    (Q'.le_trans' _ _ _
      (occurrenceTreeCarrierMajorant_le_relaxed hw
        Gamma qP b1 b2 label)
      (Q'.le_of_eqv
        (relaxedOccurrenceTreeCarrierMajorant_eqv
          w Gamma qP b1 b2 label)))

theorem fullExceptionalSource_treeAnalytic_bound
    {w : Q'} (hw : (0 : Q') ≤ w)
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    qListSum
        (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
        (fullExceptionalSource Gamma qP b1 b2) ≤
      connectingChainMajorant w qP b1 b2 Gamma label *
          XiR w qP Gamma label +
        (occurrenceTreeMajorant w Gamma qP b1 b2 label Gamma.length *
          XiR w qP Gamma label) * XiR w qP Gamma label := by
  have hcompatible := routedExternalCompatibleSource_global_bound hw
    Gamma qP b1 b2 label
  have hcompatible' :
      qListSum
          (fun entry => occurrencePairWeight w qP b1 b2 Gamma label entry.1)
          (routedExternalCompatibleSource Gamma qP b1 b2) ≤
        connectingChainMajorant w qP b1 b2 Gamma label *
          XiR w qP Gamma label :=
    Q'.le_trans' _ _ _ hcompatible
      (Q'.le_of_eqv
        (occurrenceCarrierXiCodes_sum_eqv_carrier_mul_XiR
          w qP b1 b2 Gamma label))
  have hincompatible :=
    routedExternalIncompatibleSource_treeAnalytic_bound hw
      Gamma qP b1 b2 label
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (exceptionalSource_routedExternal_partition
        w Gamma qP b1 b2 label))
    (Q'.add_le_add hcompatible' hincompatible)

#print axioms occurrenceTreeCarrierCodeWeight_le_relaxed
#print axioms occurrenceTreeCarrierMajorant_le_relaxed
#print axioms relaxedOccurrenceTreeCarrierMajorant_eqv
#print axioms routedExternalIncompatibleSource_treeAnalytic_bound
#print axioms fullExceptionalSource_treeAnalytic_bound

end YMGap.Continuum.XiExceptionalSourceTreeAnalytic
