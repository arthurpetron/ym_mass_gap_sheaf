/-
# A disconnected spectator insertion leaves original covariance unchanged

Both probes may have nonzero connected covariance in their retained region.
When the inserted face belongs to a disjoint spectator region, the old and
new connected numerators each retain the appropriate spectator partition
square. These factors cancel exactly in the original cleared response.

Disjointness includes every retained face and the inserted face, not only
omitted high-spin tails. All nomes and cutoffs are allowed; no positivity,
reciprocal, smallness, spatial estimate, or zero probe covariance is assumed.
-/

import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
import YMGap.Continuum.BF4ExactSlabSpectatorResummation

namespace YMGap.Continuum.BF4ExactSlabResponseInsertionSeparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "nblocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem response_perm (w : Q') (K extent : Nat) {xs ys : List Nat}
    (h : xs.Perm ys) (id : Nat) (p q : RatPoly) :
    response w K extent xs id p q ≈ response w K extent ys id p q := by
  have hz : heatProductHaar w (nblocks extent) extent xs K ≈
      heatProductHaar w (nblocks extent) extent ys K :=
    haar_of_coeff (polynomialProduct_perm (faceHeatPolynomial w K extent) h)
  have hr : heatProductHaar w (nblocks extent) extent (xs++[id]) K ≈
      heatProductHaar w (nblocks extent) extent (ys++[id]) K :=
    haar_of_coeff (polynomialProduct_perm (faceHeatPolynomial w K extent) (h.append_right [id]))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (response_identity w K extent xs id p q))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (qmul (connectedNumerator_perm w K extent (h.append_right [id]) p q) (qmul hz hz))
        (Q'.neg_eqv_congr _ _ (qmul (connectedNumerator_perm w K extent h p q) (qmul hr hr))))
      (response_identity w K extent ys id p q))

private theorem response_zero_of_split (w : Q') (K extent : Nat) (p q : RatPoly)
    (links : List Z4Link)
    (hp : SupportedQuaternionBlocks (nblocks extent) p)
    (hq : SupportedQuaternionBlocks (nblocks extent) q)
    (hlp : LinkLocal extent links p) (hlq : LinkLocal extent links q)
    (core spectators : List Nat) (id : Nat)
    (hd : LinksDisjoint (links++faceLinks extent core) (faceLinks extent (spectators++[id]))) :
    response w K extent (core++spectators) id p q ≈ 0 := by
  have hold : LinksDisjoint (links++faceLinks extent core) (faceLinks extent spectators) := by
    intro link hl hr
    exact hd link hl (faceLinks_mono (fun _ h => List.mem_append.mpr (Or.inl h)) link hr)
  have hfnew : LinksDisjoint (faceLinks extent core) (faceLinks extent (spectators++[id])) :=
    fun link hl hr => hd link (List.mem_append.mpr (Or.inr hl)) hr
  have hfold : LinksDisjoint (faceLinks extent core) (faceLinks extent spectators) :=
    fun link hl hr => hold link (List.mem_append.mpr (Or.inr hl)) hr
  have hcold := numerator_spectator_factorizes w K extent p q links hp hq hlp hlq core spectators hold
  have hcnew := numerator_spectator_factorizes w K extent p q links hp hq hlp hlq core (spectators++[id]) hd
  have hzold := partition_factorizes w K extent core spectators hfold
  have hznew := partition_factorizes w K extent core (spectators++[id]) hfnew
  have hi := Q'.eqv_symm (response_identity w K extent (core++spectators) id p q)
  simp only [List.append_assoc] at hi
  refine Q'.eqv_trans _ _ _ hi ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (qmul hcnew (qmul hzold hzold))
      (Q'.neg_eqv_congr _ _ (qmul hcold (qmul hznew hznew)))) ?_
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.mul (.var 0) (.mul (.var 3) (.var 3)))
        (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.neg (.mul (.mul (.var 0) (.mul (.var 2) (.var 2)))
        (.mul (.mul (.var 1) (.var 3)) (.mul (.var 1) (.var 3))))))
    (.const 0) (by decide) (fun
      | 0 => connectedNumerator w K extent core p q
      | 1 => heatProductHaar w (nblocks extent) extent core K
      | 2 => heatProductHaar w (nblocks extent) extent spectators K
      | _ => heatProductHaar w (nblocks extent) extent (spectators++[id]) K)

/-- A separator of the OLD action isolates the entire inserted face from
both probes. The covariance within the probe region is not assumed zero. -/
theorem response_zero_of_insertion_separator (w : Q') (K extent : Nat)
    (p q : RatPoly) (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (nblocks extent) p)
    (hq : SupportedQuaternionBlocks (nblocks extent) q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q)
    (ids : List Nat) (id : Nat)
    (S : Separator extent (left++right) (edgesOf (slabPlaquetteAt extent id)) ids) :
    response w K extent ids id p q ≈ 0 := by
  have hd : LinksDisjoint ((left++right)++faceLinks extent (cutLeft ids S.cut))
      (faceLinks extent (cutRight ids S.cut++[id])) := by
    intro link hleft hright
    obtain ⟨face, hface, hedge⟩ := List.mem_flatMap.mp hright
    rcases List.mem_append.mp hface with hs | hi
    · exact S.disjoint link hleft
        (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨face, hs, hedge⟩)))
    · have he := List.mem_singleton.mp hi
      subst face
      exact S.disjoint link hleft (List.mem_append.mpr (Or.inl hedge))
  exact Q'.eqv_trans _ _ _ (response_perm w K extent (cut_partition ids S.cut).symm id p q)
    (response_zero_of_split w K extent p q (left++right) hp hq
      (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
      (hr.mono (fun _ h => List.mem_append.mpr (Or.inr h)))
      (cutLeft ids S.cut) (cutRight ids S.cut) id hd)

end YMGap.Continuum.BF4ExactSlabResponseInsertionSeparation

#print axioms YMGap.Continuum.BF4ExactSlabResponseInsertionSeparation.response_zero_of_insertion_separator
