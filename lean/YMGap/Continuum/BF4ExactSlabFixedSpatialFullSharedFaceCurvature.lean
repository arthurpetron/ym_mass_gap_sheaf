/-
# Full original-slice Casimir of a shared-face mixed gradient

For two distinct canonical spatial faces sharing a physical link, the SAME
full-slice polynomial Casimir of their mixed angular gradient is
20 Gamma-6 fp*fq. Each face's four actual incidence rows contributes three;
the shared slot corrects their combined six to the produced local
2 Gamma-6 fp*fq law. Boolean row counts avoid a seven-link decomposition.

No sign is assigned to a weighted insertion of this identity. The initial
two-face algebra does not pay the complete channel error/curvature debt,
warmed-source response, MAIN scaling retention, or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSharedFaceCurvature
import YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCasimir
import YMGap.Continuum.SU2QuaternionCyclicPathCasimir

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFullSharedFaceCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDegree
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyIncidence
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments (observableBlocks_length)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSharedFaceCurvature
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger (idxOf_injective_on_members)
open YMGap.Continuum.Z4DistinctPlaquetteIntersection (common_boundary_links_equal_of_faces_ne)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (eraseIndex select_perm mem_of_mem_erase not_mem_erase)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelCasimirLocality
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct
open YMGap.Continuum.SU2QuaternionBlockLinearCasimir
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionCyclicPathCasimir (activeCasimirPolynomial_carrier)
open YMGap.Continuum.QuaternionHaarExclusiveMixedCasimir
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks plaquette

private def faceChar (width : Nat) (p : Z4Plaq) : RatPoly :=
  characterPolynomial (plaquette width p).scalar 1

private def rowTerm (width : Nat) (p : Z4Plaq) (g : RatPoly) (b : Nat) : RatPoly :=
  if blockRow width b p then polySmul 3 g else polyZero

private def correction (g r : RatPoly) : RatPoly :=
  polyAdd (polySmul (-4) g) (polySmul (-6) r)

private theorem singletonC (b : Nat) (g : RatPoly) :
    RatPolyCoeffEqv (activeCasimirPolynomial [b] g) (polyNeg (blockAngularLaplacian b g)) := by
  change RatPolyCoeffEqv (polyAdd (polyNeg (blockAngularLaplacian b g)) polyZero) _
  exact RatPolyCoeffEqv.add_zero _

private theorem three_scales (a b c d : Q') (g r : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul a g) (polySmul b g))
        (polyAdd (polySmul c g) (polySmul d r)))
      (polyAdd (polySmul ((a+b)+c) g) (polySmul d r)) :=
  ((RatPolyCoeffEqv.add_smul_same a b g).add (RatPolyCoeffEqv.refl _)).trans
    ((RatPolyCoeffEqv.add_assoc _ _ _).symm.trans
      ((RatPolyCoeffEqv.add_smul_same (a+b) c g).add (RatPolyCoeffEqv.refl _)))

private theorem common_rows (width b : Nat) (p q : Z4Plaq) (hne : p ≠ q)
    (l : Z4Link) (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q)
    (hpr : blockRow width b p = true) (hqr : blockRow width b q = true) :
    b = (baseLinks width).idxOf l := by
  obtain ⟨m, hm, hmp, hmb⟩ := (blockRow_iff width b p).mp hpr
  obtain ⟨n, hn, hnq, hnb⟩ := (blockRow_iff width b q).mp hqr
  have hmn := idxOf_injective_on_members hmp hnq (hmb.trans hnb.symm)
  subst n
  have hml := common_boundary_links_equal_of_faces_ne p q hne m l hm hlp hn hlq
  subst m
  exact hmb.symm

private theorem row_degree (width b : Nat) (p : Z4Plaq)
    (hp : p ∈ spatialFaces width) (hr : blockRow width b p = true) :
    HasQuaternionBlockDegree b 1 (faceChar width p) := by
  obtain ⟨m, hm, _, hmb⟩ := (blockRow_iff width b p).mp hr
  simpa only [hmb] using plaquette_character_degree width hp hm

private theorem off_degree (width b : Nat) (p : Z4Plaq)
    (hb : b < N width) (hr : blockRow width b p = false) :
    HasQuaternionBlockDegree b 0 (faceChar width p) :=
  independent_has_degree_zero (blockRow_character_independent width b p hb hr)

private theorem degree_one_casimir {blocks b s pd qd : Nat}
    (hb : b < blocks) (hs : s < blocks) (hne : b ≠ s)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hdp : HasQuaternionBlockDegree b pd p) (hdq : HasQuaternionBlockDegree b qd q)
    (hdegree : pd+qd = 1) :
    HaarCarrierEqv blocks (activeCasimirPolynomial [b] (blockGamma s p q))
      (polySmul 3 (blockGamma s p q)) := by
  have hd := blockGamma_degree_of_ne hne p q hdp hdq
  rw [hdegree] at hd
  have hc := blockCasimir_linear hb _ (blockGamma_supported hs p q hp hq) hd
  exact (RatPolyCoeffEqv.haarCarrier (singletonC b _)).trans
    ((HaarCarrierEqv.neg hc).trans (RatPolyCoeffEqv.haarCarrier
      ((neg_smul _).trans ((RatPolyCoeffEqv.smul_assoc (-1) (-3) _).trans
        (RatPolyCoeffEqv.smul_coefficient
          (by decide : Q'.eqv ((-1 : Q')*(-3)) 3) _)))))

private theorem block_law (width : Nat) (p q : Z4Plaq)
    (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width) (hne : p ≠ q)
    (l : Z4Link) (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q)
    (b : Nat) (hb : b < N width) :
    let s := (baseLinks width).idxOf l
    let g := blockGamma s (faceChar width p) (faceChar width q)
    HaarCarrierEqv (N width) (activeCasimirPolynomial [b] g)
      (polyAdd (polyAdd (rowTerm width p g b) (rowTerm width q g b))
        (if b = s then correction g (polyMul (faceChar width p) (faceChar width q)) else polyZero)) := by
  dsimp only
  let s := (baseLinks width).idxOf l
  let fp := faceChar width p
  let fq := faceChar width q
  let g := blockGamma s fp fq
  change HaarCarrierEqv (N width) (activeCasimirPolynomial [b] g)
    (polyAdd (polyAdd (rowTerm width p g b) (rowTerm width q g b))
      (if b = s then correction g (polyMul fp fq) else polyZero))
  have hs : s < N width := List.idxOf_lt_length_of_mem (incident_mem_baseLinks hp hlp)
  have hfp : SupportedQuaternionBlocks (N width) fp :=
    character_supported (plaquette_supported width (N width) (Nat.le_refl _) p).scalar 1
  have hfq : SupportedQuaternionBlocks (N width) fq :=
    character_supported (plaquette_supported width (N width) (Nat.le_refl _) q).scalar 1
  by_cases hbs : b = s
  · subst b
    have hpr : blockRow width s p = true := (blockRow_iff width s p).mpr
      ⟨l, hlp, incident_mem_baseLinks hp hlp, rfl⟩
    have hqr : blockRow width s q = true := (blockRow_iff width s q).mpr
      ⟨l, hlq, incident_mem_baseLinks hq hlq, rfl⟩
    have hshape : RatPolyCoeffEqv
        (polyAdd (polyAdd (polySmul 3 g) (polySmul 3 g)) (correction g (polyMul fp fq)))
        (polyAdd (polySmul 2 g) (polySmul (-6) (polyMul fp fq))) :=
      (three_scales 3 3 (-4) (-6) g _).trans
        ((RatPolyCoeffEqv.smul_coefficient
          (by decide : Q'.eqv (((3 : Q')+3)+(-4)) 2) g).add (RatPolyCoeffEqv.refl _))
    have h := (incident_pair_gamma_casimir width p q hp hq l hlp hlq).trans
      (RatPolyCoeffEqv.haarCarrier hshape.symm)
    simpa only [rowTerm, hpr, hqr, if_pos rfl, ↓reduceIte] using h
  · cases hpr : blockRow width b p <;> cases hqr : blockRow width b q
    · have h := RatPolyCoeffEqv.haarCarrier (blocks := N width)
        (blockGamma_outside_casimir_zero hbs fp fq
          (off_degree width b p hb hpr) (off_degree width b q hb hqr))
      simpa only [rowTerm, hpr, hqr, if_neg hbs, Bool.false_eq_true,
        ↓reduceIte, polyAdd, polyZero] using h
    · have h := degree_one_casimir hb hs hbs fp fq hfp hfq
        (off_degree width b p hb hpr) (row_degree width b q hq hqr) (by decide)
      have ht : RatPolyCoeffEqv (polyAdd (polyAdd polyZero (polySmul 3 g)) polyZero) (polySmul 3 g) :=
        ((RatPolyCoeffEqv.zero_add _).add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.add_zero _)
      simpa only [rowTerm, hpr, hqr, if_neg hbs, Bool.false_eq_true, ↓reduceIte]
        using h.trans (RatPolyCoeffEqv.haarCarrier ht.symm)
    · have h := degree_one_casimir hb hs hbs fp fq hfp hfq
        (row_degree width b p hp hpr) (off_degree width b q hb hqr) (by decide)
      have ht : RatPolyCoeffEqv (polyAdd (polyAdd (polySmul 3 g) polyZero) polyZero) (polySmul 3 g) :=
        ((RatPolyCoeffEqv.add_zero _).add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.add_zero _)
      simpa only [rowTerm, hpr, hqr, if_neg hbs, Bool.false_eq_true, ↓reduceIte]
        using h.trans (RatPolyCoeffEqv.haarCarrier ht.symm)
    · exact False.elim (hbs (common_rows width b p q hne l hlp hlq hpr hqr))

private theorem sum_carrier {blocks : Nat} (f g : Nat → RatPoly) :
    ∀ ids : List Nat, (∀ b, b ∈ ids → HaarCarrierEqv blocks (f b) (g b)) →
      HaarCarrierEqv blocks (polySum (ids.map f)) (polySum (ids.map g))
  | [], _ => HaarCarrierEqv.refl _ _
  | b::bs, h => HaarCarrierEqv.add (h b List.mem_cons_self)
      (sum_carrier f g bs (fun c hc => h c (List.mem_cons_of_mem b hc)))

private theorem sum_add (f g : Nat → RatPoly) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polySum (ids.map fun b => polyAdd (f b) (g b)))
      (polyAdd (polySum (ids.map f)) (polySum (ids.map g)))
  | [] => RatPolyCoeffEqv.refl _
  | b::bs => ((RatPolyCoeffEqv.refl _).add (sum_add f g bs)).trans
      (RatPolyCoeffEqv.four_add_swap _ _ _ _)

private theorem sum_perm (f : Nat → RatPoly) {xs ys : List Nat} (h : xs.Perm ys) :
    RatPolyCoeffEqv (polySum (xs.map f)) (polySum (ys.map f)) := by
  induction h with
  | nil => exact .refl _
  | cons _ _ ih => exact (RatPolyCoeffEqv.refl _).add ih
  | swap b c bs =>
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.add (.var 1) (.var 2)))
      (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
      (fun | 0 => f c | 1 => f b | _ => polySum (bs.map f))
  | trans _ _ ih ih' => exact ih.trans ih'

private theorem sum_zero (f : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ b, b ∈ ids → RatPolyCoeffEqv (f b) polyZero) →
    RatPolyCoeffEqv (polySum (ids.map f)) polyZero
  | [], _ => .refl _
  | b::bs, h => ((h b List.mem_cons_self).add
      (sum_zero f bs (fun c hc => h c (List.mem_cons_of_mem b hc)))).trans
        (RatPolyCoeffEqv.add_zero _)

private def copies (p : RatPoly) : Nat → RatPoly
  | 0 => polyZero
  | n+1 => polyAdd p (copies p n)

private theorem sum_count (row : Nat → Bool) (p : RatPoly) : ∀ ids : List Nat,
    RatPolyCoeffEqv (polySum (ids.map fun b => if row b then p else polyZero))
      (copies p (ids.filter row).length)
  | [] => .refl _
  | b::bs => by
      cases hr : row b
      · simpa only [List.map_cons, polySum, hr, Bool.false_eq, ↓reduceIte,
          List.filter_cons] using
          (((RatPolyCoeffEqv.refl polyZero).add (sum_count row p bs)).trans
            (RatPolyCoeffEqv.zero_add _))
      · simpa only [List.map_cons, polySum, hr, Bool.true_eq, ↓reduceIte,
          List.filter_cons, List.length_cons, copies] using
          (RatPolyCoeffEqv.refl p).add (sum_count row p bs)

private theorem copies_four (g : RatPoly) :
    RatPolyCoeffEqv (copies (polySmul 3 g) 4) (polySmul 12 g) := by
  have h3 := RatPolyCoeffEqv.add_zero (polySmul 3 g)
  have h6 : RatPolyCoeffEqv (copies (polySmul 3 g) 2) (polySmul 6 g) :=
    ((RatPolyCoeffEqv.refl _).add h3).trans
      ((RatPolyCoeffEqv.add_smul_same 3 3 g).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv ((3 : Q')+3) 6) g))
  have h9 : RatPolyCoeffEqv (copies (polySmul 3 g) 3) (polySmul 9 g) :=
    ((RatPolyCoeffEqv.refl _).add h6).trans
      ((RatPolyCoeffEqv.add_smul_same 3 6 g).trans
        (RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv ((3 : Q')+6) 9) g))
  exact ((RatPolyCoeffEqv.refl _).add h9).trans
    ((RatPolyCoeffEqv.add_smul_same 3 9 g).trans
      (RatPolyCoeffEqv.smul_coefficient (by decide : Q'.eqv ((3 : Q')+9) 12) g))

private theorem row_filter (width : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) :
    (List.range (N width)).filter (fun b => blockRow width b p) = observableBlocks width p := by
  have hrow : (fun b => blockRow width b p) = (fun b => decide (b ∈ faceSlots width p)) := by
    funext b
    by_cases hb : b ∈ faceSlots width p
    · obtain ⟨l, hl, hidx⟩ := List.mem_map.mp hb
      have ht := (blockRow_iff width b p).mpr ⟨l, hl, incident_mem_baseLinks hp hl, hidx⟩
      simp only [ht, hb, decide_true]
    · have ht : blockRow width b p = false := by
        cases hr : blockRow width b p
        · rfl
        · obtain ⟨l, hl, _, hidx⟩ := (blockRow_iff width b p).mp hr
          exact False.elim (hb (List.mem_map.mpr ⟨l, hl, hidx⟩))
      simp only [ht, hb, decide_false]
  rw [hrow]
  rfl

private theorem row_sum (width : Nat) (p : Z4Plaq) (hp : p ∈ spatialFaces width) (g : RatPoly) :
    RatPolyCoeffEqv (polySum ((List.range (N width)).map (rowTerm width p g))) (polySmul 12 g) := by
  have h := sum_count (fun b => blockRow width b p) (polySmul 3 g) (List.range (N width))
  rw [row_filter width p hp, observableBlocks_length width p hp] at h
  exact h.trans (copies_four g)

private theorem singleton_sum (n s : Nat) (hs : s < n) (c : RatPoly) :
    RatPolyCoeffEqv (polySum ((List.range n).map fun b => if b = s then c else polyZero)) c := by
  let f := fun b => if b = s then c else polyZero
  have hz := sum_zero f (eraseIndex s (List.range n)) (fun b hb => by
    have hne : b ≠ s := by
      intro he
      subst b
      exact not_mem_erase s (YMGap.Continuum.CayleyParentInj.range_nodup n) hb
    simpa only [f, if_neg hne] using RatPolyCoeffEqv.refl polyZero)
  have ht : RatPolyCoeffEqv (polySum ((s::eraseIndex s (List.range n)).map f)) c := by
    simpa only [List.map_cons, polySum, f, if_pos rfl] using
      (((RatPolyCoeffEqv.refl c).add hz).trans (RatPolyCoeffEqv.add_zero c))
  exact (sum_perm f (select_perm s (List.mem_range.mpr hs))).trans ht

/-- The complete original slice Casimir on the shared-block mixed gradient.
The two incidence counts and the shared correction are all produced. -/
theorem distinct_pair_sharedGamma_full_casimir
    (width : Nat) (p q : Z4Plaq) (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width)
    (hne : p ≠ q) (l : Z4Link) (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q) :
    let fp := characterPolynomial (plaquette width p).scalar 1
    let fq := characterPolynomial (plaquette width q).scalar 1
    let g := blockGamma ((baseLinks width).idxOf l) fp fq
    HaarCarrierEqv (N width) (activeCasimirPolynomial (List.range (N width)) g)
      (polyAdd (polySmul 20 g) (polySmul (-6) (polyMul fp fq))) := by
  dsimp only
  let fp := faceChar width p
  let fq := faceChar width q
  let s := (baseLinks width).idxOf l
  let g := blockGamma s fp fq
  let c := correction g (polyMul fp fq)
  let rp := rowTerm width p g
  let rq := rowTerm width q g
  let delta := fun b => if b = s then c else polyZero
  let ids := List.range (N width)
  have hs : s < N width := List.idxOf_lt_length_of_mem (incident_mem_baseLinks hp hlp)
  have h := sum_carrier (fun b => polyNeg (blockAngularLaplacian b g))
    (fun b => polyAdd (polyAdd (rp b) (rq b)) (delta b)) ids (fun b hb =>
      (RatPolyCoeffEqv.haarCarrier (singletonC b g)).symm.trans
        (block_law width p q hp hq hne l hlp hlq b (List.mem_range.mp hb)))
  have hsplit := (sum_add (fun b => polyAdd (rp b) (rq b)) delta ids).trans
    ((sum_add rp rq ids).add (RatPolyCoeffEqv.refl _))
  have hcount := ((row_sum width p hp g).add (row_sum width q hq g)).add
    (singleton_sum (N width) s hs c)
  have hcollapse : RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul 12 g) (polySmul 12 g)) c)
      (polyAdd (polySmul 20 g) (polySmul (-6) (polyMul fp fq))) :=
    (three_scales 12 12 (-4) (-6) g _).trans
      ((RatPolyCoeffEqv.smul_coefficient
        (by decide : Q'.eqv (((12 : Q')+12)+(-4)) 20) g).add (RatPolyCoeffEqv.refl _))
  exact h.trans (RatPolyCoeffEqv.haarCarrier (hsplit.trans (hcount.trans hcollapse)))

/-- Literal full Gamma and full Casimir for the two original distinct faces.
No source, weight, incidence or normalization is replaced. -/
theorem distinct_pair_full_gamma_casimir
    (width : Nat) (p q : Z4Plaq) (hp : p ∈ spatialFaces width) (hq : q ∈ spatialFaces width)
    (hne : p ≠ q) (l : Z4Link) (hlp : l ∈ edgesOf p) (hlq : l ∈ edgesOf q) :
    let fp := characterPolynomial (plaquette width p).scalar 1
    let fq := characterPolynomial (plaquette width q).scalar 1
    let g := activeGamma (List.range (N width)) fp fq
    HaarCarrierEqv (N width) (activeCasimirPolynomial (List.range (N width)) g)
      (polyAdd (polySmul 20 g) (polySmul (-6) (polyMul fp fq))) := by
  dsimp only
  have hlocal := distinct_pair_activeGamma_localizes width p q hp hq hne l hlp hlq
  have hC := activeCasimirPolynomial_carrier (List.range (N width))
    (fun b hb => List.mem_range.mp hb) hlocal
  exact hC.trans ((distinct_pair_sharedGamma_full_casimir width p q hp hq hne l hlp hlq).trans
    (HaarCarrierEqv.add (HaarCarrierEqv.smul 20 hlocal.symm) (HaarCarrierEqv.refl (N width) _)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFullSharedFaceCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFullSharedFaceCurvature.distinct_pair_sharedGamma_full_casimir
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFullSharedFaceCurvature.distinct_pair_full_gamma_casimir
