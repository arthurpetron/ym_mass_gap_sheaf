/-
# Conditional Bessel bound at an arbitrary selected block

The literal Gram list at a selected block is transported to the head list by
the constructive head transposition.  Raw polynomial equality is deliberately
not used: block reindexing pads exponent vectors, so the channel leaves are
related by finite-prefix equality and then by the existing Haar carrier.
-/

import YMGap.Continuum.SU2QuaternionHeadHeatGramBessel
import YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
import YMGap.Continuum.SU2QuaternionAngularReindex
import YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionPolynomialGramPositivity
open YMGap.Continuum.SU2QuaternionCoordinateColumnLift
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionSelectedProjectionReindex
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHeadHeatGramBessel
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private def ReindexImage {n : Nat} (s : QuaternionBlockInvolution n)
    (p q : RatPoly) : Prop :=
  QuaternionPrefixPolynomialEqv n (reindexQuaternionPolynomial s p) q

private def TensorRelates (R : RatPoly → RatPoly → Prop) :
    (degree : Nat) → PolyTensor degree → PolyTensor degree → Prop
  | 0, x, y => R x.1 y.1 ∧ R x.2 y.2
  | degree + 1, x, y => ∀ bit, TensorRelates R degree (x bit) (y bit)

private inductive ListRel {A B : Type} (R : A → B → Prop) : List A → List B → Prop
  | nil : ListRel R [] []
  | cons {a b as bs} : R a b → ListRel R as bs → ListRel R (a :: as) (b :: bs)

private theorem ListRel.append {A B : Type} {R : A → B → Prop} :
    ∀ {as bs cs ds}, ListRel R as bs → ListRel R cs ds → ListRel R (as ++ cs) (bs ++ ds)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hab hs, h => .cons hab (ListRel.append hs h)

private theorem image_zero {n : Nat} (s : QuaternionBlockInvolution n) :
    ReindexImage s polyZero polyZero := .nil

private theorem image_one {n : Nat} (s : QuaternionBlockInvolution n) :
    ReindexImage s polyOne polyOne := by
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro coordinate hc
      rw [exponentAt_reindexQuaternionExponents s [] hc]
      simp [exponentAt]
  · exact .nil

private theorem image_add {n : Nat} {s : QuaternionBlockInvolution n}
    {p p' q q' : RatPoly} (hp : ReindexImage s p p') (hq : ReindexImage s q q') :
    ReindexImage s (polyAdd p q) (polyAdd p' q') := by
  unfold ReindexImage at *
  rw [reindexQuaternionPolynomial_add]
  exact hp.append hq

private theorem image_neg {n : Nat} {s : QuaternionBlockInvolution n}
    {p q : RatPoly} (h : ReindexImage s p q) :
    ReindexImage s (polyNeg p) (polyNeg q) := by
  unfold ReindexImage at *
  rw [reindexQuaternionPolynomial_neg]
  exact h.neg

private theorem image_mul {n : Nat} {s : QuaternionBlockInvolution n}
    {p p' q q' : RatPoly} (hp : ReindexImage s p p') (hq : ReindexImage s q q') :
    ReindexImage s (polyMul p q) (polyMul p' q') := by
  unfold ReindexImage at *
  rw [reindexQuaternionPolynomial_mul]
  exact hp.mul hq

private def ComplexImage {n : Nat} (s : QuaternionBlockInvolution n)
    (p q : ComplexRatPoly) : Prop := ReindexImage s p.1 q.1 ∧ ReindexImage s p.2 q.2

private theorem complex_add {n : Nat} {s : QuaternionBlockInvolution n}
    {p p' q q' : ComplexRatPoly} (hp : ComplexImage s p p') (hq : ComplexImage s q q') :
    ComplexImage s (complexRatPolyAdd p q) (complexRatPolyAdd p' q') :=
  ⟨image_add hp.1 hq.1, image_add hp.2 hq.2⟩

private theorem complex_mul {n : Nat} {s : QuaternionBlockInvolution n}
    {p p' q q' : ComplexRatPoly} (hp : ComplexImage s p p') (hq : ComplexImage s q q') :
    ComplexImage s (complexRatPolyMul p q) (complexRatPolyMul p' q') :=
  ⟨image_add (image_mul hp.1 hq.1) (image_neg (image_mul hp.2 hq.2)),
    image_add (image_mul hp.1 hq.2) (image_mul hp.2 hq.1)⟩

private theorem tensor_add {n : Nat} {s : QuaternionBlockInvolution n} :
    ∀ {degree} {x x' y y' : PolyTensor degree},
      TensorRelates (ReindexImage s) degree x x' →
      TensorRelates (ReindexImage s) degree y y' →
      TensorRelates (ReindexImage s) degree
        (polyTensorAdd degree x y) (polyTensorAdd degree x' y')
  | 0, _, _, _, _, hx, hy => complex_add hx hy
  | _ + 1, _, _, _, _, hx, hy => fun bit => tensor_add (hx bit) (hy bit)

private theorem tensor_scale {n : Nat} {s : QuaternionBlockInvolution n}
    {a b : ComplexRatPoly} (hab : ComplexImage s a b) :
    ∀ {degree} {x y : PolyTensor degree}, TensorRelates (ReindexImage s) degree x y →
      TensorRelates (ReindexImage s) degree
        (polyTensorScale degree a x) (polyTensorScale degree b y)
  | 0, _, _, h => complex_mul hab h
  | _ + 1, _, _, h => fun bit => tensor_scale hab (h bit)

private theorem matrix_action {n : Nat} {s : QuaternionBlockInvolution n}
    {M N : PolynomialMatrix} (hMN : ∀ i j, ComplexImage s (M i j) (N i j)) :
    ∀ {degree} {x y : PolyTensor degree}, TensorRelates (ReindexImage s) degree x y →
      TensorRelates (ReindexImage s) degree
        (polyMatrixAction degree M x) (polyMatrixAction degree N y)
  | 0, _, _, h => h
  | _ + 1, _, _, h => fun row => tensor_add
      (tensor_scale (hMN row false) (matrix_action hMN (h false)))
      (tensor_scale (hMN row true) (matrix_action hMN (h true)))

private theorem embed_image {n : Nat} {s : QuaternionBlockInvolution n} :
    ∀ degree (f g : Nat → ComplexRatPoly), (∀ k, ComplexImage s (f k) (g k)) →
      TensorRelates (ReindexImage s) degree (polyEmbed degree f) (polyEmbed degree g)
  | 0, _, _, h => h 0
  | degree + 1, f, g, h => by
      intro bit
      cases bit
      · exact embed_image degree f g h
      · exact embed_image degree (fun k => f (k+1)) (fun k => g (k+1)) (fun k => h (k+1))

private theorem basis_image {n k j : Nat} (s : QuaternionBlockInvolution n) :
    ComplexImage s (polynomialBasis k j) (polynomialBasis k j) := by
  unfold polynomialBasis
  split
  · exact ⟨image_one s, image_zero s⟩
  · exact ⟨image_zero s, image_zero s⟩

private theorem fundamental_image {n slot : Nat} (s : QuaternionBlockInvolution n)
    (hslot : slot < n) : ∀ row column,
    ComplexImage s
      (fundamentalMatrixCoefficient
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) row column)
      (fundamentalMatrixCoefficient
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable (s.map slot))) row column) := by
  have hc (component : Nat) (hcomponent : component < 4) :=
    reindex_coordinate_prefix s slot hslot component hcomponent
  intro row column
  cases row <;> cases column
  · exact ⟨by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 0 (by omega),
      by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 1 (by omega)⟩
  · exact ⟨by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 2 (by omega),
      by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 3 (by omega)⟩
  · exact ⟨image_neg (by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 2 (by omega)),
      by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 3 (by omega)⟩
  · exact ⟨by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 0 (by omega),
      image_neg (by simpa [ReindexImage, asRepresentationQuaternion, PolyQuaternion.coordinateVariable] using hc 1 (by omega))⟩

private theorem column_image {n slot degree k : Nat} (s : QuaternionBlockInvolution n)
    (hslot : slot < n) :
    TensorRelates (ReindexImage s) degree
      (polynomialColumn
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k)
      (polynomialColumn
        (asRepresentationQuaternion (PolyQuaternion.coordinateVariable (s.map slot))) degree k) :=
  matrix_action (fundamental_image s hslot)
    (embed_image degree _ _ (fun j => basis_image (k := k) (j := j) s))

private def LeafImage {n : Nat} (s : QuaternionBlockInvolution n) (p q : RatPoly) : Prop :=
  ReindexImage s p q ∧ SupportedQuaternionBlocks n p ∧ SupportedQuaternionBlocks n q

private theorem leaves_image {n degree : Nat} {s : QuaternionBlockInvolution n}
    {x y : PolyTensor degree} (hxy : TensorRelates (ReindexImage s) degree x y)
    (hx : PolyTensorSupported n degree x) (hy : PolyTensorSupported n degree y) :
    ListRel (LeafImage s) (tensorLeaves degree x) (tensorLeaves degree y) := by
  induction degree with
  | zero => exact .cons ⟨hxy.1, hx.1, hy.1⟩ (.cons ⟨hxy.2, hx.2, hy.2⟩ .nil)
  | succ degree ih =>
      exact ListRel.append (ih (hxy false) (hx false) (hy false))
        (ih (hxy true) (hx true) (hy true))

private theorem forall₂_map {A B C D : Type} {R : A → B → Prop}
    {S : C → D → Prop} (f : A → C) (g : B → D)
    (h : ∀ a b, R a b → S (f a) (g b)) :
    ∀ {as bs}, ListRel R as bs → ListRel S (as.map f) (bs.map g)
  | _, _, .nil => .nil
  | _, _, .cons hab hs => .cons (h _ _ hab) (forall₂_map f g h hs)

private theorem forall₂_flatMap {A B C D : Type} {R : A → B → Prop}
    {S : C → D → Prop} (f : A → List C) (g : B → List D)
    (h : ∀ a b, R a b → ListRel S (f a) (g b)) :
    ∀ {as bs}, ListRel R as bs → ListRel S (as.flatMap f) (bs.flatMap g)
  | _, _, .nil => .nil
  | _, _, .cons hab hs => ListRel.append (h _ _ hab) (forall₂_flatMap f g h hs)

private theorem forall₂_refl {A : Type} (R : A → A → Prop) (h : ∀ a, R a a) :
    ∀ xs, ListRel R xs xs
  | [] => .nil
  | a :: xs => .cons (h a) (forall₂_refl R h xs)

private def ChannelImage {n : Nat} (s : QuaternionBlockInvolution n)
    (a b : GramChannel) : Prop := a.1 = b.1 ∧ LeafImage s a.2 b.2

private theorem heatChannels_image {n slot : Nat} (s : QuaternionBlockInvolution n)
    (hslot : slot < n) (w : Q') (K : Nat) :
    ListRel (ChannelImage s) (heatChannels slot w K) (heatChannels (s.map slot) w K) := by
  apply forall₂_flatMap _ _ (fun degree degree' hdegree => ?_)
    (forall₂_refl (fun a b : Nat => a = b) (fun _ => rfl) (List.range (K+1)))
  subst degree'
  apply forall₂_flatMap _ _ (fun k k' hk => ?_)
    (forall₂_refl (fun a b : Nat => a = b) (fun _ => rfl) (List.range (degree+1)))
  subst k'
  apply forall₂_map _ _ (fun p q hp => ?_)
    (leaves_image (column_image s hslot (degree := degree) (k := k))
      (coordinateColumn_supported hslot degree k)
      (coordinateColumn_supported (s.map_lt slot hslot) degree k))
  exact ⟨rfl, hp⟩

private theorem support_smul {n : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

private theorem reindex_supported {n : Nat} (s : QuaternionBlockInvolution n) (p : RatPoly) :
    SupportedQuaternionBlocks n (reindexQuaternionPolynomial s p) := by
  intro t ht
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht
  exact Nat.le_of_eq (reindexQuaternionExponents_length s u.1)

private theorem project_square_carrier {n block : Nat} (hblock : block < n)
    {p q : RatPoly}
    (h : HaarCarrierEqv n p q) :
    H n (polyMul (project block p) (project block p)) ≈
      H n (polyMul (project block q) (project block q)) := by
  have hidem (r t : RatPoly) : H n (polyMul r (project block (project block t))) ≈
      H n (polyMul r (project block t)) :=
    haar_of_coeff ((project_idempotent block t).mul_left r)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _ (project_selfAdjoint n block hblock p (project block p))
      (hidem p p))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (h (project block p))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
          (Q'.eqv_trans _ _ _
            (Q'.eqv_symm (project_selfAdjoint n block hblock q p))
            (Q'.eqv_trans _ _ _ (h (project block q))
              (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
                (Q'.eqv_trans _ _ _
                  (Q'.eqv_symm (hidem q q))
                  (Q'.eqv_symm
                    (project_selfAdjoint n block hblock q (project block q))))))))))

private theorem channel_value_image {n slot : Nat} (hslot : slot < n)
    (s : QuaternionBlockInvolution n) (hs : s.map slot = 0)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) {a b : GramChannel}
    (hab : ChannelImage s a b) :
    H n (polyMul (project slot (polyMul q a.2)) (project slot (polyMul q a.2))) ≈
      H n (polyMul (project 0 (polyMul (reindexQuaternionPolynomial s q) b.2))
        (project 0 (polyMul (reindexQuaternionPolynomial s q) b.2))) := by
  have hleafA : SupportedQuaternionBlocks n a.2 := hab.2.2.1
  have hleafB : SupportedQuaternionBlocks n b.2 := hab.2.2.2
  have hpref : QuaternionPrefixPolynomialEqv n
      (polyMul (reindexQuaternionPolynomial s q) (reindexQuaternionPolynomial s a.2))
      (polyMul (reindexQuaternionPolynomial s q) b.2) :=
    (QuaternionPrefixPolynomialEqv.refl n _).mul hab.2.1
  have hcar := carrierOfPrefix
    (supported_polyMul (reindex_supported s q) (reindex_supported s a.2))
    (supported_polyMul (reindex_supported s q) hleafB) hpref
  have hre := reindex_integrateQuaternionBlock s slot hslot (polyMul q a.2)
  rw [reindexQuaternionPolynomial_mul] at hre
  have hchange := quaternionHaar_reindex s
    (polyMul (project slot (polyMul q a.2)) (project slot (polyMul q a.2)))
    (supported_polyMul (project_supported slot (supported_polyMul hq hleafA))
      (project_supported slot (supported_polyMul hq hleafA)))
  rw [reindexQuaternionPolynomial_mul] at hchange
  have hproject : RatPolyCoeffEqv
      (reindexQuaternionPolynomial s (project slot (polyMul q a.2)))
      (project 0 (polyMul (reindexQuaternionPolynomial s q)
        (reindexQuaternionPolynomial s a.2))) := by simpa [hs] using hre
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hchange)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hproject.mul hproject))
      (project_square_carrier (by omega) hcar))

private theorem channelSum_image {n slot : Nat} (hslot : slot < n)
    (s : QuaternionBlockInvolution n) (hs : s.map slot = 0)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    ∀ {as bs}, ListRel (ChannelImage s) as bs →
      channelSum as (fun h => H n (polyMul (project slot (polyMul q h))
        (project slot (polyMul q h)))) ≈
      channelSum bs (fun h => H n (polyMul
        (project 0 (polyMul (reindexQuaternionPolynomial s q) h))
        (project 0 (polyMul (reindexQuaternionPolynomial s q) h))))
  | _, _, .nil => Q'.eqv_refl _
  | _, _, .cons hab hrest => Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_of_eq hab.1))
        (Q'.mul_eqv_congr_left _ _ _ (channel_value_image hslot s hs q hq hab)))
      (channelSum_image hslot s hs q hq hrest)

/-- The coefficient-one channel Bessel bound at an arbitrary selected block. -/
theorem heatChannels_project_square_le_at (n slot : Nat) (hslot : slot < n) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    channelSum (heatChannels slot w K) (fun h => H n
      (polyMul (project slot (polyMul q h)) (project slot (polyMul q h)))) ≤
      H n (polyMul q q) := by
  have hn : (n-1)+1 = n := by omega
  let s := headSwapBlockInvolution n slot hslot
  have hs : s.map slot = 0 := headSwapBlockInvolution_map_selected n slot hslot
  have himage := heatChannels_image s hslot w K
  rw [hs] at himage
  have hsum := channelSum_image hslot s hs q hq himage
  have hqs : SupportedQuaternionBlocks ((n-1)+1) (reindexQuaternionPolynomial s q) := by
    rw [hn]
    exact reindex_supported s q
  have hhead0 := heatChannels_project_square_le (n-1) hw0 hw1 K
    (reindexQuaternionPolynomial s q) hqs
  have hhead : channelSum (heatChannels 0 w K) (fun h => H n
      (polyMul (project 0 (polyMul (reindexQuaternionPolynomial s q) h))
        (project 0 (polyMul (reindexQuaternionPolynomial s q) h)))) ≤
      H n (polyMul (reindexQuaternionPolynomial s q) (reindexQuaternionPolynomial s q)) := by
    simpa only [hn] using hhead0
  have hnorm := quaternionHaar_reindex s (polyMul q q) (supported_polyMul hq hq)
  rw [reindexQuaternionPolynomial_mul] at hnorm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (Q'.le_trans' _ _ _ hhead (Q'.le_of_eqv hnorm))

/-- At one arbitrary selected block, the norm lost by the complete Gram
channel analysis is bounded by the sharp local angular defect. -/
theorem heatChannels_project_square_loss_le_at (n slot : Nat) (hslot : slot < n)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (p : RatPoly)
    (hp : SupportedQuaternionBlocks n p) :
    H n (polyMul p p) -
        channelSum (heatChannels slot w K) (fun h => H n
          (polyMul (project slot (polyMul p h)) (project slot (polyMul p h)))) ≤
      ((1 : Q')-w) * H n (blockAngularSquare slot p) := by
  have hn : (n-1)+1 = n := by omega
  let s := headSwapBlockInvolution n slot hslot
  have hs : s.map slot = 0 := headSwapBlockInvolution_map_selected n slot hslot
  have hs0 : s.map 0 = slot := headSwapBlockInvolution_map_zero n slot hslot
  have himage := heatChannels_image s hslot w K
  rw [hs] at himage
  have hsum := channelSum_image hslot s hs p hp himage
  let p' := reindexQuaternionPolynomial s p
  have hp' : SupportedQuaternionBlocks ((n-1)+1) p' := by
    rw [hn]
    exact reindex_supported s p
  have hpair0 := heatChannels_project_square_eq_pair (n-1) w K p' hp'
  have hpair : channelSum (heatChannels 0 w K) (fun h => H n
      (polyMul (project 0 (polyMul p' h)) (project 0 (polyMul p' h)))) ≈
      H n (polyMul p' (headMap w K p')) := by
    simpa only [hn] using hpair0
  have hnorm := quaternionHaar_reindex s (polyMul p p) (supported_polyMul hp hp)
  rw [reindexQuaternionPolynomial_mul] at hnorm
  have hloss : H n (polyMul p p) -
      channelSum (heatChannels slot w K) (fun h => H n
        (polyMul (project slot (polyMul p h)) (project slot (polyMul p h)))) ≈
      H n (polyMul p' p') - H n (polyMul p' (headMap w K p')) :=
    Q'.add_eqv_congr' (Q'.eqv_symm hnorm)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _ hsum hpair))
  have hdef0 := headMap_defect_le_angular (n-1) hw0 hw1 K hK p' hp'
  have hdef : H n (polyMul p' p') - H n (polyMul p' (headMap w K p')) ≤
      ((1 : Q')-w) * H n (angularSquare p') := by
    simpa only [hn] using hdef0
  have hangReindex := reindex_blockAngularSquare_haar s (by omega : 0 < n) p
  rw [hs0] at hangReindex
  have hangNorm := quaternionHaar_reindex s (blockAngularSquare slot p)
    (blockAngularSquare_supported hslot hp)
  have hang : H n (angularSquare p') ≈ H n (blockAngularSquare slot p) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hangReindex) hangNorm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hloss)
    (Q'.le_trans' _ _ _ hdef
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hang)))

end YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel

#print axioms YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel.heatChannels_project_square_le_at
#print axioms YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel.heatChannels_project_square_loss_le_at
