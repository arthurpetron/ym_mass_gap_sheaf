/-
# Angular contraction through explicit spectator Gram channels

For a block outside the projected spectator family, angular differentiation
commutes with the family projection.  The computed channel polynomial is also
independent of that block, so Leibniz reduces the derivative to the source
derivative.  The family Gram Bessel inequality then contracts each angular
plane with coefficient one.
-/

import YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
import YMGap.Continuum.SU2QuaternionProductHeatSharpAngularDefect
import YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
import YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction

namespace YMGap.Continuum.SU2QuaternionChannelAngularContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramLocality
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.SU2QuaternionSelectedHeatGramBessel
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionProductHeatSharpAngularDefect
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local notation "H" => quaternionHaar
local infix:50 " ≈ " => Q'.eqv

/-- Angular energy summed over an explicit list of original block indices. -/
def angularListSum (n : Nat) (ids : List Nat) (p : RatPoly) : Q' :=
  qListSum (ids.map fun i => H n (blockAngularSquare i p))

private theorem qsum_append : ∀ left right : List Q',
    qListSum (left ++ right) ≈ qListSum left + qListSum right
  | [], _ => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | _::xs, right => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (qsum_append xs right))
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem qsum_perm {left right : List Q'} (h : left.Perm right) :
    qListSum left ≈ qListSum right := by
  induction h with
  | nil => exact Q'.eqv_refl _
  | cons x _ ih => exact Q'.add_eqv_congr' (Q'.eqv_refl x) ih
  | swap x y rest =>
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
        (fun | 0 => y | 1 => x | _ => qListSum rest)
  | trans _ _ ih ih' => exact Q'.eqv_trans _ _ _ ih ih'

theorem angularListSum_append (n : Nat) (left right : List Nat) (p : RatPoly) :
    angularListSum n (left ++ right) p ≈
      angularListSum n left p + angularListSum n right p := by
  unfold angularListSum
  rw [List.map_append]
  exact qsum_append _ _

theorem angularListSum_perm (n : Nat) {left right : List Nat}
    (h : left.Perm right) (p : RatPoly) :
    angularListSum n left p ≈ angularListSum n right p := by
  unfold angularListSum
  exact qsum_perm (h.map (fun i => H n (blockAngularSquare i p)))

private theorem qsum_map_range (f : Nat → Q') : ∀ m,
    qListSum ((List.range m).map f) ≈ finSum f m
  | 0 => Q'.eqv_refl _
  | m+1 => by
      rw [List.range_succ, List.map_append]
      exact Q'.eqv_trans _ _ _ (qsum_append _ _)
        (Q'.add_eqv_congr' (qsum_map_range f m) (QPoly.q_add_zero_eqv _))

theorem angularListSum_range (n : Nat) (p : RatPoly) :
    angularListSum n (List.range n) p ≈
      finSum (fun i => H n (blockAngularSquare i p)) n :=
  qsum_map_range (fun i => H n (blockAngularSquare i p)) n

/-- Outside the projected family, differentiating a channel source differentiates
only the original source; the computed channel multiplier is local to `ids`. -/
theorem blockDerivative_channelSource (ids : List Nat)
    (block i j : Nat) (hi : i < 4) (hj : j < 4) (hnot : block ∉ ids)
    (q c : RatPoly) (hc : QuaternionBlockIndependent block c) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j (channelSource ids q c))
      (familyProject ids
        (polyMul (blockAngularDerivative block i j q) c)) := by
  have hcomm := blockAngularDerivative_familyProject ids block i j hi hj hnot
    (polyMul q c)
  have hzero := angularDerivative_blockIndependent_zero hi hj hc
  have hleib := angularDerivative_mul (4*block+i) (4*block+j) q c
  have hsimpl : RatPolyCoeffEqv
      (blockAngularDerivative block i j (polyMul q c))
      (polyMul (blockAngularDerivative block i j q) c) := by
    unfold blockAngularDerivative
    exact hleib.trans (((RatPolyCoeffEqv.refl _).add
      ((hzero.mul_left q).trans (RatPolyCoeffEqv.mul_zero_right q))).trans
        (RatPolyCoeffEqv.add_zero _))
  exact hcomm.trans (familyProject_congr ids hsimpl)

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_add (f g : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun p => f p+g p) ≈ channelSum cs f+channelSum cs g
  | [] => by change (0 : Q') ≈ 0+0; decide
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_add_eqv _ _ _) (channelSum_add f g cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
        (fun | 0 => c.1*f c.2 | 1 => c.1*g c.2
             | 2 => channelSum cs f | _ => channelSum cs g))

private theorem channelSum_six (cs : List GramChannel)
    (value : RatPoly → Nat → Nat → Q') :
    channelSum cs (fun p => sixValue (value p)) ≈
      sixValue (fun i j => channelSum cs (fun p => value p i j)) := by
  have hadd (a b : RatPoly → Q') : channelSum cs (fun p => a p+b p) ≈
      channelSum cs a+channelSum cs b := channelSum_add a b cs
  have h (a b : RatPoly → Q') (v : Q') (hb : channelSum cs b ≈ v) :
      channelSum cs (fun p => a p+b p) ≈ channelSum cs a+v :=
    Q'.eqv_trans _ _ _ (hadd a b) (Q'.add_eqv_congr' (Q'.eqv_refl _) hb)
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _ (hadd _ _))))

private theorem unweighted_haar_six (blocks : Nat) (f : Nat → Nat → RatPoly) :
    H blocks (six f) ≈ sixValue (fun i j => H blocks (f i j)) :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul (six f))))
    (Q'.eqv_trans _ _ _ (haar_six blocks polyOne f)
      (sixValue_congr _ _
        (fun _ _ _ _ => haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

/-- Exact plane-by-plane expansion of a channel angular square.  This identity
uses only channel locality and conditional differentiation; positivity and
the Bessel estimate enter only in the subsequent inequality. -/
theorem channelSource_blockAngularSquare_eq (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (block : Nat) (hnot : block ∉ ids) (q : RatPoly) :
    channelSum (productChannels n w K ids) (fun c =>
      H n (blockAngularSquare block (channelSource ids q c))) ≈
      sixValue (fun i j =>
        channelSum (productChannels n w K ids) (fun c => H n (polyMul
          (familyProject ids
            (polyMul (blockAngularDerivative block i j q) c))
          (familyProject ids
            (polyMul (blockAngularDerivative block i j q) c))))) := by
  let cs := productChannels n w K ids
  let plane := fun c i j => H n
    (polyMul (blockAngularDerivative block i j (channelSource ids q c))
      (blockAngularDerivative block i j (channelSource ids q c)))
  let projectedPlane := fun c i j => H n (polyMul
    (familyProject ids (polyMul (blockAngularDerivative block i j q) c))
    (familyProject ids (polyMul (blockAngularDerivative block i j q) c)))
  have hexpand : channelSum cs (fun c => H n
      (blockAngularSquare block (channelSource ids q c))) ≈
      channelSum cs (fun c => sixValue (plane c)) :=
    channelSum_congr _ _ cs (fun c _ => unweighted_haar_six n _)
  have hplanes : sixValue (fun i j => channelSum cs (fun c => plane c i j)) ≈
      sixValue (fun i j => channelSum cs (fun c => projectedPlane c i j)) :=
    sixValue_congr _ _ (fun i j hi hj =>
      channelSum_congr _ _ cs (fun c hc =>
        let hd := blockDerivative_channelSource ids block i j hi hj hnot q c.2
          (productChannels_independent n w K ids block hnot c hc)
        haar_of_coeff (RatPolyCoeffEqv.mul hd hd)))
  exact Q'.eqv_trans _ _ _ hexpand
    (Q'.eqv_trans _ _ _ (channelSum_six cs plane) hplanes)

/-- Every angular block outside the projected channel family contracts with
coefficient one under the complete finite Gram-channel sum. -/
theorem channelSource_blockAngularSquare_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (block : Nat) (hblock : block < n) (hnot : block ∉ ids)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    channelSum (productChannels n w K ids) (fun c =>
      H n (blockAngularSquare block (channelSource ids q c))) ≤
      H n (blockAngularSquare block q) := by
  let cs := productChannels n w K ids
  have hexpand := channelSource_blockAngularSquare_eq n w K ids block hnot q
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexpand) ?_
  refine Q'.le_trans' _ _ _ (sixValue_mono _ _ (fun i j hi hj => ?_))
    (Q'.le_of_eqv (Q'.eqv_symm (unweighted_haar_six n _)))
  exact productChannels_familyProject_square_le n hw0 hw1 K ids hnd hids
    (blockAngularDerivative block i j q)
    (angularDerivative_supported_at (by omega) (by omega) hq)

/-- One selected heat list contracts every distinct block-angular square after
the matching in-place projection. -/
theorem heatChannels_project_blockAngularSquare_le_at (n slot : Nat)
    (hslot : slot < n) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (K block : Nat) (hblock : block < n) (hne : block ≠ slot)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    channelSum (heatChannels slot w K) (fun a =>
      H n (blockAngularSquare block (project slot (polyMul q a)))) ≤
      H n (blockAngularSquare block q) := by
  let cs := heatChannels slot w K
  let plane := fun a i j => H n
    (polyMul (blockAngularDerivative block i j (project slot (polyMul q a)))
      (blockAngularDerivative block i j (project slot (polyMul q a))))
  have hexpand : channelSum cs (fun a => H n
      (blockAngularSquare block (project slot (polyMul q a)))) ≈
      channelSum cs (fun a => sixValue (plane a)) :=
    channelSum_congr _ _ cs (fun a _ => unweighted_haar_six n _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ hexpand (channelSum_six cs plane))) ?_
  refine Q'.le_trans' _ _ _ (sixValue_mono _ _ (fun i j hi hj => ?_))
    (Q'.le_of_eqv (Q'.eqv_symm (unweighted_haar_six n _)))
  have hnot : block ∉ [slot] := by
    intro hm
    simp only [List.mem_singleton] at hm
    exact hne hm
  have hd := blockDerivative_channelSource [slot] block i j hi hj hnot q
  have hsquare (a : GramChannel) (ha : a ∈ cs) : plane a.2 i j ≈
      H n (polyMul
        (project slot (polyMul (blockAngularDerivative block i j q) a.2))
        (project slot (polyMul (blockAngularDerivative block i j q) a.2))) := by
    have hc := heatChannels_independent hne.symm w K a ha
    exact haar_of_coeff (RatPolyCoeffEqv.mul (hd a.2 hc) (hd a.2 hc))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (channelSum_congr _ _ cs hsquare))
    (heatChannels_project_square_le_at n slot hslot hw0 hw1 K
      (blockAngularDerivative block i j q)
      (angularDerivative_supported_at (by omega) (by omega) hq))

/-- The diagonal Casimir is the literal angular list sum over all blocks. -/
theorem pairCasimir_diagonal_eq_angularListSum (n : Nat) (hn : 0 < n)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    pairCasimir (n-1) q q ≈ angularListSum n (List.range n) q := by
  have hN : n-1+1=n := Nat.sub_add_cancel hn
  have h := pairCasimir_diagonal_eq_angular (n-1) q (by simpa only [hN] using hq)
  unfold weightedAngularEnergy at h
  rw [hN] at h
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (finSum_eqv_congr_lt _ _ n (fun i hi => haar_of_coeff
        (((RatPolyCoeffEqv.one_mul polyOne).mul_right (blockAngularSquare i q)).trans
          (RatPolyCoeffEqv.one_mul _))))
      (Q'.eqv_symm (angularListSum_range n q)))

/-- A covering permutation splits the diagonal Casimir into passive and active
original block sums, without changing either summand. -/
theorem pairCasimir_eq_angular_partition (n : Nat) (hn : 0 < n)
    (passive active : List Nat)
    (hcover : (passive++active).Perm (List.range n))
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    pairCasimir (n-1) q q ≈
      angularListSum n passive q + angularListSum n active q := by
  exact Q'.eqv_trans _ _ _ (pairCasimir_diagonal_eq_angularListSum n hn q hq)
    (Q'.eqv_trans _ _ _ (angularListSum_perm n hcover.symm q)
      (angularListSum_append n passive active q))

private theorem independent_blockAngularSquare_zero (n block : Nat) (p : RatPoly)
    (hp : QuaternionBlockIndependent block p) :
    H n (blockAngularSquare block p) ≈ 0 := by
  have hz (i j : Nat) (hi : i < 4) (hj : j < 4) :
      RatPolyCoeffEqv
        (polyMul (blockAngularDerivative block i j p)
          (blockAngularDerivative block i j p)) polyZero :=
    let h := angularDerivative_blockIndependent_zero hi hj hp
    (RatPolyCoeffEqv.mul h h).trans (RatPolyCoeffEqv.mul_zero_left polyZero)
  exact Q'.eqv_trans _ _ _ (unweighted_haar_six n _)
    (Q'.eqv_trans _ _ _
      (sixValue_congr _ _ (fun i j hi hj => haar_of_coeff (hz i j hi hj)))
      (by change (sixValue fun _ _ => (0 : Q')) ≈ 0; decide))

private theorem angularListSum_zero (n : Nat) : ∀ ids p,
    (∀ i, i ∈ ids → QuaternionBlockIndependent i p) →
    angularListSum n ids p ≈ 0
  | [], _, _ => Q'.eqv_refl _
  | i::ids, p, hp => by
      change H n (blockAngularSquare i p) + angularListSum n ids p ≈ 0
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (independent_blockAngularSquare_zero n i p (hp i List.mem_cons_self))
          (angularListSum_zero n ids p
            (fun j hj => hp j (List.mem_cons_of_mem i hj))))
        (by decide)

private theorem channelSum_zero : ∀ cs : List GramChannel,
    channelSum cs (fun _ => 0) ≈ 0
  | [] => Q'.eqv_refl _
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_zero_eqv c.1) (channelSum_zero cs)) (by decide)

private theorem channelSum_angularList (n : Nat) (cs : List GramChannel)
    (ids : List Nat) (source : RatPoly → RatPoly) :
    channelSum cs (fun c => angularListSum n ids (source c)) ≈
      qListSum (ids.map fun i => channelSum cs
        (fun c => H n (blockAngularSquare i (source c)))) := by
  induction ids with
  | nil => exact channelSum_zero cs
  | cons i ids ih =>
      change channelSum cs (fun c =>
        H n (blockAngularSquare i (source c)) + angularListSum n ids (source c)) ≈ _
      exact Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)

private theorem qsum_map_le (f g : Nat → Q') : ∀ ids : List Nat,
    (∀ i, i ∈ ids → f i ≤ g i) →
    qListSum (ids.map f) ≤ qListSum (ids.map g)
  | [], _ => Q'.le_refl' _
  | i::ids, h => Q'.add_le_add (h i List.mem_cons_self)
      (qsum_map_le f g ids (fun j hj => h j (List.mem_cons_of_mem i hj)))

/-- Exact reduction of the channel first Casimir moment to the complementary
active links. No norm contraction or sign estimate is taken here. -/
theorem pairCasimir_channel_eq_active (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    (passive active : List Nat)
    (hpassive : ∀ i, i ∈ passive → i < n)
    (hcover : (passive++active).Perm (List.range n))
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    channelSum (productChannels n w K passive) (fun c =>
      pairCasimir (n-1) (channelSource passive q c)
        (channelSource passive q c)) ≈
      qListSum (active.map fun i => channelSum (productChannels n w K passive)
        (fun c => H n (blockAngularSquare i (channelSource passive q c)))) := by
  let cs := productChannels n w K passive
  let source := fun c => channelSource passive q c
  have hsource (c : GramChannel) (hc : c ∈ cs) : SupportedQuaternionBlocks n (source c.2) :=
    familyProject_supported passive (supported_polyMul hq
      (productChannels_supported n w K passive hpassive c hc))
  have hcasimir : channelSum cs (fun c => pairCasimir (n-1) (source c) (source c)) ≈
      channelSum cs (fun c => angularListSum n (List.range n) (source c)) :=
    channelSum_congr _ _ cs (fun c hc =>
      pairCasimir_diagonal_eq_angularListSum n hn (source c.2) (hsource c hc))
  have hsplit : channelSum cs (fun c => angularListSum n (List.range n) (source c)) ≈
      channelSum cs (fun c => angularListSum n passive (source c) +
        angularListSum n active (source c)) :=
    channelSum_congr _ _ cs (fun c hc =>
      Q'.eqv_trans _ _ _ (angularListSum_perm n hcover.symm (source c.2))
        (angularListSum_append n passive active (source c.2)))
  have hpasszero : channelSum cs (fun c => angularListSum n passive (source c)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (channelSum_congr _ _ cs (fun c _ =>
      angularListSum_zero n passive (source c.2)
        (fun i hi => channelSource_independent passive q c.2 i hi)))
      (channelSum_zero cs)
  have hreduce : channelSum cs (fun c => pairCasimir (n-1) (source c) (source c)) ≈
      qListSum (active.map fun i => channelSum cs
        (fun c => H n (blockAngularSquare i (source c)))) :=
    Q'.eqv_trans _ _ _ hcasimir
      (Q'.eqv_trans _ _ _ hsplit
        (Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
          (Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr' hpasszero (Q'.eqv_refl _))
            (Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _)
              (channelSum_angularList n cs active source)))))
  exact hreduce

/-- The complete diagonal Casimir cost of the projected spectator channels is
bounded by the angular cost on the complementary active block list. -/
theorem pairCasimir_channel_le_active (n : Nat) (hn : 0 < n) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat)
    (passive active : List Nat) (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < n)
    (hactive : ∀ i, i ∈ active → i < n)
    (hnot : ∀ i, i ∈ active → i ∉ passive)
    (hcover : (passive++active).Perm (List.range n))
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    channelSum (productChannels n w K passive) (fun c =>
      pairCasimir (n-1) (channelSource passive q c)
        (channelSource passive q c)) ≤ angularListSum n active q := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (pairCasimir_channel_eq_active n hn w K passive active hpassive hcover q hq)) ?_
  unfold angularListSum
  apply qsum_map_le
  intro i hi
  exact channelSource_blockAngularSquare_le n hw0 hw1 K passive hnd hpassive
    i (hactive i hi) (hnot i hi) q hq

#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.angularListSum
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.angularListSum_append
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.angularListSum_perm
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.angularListSum_range
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.blockDerivative_channelSource
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.channelSource_blockAngularSquare_eq
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.channelSource_blockAngularSquare_le
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.heatChannels_project_blockAngularSquare_le_at
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.pairCasimir_diagonal_eq_angularListSum
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.pairCasimir_eq_angular_partition
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.pairCasimir_channel_eq_active
#print axioms YMGap.Continuum.SU2QuaternionChannelAngularContraction.pairCasimir_channel_le_active

end YMGap.Continuum.SU2QuaternionChannelAngularContraction
