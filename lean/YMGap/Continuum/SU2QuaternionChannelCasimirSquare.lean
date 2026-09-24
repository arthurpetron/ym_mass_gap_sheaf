/-
# Active Casimir-square contraction through spectator Gram channels

The literal sum of negative block angular Laplacians over the active blocks
commutes with the spectator family projection and channel multipliers.  The
family Gram Bessel theorem is then applied once to this complete polynomial,
so every cross term in the square is retained.
-/

import YMGap.Continuum.SU2QuaternionChannelAngularContraction
import YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel

namespace YMGap.Continuum.SU2QuaternionChannelCasimirSquare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyAngularContraction
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatGramLocality
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private def angularPlanes : List (Nat × Nat) :=
  [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

/-- The literal angular Laplacian on one original quaternion block. -/
def blockAngularLaplacian (block : Nat) (p : RatPoly) : RatPoly :=
  polySum (angularPlanes.map fun ij =>
    blockAngularDerivative block ij.1 ij.2
      (blockAngularDerivative block ij.1 ij.2 p))

/-- The positive-Casimir polynomial on a finite list of original blocks. -/
def activeCasimirPolynomial (active : List Nat) (p : RatPoly) : RatPoly :=
  polySum (active.map fun block => polyNeg (blockAngularLaplacian block p))

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem sum_supported (n : Nat) : ∀ ps : List RatPoly,
    (∀ p, p ∈ ps → SupportedQuaternionBlocks n p) →
      SupportedQuaternionBlocks n (polySum ps)
  | [], _ => fun _ h => False.elim (List.not_mem_nil h)
  | p::ps, h => polyAdd_supported (h p List.mem_cons_self)
      (sum_supported n ps (fun q hq => h q (List.mem_cons_of_mem p hq)))

theorem blockAngularLaplacian_supported {n block : Nat} (hblock : block < n)
    {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (blockAngularLaplacian block p) := by
  apply sum_supported
  intro term ht
  obtain ⟨ij, hij, rfl⟩ := List.mem_map.mp ht
  have hi : ij.1 < 4 := by
    simp only [angularPlanes, List.mem_cons, List.not_mem_nil, or_false] at hij
    rcases hij with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hj : ij.2 < 4 := by
    simp only [angularPlanes, List.mem_cons, List.not_mem_nil, or_false] at hij
    rcases hij with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact angularDerivative_supported_at (by omega) (by omega)
    (angularDerivative_supported_at (by omega) (by omega) hp)

theorem activeCasimirPolynomial_supported {n : Nat} (active : List Nat)
    (hactive : ∀ i, i ∈ active → i < n) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (activeCasimirPolynomial active p) := by
  apply sum_supported
  intro term ht
  obtain ⟨block, hb, rfl⟩ := List.mem_map.mp ht
  exact neg_supported (blockAngularLaplacian_supported (hactive block hb) hp)

private theorem derivative_mul_independent (block i j : Nat)
    (hi : i < 4) (hj : j < 4) (p c : RatPoly)
    (hc : QuaternionBlockIndependent block c) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j (polyMul p c))
      (polyMul (blockAngularDerivative block i j p) c) := by
  have hz := angularDerivative_blockIndependent_zero hi hj hc
  unfold blockAngularDerivative
  exact (angularDerivative_mul (4*block+i) (4*block+j) p c).trans
    (((RatPolyCoeffEqv.refl _).add
      ((hz.mul_left p).trans (RatPolyCoeffEqv.mul_zero_right p))).trans
        (RatPolyCoeffEqv.add_zero _))

private theorem secondDerivative_channelSource (ids : List Nat)
    (block i j : Nat) (hi : i < 4) (hj : j < 4) (hnot : block ∉ ids)
    (q c : RatPoly) (hc : QuaternionBlockIndependent block c) :
    RatPolyCoeffEqv
      (blockAngularDerivative block i j
        (blockAngularDerivative block i j (channelSource ids q c)))
      (familyProject ids (polyMul
        (blockAngularDerivative block i j (blockAngularDerivative block i j q)) c)) := by
  have hfirst : RatPolyCoeffEqv
      (blockAngularDerivative block i j (channelSource ids q c))
      (familyProject ids (polyMul (blockAngularDerivative block i j q) c)) := by
    exact (blockAngularDerivative_familyProject ids block i j hi hj hnot
      (polyMul q c)).trans
      (familyProject_congr ids (derivative_mul_independent block i j hi hj q c hc))
  exact (angularDerivative_congr (4*block+i) (4*block+j) hfirst).trans
    ((blockAngularDerivative_familyProject ids block i j hi hj hnot
      (polyMul (blockAngularDerivative block i j q) c)).trans
      (familyProject_congr ids (derivative_mul_independent block i j hi hj
        (blockAngularDerivative block i j q) c hc)))

private theorem sum_coeff {f g : (Nat × Nat) → RatPoly}
    (h : ∀ ij, ij ∈ angularPlanes → RatPolyCoeffEqv (f ij) (g ij)) :
    RatPolyCoeffEqv (polySum (angularPlanes.map f))
      (polySum (angularPlanes.map g)) := by
  unfold angularPlanes at h ⊢
  exact (h (0,1) (by simp)).add ((h (0,2) (by simp)).add
    ((h (0,3) (by simp)).add ((h (1,2) (by simp)).add
      ((h (1,3) (by simp)).add
        ((h (2,3) (by simp)).add (RatPolyCoeffEqv.refl polyZero))))))

private theorem familyProject_zero : ∀ ids : List Nat,
    RatPolyCoeffEqv (familyProject ids polyZero) polyZero
  | [] => RatPolyCoeffEqv.refl polyZero
  | _::ids => familyProject_zero ids

private theorem familyProject_sum (ids : List Nat) : ∀ ps : List RatPoly,
    RatPolyCoeffEqv (familyProject ids (polySum ps))
      (polySum (ps.map (familyProject ids)))
  | [] => familyProject_zero ids
  | p::ps => by
      change RatPolyCoeffEqv
        (familyProject ids (polyAdd p (polySum ps)))
        (polyAdd (familyProject ids p)
          (polySum (ps.map (familyProject ids))))
      rw [familyProject_add]
      exact (RatPolyCoeffEqv.refl _).add (familyProject_sum ids ps)

private theorem blockLaplacian_channelSource (ids : List Nat)
    (block : Nat) (hnot : block ∉ ids) (q c : RatPoly)
    (hc : QuaternionBlockIndependent block c) :
    RatPolyCoeffEqv (blockAngularLaplacian block (channelSource ids q c))
      (familyProject ids (polyMul (blockAngularLaplacian block q) c)) := by
  let term := fun p : RatPoly => fun ij : Nat × Nat =>
    blockAngularDerivative block ij.1 ij.2
      (blockAngularDerivative block ij.1 ij.2 p)
  have hterms : RatPolyCoeffEqv
      (polySum (angularPlanes.map (term (channelSource ids q c))))
      (polySum (angularPlanes.map fun ij =>
        familyProject ids (polyMul (term q ij) c))) := by
    apply sum_coeff
    intro ij hij
    have hi : ij.1 < 4 := by
      simp only [angularPlanes, List.mem_cons, List.not_mem_nil, or_false] at hij
      rcases hij with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hj : ij.2 < 4 := by
      simp only [angularPlanes, List.mem_cons, List.not_mem_nil, or_false] at hij
      rcases hij with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact secondDerivative_channelSource ids block ij.1 ij.2 hi hj hnot q c hc
  have hpull := familyProject_sum ids ((angularPlanes.map fun ij => polyMul (term q ij) c))
  have hmul : RatPolyCoeffEqv
      (polyMul (polySum (angularPlanes.map (term q))) c)
      (polySum (angularPlanes.map fun ij => polyMul (term q ij) c)) := by
    exact RatPolyCoeffEqv.polySum_mul_right (angularPlanes.map (term q)) c
  exact hterms.trans ((RatPolyCoeffEqv.symm hpull).trans
    (familyProject_congr ids (RatPolyCoeffEqv.symm hmul)))

set_option maxHeartbeats 400000 in
private theorem casimirTerm_channelSource (ids : List Nat)
    (block : Nat) (hnot : block ∉ ids) (q c : RatPoly)
    (hc : QuaternionBlockIndependent block c) :
    RatPolyCoeffEqv
      (polyNeg (blockAngularLaplacian block (channelSource ids q c)))
      (familyProject ids (polyMul (polyNeg (blockAngularLaplacian block q)) c)) := by
  have h := RatPolyCoeffEqv.neg (blockLaplacian_channelSource ids block hnot q c hc)
  have hpull := familyProject_neg ids (polyMul (blockAngularLaplacian block q) c)
  have hmul : RatPolyCoeffEqv
      (polyNeg (polyMul (blockAngularLaplacian block q) c))
      (polyMul (polyNeg (blockAngularLaplacian block q)) c) :=
    (QuaternionHaarAngularCarrier.neg_smul _).trans
      ((RatPolyCoeffEqv.polyMul_smul_left (-1) _ c).symm.trans
        ((QuaternionHaarAngularCarrier.neg_smul _).symm.mul_right c))
  exact h.trans (hpull.symm.trans (familyProject_congr ids hmul))

/-- The complete active Casimir polynomial pulls through every spectator
channel without splitting its later square into blockwise pieces. -/
theorem activeCasimir_channelSource (ids active : List Nat)
    (hnot : ∀ block, block ∈ active → block ∉ ids)
    (q c : RatPoly)
    (hc : ∀ block, block ∈ active → QuaternionBlockIndependent block c) :
    RatPolyCoeffEqv (activeCasimirPolynomial active (channelSource ids q c))
      (familyProject ids (polyMul (activeCasimirPolynomial active q) c)) := by
  induction active with
  | nil =>
      exact ((familyProject_congr ids
        (RatPolyCoeffEqv.mul_zero_left c)).trans
          (familyProject_zero ids)).symm
  | cons block rest ih =>
      have hhead := casimirTerm_channelSource ids block
        (hnot block List.mem_cons_self) q c (hc block List.mem_cons_self)
      have htail := ih
        (fun i hi => hnot i (List.mem_cons_of_mem block hi))
        (fun i hi => hc i (List.mem_cons_of_mem block hi))
      change RatPolyCoeffEqv (polyAdd _ _)
        (familyProject ids (polyMul (polyAdd _ _) c))
      rw [polyMul_add_left_exact, familyProject_add]
      exact hhead.add htail

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- The full active Casimir square contracts with coefficient one through the
complete spectator Gram family. All mixed active-block terms are retained. -/
theorem channelSource_activeCasimir_square_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (K : Nat)
    (passive active : List Nat) (hnd : passive.Nodup)
    (hpassive : ∀ i, i ∈ passive → i < n)
    (hactive : ∀ i, i ∈ active → i < n)
    (hnot : ∀ i, i ∈ passive → i ∉ active)
    (q : RatPoly) (hq : SupportedQuaternionBlocks n q) :
    channelSum (productChannels n w K passive) (fun c =>
      H n (polyMul
        (activeCasimirPolynomial active (channelSource passive q c))
        (activeCasimirPolynomial active (channelSource passive q c)))) ≤
      H n (polyMul (activeCasimirPolynomial active q)
        (activeCasimirPolynomial active q)) := by
  let cs := productChannels n w K passive
  let C := activeCasimirPolynomial active q
  have hdisjoint : ∀ i, i ∈ active → i ∉ passive := by
    intro i hi hp
    exact hnot i hp hi
  have hre (c : GramChannel) (hc : c ∈ cs) : RatPolyCoeffEqv
      (activeCasimirPolynomial active (channelSource passive q c.2))
      (familyProject passive (polyMul C c.2)) :=
    activeCasimir_channelSource passive active hdisjoint q c.2
      (fun block hb => productChannels_independent n w K passive block
        (hdisjoint block hb) c hc)
  have he : channelSum cs (fun c => H n (polyMul
      (activeCasimirPolynomial active (channelSource passive q c))
      (activeCasimirPolynomial active (channelSource passive q c)))) ≈
      channelSum cs (fun c => H n (polyMul
        (familyProject passive (polyMul C c))
        (familyProject passive (polyMul C c)))) := by
    exact channelSum_congr _ _ cs (fun c hc =>
      haar_of_coeff ((hre c hc).mul (hre c hc)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (productChannels_familyProject_square_le n hw0 hw1 K passive hnd hpassive C
      (activeCasimirPolynomial_supported active hactive hq))

end YMGap.Continuum.SU2QuaternionChannelCasimirSquare

#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirSquare.blockAngularLaplacian
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirSquare.activeCasimirPolynomial
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirSquare.blockAngularLaplacian_supported
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirSquare.activeCasimirPolynomial_supported
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirSquare.activeCasimir_channelSource
#print axioms YMGap.Continuum.SU2QuaternionChannelCasimirSquare.channelSource_activeCasimir_square_le
