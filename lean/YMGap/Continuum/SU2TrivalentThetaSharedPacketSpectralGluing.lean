/-
# A genuinely wired theta network from trivalent shared-link packets

The single-cell shared-link bridge identifies three incident fundamental
plaquettes with the exact cutoff-three character packet.  This file performs
the next finite gluing: three such fused links are joined at both endpoints of
a theta graph.  The two vertex projectors are the existing trivalent
admissibility-and-global-vacuum projector, applied twice.  The interacting
weight on every edge is the SAME `packetWilsonGram` heat-kernel coefficient.

There is an exact obstruction to the most obvious gluing.  The all-fundamental
three-plaquette link fuses to `2 chi_1 + chi_3`, hence all three theta edges are
odd.  Every triple of labels in `{1,3}` is inadmissible, so the entire wired
theta state is zero.  This is not repaired by pretending that the links are
independent.

The corrected even-sector quotient uses the canonical raw fusion section of
the pure `chi_2` channel.  Three copies glue to the nonzero spin-one theta
label `(2,2,2)`.  Its global Wilson weight is exactly the product of three
copies of the existing interacting packet Wilson state.  Cyclic rotation of
the three shared links is proved on arbitrary fused inputs and then on the
full finite theta sum.  Finally the squared global transfer is realized by a
concrete one-mode diagonal operator with a located separator.

Honest scope: this is one closed, globally wired theta spin network and its
exact even-sector spectral mode.  It is not yet a simultaneous quotient for
all overlapping plaquettes of a four-dimensional lattice.
-/

import YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge
import YMGap.Continuum.SU2TrivalentThetaRecoupling
import YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing

set_option maxHeartbeats 1200000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketWilsonTransfer
open YMGap.Continuum.SU2SharedLinkFusionQuotientSpectrum
open YMGap.Continuum.SU2TrivalentClassFusionGNSCompleted
open YMGap.Continuum.SU2TrivalentSharedLinkPacketSpectralBridge
open YMGap.Continuum.SU2TrivalentThetaRecoupling

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one, Int.zero_mul,
               Int.mul_zero, Int.zero_add, Int.add_zero];
             ac_rfl))

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## Three shared links wired into a theta graph -/

/-- Three already-fused trivalent shared-link carriers, one for every theta
edge.  Each component is still connected to an eight-coordinate raw local
plaquette carrier by `fuseThetaRaw` below. -/
abbrev ThetaFusedLinks := TripleIrrep × (TripleIrrep × TripleIrrep)

/-- The corresponding three raw, eight-coordinate shared-link carriers. -/
abbrev ThetaRawLinks := TripleVec × (TripleVec × TripleVec)

def fuseThetaRaw (x : ThetaRawLinks) : ThetaFusedLinks :=
  (fuseFirstPairThenThird x.1,
    (fuseFirstPairThenThird x.2.1, fuseFirstPairThenThird x.2.2))

def thetaFusedEdge (x : ThetaFusedLinks) : Nat → TripleIrrep
  | 0 => x.1
  | 1 => x.2.1
  | _ => x.2.2

def thetaEdgePacket (x : ThetaFusedLinks) (e : Nat) : CharacterPacket 3 :=
  tripleIrrepPacket (thetaFusedEdge x e)

/-- Tensor amplitude before the two theta endpoints are gauge-projected. -/
def thetaTensorAmplitude (x : ThetaFusedLinks) (j : TrivalentLabel) : Q' :=
  coeffAt (thetaEdgePacket x 0) j.1 *
    (coeffAt (thetaEdgePacket x 1) j.2.1 *
      coeffAt (thetaEdgePacket x 2) j.2.2)

/-- Scalar global-vacuum guard for a closed theta labeling. -/
def thetaNonvacuum : TrivalentLabel → Q'
  | (0, 0, 0) => 0
  | _ => 1

/-- Both trivalent endpoints are imposed.  Their two multiplicity factors are
kept explicitly; `theta_two_vertex_project_collapses` proves that this is
exactly the existing idempotent theta gauge/vacuum projector. -/
def thetaTwoVertexAmplitude (x : ThetaFusedLinks) (j : TrivalentLabel) : Q' :=
  trivalentMultiplicity j *
    (trivalentMultiplicity j *
      (thetaNonvacuum j * thetaTensorAmplitude x j))

private theorem thetaGlobalVacuumProject_of_ne (f : ThetaPacket)
    {j : TrivalentLabel} (h : j ≠ (0, 0, 0)) :
    thetaGlobalVacuumProject f j = f j := by
  rcases j with ⟨a, b, c⟩
  cases a with
  | zero =>
      cases b with
      | zero =>
          cases c with
          | zero => exact False.elim (h rfl)
          | succ c => rfl
      | succ b => rfl
  | succ a => rfl

private theorem thetaNonvacuum_of_ne {j : TrivalentLabel}
    (h : j ≠ (0, 0, 0)) : thetaNonvacuum j = 1 := by
  rcases j with ⟨a, b, c⟩
  cases a with
  | zero =>
      cases b with
      | zero =>
          cases c with
          | zero => exact False.elim (h rfl)
          | succ c => rfl
      | succ b => rfl
  | succ a => rfl

theorem theta_two_vertex_project_collapses (x : ThetaFusedLinks)
    (j : TrivalentLabel) :
    thetaTwoVertexAmplitude x j ≈
      thetaGaugeVacuumProject (thetaTensorAmplitude x) j :=
by
  by_cases h0 : j = (0, 0, 0)
  · subst j
    unfold thetaTwoVertexAmplitude thetaNonvacuum thetaGaugeVacuumProject
      thetaGlobalVacuumProject
    let m := trivalentMultiplicity (0, 0, 0)
    let t := thetaTensorAmplitude x (0, 0, 0)
    change m * (m * (0 * t)) ≈ m * 0
    have hz : (0 : Q') * t ≈ 0 := Q'.zero_mul_eqv t
    have hi : m * (0 * t) ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left m _ _ hz)
        (Q'.mul_zero_eqv m)
    have hl : m * (m * (0 * t)) ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left m _ _ hi)
        (Q'.mul_zero_eqv m)
    exact Q'.eqv_trans _ _ _ hl (Q'.eqv_symm (Q'.mul_zero_eqv m))
  · have hn := thetaNonvacuum_of_ne h0
    have hg := thetaGlobalVacuumProject_of_ne (thetaTensorAmplitude x) h0
    rcases trivalentMultiplicity_zero_or_one j with hm | hm
    · unfold thetaTwoVertexAmplitude thetaGaugeVacuumProject
      rw [hn, hg, hm]
      exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _)
        (Q'.eqv_symm (Q'.zero_mul_eqv _))
    · unfold thetaTwoVertexAmplitude thetaGaugeVacuumProject
      rw [hn, hg, hm]
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        (Q'.one_mul_eqv _)

/-- Product of the three physical packet eigenvalues on the wired links. -/
def thetaPacketEigen (j : TrivalentLabel) : Q' :=
  packetEigen j.1 * (packetEigen j.2.1 * packetEigen j.2.2)

theorem thetaPacketEigen_eq_existingThetaEigen (j : TrivalentLabel) :
    thetaPacketEigen j = thetaEigen j := rfl

/-- A single globally wired theta term.  The amplitudes carry both vertex
projectors; the edge weight is the same interacting packet Wilson weight. -/
def thetaWiredWilsonTerm (x y : ThetaFusedLinks)
    (j : TrivalentLabel) : Q' :=
  thetaPacketEigen j *
    (thetaTwoVertexAmplitude x j * thetaTwoVertexAmplitude y j)

/-- The full cutoff-three theta Wilson Gram (all `4^3` shared-channel labels),
not a product of three independently summed link forms. -/
def thetaWiredWilsonGram (x y : ThetaFusedLinks) : Q' :=
  fsum (fun a => fsum (fun b => fsum (fun c =>
    thetaWiredWilsonTerm x y (a, b, c)) 4) 4) 4

/-- Each unglued edge marginal is literally the previously constructed
interacting packet Wilson state. -/
def thetaEdgeWilsonGram (x y : ThetaFusedLinks) (e : Nat) : Q' :=
  packetWilsonGram (thetaEdgePacket x e) (thetaEdgePacket y e)

theorem thetaEdgeWilsonGram_diagonal (x y : ThetaFusedLinks) (e : Nat) :
    thetaEdgeWilsonGram x y e ≈
      fsum (fun s => packetEigen s *
        (coeffAt (thetaEdgePacket x e) s *
          coeffAt (thetaEdgePacket y e) s)) 4 :=
  packetWilsonGram_diagonal (thetaEdgePacket x e) (thetaEdgePacket y e)

/-- Apply the already constructed physical packet transfer on all three
shared links before they are wired at the theta vertices. -/
def transferThetaLinks (x : ThetaFusedLinks) : ThetaFusedLinks :=
  (SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepTransfer x.1,
    (SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepTransfer x.2.1,
      SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepTransfer x.2.2))

theorem thetaEdgePacket_transfer_intertwines (x : ThetaFusedLinks) (e : Nat) :
    PacketEqv (thetaEdgePacket (transferThetaLinks x) e)
      (packetTransfer (thetaEdgePacket x e)) := by
  cases e with
  | zero => exact tripleIrrepPacket_transfer_intertwines x.1
  | succ e =>
      cases e with
      | zero => exact tripleIrrepPacket_transfer_intertwines x.2.1
      | succ e => exact tripleIrrepPacket_transfer_intertwines x.2.2

/-! ## Exact cyclic compatibility of the closed shared-link network -/

def rotateThetaLinks (x : ThetaFusedLinks) : ThetaFusedLinks :=
  (x.2.1, (x.2.2, x.1))

def rotateThetaLabel (j : TrivalentLabel) : TrivalentLabel :=
  (j.2.1, j.2.2, j.1)

theorem trivalentMultiplicity_rotate (j : TrivalentLabel) :
    trivalentMultiplicity (rotateThetaLabel j) =
      trivalentMultiplicity j := by
  rcases j with ⟨a, b, c⟩
  unfold trivalentMultiplicity rotateThetaLabel
  change fusionInd b c a = fusionInd a b c
  unfold fusionInd
  rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_bt b c a]
  rw [YMGap.Continuum.FusionCoreStepRoundD.fusionOK_symm_ab b a c]

theorem thetaTensorAmplitude_rotate (x : ThetaFusedLinks)
    (j : TrivalentLabel) :
    thetaTensorAmplitude (rotateThetaLinks x) (rotateThetaLabel j) ≈
      thetaTensorAmplitude x j := by
  rcases j with ⟨a, b, c⟩
  unfold thetaTensorAmplitude rotateThetaLinks rotateThetaLabel
    thetaEdgePacket thetaFusedEdge
  ring_qeqv

private theorem thetaNonvacuum_rotate (j : TrivalentLabel) :
    thetaNonvacuum (rotateThetaLabel j) = thetaNonvacuum j := by
  rcases j with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> rfl

theorem thetaTwoVertexAmplitude_rotate (x : ThetaFusedLinks)
    (j : TrivalentLabel) :
    thetaTwoVertexAmplitude (rotateThetaLinks x) (rotateThetaLabel j) ≈
      thetaTwoVertexAmplitude x j := by
  unfold thetaTwoVertexAmplitude
  exact q_mul_congr
    (Q'.eqv_of_eq (trivalentMultiplicity_rotate j))
    (q_mul_congr
      (Q'.eqv_of_eq (trivalentMultiplicity_rotate j))
      (q_mul_congr
        (Q'.eqv_of_eq (thetaNonvacuum_rotate j))
        (thetaTensorAmplitude_rotate x j)))

theorem thetaPacketEigen_rotate (j : TrivalentLabel) :
    thetaPacketEigen (rotateThetaLabel j) ≈ thetaPacketEigen j := by
  rcases j with ⟨a, b, c⟩
  unfold thetaPacketEigen rotateThetaLabel
  ring_qeqv

/-- Nontrivial shared-cycle compatibility: rotating all three wired links and
the theta channel leaves every globally projected Wilson term unchanged. -/
theorem thetaWiredWilsonTerm_rotate (x y : ThetaFusedLinks)
    (j : TrivalentLabel) :
    thetaWiredWilsonTerm (rotateThetaLinks x) (rotateThetaLinks y)
        (rotateThetaLabel j) ≈
      thetaWiredWilsonTerm x y j := by
  unfold thetaWiredWilsonTerm
  exact q_mul_congr (thetaPacketEigen_rotate j)
    (q_mul_congr (thetaTwoVertexAmplitude_rotate x j)
      (thetaTwoVertexAmplitude_rotate y j))

/-- The full `4^3` wired state, not merely an individual tensor coordinate,
is cyclically invariant. -/
theorem thetaWiredWilsonGram_rotate (x y : ThetaFusedLinks) :
    thetaWiredWilsonGram (rotateThetaLinks x) (rotateThetaLinks y) ≈
      thetaWiredWilsonGram x y := by
  unfold thetaWiredWilsonGram
  let H := fun a b c => thetaWiredWilsonTerm x y (a, b, c)
  refine Q'.eqv_trans _
    (fsum (fun a => fsum (fun b => fsum (fun c => H c a b) 4) 4) 4) _ ?_ ?_
  · exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun a =>
      YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun b =>
        YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun c => by
          exact thetaWiredWilsonTerm_rotate x y (c, a, b)) 4) 4) 4
  · refine Q'.eqv_trans _
      (fsum (fun a => fsum (fun c => fsum (fun b => H c a b) 4) 4) 4) _ ?_ ?_
    · exact YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr _ _ (fun a =>
        YMGap.Continuum.CubeRatioBounds.fsum_swap
          (fun b c => H c a b) 4 4) 4
    · exact YMGap.Continuum.CubeRatioBounds.fsum_swap
        (fun a c => fsum (fun b => H c a b) 4) 4 4

/-! ## The odd-parity obstruction and the corrected even quotient -/

def fundamentalFusedLink : TripleIrrep := (0, (2, (0, 1)))

def fundamentalThetaLinks : ThetaFusedLinks :=
  (fundamentalFusedLink, (fundamentalFusedLink, fundamentalFusedLink))

/-- The raw all-fundamental local carrier maps to the fused link used above. -/
theorem fundamental_raw_link_maps :
    TripleIrrepEq (fuseFirstPairThenThird tripleFundamentalMode)
      fundamentalFusedLink :=
  tripleFundamental_fusion_multiplicity

/-- Every possible triple in the support `{1,3}^3` is forbidden at a theta
vertex.  This is the exact parity/triangle obstruction to naively gluing three
all-fundamental shared links. -/
theorem fundamental_theta_odd_support_forbidden :
    trivalentMultiplicity (1, 1, 1) = 0 ∧
    trivalentMultiplicity (1, 1, 3) = 0 ∧
    trivalentMultiplicity (1, 3, 1) = 0 ∧
    trivalentMultiplicity (3, 1, 1) = 0 ∧
    trivalentMultiplicity (1, 3, 3) = 0 ∧
    trivalentMultiplicity (3, 1, 3) = 0 ∧
    trivalentMultiplicity (3, 3, 1) = 0 ∧
    trivalentMultiplicity (3, 3, 3) = 0 := by decide

/-- **Banked gluing obstruction.**  The complete cutoff-three theta state of
three all-fundamental local packets vanishes after the actual shared-cycle
vertex quotient. -/
theorem fundamental_theta_wired_state_zero :
    thetaWiredWilsonGram fundamentalThetaLinks fundamentalThetaLinks ≈ 0 := by
  unfold thetaWiredWilsonGram thetaWiredWilsonTerm thetaTwoVertexAmplitude
    thetaNonvacuum thetaTensorAmplitude thetaEdgePacket thetaFusedEdge
    fundamentalThetaLinks fundamentalFusedLink tripleIrrepPacket
    thetaPacketEigen fsum packetEigen
    SpectralLocalizationCrux.eigA
    SU2PeterWeylWilsonBlock.coupling trivalentMultiplicity fusionInd fusionOK
  decide

/-- The corrected even channel on one shared link. -/
def pureQuadraticIrrep : TripleIrrep := (0, (0, (1, 0)))

/-- Its canonical eight-coordinate raw local representative. -/
def pureQuadraticRaw : TripleVec := tripleFusionSection pureQuadraticIrrep

theorem pureQuadratic_raw_fuses :
    TripleIrrepEq (fuseFirstPairThenThird pureQuadraticRaw)
      pureQuadraticIrrep :=
  tripleFusion_section pureQuadraticIrrep

def pureQuadraticThetaLinks : ThetaFusedLinks :=
  (pureQuadraticIrrep, (pureQuadraticIrrep, pureQuadraticIrrep))

theorem pureQuadratic_packet_coefficients :
    coeffAt (tripleIrrepPacket pureQuadraticIrrep) 0 ≈ 0 ∧
    coeffAt (tripleIrrepPacket pureQuadraticIrrep) 1 ≈ 0 ∧
    coeffAt (tripleIrrepPacket pureQuadraticIrrep) 2 ≈ 1 ∧
    coeffAt (tripleIrrepPacket pureQuadraticIrrep) 3 ≈ 0 := by
  exact ⟨Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _, Q'.eqv_refl _⟩

theorem pureQuadratic_linkWilson_exact :
    packetWilsonGram (tripleIrrepPacket pureQuadraticIrrep)
        (tripleIrrepPacket pureQuadraticIrrep) ≈ packetEigen 2 := by
  refine Q'.eqv_trans _ _ _
    (packetWilsonGram_diagonal
      (tripleIrrepPacket pureQuadraticIrrep)
      (tripleIrrepPacket pureQuadraticIrrep)) ?_
  unfold fsum tripleIrrepPacket pureQuadraticIrrep coeffAt packetEigen
    SpectralLocalizationCrux.eigA
    SU2PeterWeylWilsonBlock.coupling
  decide

/-- The even quotient really glues: the unique retained coordinate is the
nonzero spin-one theta labeling `(2,2,2)`. -/
theorem pureQuadratic_theta_amplitude_exact :
    thetaTwoVertexAmplitude pureQuadraticThetaLinks (2, 2, 2) ≈ 1 := by
  unfold thetaTwoVertexAmplitude thetaNonvacuum thetaTensorAmplitude
    thetaEdgePacket thetaFusedEdge pureQuadraticThetaLinks pureQuadraticIrrep
    tripleIrrepPacket trivalentMultiplicity fusionInd fusionOK coeffAt
  decide

theorem pureQuadratic_thetaGram_exact :
    thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks ≈
      packetEigen 2 * (packetEigen 2 * packetEigen 2) := by
  unfold thetaWiredWilsonGram thetaWiredWilsonTerm thetaTwoVertexAmplitude
    thetaNonvacuum thetaTensorAmplitude thetaEdgePacket thetaFusedEdge
    pureQuadraticThetaLinks pureQuadraticIrrep tripleIrrepPacket
    thetaPacketEigen fsum packetEigen
    SpectralLocalizationCrux.eigA
    SU2PeterWeylWilsonBlock.coupling trivalentMultiplicity fusionInd fusionOK
  decide

/-- The global nonzero theta weight is exactly the product of THREE copies of
the same interacting packet Wilson state, with the two vertex projectors
already imposed. -/
theorem pureQuadratic_thetaGram_is_same_state_product :
    thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks ≈
      packetWilsonGram (tripleIrrepPacket pureQuadraticIrrep)
          (tripleIrrepPacket pureQuadraticIrrep) *
        (packetWilsonGram (tripleIrrepPacket pureQuadraticIrrep)
            (tripleIrrepPacket pureQuadraticIrrep) *
          packetWilsonGram (tripleIrrepPacket pureQuadraticIrrep)
            (tripleIrrepPacket pureQuadraticIrrep)) := by
  refine Q'.eqv_trans _ _ _ pureQuadratic_thetaGram_exact ?_
  exact q_mul_congr (Q'.eqv_symm pureQuadratic_linkWilson_exact)
    (q_mul_congr (Q'.eqv_symm pureQuadratic_linkWilson_exact)
      (Q'.eqv_symm pureQuadratic_linkWilson_exact))

/-! ## A located finite operator for the wired theta mode -/

/-- One physical theta-transfer eigenvalue, before squaring the same-state
transfer, is the product over its three shared links. -/
def thetaSpinOneTransferEigen : Q' :=
  packetEigen 2 * (packetEigen 2 * packetEigen 2)

/-- The same-state spectral operator applies the transfer to both reflected
arguments, hence has the squared global eigenvalue. -/
def thetaSpinOneSquaredEigen : Nat → Q' := fun _ =>
  thetaSpinOneTransferEigen * thetaSpinOneTransferEigen

/-- Its spectral weight is the actual globally projected interacting theta
Wilson Gram, not a free-Haar normalization. -/
def thetaSpinOneWeight : Nat → Q' := fun _ =>
  thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks

theorem thetaSpinOneSquaredEigen_nonneg :
    ∀ i, (0 : Q') ≤ thetaSpinOneSquaredEigen i := by
  intro i
  unfold thetaSpinOneSquaredEigen thetaSpinOneTransferEigen packetEigen
    SpectralLocalizationCrux.eigA
    SU2PeterWeylWilsonBlock.coupling
  decide

theorem thetaSpinOneWeight_nonneg :
    ∀ i, (0 : Q') ≤ thetaSpinOneWeight i := by
  intro i
  have he : thetaWiredWilsonGram pureQuadraticThetaLinks
      pureQuadraticThetaLinks ≈ thetaSpinOneTransferEigen := by
    exact pureQuadratic_thetaGram_exact
  have hp : (0 : Q') ≤ thetaSpinOneTransferEigen := by
    unfold thetaSpinOneTransferEigen packetEigen
      SpectralLocalizationCrux.eigA
      SU2PeterWeylWilsonBlock.coupling
    decide
  exact Q'.le_trans' _ _ _ hp (Q'.le_of_eqv (Q'.eqv_symm he))

def thetaSpinOneSpectralModel : SpectralModel :=
  diagOp.toSpectralModel thetaSpinOneSquaredEigen thetaSpinOneWeight 1
    thetaSpinOneWeight_nonneg thetaSpinOneSquaredEigen_nonneg

def thetaSpinOneSquaredOp : FiniteOp :=
  diagOp thetaSpinOneSquaredEigen 1

theorem thetaSpinOne_model_lam_is_operator_eigen :
    thetaSpinOneSpectralModel.lam 0 ≈
      thetaSpinOneSquaredOp.apply (basis 0) 0 :=
  toSpectralModel_lam_is_eigen thetaSpinOneSquaredEigen thetaSpinOneWeight 1
    thetaSpinOneWeight_nonneg thetaSpinOneSquaredEigen_nonneg 0 (by decide)

def thetaSpinOneSep : Q' := thetaSpinOneSquaredEigen 0

theorem thetaSpinOneSep_lt_one : thetaSpinOneSep < (1 : Q') := by
  unfold thetaSpinOneSep thetaSpinOneSquaredEigen thetaSpinOneTransferEigen
    packetEigen SpectralLocalizationCrux.eigA
    SU2PeterWeylWilsonBlock.coupling
  decide

def thetaSpinOneLocatedGap : LocatedSpectralGap thetaSpinOneSpectralModel :=
  diagLocatedGap thetaSpinOneSquaredEigen thetaSpinOneWeight 1
    thetaSpinOneWeight_nonneg thetaSpinOneSquaredEigen_nonneg thetaSpinOneSep
    thetaSpinOneSep_lt_one (fun _ => Q'.le_refl' _)

theorem thetaSpinOne_gapMargin_pos :
    (0 : Q') < thetaSpinOneLocatedGap.gapMargin :=
  thetaSpinOneLocatedGap.gapMargin_pos

/-- Time zero of the located model is exactly the globally wired interacting
theta Wilson state. -/
theorem thetaSpinOne_corr_zero_is_wired_state :
    SpectralGap.corr thetaSpinOneSpectralModel 0 ≈
      thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks := by
  refine Q'.eqv_trans _ _ _ (SpectralGap.corr_zero thetaSpinOneSpectralModel) ?_
  change ((0 : Q') + thetaSpinOneWeight 0) ≈
    thetaWiredWilsonGram pureQuadraticThetaLinks pureQuadraticThetaLinks
  exact QPoly.q_zero_add_eqv _

/-- Time one is the SAME globally wired state after the existing physical
packet transfer has been applied on all three shared links. -/
theorem thetaSpinOne_corr_one_is_transferred_wired_state :
    SpectralGap.corr thetaSpinOneSpectralModel 1 ≈
      thetaWiredWilsonGram (transferThetaLinks pureQuadraticThetaLinks)
        (transferThetaLinks pureQuadraticThetaLinks) := by
  unfold SpectralGap.corr thetaSpinOneSpectralModel thetaSpinOneWeight
    thetaSpinOneSquaredEigen thetaSpinOneTransferEigen transferThetaLinks
    thetaWiredWilsonGram thetaWiredWilsonTerm thetaTwoVertexAmplitude
    thetaNonvacuum thetaTensorAmplitude thetaEdgePacket thetaFusedEdge
    pureQuadraticThetaLinks pureQuadraticIrrep
    SU2TrivalentSharedLinkPacketSpectralBridge.tripleIrrepTransfer
    tripleIrrepPacket thetaPacketEigen packetEigen SpectralLocalizationCrux.eigA
    trivalentMultiplicity fusionInd fusionOK fsum
  decide

end YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing

#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.thetaWiredWilsonGram_rotate
#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.fundamental_theta_wired_state_zero
#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.pureQuadratic_raw_fuses
#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.pureQuadratic_thetaGram_is_same_state_product
#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.thetaSpinOne_model_lam_is_operator_eigen
#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.thetaSpinOneLocatedGap
#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.thetaSpinOne_corr_zero_is_wired_state
#print axioms YMGap.Continuum.SU2TrivalentThetaSharedPacketSpectralGluing.thetaSpinOne_corr_one_is_transferred_wired_state
