/-
# Fusion-tilt identity for the whole-slab recoupling kernel (surrogate carrier)

**Scope.**  Everything here is a fact about the positive *multiplicity-product
surrogate* carrier (`CompactDual*` / `slabParametricKPhysicalTerm`: face heat
coefficients times link invariant counts).  That law equals the SU(2)
heat-kernel lattice gauge theory only for abelian groups
(`BF4ExactPhysicalPerronSameActionFence`, notes/physical-gibbs-semantic-gap.md),
so these identities are U(1)-exact statements and carry NO SU(2) Yang--Mills
content.  No chart closure, continuum limit or gap is claimed.

**Content** (math_frontier_1124/remainder_obstruction.md §3 (I2);
route_design_check.md §5).
* `fourFoldMultiplicity p s`: the multiplicity of twice-spin `s` in the
  four-fold SU(2) tensor product `s₀ ⊗ s₁ ⊗ s₂ ⊗ s₃`, counted as the number of
  Clebsch--Gordan pair channels `(a, b)` with `s₀⊗s₁ ∋ a`, `s₂⊗s₃ ∋ b`,
  `a⊗b ∋ s` (natural-number count, no cutoff).
* `fusionTilt S x y = ∏_f fourFoldMultiplicity (packet_f x) (y f)` over the
  coarse faces.
* `wholeSlabRecouplingRawWeight_eqv_coarseTerm_mul_fusionTilt`: on the
  physical labelling lists the raw recoupling row factors exactly as the coarse
  surrogate summand times the fusion tilt.  Key steps: the pair-channel ranges
  `a, b ≤ 2K`, `s ≤ 4K` are automatic for packets bounded by `K`, and
  `coeffAt (heatKernelPacket (4K) w') s = coeffW w' s` for `s ≤ 4K`.
* Covariance form of the one-step remainder for `allCutoffPhysicalKernel`:
  `remainderObservableExpectation K F` is the fine-law average of the row
  defects `E_K(x)[F] − E_ν[F]`, and on every coherent row (positive fine summand,
  positive raw partition) the defect is `Cov_ν(F, N_x) / E_ν[N_x]` with
  `N_x = fusionTilt S x`.  Incoherent rows keep their null-completion defect;
  this is the exact case split, not an estimate.

Mathlib-free; finite exact-rational algebra only; no choice, `sorry`, or new
axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable

namespace YMGap.Continuum.CompactDualWholeSlabFusionTilt

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4ObservableMatchedOneStep (observableExpectation)
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward (allCutoffPhysicalKernel)
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
  (remainderObservableExpectation)
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2CharacterVacuumHaar (coeffAt)
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork (eliminateLinks)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph (EdgeLabelling)
open YMGap.Continuum.Z4DyadicSlabCharacterFusionConditionalKernel
open YMGap.Continuum.Z4DyadicSlabMultiCharacterPacketKernel
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
  (heatKernelPacket coeffAt_heatKernelPacket)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Local finite-sum algebra -/

/-- Natural-number list sum. -/
def natListSum {A : Type} (value : A → Nat) : List A → Nat
  | [] => 0
  | head :: tail => value head + natListSum value tail

private theorem ofNat_add_local (i j : Nat) :
    Q'.ofNat (i + j) ≈ Q'.ofNat i + Q'.ofNat j :=
  YMGap.Constructive.Q'.ofNat_add_eqv i j

private theorem ofNat_natListSum {A : Type} (value : A → Nat) :
    ∀ xs : List A,
      Q'.ofNat (natListSum value xs) ≈ listQSum (fun x => Q'.ofNat (value x)) xs
  | [] => by
      show Q'.ofNat 0 ≈ 0
      decide
  | head :: tail =>
      Q'.eqv_trans _ _ _ (ofNat_add_local _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (ofNat_natListSum value tail))

private theorem listQSum_append_local {A : Type} (f : A → Q') :
    ∀ xs ys : List A, listQSum f (xs ++ ys) ≈ listQSum f xs + listQSum f ys
  | [], _ => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | head :: tail, ys =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl (f head)) (listQSum_append_local f tail ys))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_map_local {A B : Type} (f : B → Q') (g : A → B) :
    ∀ xs : List A, listQSum f (xs.map g) = listQSum (fun x => f (g x)) xs
  | [] => rfl
  | head :: tail => by
      show f (g head) + listQSum f (tail.map g) = f (g head) + listQSum (fun x => f (g x)) tail
      rw [listQSum_map_local f g tail]

private theorem listQSum_cartesian_local {A B : Type} (h : A × B → Q') :
    ∀ (xs : List A) (ys : List B),
      listQSum h (cartesian xs ys) ≈ listQSum (fun x => listQSum (fun y => h (x, y)) ys) xs
  | [], _ => Q'.eqv_refl 0
  | head :: tail, ys => by
      show listQSum h ((ys.map (fun y => (head, y))) ++
          tail.flatMap (fun x => ys.map (fun y => (x, y)))) ≈ _
      refine Q'.eqv_trans _ _ _ (listQSum_append_local h _ _) ?_
      rw [listQSum_map_local h (fun y => (head, y)) ys]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (listQSum_cartesian_local h tail ys)

private theorem listQSum_neg_local {A : Type} (f : A → Q') :
    ∀ xs : List A, listQSum (fun x => -(f x)) xs ≈ -(listQSum f xs)
  | [] => by
      show (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (listQSum_neg_local f tail))
        (Q'.eqv_symm (Q'.neg_add_eqv _ _))

private theorem listQSum_zero_on_local {A : Type} (f : A → Q') :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ 0) → listQSum f xs ≈ 0
  | xs, h => Q'.eqv_trans _ _ _ (listQSum_congr_on f (fun _ => (0 : Q')) xs h) (listQSum_zero xs)

private theorem add_zero_local (a : Q') : a + 0 ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv a 0) (Q'.eqv_of_eq (Q'.zero_add' a))

/-- Extending a range past the support of the summand does not change the sum. -/
private theorem listQSum_range_extend (f : Nat → Q') (m : Nat)
    (hzero : ∀ a, m ≤ a → f a ≈ 0) :
    ∀ k, listQSum f (List.range (m + k)) ≈ listQSum f (List.range m)
  | 0 => Q'.eqv_refl _
  | k + 1 => by
      show listQSum f (List.range ((m + k) + 1)) ≈ _
      rw [List.range_succ]
      refine Q'.eqv_trans _ _ _ (listQSum_append_local f _ _) ?_
      have hlast : listQSum f [m + k] ≈ 0 :=
        Q'.eqv_trans _ _ _ (add_zero_local (f (m + k))) (hzero (m + k) (Nat.le_add_right m k))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (listQSum_range_extend f m hzero k) hlast)
        (add_zero_local _)

/-- Dirac sum on a range. -/
private theorem listQSum_dirac_range (g : Nat → Q') (s : Nat) :
    ∀ n, s < n → listQSum (fun c => if c = s then g c else 0) (List.range n) ≈ g s
  | 0, h => absurd h (Nat.not_lt_zero s)
  | n + 1, h => by
      rw [List.range_succ]
      refine Q'.eqv_trans _ _ _ (listQSum_append_local _ _ _) ?_
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hlt | heq
      · have hne : ¬ n = s := fun e => Nat.lt_irrefl s (e ▸ hlt)
        have hlast : listQSum (fun c => if c = s then g c else 0) [n] ≈ 0 := by
          show (if n = s then g n else 0) + 0 ≈ 0
          rw [if_neg hne]
          exact add_zero_local 0
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (listQSum_dirac_range g s n hlt) hlast) (add_zero_local _)
      · have hhead : listQSum (fun c => if c = s then g c else 0) (List.range n) ≈ 0 := by
          apply listQSum_zero_on_local
          intro c hc
          have hcn : c < n := List.mem_range.mp hc
          have hne : ¬ c = s := fun e => Nat.ne_of_lt (by rw [← e]; exact hcn) heq
          show (if c = s then g c else 0) ≈ 0
          rw [if_neg hne]
          exact Q'.eqv_refl 0
        have hlast : listQSum (fun c => if c = s then g c else 0) [n] ≈ g s := by
          show (if n = s then g n else 0) + 0 ≈ g s
          rw [if_pos heq.symm, heq]
          exact add_zero_local _
        exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hhead hlast) (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem mul_mul_mul_comm_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  refine Q'.eqv_trans _ (a * (b * (c * d))) _ (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (a * ((b * c) * d)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))) ?_
  refine Q'.eqv_trans _ (a * ((c * b) * d)) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ (a * (c * (b * d))) _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- `(a * b) * c ≈ (a * c) * b`. -/
private theorem mul_right_comm_local (a b c : Q') : (a * b) * c ≈ (a * c) * b :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv b c))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))

/-! ## 1. Four-fold fusion multiplicity -/

/-- Indicator of one Clebsch--Gordan pair channel `(a, b)` from the packet to `s`. -/
def fourFoldChannelInd (p : FaceSpinPacket) (s a b : Nat) : Nat :=
  bif fusionOK p.spin0 p.spin1 a && (fusionOK p.spin2 p.spin3 b && fusionOK a b s) then 1 else 0

/-- **Multiplicity of twice-spin `s` in `s₀ ⊗ s₁ ⊗ s₂ ⊗ s₃`** (SU(2) fusion rules),
as the number of pair channels `a ∈ s₀⊗s₁`, `b ∈ s₂⊗s₃`, `s ∈ a⊗b`.  The ranges
`a ≤ s₀+s₁`, `b ≤ s₂+s₃` are exactly the fusion ranges, so no cutoff enters. -/
def fourFoldMultiplicity (p : FaceSpinPacket) (s : Nat) : Nat :=
  natListSum
    (fun a => natListSum (fun b => fourFoldChannelInd p s a b)
      (List.range (p.spin2 + p.spin3 + 1)))
    (List.range (p.spin0 + p.spin1 + 1))

/-- The rational pair-channel weight used by `packetPairChannelRawWeight`. -/
def channelQ (p : FaceSpinPacket) (s a b : Nat) : Q' :=
  fusionInd p.spin0 p.spin1 a * (fusionInd p.spin2 p.spin3 b * fusionInd a b s)

theorem ofNat_fourFoldChannelInd (p : FaceSpinPacket) (s a b : Nat) :
    Q'.ofNat (fourFoldChannelInd p s a b) ≈ channelQ p s a b := by
  unfold fourFoldChannelInd channelQ fusionInd
  cases fusionOK p.spin0 p.spin1 a <;> cases fusionOK p.spin2 p.spin3 b <;>
    cases fusionOK a b s <;> decide

theorem le_add_of_fusionOK {a b s : Nat} (h : fusionOK a b s = true) : s ≤ a + b := by
  unfold fusionOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2

private theorem fusionInd_eq_zero_of_lt {a b s : Nat} (h : a + b < s) : fusionInd a b s = 0 := by
  unfold fusionInd
  cases hf : fusionOK a b s with
  | false => rfl
  | true => exact absurd (le_add_of_fusionOK hf) (Nat.not_le_of_lt h)

theorem ofNat_fourFoldMultiplicity (p : FaceSpinPacket) (s : Nat) :
    Q'.ofNat (fourFoldMultiplicity p s) ≈
      listQSum (fun a => listQSum (fun b => channelQ p s a b)
          (List.range (p.spin2 + p.spin3 + 1)))
        (List.range (p.spin0 + p.spin1 + 1)) := by
  unfold fourFoldMultiplicity
  refine Q'.eqv_trans _ _ _ (ofNat_natListSum _ _) ?_
  apply listQSum_congr_on
  intro a _
  refine Q'.eqv_trans _ _ _ (ofNat_natListSum _ _) ?_
  apply listQSum_congr_on
  intro b _
  exact ofNat_fourFoldChannelInd p s a b

private theorem range_split_local {m n : Nat} (h : m ≤ n) : n + 1 = (m + 1) + (n - m) := by
  rw [Nat.add_right_comm, Nat.add_sub_cancel' h]

/-- The fixed-final-character pair-channel sum of one packet is
`coeffW w s · n(s | packet)` whenever the packet spins are bounded by `K`
(so `a, b ≤ 2K`) and `s ≤ 4K`. -/
theorem packetFixedFinalSum_eqv_coeffW_mul_fourFold
    (w : Q') (K : Nat) (p : FaceSpinPacket) (s : Nat)
    (h01 : p.spin0 + p.spin1 ≤ 2 * K) (h23 : p.spin2 + p.spin3 ≤ 2 * K)
    (hs : s ≤ 4 * K) :
    listQSum
        (fun channel : PairChannelState =>
          if channel.2 = s then packetPairChannelRawWeight w p channel else 0)
        (pairChannelStateSpace K) ≈
      coeffW w s * Q'.ofNat (fourFoldMultiplicity p s) := by
  unfold pairChannelStateSpace
  refine Q'.eqv_trans _ _ _ (listQSum_cartesian_local _ _ _) ?_
  -- collapse the final character
  refine Q'.eqv_trans _
    (listQSum (fun ab : Nat × Nat => coeffW w s * channelQ p s ab.1 ab.2)
      (cartesian (List.range (2 * K + 1)) (List.range (2 * K + 1)))) _ ?_ ?_
  · apply listQSum_congr_on
    intro ab _
    exact listQSum_dirac_range
      (fun c => packetPairChannelRawWeight w p (ab, c)) s (4 * K + 1) (Nat.lt_succ_of_le hs)
  refine Q'.eqv_trans _ _ _ (listQSum_mul_left _ _ _) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ (listQSum_cartesian_local _ _ _) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (ofNat_fourFoldMultiplicity p s))
  -- shrink the inner range to the fusion range of (spin2, spin3)
  refine Q'.eqv_trans _
    (listQSum (fun a => listQSum (fun b => channelQ p s a b)
        (List.range (p.spin2 + p.spin3 + 1)))
      (List.range (2 * K + 1))) _ ?_ ?_
  · apply listQSum_congr_on
    intro a _
    show listQSum (fun b => channelQ p s a b) (List.range (2 * K + 1)) ≈ _
    rw [range_split_local h23]
    apply listQSum_range_extend
    intro b hb
    unfold channelQ
    rw [fusionInd_eq_zero_of_lt hb]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) (Q'.mul_zero_eqv _)
  rw [range_split_local h01]
  apply listQSum_range_extend
  intro a ha
  apply listQSum_zero_on_local
  intro b _
  show channelQ p s a b ≈ 0
  unfold channelQ
  rw [fusionInd_eq_zero_of_lt ha]
  exact Q'.zero_mul_eqv _

/-! ## 2. The fusion tilt and the raw-row factorization -/

/-- **Fusion tilt** `N_x(y) = ∏_f n(y_f | packet_f(x))` over the coarse faces
(multiplicity-product surrogate carrier; U(1)-exact, not SU(2) YM). -/
def fusionTilt (S : SlabScalePair) (x y : EdgeLabelling) : Q' :=
  wholeSlabFiniteQProduct
    (fun f => Q'.ofNat (fourFoldMultiplicity (wholeSlabFinePacket S x f) (y f)))
    S.coarse.faceEdges

private theorem slabSpinAtPlaquette_le_fineCutoff
    {S : SlabScalePair} {x : EdgeLabelling} (hx : x ∈ S.fine.physicalLabellings)
    (plaquette : YMGap.Continuum.ClusterCount4DProgress.Z4Plaq) :
    slabSpinAtPlaquette S.fine.extent x plaquette ≤ S.fine.cutoff := by
  by_cases hslab : plaquette ∈ boundaryCompleteSlabPlaquettes S.fine.extent
  · rw [slabSpinAtPlaquette_eq_of_mem hslab]
    have hidLt := listIndexOf_lt_of_mem plaquette
      (boundaryCompleteSlabPlaquettes S.fine.extent) hslab
    have hidMem : listIndexOf plaquette (boundaryCompleteSlabPlaquettes S.fine.extent) ∈
        S.fine.faceEdges := by
      unfold SlabPhysicalData.faceEdges slabPhysicalFaceEdges
      exact List.mem_range.mpr hidLt
    exact Nat.le_of_lt_succ
      ((boundedEdgeLabellings_sound S.fine.cutoff S.fine.faceEdges x hx).1 _ hidMem)
  · rw [slabSpinAtPlaquette_eq_zero_of_not_mem hslab]
    exact Nat.zero_le _

private theorem pair_le_two_mul {u v K : Nat} (hu : u ≤ K) (hv : v ≤ K) : u + v ≤ 2 * K := by
  rw [Nat.two_mul]
  exact Nat.add_le_add hu hv

/-- One coarse face: raw face weight = coarse heat coefficient × multiplicity. -/
theorem wholeSlabFaceRawWeight_eqv_coeffAt_mul_fourFold
    (S : SlabScalePair) {x y : EdgeLabelling}
    (hx : x ∈ S.fine.physicalLabellings) (hy : y ∈ S.coarse.physicalLabellings)
    {f : Nat} (hf : f ∈ S.coarse.faceEdges) :
    wholeSlabFaceRawWeight S x y f ≈
      coeffAt (heatKernelPacket S.coarse.cutoff S.coarse.coupling) (y f) *
        Q'.ofNat (fourFoldMultiplicity (wholeSlabFinePacket S x f) (y f)) := by
  have hyf : y f < S.coarse.cutoff + 1 :=
    (boundedEdgeLabellings_sound S.coarse.cutoff S.coarse.faceEdges y hy).1 f hf
  rw [coeffAt_heatKernelPacket hyf]
  have hs : y f ≤ 4 * S.fine.cutoff := by
    have h := Nat.le_of_lt_succ hyf
    rw [S.coarse_cutoff] at h
    exact h
  have hb := slabSpinAtPlaquette_le_fineCutoff (S := S) hx
  unfold wholeSlabFaceRawWeight
  exact packetFixedFinalSum_eqv_coeffW_mul_fourFold S.coarse.coupling S.fine.cutoff
    (wholeSlabFinePacket S x f) (y f)
    (pair_le_two_mul (hb _) (hb _)) (pair_le_two_mul (hb _) (hb _)) hs

private theorem finiteQProduct_congr_on (F G : Nat → Q') :
    ∀ l : List Nat, (∀ i, i ∈ l → F i ≈ G i) →
      wholeSlabFiniteQProduct F l ≈ wholeSlabFiniteQProduct G l
  | [], _ => Q'.eqv_refl 1
  | head :: tail, h =>
      Q'.eqv_trans _ (G head * wholeSlabFiniteQProduct F tail) _
        (Q'.mul_eqv_congr_right _ _ _ (h head List.mem_cons_self))
        (Q'.mul_eqv_congr_left _ _ _
          (finiteQProduct_congr_on F G tail (fun i hi => h i (List.mem_cons_of_mem head hi))))

private theorem finiteQProduct_mul_split (A B : Nat → Q') :
    ∀ l : List Nat,
      wholeSlabFiniteQProduct (fun i => A i * B i) l ≈
        eliminateLinks A l * wholeSlabFiniteQProduct B l
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail =>
      Q'.eqv_trans _ ((A head * B head) * (eliminateLinks A tail * wholeSlabFiniteQProduct B tail)) _
        (Q'.mul_eqv_congr_left _ _ _ (finiteQProduct_mul_split A B tail))
        (mul_mul_mul_comm_local _ _ _ _)

/-- **Fusion-tilt identity (PROVED; surrogate carrier).**  On the physical
labelling lists, the whole-slab raw recoupling weight is the coarse surrogate
summand times the fusion tilt.  U(1)-exact; not an SU(2) Yang--Mills statement. -/
theorem wholeSlabRecouplingRawWeight_eqv_coarseTerm_mul_fusionTilt
    (S : SlabScalePair) (x y : EdgeLabelling)
    (hx : x ∈ S.fine.physicalLabellings) (hy : y ∈ S.coarse.physicalLabellings) :
    wholeSlabRecouplingRawWeight S x y ≈ S.coarse.physicalTerm y * fusionTilt S x y := by
  let E := eliminateLinks
    (fun f => coeffAt (heatKernelPacket S.coarse.cutoff S.coarse.coupling) (y f))
    S.coarse.faceEdges
  let L := Q'.ofNat (slabExplicitLinkMultiplicityProduct S.coarse.cutoff S.coarse.extent y)
  have hface : wholeSlabFaceRawProduct S x y ≈ E * fusionTilt S x y := by
    refine Q'.eqv_trans _ _ _ (wholeSlabFaceRawProduct_eqv_finiteQProduct S x y) ?_
    refine Q'.eqv_trans _ _ _ (finiteQProduct_congr_on _
      (fun f => coeffAt (heatKernelPacket S.coarse.cutoff S.coarse.coupling) (y f) *
        Q'.ofNat (fourFoldMultiplicity (wholeSlabFinePacket S x f) (y f)))
      S.coarse.faceEdges
      (fun f hf => wholeSlabFaceRawWeight_eqv_coeffAt_mul_fourFold S hx hy hf)) ?_
    exact finiteQProduct_mul_split _ _ _
  show wholeSlabFaceRawProduct S x y * L ≈ (E * L) * fusionTilt S x y
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hface) (mul_right_comm_local _ _ _)

/-! ## 3. Normalized tilt and the coherent-row covariance form -/

/-- `E_ν[N_x]`: the coarse surrogate-law mean of the fusion tilt. -/
def fusionTiltMean (S : SlabScalePair) (x : EdgeLabelling) : Q' :=
  listQSum (fun y => S.coarse.normalizedMass y * fusionTilt S x y) S.coarse.physicalLabellings

private theorem sum_eqv_partition_mul_mean_core {A : Type} (R P T : A → Q') (Z : Q')
    (hZ : (0 : Q') < Z) (l : List A) (hR : ∀ y, y ∈ l → R y ≈ P y * T y) :
    listQSum R l ≈ Z * listQSum (fun y => Q'.divPos (P y) Z hZ * T y) l := by
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_mul_left _ _ _)
  apply listQSum_congr_on
  intro y hy
  refine Q'.eqv_trans _ _ _ (hR y hy) ?_
  refine Q'.eqv_trans _ ((Q'.divPos (P y) Z hZ * Z) * T y) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.divPos_mul_eqv (P y) Z hZ))) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) (Q'.mul_assoc_eqv _ _ _)

/-- `Σ_y raw(x,y) = Z_coarse · E_ν[N_x]` on the physical lists. -/
theorem wholeSlabRawRowPartition_eqv_partition_mul_tiltMean
    (S : SlabScalePair) {x : EdgeLabelling} (hx : x ∈ S.fine.physicalLabellings) :
    wholeSlabRawRowPartition S x ≈ S.coarse.physicalPartition * fusionTiltMean S x := by
  unfold wholeSlabRawRowPartition fusionTiltMean SlabPhysicalData.normalizedMass
  exact sum_eqv_partition_mul_mean_core _ _ _ _ _ _
    (fun y hy => wholeSlabRecouplingRawWeight_eqv_coarseTerm_mul_fusionTilt S x y hx hy)

private theorem kernel_mul_mean_core (R P T Z Part M : Q') (hZ : (0 : Q') < Z)
    (hPart : (0 : Q') < Part) (hR : R ≈ P * T) (hM : Part ≈ Z * M) :
    Q'.divPos R Part hPart * M ≈ Q'.divPos P Z hZ * T := by
  -- M ≈ rZ * Part
  have hrZ : Q'.recipPos Z hZ * Z ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hZ)
  have hrP : Q'.recipPos Part hPart * Part ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Part hPart)
  have hMeq : M ≈ Q'.recipPos Z hZ * Part := by
    refine Q'.eqv_trans _ ((Q'.recipPos Z hZ * Z) * M) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hrZ) (Q'.one_mul_eqv M))
    · exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hM))
  unfold Q'.divPos
  refine Q'.eqv_trans _ ((R * Q'.recipPos Part hPart) * (Q'.recipPos Z hZ * Part)) _
    (Q'.mul_eqv_congr_left _ _ _ hMeq) ?_
  refine Q'.eqv_trans _ ((R * Q'.recipPos Z hZ) * (Q'.recipPos Part hPart * Part)) _
    (mul_mul_mul_comm_local _ _ _ _) ?_
  refine Q'.eqv_trans _ (R * Q'.recipPos Z hZ) _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hrP) (Q'.mul_one_eqv _)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hR) (mul_right_comm_local _ _ _)

/-- **Coherent conditional row (PROVED; surrogate carrier).**
`K(x, y) · E_ν[N_x] = ν(y) · N_x(y)`, i.e. `K(x, ·) = ν · N_x / E_ν[N_x]`. -/
theorem wholeSlabRecouplingConditionalKernel_mul_tiltMean
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    {y : EdgeLabelling} (hy : y ∈ S.coarse.physicalLabellings) :
    wholeSlabRecouplingConditionalKernel source y * fusionTiltMean S source.fineState ≈
      S.coarse.normalizedMass y * fusionTilt S source.fineState y := by
  unfold wholeSlabRecouplingConditionalKernel SlabPhysicalData.normalizedMass
  exact kernel_mul_mean_core _ _ _ _ _ _ _ _
    (wholeSlabRecouplingRawWeight_eqv_coarseTerm_mul_fusionTilt S _ y source.fine_mem hy)
    (wholeSlabRawRowPartition_eqv_partition_mul_tiltMean S source.fine_mem)

/-- `E_ν[N_x] > 0` on every coherent row. -/
theorem fusionTiltMean_pos {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) :
    (0 : Q') < fusionTiltMean S source.fineState := by
  have hZ : (0 : Q') < S.coarse.physicalPartition :=
    YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram.slabParametricKPhysicalPartition_pos
      S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  have hPart := wholeSlabRecouplingPartition_pos source
  have hM := wholeSlabRawRowPartition_eqv_partition_mul_tiltMean S source.fine_mem
  -- M ≈ rZ * Part, a product of positives
  have hrZ : Q'.recipPos _ hZ * S.coarse.physicalPartition ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ hZ)
  have hMeq : Q'.recipPos _ hZ * wholeSlabRecouplingPartition source ≈
      fusionTiltMean S source.fineState := by
    refine Q'.eqv_trans _
      (Q'.recipPos _ hZ * (S.coarse.physicalPartition * fusionTiltMean S source.fineState)) _
      (Q'.mul_eqv_congr_left _ _ _ hM) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hrZ) (Q'.one_mul_eqv _)
  exact Q'.pos_of_lt_of_le (Q'.mul_pos (Q'.recipPos_pos _ hZ) hPart) (Q'.le_of_eqv hMeq)

/-- **Coherent-row covariance (PROVED; surrogate carrier).**
`(E_{K(x,·)}[F] − E_ν[F]) · E_ν[N_x] = E_ν[N_x F] − E_ν[N_x] E_ν[F]`. -/
theorem coherentRowDefect_mul_tiltMean
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) (F : EdgeLabelling → Q') :
    (listQSum (fun y => wholeSlabRecouplingConditionalKernel source y * F y)
          S.coarse.physicalLabellings +
        -(observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F)) *
      fusionTiltMean S source.fineState ≈
    observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings
        (fun y => fusionTilt S source.fineState y * F y) +
      -(fusionTiltMean S source.fineState *
        observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_right _ _ _)) ?_
    unfold observableExpectation
    apply listQSum_congr_on
    intro y hy
    refine Q'.eqv_trans _ _ _ (mul_right_comm_local _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (wholeSlabRecouplingConditionalKernel_mul_tiltMean source hy)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv _ _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv _ _))

/-- Divided covariance form on a coherent row:
`E_{K(x,·)}[F] − E_ν[F] = Cov_ν(F, N_x) / E_ν[N_x]`. -/
theorem coherentRowDefect_eqv_tiltCovariance_div
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S) (F : EdgeLabelling → Q') :
    listQSum (fun y => wholeSlabRecouplingConditionalKernel source y * F y)
          S.coarse.physicalLabellings +
        -(observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F) ≈
      Q'.divPos
        (observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings
            (fun y => fusionTilt S source.fineState y * F y) +
          -(fusionTiltMean S source.fineState *
            observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F))
        (fusionTiltMean S source.fineState) (fusionTiltMean_pos source) := by
  have hM := fusionTiltMean_pos source
  have h := coherentRowDefect_mul_tiltMean source F
  generalize hD : (listQSum (fun y => wholeSlabRecouplingConditionalKernel source y * F y)
          S.coarse.physicalLabellings +
        -(observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F)) = D at h ⊢
  unfold Q'.divPos
  refine Q'.eqv_trans _ (D * (fusionTiltMean S source.fineState *
      Q'.recipPos _ hM)) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hM)) (Q'.mul_one_eqv D))
  · exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ h)

/-! ## 4. The one-step remainder as a fine-law average of row defects -/

/-- For any finite slab kernel, the remainder expectation of `F` is the
fine-law average of the row defects `E_K(x)[F] − E_ν[F]`. -/
theorem remainderObservableExpectation_eqv_rowDefectAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (F : EdgeLabelling → Q') :
    remainderObservableExpectation K F ≈
      listQSum
        (fun x => S.fine.normalizedMass x *
          (listQSum (fun y => K.kernel x y * F y) S.coarse.physicalLabellings +
            -(observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F)))
        S.fine.physicalLabellings := by
  let Lc := S.coarse.physicalLabellings
  let Lf := S.fine.physicalLabellings
  let EF := observableExpectation S.coarse.normalizedMass Lc F
  let A := fun x => listQSum (fun y => K.kernel x y * F y) Lc
  -- left side
  have hleft : remainderObservableExpectation K F ≈
      listQSum (fun x => S.fine.normalizedMass x * A x) Lf + -EF := by
    unfold remainderObservableExpectation observableExpectation
      SlabScalePair.FiniteSlabKernel.remainder
    refine Q'.eqv_trans _
      (listQSum (fun y => K.blockedMass y * F y + -(S.coarse.normalizedMass y * F y)) Lc) _
      (listQSum_congr_on _ _ _ (fun y _ => Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_mul_eqv _ _)))) ?_
    refine Q'.eqv_trans _ _ _ (listQSum_add _ _ _) ?_
    refine Q'.add_eqv_congr' ?_ (listQSum_neg_local _ _)
    unfold SlabScalePair.FiniteSlabKernel.blockedMass
    refine Q'.eqv_trans _
      (listQSum (fun y => listQSum (fun x => S.fine.normalizedMass x * (K.kernel x y * F y)) Lf) Lc) _
      (listQSum_congr_on _ _ _ (fun y _ => Q'.eqv_trans _ _ _
        (Q'.eqv_symm (listQSum_mul_right _ _ _))
        (listQSum_congr_on _ _ _ (fun x _ => Q'.mul_assoc_eqv _ _ _)))) ?_
    refine Q'.eqv_trans _ _ _ (listQSum_swap _ _ _) ?_
    exact listQSum_congr_on _ _ _ (fun x _ => listQSum_mul_left _ _ _)
  refine Q'.eqv_trans _ _ _ hleft ?_
  -- right side
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _
    (listQSum (fun x => S.fine.normalizedMass x * A x + -(S.fine.normalizedMass x * EF)) Lf) _
    (listQSum_congr_on _ _ _ (fun x _ => Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_neg_eqv _ _)))) ?_
  refine Q'.eqv_trans _ _ _ (listQSum_add _ _ _) ?_
  refine Q'.add_eqv_congr' (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _ _ _ (listQSum_neg_local _ _) (Q'.neg_eqv_congr _ _ ?_)
  refine Q'.eqv_trans _ _ _ (listQSum_mul_right _ _ _) ?_
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (SlabPhysicalData.normalizedMass_total S.fine))
    (Q'.one_mul_eqv _)

/-- **Covariance form for `allCutoffPhysicalKernel` (PROVED; surrogate carrier).**
On every coherent fine row (`x` physical, positive fine summand, positive raw
partition) the row defect of `allCutoffPhysicalKernel` is
`Cov_ν(F, N_x) / E_ν[N_x]`.  Together with
`remainderObservableExpectation_eqv_rowDefectAverage` this is the exact
covariance form of the one-step remainder; incoherent rows contribute their
null-completion defect (`allCutoffWholeSlabKernel_eq_null_of_*`). -/
theorem allCutoffRowDefect_eqv_tiltCovariance_div
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff) {x : EdgeLabelling}
    (hx : x ∈ S.fine.physicalLabellings) (hpositive : (0 : Q') < S.fine.physicalTerm x)
    (hpartition : (0 : Q') < wholeSlabRawRowPartition S x) (F : EdgeLabelling → Q') :
    listQSum (fun y => (allCutoffPhysicalKernel S hfineCutoff).kernel x y * F y)
          S.coarse.physicalLabellings +
        -(observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F) ≈
      Q'.divPos
        (observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings
            (fun y => fusionTilt S x y * F y) +
          -(fusionTiltMean S x *
            observableExpectation S.coarse.normalizedMass S.coarse.physicalLabellings F))
        (fusionTiltMean S x)
        (fusionTiltMean_pos (coherentSlabRecouplingSourceOfRawPartitionPos S x hx hpartition)) := by
  have hk : (fun y => (allCutoffPhysicalKernel S hfineCutoff).kernel x y * F y) =
      (fun y => wholeSlabRecouplingConditionalKernel
        (coherentSlabRecouplingSourceOfRawPartitionPos S x hx hpartition) y * F y) := by
    funext y
    show allCutoffWholeSlabKernel S x y * F y = _
    rw [allCutoffWholeSlabKernel_eq_recoupling S hx hpositive hpartition y]
  rw [hk]
  exact coherentRowDefect_eqv_tiltCovariance_div
    (coherentSlabRecouplingSourceOfRawPartitionPos S x hx hpartition) F

end YMGap.Continuum.CompactDualWholeSlabFusionTilt

#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.ofNat_fourFoldChannelInd
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.le_add_of_fusionOK
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.ofNat_fourFoldMultiplicity
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.packetFixedFinalSum_eqv_coeffW_mul_fourFold
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.wholeSlabFaceRawWeight_eqv_coeffAt_mul_fourFold
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.wholeSlabRecouplingRawWeight_eqv_coarseTerm_mul_fusionTilt
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.wholeSlabRawRowPartition_eqv_partition_mul_tiltMean
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.wholeSlabRecouplingConditionalKernel_mul_tiltMean
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.fusionTiltMean_pos
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.coherentRowDefect_mul_tiltMean
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.coherentRowDefect_eqv_tiltCovariance_div
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.remainderObservableExpectation_eqv_rowDefectAverage
#print axioms YMGap.Continuum.CompactDualWholeSlabFusionTilt.allCutoffRowDefect_eqv_tiltCovariance_div
