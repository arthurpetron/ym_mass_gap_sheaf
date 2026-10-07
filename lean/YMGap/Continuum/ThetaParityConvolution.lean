/-
# Exact finite theta-convolution parity reindex

The signed box [-N,N]^2 is the disjoint image of an even diamond and a
shifted odd diamond. Explicit integer-halving data give the inverse maps.
The finite rational sum equality holds for arbitrary weights, hence also
signed theta terms. The exponent and frequency pins retain both branches.

The transformed domains are diamonds, NOT same-cutoff rectangles. This is
finite algebra only; no completed theta addition/product identity or tail
transport is asserted here.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.TorusWilsonAction

namespace YMGap.Continuum.ThetaParityConvolution

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

abbrev SignedPair := Int × Int
abbrev ParityIndex := Sum SignedPair SignedPair

def encodeEven (z : SignedPair) : SignedPair := (z.1+z.2, z.1-z.2)
def encodeOdd (z : SignedPair) : SignedPair := (z.1+z.2+1, z.1-z.2)

def encode : ParityIndex → SignedPair
  | .inl z => encodeEven z
  | .inr z => encodeOdd z

/-- Actual inverse data, including negative integers (Euclidean division). -/
def decode (z : SignedPair) : ParityIndex :=
  if (z.1+z.2)%2 = 0 then
    .inl ((z.1+z.2)/2, (z.1-z.2)/2)
  else
    .inr ((z.1+z.2-1)/2, (z.1-z.2-1)/2)

theorem encode_decode (z : SignedPair) : encode (decode z) = z := by
  rcases z with ⟨m,n⟩
  by_cases hp : (m+n)%2 = 0
  · simp only [decode, hp, ↓reduceIte, encode, encodeEven]
    apply Prod.ext <;> dsimp <;> omega
  · simp only [decode, hp, ↓reduceIte, encode, encodeOdd]
    apply Prod.ext <;> dsimp <;> omega

theorem decode_encode_even (z : SignedPair) : decode (encodeEven z) = .inl z := by
  rcases z with ⟨j,k⟩
  have hp : ((j+k)+(j-k))%2 = 0 := by omega
  simp only [decode, encodeEven, hp, ↓reduceIte]
  congr 1
  apply Prod.ext <;> dsimp <;> omega

theorem decode_encode_odd (z : SignedPair) : decode (encodeOdd z) = .inr z := by
  rcases z with ⟨j,k⟩
  have hp : ((j+k+1)+(j-k))%2 ≠ 0 := by omega
  simp only [decode, encodeOdd, hp, ↓reduceIte]
  congr 1
  apply Prod.ext <;> dsimp <;> omega

theorem decode_encode (z : ParityIndex) : decode (encode z) = z := by
  cases z with
  | inl z => exact decode_encode_even z
  | inr z => exact decode_encode_odd z

theorem even_frequency_pin (j k : Int) :
    (encodeEven (j,k)).1+(encodeEven (j,k)).2 = 2*j ∧
      (encodeEven (j,k)).1-(encodeEven (j,k)).2 = 2*k := by
  dsimp [encodeEven]
  constructor <;> omega

theorem odd_frequency_pin (j k : Int) :
    (encodeOdd (j,k)).1+(encodeOdd (j,k)).2 = 2*j+1 ∧
      (encodeOdd (j,k)).1-(encodeOdd (j,k)).2 = 2*k+1 := by
  dsimp [encodeOdd]
  constructor <;> omega

theorem even_exponent_pin (j k : Int) :
    (encodeEven (j,k)).1*(encodeEven (j,k)).1 +
      (encodeEven (j,k)).2*(encodeEven (j,k)).2 = 2*(j*j+k*k) := by
  dsimp [encodeEven]
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  rw [Int.mul_comm k j]
  omega

theorem odd_exponent_pin (j k : Int) :
    (encodeOdd (j,k)).1*(encodeOdd (j,k)).1 +
      (encodeOdd (j,k)).2*(encodeOdd (j,k)).2 =
        2*(j*(j+1)+k*(k+1))+1 := by
  dsimp [encodeOdd]
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub,
    Int.mul_one, Int.one_mul]
  rw [Int.mul_comm k j]
  omega

def BoxBound (N : Nat) (z : SignedPair) : Prop :=
  -(N : Int) ≤ z.1 ∧ z.1 ≤ (N : Int) ∧
    -(N : Int) ≤ z.2 ∧ z.2 ≤ (N : Int)

def EvenDiamondBound (N : Nat) (z : SignedPair) : Prop := BoxBound N (encodeEven z)
def OddDiamondBound (N : Nat) (z : SignedPair) : Prop := BoxBound N (encodeOdd z)

instance (N : Nat) (z : SignedPair) : Decidable (BoxBound N z) :=
  inferInstanceAs (Decidable (-(N : Int) ≤ z.1 ∧ z.1 ≤ (N : Int) ∧
    -(N : Int) ≤ z.2 ∧ z.2 ≤ (N : Int)))

instance (N : Nat) (z : SignedPair) : Decidable (EvenDiamondBound N z) :=
  inferInstanceAs (Decidable (BoxBound N (encodeEven z)))

instance (N : Nat) (z : SignedPair) : Decidable (OddDiamondBound N z) :=
  inferInstanceAs (Decidable (BoxBound N (encodeOdd z)))

/-- Written signed interval, including both endpoints and N=0. -/
def signedIndices (N : Nat) : List Int :=
  (List.range (2*N+1)).map (fun i : Nat => (i : Int)-(N : Int))

def boxIndices (N : Nat) : List SignedPair := cartesian (signedIndices N) (signedIndices N)

/-- Independent diamond enumeration; the containing rectangle N+1 is only
an enumeration device and the exact original box constraints are filtered. -/
def evenDiamondIndices (N : Nat) : List SignedPair :=
  (boxIndices (N+1)).filter (fun z => decide (EvenDiamondBound N z))

def oddDiamondIndices (N : Nat) : List SignedPair :=
  (boxIndices (N+1)).filter (fun z => decide (OddDiamondBound N z))

private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro i hi j hj hij
      have hjN : j = N := List.mem_singleton.mp hj
      rw [hij, hjN] at hi
      exact (Nat.lt_irrefl N) (List.mem_range.mp hi)

theorem signedIndices_mem (N : Nat) (m : Int) :
    m ∈ signedIndices N ↔ -(N : Int) ≤ m ∧ m ≤ (N : Int) := by
  constructor
  · intro hm
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hm
    have hilt := List.mem_range.mp hi
    change (i : Int)-(N : Int) = m at he
    constructor <;> omega
  · intro hm
    have hnonneg : 0 ≤ m+(N : Int) := by omega
    have hcast : ((m+(N : Int)).toNat : Int) = m+(N : Int) := Int.toNat_of_nonneg hnonneg
    apply List.mem_map.mpr
    refine ⟨(m+(N : Int)).toNat, List.mem_range.mpr (by omega), ?_⟩
    change ((m+(N : Int)).toNat : Int)-(N : Int) = m
    omega

theorem boxIndices_mem (N : Nat) (z : SignedPair) : z ∈ boxIndices N ↔ BoxBound N z := by
  rw [boxIndices, mem_cartesian_iff, signedIndices_mem, signedIndices_mem]
  unfold BoxBound
  constructor
  · intro h
    exact ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩
  · intro h
    exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩

theorem boxIndices_nodup (N : Nat) : (boxIndices N).Nodup := by
  have hi : (signedIndices N).Nodup :=
    TorusWilsonAction.nodup_map_on (fun i : Nat => (i : Int)-(N : Int))
      (fun i _ j _ he => by
        change (i : Int)-(N : Int) = (j : Int)-(N : Int) at he
        omega) (range_nodup (2*N+1))
  exact cartesian_nodup _ _ hi hi

theorem evenDiamondIndices_mem (N : Nat) (z : SignedPair) :
    z ∈ evenDiamondIndices N ↔ EvenDiamondBound N z := by
  constructor
  · intro hz
    exact of_decide_eq_true (List.mem_filter.mp hz).2
  · intro hz
    apply List.mem_filter.mpr
    refine ⟨(boxIndices_mem (N+1) z).2 ?_, decide_eq_true hz⟩
    rcases z with ⟨j,k⟩
    dsimp [EvenDiamondBound, BoxBound, encodeEven] at hz ⊢
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

theorem oddDiamondIndices_mem (N : Nat) (z : SignedPair) :
    z ∈ oddDiamondIndices N ↔ OddDiamondBound N z := by
  constructor
  · intro hz
    exact of_decide_eq_true (List.mem_filter.mp hz).2
  · intro hz
    apply List.mem_filter.mpr
    refine ⟨(boxIndices_mem (N+1) z).2 ?_, decide_eq_true hz⟩
    rcases z with ⟨j,k⟩
    dsimp [OddDiamondBound, BoxBound, encodeOdd] at hz ⊢
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega

/-- Concrete Type-valued decoder into the two actual diamond domains. -/
def boxParityDecode (N : Nat) (z : {z : SignedPair // BoxBound N z}) :
    Sum {z : SignedPair // EvenDiamondBound N z} {z : SignedPair // OddDiamondBound N z} :=
  if hp : (z.val.1+z.val.2)%2 = 0 then
    .inl ⟨((z.val.1+z.val.2)/2,(z.val.1-z.val.2)/2), by
      have hz := z.property
      dsimp [EvenDiamondBound, BoxBound, encodeEven] at *
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega⟩
  else
    .inr ⟨((z.val.1+z.val.2-1)/2,(z.val.1-z.val.2-1)/2), by
      have hz := z.property
      dsimp [OddDiamondBound, BoxBound, encodeOdd] at *
      constructor
      · omega
      constructor
      · omega
      constructor <;> omega⟩

private theorem encodeEven_injective (a b : SignedPair) (he : encodeEven a = encodeEven b) : a = b := by
  have h := congrArg decode he
  rw [decode_encode_even, decode_encode_even] at h
  exact Sum.inl.inj h

private theorem encodeOdd_injective (a b : SignedPair) (he : encodeOdd a = encodeOdd b) : a = b := by
  have h := congrArg decode he
  rw [decode_encode_odd, decode_encode_odd] at h
  exact Sum.inr.inj h

/-- Exact finite permutation of the box, preserving the shifted diamond. -/
theorem box_parity_permutation (N : Nat) :
    (boxIndices N).Perm
      ((evenDiamondIndices N).map encodeEven ++ (oddDiamondIndices N).map encodeOdd) := by
  apply TorusWilsonAction.perm_of_nodup_mem (boxIndices_nodup N)
  · apply List.nodup_append.mpr
    refine ⟨TorusWilsonAction.nodup_map_on encodeEven
      (fun a _ b _ => encodeEven_injective a b)
      (List.filter_sublist.nodup (boxIndices_nodup (N+1))),
      TorusWilsonAction.nodup_map_on encodeOdd
      (fun a _ b _ => encodeOdd_injective a b)
      (List.filter_sublist.nodup (boxIndices_nodup (N+1))), ?_⟩
    intro a ha b hb hab
    obtain ⟨j,hj,he⟩ := List.mem_map.mp ha
    obtain ⟨k,hk,ho⟩ := List.mem_map.mp hb
    have hencode : encodeEven j = encodeOdd k := he.trans (hab.trans ho.symm)
    have h := congrArg decode hencode
    rw [decode_encode_even, decode_encode_odd] at h
    cases h
  · intro z
    constructor
    · intro hz
      have hbound := (boxIndices_mem N z).1 hz
      cases hd : decode z with
      | inl jk =>
          have he : encodeEven jk = z := by
            have h := encode_decode z
            rw [hd] at h
            exact h
          have hjk : EvenDiamondBound N jk := by
            change BoxBound N (encodeEven jk)
            rw [he]
            exact hbound
          exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
            ⟨jk,(evenDiamondIndices_mem N jk).2 hjk,he⟩))
      | inr jk =>
          have he : encodeOdd jk = z := by
            have h := encode_decode z
            rw [hd] at h
            exact h
          have hjk : OddDiamondBound N jk := by
            change BoxBound N (encodeOdd jk)
            rw [he]
            exact hbound
          exact List.mem_append.mpr (Or.inr (List.mem_map.mpr
            ⟨jk,(oddDiamondIndices_mem N jk).2 hjk,he⟩))
    · intro hz
      rcases List.mem_append.mp hz with he | ho
      · obtain ⟨jk,hjk,hz⟩ := List.mem_map.mp he
        have hbound : BoxBound N (encodeEven jk) := (evenDiamondIndices_mem N jk).1 hjk
        rw [hz] at hbound
        exact (boxIndices_mem N z).2 hbound
      · obtain ⟨jk,hjk,hz⟩ := List.mem_map.mp ho
        have hbound : BoxBound N (encodeOdd jk) := (oddDiamondIndices_mem N jk).1 hjk
        rw [hz] at hbound
        exact (boxIndices_mem N z).2 hbound

private theorem listQSum_perm {A : Type} (f : A → Q') {xs ys : List A} (h : xs.Perm ys) :
    listQSum f xs ≈ listQSum f ys := by
  induction h with
  | nil => exact Q'.eqv_refl 0
  | cons x _ ih => exact Q'.add_eqv_congr_left (f x) _ _ ih
  | swap x y xs =>
      exact poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.var 2)))
        (.add (.var 1) (.add (.var 0) (.var 2)))
        (by decide) (fun | 0 => f y | 1 => f x | _ => listQSum f xs)
  | trans _ _ ih₁ ih₂ => exact Q'.eqv_trans _ _ _ ih₁ ih₂

/-- Exact signed finite convolution, for arbitrary rational weights. The
two RHS sums have the actual even/odd DIAMOND domains. -/
theorem signed_box_parity_convolution (weight : SignedPair → Q') (N : Nat) :
    listQSum weight (boxIndices N) ≈
      listQSum (fun jk => weight (encodeEven jk)) (evenDiamondIndices N) +
        listQSum (fun jk => weight (encodeOdd jk)) (oddDiamondIndices N) := by
  have hp := listQSum_perm weight (box_parity_permutation N)
  have ha := listQSum_append weight ((evenDiamondIndices N).map encodeEven)
    ((oddDiamondIndices N).map encodeOdd)
  rw [listQSum_map, listQSum_map] at ha
  exact Q'.eqv_trans _ _ _ hp ha

end YMGap.Continuum.ThetaParityConvolution

#print axioms YMGap.Continuum.ThetaParityConvolution.boxIndices_nodup

#print axioms YMGap.Continuum.ThetaParityConvolution.encode_decode
#print axioms YMGap.Continuum.ThetaParityConvolution.decode_encode
#print axioms YMGap.Continuum.ThetaParityConvolution.even_frequency_pin
#print axioms YMGap.Continuum.ThetaParityConvolution.odd_frequency_pin
#print axioms YMGap.Continuum.ThetaParityConvolution.even_exponent_pin
#print axioms YMGap.Continuum.ThetaParityConvolution.odd_exponent_pin
#print axioms YMGap.Continuum.ThetaParityConvolution.signedIndices_mem
#print axioms YMGap.Continuum.ThetaParityConvolution.boxIndices_mem
#print axioms YMGap.Continuum.ThetaParityConvolution.evenDiamondIndices_mem
#print axioms YMGap.Continuum.ThetaParityConvolution.oddDiamondIndices_mem
#print axioms YMGap.Continuum.ThetaParityConvolution.boxParityDecode
#print axioms YMGap.Continuum.ThetaParityConvolution.box_parity_permutation
#print axioms YMGap.Continuum.ThetaParityConvolution.signed_box_parity_convolution
