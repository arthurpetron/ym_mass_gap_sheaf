/-
# Adjointness of the complete signed chronological window

Reversing every slice of the actual finite K/V chain exchanges its two
endpoint insertions. Kernel symmetry is used on each two-slice factor;
the weight on every slice, including both endpoints, is retained once.
The source probe is an arbitrary supported polynomial on the full window.
No positivity, normalization, stationarity, or factorization of that probe
is assumed. The consumer is the original odd-window kinetic quadratic.
-/

import YMGap.Continuum.SU2QuaternionSliceReversal
import YMGap.Continuum.SU2QuaternionHeadWindowContraction
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.SU2QuaternionHeadWindowReversal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionSliceReversal
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.SU2QuaternionHeadWindowContraction
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem support_mono {a b : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks a p) (hab : a≤b) :
    SupportedQuaternionBlocks b p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hab)

private theorem exponent_zero : ∀ (m : List Nat) (c : Nat),
    m.length≤c → exponentAt m c=0
  | [], _, _ => rfl
  | _::_, 0, h => by simp at h
  | _::m, c+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero m c (by simp only [List.length_cons] at h; omega)

private theorem identity_exponent (n : Nat) (m : List Nat)
    (hm : m.length≤4*n) (c : Nat) :
    exponentAt (reindexQuaternionExponents (identityQuaternionBlockInvolution n) m) c =
      exponentAt m c := by
  by_cases hc : c<4*n
  · rw [exponentAt_reindexQuaternionExponents _ _ hc]
    exact congrArg (exponentAt m) (by change 4*(c/4)+c%4=c; omega)
  · rw [exponent_zero _ c (by rw [reindexQuaternionExponents_length]; omega),
      exponent_zero m c (by omega)]

private theorem lift_list : ∀ (n : Nat) (p : RatPoly),
    liftBoundary n p = p.map (fun t => (List.replicate (4*n) 0 ++ t.1,t.2))
  | 0, p => by simpa only [liftBoundary, Nat.mul_zero, List.replicate_zero,
      List.nil_append] using (List.map_id p).symm
  | n+1, p => by
      rw [liftBoundary, lift_list]
      simp only [liftHead, List.map_map]
      apply List.map_congr_left
      intro t _
      rw [show 4*(n+1)=4*n+1+1+1+1 by omega]
      rfl

private theorem exponent_lift : ∀ (n c : Nat) (m : List Nat),
    exponentAt (List.replicate n 0 ++ m) c =
      if c<n then 0 else exponentAt m (c-n)
  | 0, c, m => by simp only [List.replicate_zero, List.nil_append,
      Nat.not_lt_zero, if_false, Nat.sub_zero]
  | n+1, 0, m => by simp only [List.replicate_succ, List.cons_append,
      exponentAt, List.getD_cons_zero, Nat.zero_lt_succ, if_true]
  | n+1, c+1, m => by
      rw [List.replicate_succ, List.cons_append]
      change exponentAt (List.replicate n 0 ++ m) c = _
      rw [exponent_lift]
      by_cases h : c<n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
        exact congrArg (exponentAt m) (by omega)

private theorem pad_lift_identity (source target offset : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks source p) :
    reindexQuaternionPolynomial (identityQuaternionBlockInvolution target)
        (liftBoundary offset
          (reindexQuaternionPolynomial (identityQuaternionBlockInvolution source) p)) =
      reindexQuaternionPolynomial (identityQuaternionBlockInvolution target) (liftBoundary offset p) := by
  rw [lift_list, lift_list]
  simp only [reindexQuaternionPolynomial, List.map_map]
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply]
  apply Prod.ext
  · apply natList_eq_of_length_getD
    · rw [reindexQuaternionExponents_length, reindexQuaternionExponents_length]
    · intro c hc
      rw [reindexQuaternionExponents_length] at hc
      change exponentAt (reindexQuaternionExponents _ _) c = exponentAt (reindexQuaternionExponents _ _) c
      rw [exponentAt_reindexQuaternionExponents _ _ hc,
        exponentAt_reindexQuaternionExponents _ _ hc, exponent_lift, exponent_lift]
      split
      · rfl
      · exact identity_exponent source t.1 (hp t ht) _
  · rfl

/-- Complete supported source padding can be transported through a lift. -/
theorem lift_padded {source target : Nat} (offset : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks source p) (hq : SupportedQuaternionBlocks source q)
    (h : PaddedPolynomialCoeffEqv source p q) :
    PaddedPolynomialCoeffEqv target (liftBoundary offset p) (liftBoundary offset q) := by
  have hh := RatPolyCoeffEqv.reindex (identityQuaternionBlockInvolution target)
    (lift_coeff offset h)
  rw [pad_lift_identity source target offset p hp,
    pad_lift_identity source target offset q hq] at hh
  exact hh

/-- Supported prefix equality survives any common lift and target padding. -/
theorem prefix_lift {source target : Nat} (offset : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks source p) (hq : SupportedQuaternionBlocks source q)
    (h : QuaternionPrefixPolynomialEqv source p q) :
    PaddedPolynomialCoeffEqv target (liftBoundary offset p) (liftBoundary offset q) :=
  lift_padded offset hp hq (.of_prefix h)

private def placedProduct (blocks count : Nat) (p : RatPoly) : RatPoly :=
  polynomialProduct (fun j => liftBoundary (j*blocks) p) (List.range count)

private theorem product_map {A B : Type} (f : B→RatPoly) (g : A→B) (xs : List A) :
    polynomialProduct f (xs.map g) = polynomialProduct (fun x=>f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (polyMul (f (g x))) ih

private theorem product_lift (target offset : Nat) (f : Nat→RatPoly) (xs : List Nat) :
    PaddedPolynomialCoeffEqv target
      (liftBoundary offset (polynomialProduct f xs))
      (polynomialProduct (fun i=>liftBoundary offset (f i)) xs) := by
  induction xs with
  | nil => exact lift_one target offset
  | cons i xs ih =>
      change PaddedPolynomialCoeffEqv target (liftBoundary offset (polyMul _ _)) (polyMul _ _)
      rw [lift_product]
      exact (PaddedPolynomialCoeffEqv.refl target _).mul ih

private theorem placedProduct_succ (target blocks count : Nat) (p : RatPoly) :
    PaddedPolynomialCoeffEqv target (placedProduct blocks (count+1) p)
      (polyMul p (liftBoundary blocks (placedProduct blocks count p))) := by
  unfold placedProduct
  rw [List.range_succ_eq_map]
  change PaddedPolynomialCoeffEqv target
    (polyMul (liftBoundary (0*blocks) p)
      (polynomialProduct (fun j=>liftBoundary (j*blocks) p) ((List.range count).map Nat.succ))) _
  simp only [Nat.zero_mul, liftBoundary]
  rw [product_map]
  have he : (fun j => liftBoundary ((j+1)*blocks) p) =
      (fun j => liftBoundary blocks (liftBoundary (j*blocks) p)) := by
    funext j
    rw [show (j+1)*blocks=blocks+j*blocks by rw [Nat.succ_mul]; omega, liftBoundary_add]
  rw [he]
  exact (PaddedPolynomialCoeffEqv.refl target _).mul (product_lift target blocks _ _).symm

private theorem product_padded (target : Nat) (f g : Nat→RatPoly) (xs : List Nat)
    (h : ∀ i, i∈xs → PaddedPolynomialCoeffEqv target (f i) (g i)) :
    PaddedPolynomialCoeffEqv target (polynomialProduct f xs) (polynomialProduct g xs) := by
  induction xs with
  | nil => exact .refl _ _
  | cons i xs ih =>
      exact (h i List.mem_cons_self).mul
        (ih (fun j hj=>h j (List.mem_cons_of_mem i hj)))

private theorem product_supported {blocks : Nat} (f : Nat→RatPoly) (xs : List Nat)
    (h : ∀ i, i∈xs → SupportedQuaternionBlocks blocks (f i)) :
    SupportedQuaternionBlocks blocks (polynomialProduct f xs) := by
  induction xs with
  | nil => exact supported_one _
  | cons i xs ih =>
      exact supported_polyMul (h i List.mem_cons_self)
        (ih (fun j hj=>h j (List.mem_cons_of_mem i hj)))

private theorem placedProduct_supported {blocks L r count : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((r+1)*blocks) p) (hcount : count+r≤L+1) :
    SupportedQuaternionBlocks ((L+1)*blocks) (placedProduct blocks count p) := by
  apply product_supported
  intro i hi
  have hi' : i<count := List.mem_range.mp hi
  have hh := Nat.mul_le_mul_right blocks (show (r+1)+i≤L+1 by omega)
  exact support_mono (lift_supported hp (i*blocks)) (by simpa only [Nat.add_mul] using hh)

private theorem closed_chain (target blocks L : Nat) (kernel weight : RatPoly)
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight) :
    PaddedPolynomialCoeffEqv target (chain blocks kernel weight L polyOne)
      (polyMul (placedProduct blocks L kernel) (placedProduct blocks (L+1) weight)) := by
  induction L generalizing target with
  | zero =>
      change PaddedPolynomialCoeffEqv target (polyMul weight polyOne)
        (polyMul polyOne (polyMul (liftBoundary (0*blocks) weight) polyOne))
      simp only [Nat.zero_mul, liftBoundary]
      exact .of_coeff (RatPolyCoeffEqv.one_mul _).symm
  | succ L ih =>
      have htail : PaddedPolynomialCoeffEqv target
          (liftBoundary blocks (chain blocks kernel weight L polyOne))
          (polyMul (liftBoundary blocks (placedProduct blocks L kernel))
            (liftBoundary blocks (placedProduct blocks (L+1) weight))) := by
        have hleft := chain_supported hk hw L (supported_one blocks)
        have hright : SupportedQuaternionBlocks ((L+1)*blocks)
            (polyMul (placedProduct blocks L kernel) (placedProduct blocks (L+1) weight)) :=
          supported_polyMul
            (placedProduct_supported (blocks:=blocks) (L:=L) (r:=1) (count:=L)
              (p:=kernel) (by simpa only [Nat.add_mul, Nat.one_mul] using hk) (Nat.le_refl _))
            (placedProduct_supported (blocks:=blocks) (L:=L) (r:=0) (count:=L+1)
              (p:=weight) (by simpa only [Nat.zero_add, Nat.one_mul] using hw) (by omega))
        have hh := lift_padded (target:=target) blocks hleft hright (ih ((L+1)*blocks))
        rw [lift_product] at hh
        exact hh
      have hh : PaddedPolynomialCoeffEqv target
          (chain blocks kernel weight (L+1) polyOne)
          (polyMul kernel (polyMul weight
            (polyMul (liftBoundary blocks (placedProduct blocks L kernel))
              (liftBoundary blocks (placedProduct blocks (L+1) weight))))) :=
        (PaddedPolynomialCoeffEqv.refl target kernel).mul
          ((PaddedPolynomialCoeffEqv.refl target weight).mul htail)
      have hr : RatPolyCoeffEqv
          (polyMul kernel (polyMul weight
            (polyMul (liftBoundary blocks (placedProduct blocks L kernel))
              (liftBoundary blocks (placedProduct blocks (L+1) weight)))))
          (polyMul (polyMul kernel (liftBoundary blocks (placedProduct blocks L kernel)))
            (polyMul weight (liftBoundary blocks (placedProduct blocks (L+1) weight)))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
          (fun
            | 0 => kernel
            | 1 => weight
            | 2 => liftBoundary blocks (placedProduct blocks L kernel)
            | _ => liftBoundary blocks (placedProduct blocks (L+1) weight))
      exact hh.trans ((PaddedPolynomialCoeffEqv.of_coeff hr).trans
        ((placedProduct_succ target blocks L kernel).mul
          (placedProduct_succ target blocks (L+1) weight)).symm)

private theorem reindex_padded {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q) :
    PaddedPolynomialCoeffEqv blocks
      (reindexQuaternionPolynomial s p) (reindexQuaternionPolynomial s q) :=
  (PaddedPolynomialCoeffEqv.of_prefix (QuaternionPrefixPolynomialEqv.reindex s
    (identityReindexQuaternionPolynomial_prefix blocks p))).symm.trans
      ((PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.reindex s h)).trans
        (.of_prefix (QuaternionPrefixPolynomialEqv.reindex s
          (identityReindexQuaternionPolynomial_prefix blocks q))))

private theorem reindex_product {blocks : Nat} (s : QuaternionBlockInvolution blocks)
    (f : Nat→RatPoly) (xs : List Nat) :
    PaddedPolynomialCoeffEqv blocks (reindexQuaternionPolynomial s (polynomialProduct f xs))
      (polynomialProduct (fun i=>reindexQuaternionPolynomial s (f i)) xs) := by
  induction xs with
  | nil => exact .of_prefix (reindex_polyOne_prefix s)
  | cons i xs ih =>
      change PaddedPolynomialCoeffEqv blocks (reindexQuaternionPolynomial s (polyMul _ _)) _
      rw [reindexQuaternionPolynomial_mul]
      exact (PaddedPolynomialCoeffEqv.refl blocks _).mul ih

private theorem reverse_range_perm (count : Nat) :
    ((List.range count).map (fun j=>count-1-j)).Perm (List.range count) := by
  apply @YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff Nat Nat.decEq
  · exact YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn _ _
      (YMGap.Continuum.CayleyParentInj.range_nodup count) (fun i hi j hj h=>by
        have hi' := List.mem_range.mp hi
        have hj' := List.mem_range.mp hj
        omega)
  · exact YMGap.Continuum.CayleyParentInj.range_nodup count
  · intro j
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      have hi' := List.mem_range.mp hi
      exact List.mem_range.mpr (by omega)
    · intro hj
      have hj' := List.mem_range.mp hj
      exact List.mem_map.mpr ⟨count-1-j,List.mem_range.mpr (by omega),by omega⟩

private theorem placedProduct_reverse {blocks L r count : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks ((r+1)*blocks) p) (hlen : count+r=L+1)
    (hs : PaddedPolynomialCoeffEqv ((r+1)*blocks) (reversePolynomial blocks r p) p) :
    PaddedPolynomialCoeffEqv ((L+1)*blocks)
      (reversePolynomial blocks L (placedProduct blocks count p)) (placedProduct blocks count p) := by
  have hfirst := reindex_product (sliceReverse blocks L)
    (fun j=>liftBoundary (j*blocks) p) (List.range count)
  have hmiddle : PaddedPolynomialCoeffEqv ((L+1)*blocks)
      (polynomialProduct (fun j=>reversePolynomial blocks L (liftBoundary (j*blocks) p))
        (List.range count))
      (polynomialProduct (fun j=>liftBoundary ((count-1-j)*blocks) p) (List.range count)) := by
    apply product_padded
    intro j hj
    have hj' := List.mem_range.mp hj
    have hfit : j+r≤L := by omega
    have hh := (PaddedPolynomialCoeffEqv.of_prefix (reversePolynomial_lift blocks L j r hfit p hp)).trans
      (lift_padded (target:=(L+1)*blocks) ((L-j-r)*blocks)
        (reversePolynomial_supported blocks r p) hp hs)
    simpa only [show L-j-r=count-1-j by omega] using hh
  have hlast : PaddedPolynomialCoeffEqv ((L+1)*blocks)
      (polynomialProduct (fun j=>liftBoundary ((count-1-j)*blocks) p) (List.range count))
      (placedProduct blocks count p) := by
    rw [← product_map (fun j=>liftBoundary (j*blocks) p)
      (fun j=>count-1-j) (List.range count)]
    exact .of_coeff (polynomialProduct_perm _ (reverse_range_perm count))
  exact hfirst.trans (hmiddle.trans hlast)

private theorem reverse_one_swap (blocks : Nat) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv (blocks+blocks)
      (reversePolynomial blocks 1 p)
      (reindexQuaternionPolynomial (SU2QuaternionTwoSliceSwap.swap blocks) p) := by
  have hmap (i : Nat) (hi : i<blocks+blocks) :
      (sliceReverse blocks 1).map i=(SU2QuaternionTwoSliceSwap.swap blocks).map i := by
    have hn : 0<blocks := by omega
    have hd : blocks*(i/blocks)+i%blocks=i := Nat.div_add_mod i blocks
    have hr := Nat.mod_lt i hn
    by_cases hlo : i<blocks
    · rw [SU2QuaternionTwoSliceSwap.swap_lower blocks i hlo]
      change blocks*(1-i/blocks)+i%blocks = blocks+i
      rw [Nat.div_eq_of_lt hlo, Nat.mod_eq_of_lt hlo, Nat.sub_zero, Nat.mul_one]
    · have hq : i/blocks=1 := by
        have hquot : i/blocks≤1 := by
          by_cases h : i/blocks≤1
          · exact h
          · have hm := Nat.mul_le_mul_left blocks (show 2≤i/blocks by omega)
            rw [Nat.mul_two] at hm
            omega
        have hpositive : 0<i/blocks := by
          by_cases hz : i/blocks=0
          · rw [hz, Nat.mul_zero, Nat.zero_add] at hd
            exact False.elim (hlo (hd ▸ hr))
          · exact Nat.pos_of_ne_zero hz
        omega
      rw [show (SU2QuaternionTwoSliceSwap.swap blocks).map i=i-blocks from if_neg hlo]
      change blocks*(1-i/blocks)+i%blocks = i-blocks
      rw [hq, Nat.sub_self, Nat.mul_zero, Nat.zero_add]
      rw [hq, Nat.mul_one] at hd
      omega
  induction p with
  | nil => exact .nil
  | cons t ts ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro c hc
        change exponentAt (reindexQuaternionExponents (sliceReverse blocks 1) t.1) c =
          exponentAt (reindexQuaternionExponents (SU2QuaternionTwoSliceSwap.swap blocks) t.1) c
        rw [exponentAt_reindexQuaternionExponents _ _ (by simpa [Nat.two_mul] using hc),
          exponentAt_reindexQuaternionExponents _ _ hc, hmap (c/4) (by omega)]
      · exact ih

/-- The full closed action is reversal-invariant, with every endpoint V
retained and every original kernel compared by its supplied slice symmetry. -/
theorem closedChain_reversal {blocks : Nat} {kernel weight : RatPoly} (L : Nat)
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight)
    (hs : PaddedPolynomialCoeffEqv (blocks+blocks)
      (reindexQuaternionPolynomial (SU2QuaternionTwoSliceSwap.swap blocks) kernel) kernel) :
    PaddedPolynomialCoeffEqv ((L+1)*blocks)
      (reversePolynomial blocks L (chain blocks kernel weight L polyOne))
      (chain blocks kernel weight L polyOne) := by
  have hkernel : PaddedPolynomialCoeffEqv ((1+1)*blocks) (reversePolynomial blocks 1 kernel) kernel := by
    simpa only [Nat.add_mul, Nat.one_mul] using
      (PaddedPolynomialCoeffEqv.of_prefix (reverse_one_swap blocks kernel)).trans hs
  have hweight : PaddedPolynomialCoeffEqv ((0+1)*blocks) (reversePolynomial blocks 0 weight) weight := by
    simpa only [Nat.zero_add, Nat.one_mul] using
      PaddedPolynomialCoeffEqv.of_prefix (reversePolynomial_zero blocks weight hw)
  have hc := closed_chain ((L+1)*blocks) blocks L kernel weight hk hw
  have hr := reindex_padded (sliceReverse blocks L) hc
  rw [reindexQuaternionPolynomial_mul] at hr
  exact hr.trans
    (((placedProduct_reverse (L:=L) (r:=1) (count:=L)
      (by simpa only [Nat.add_mul, Nat.one_mul] using hk) (by omega) hkernel).mul
      (placedProduct_reverse (L:=L) (r:=0) (count:=L+1) (by simpa using hw) (by omega) hweight)).trans hc.symm)

private theorem chain_terminal_coeff (blocks L : Nat) (kernel weight g : RatPoly) :
    RatPolyCoeffEqv (chain blocks kernel weight L g)
      (polyMul (chain blocks kernel weight L polyOne) (liftBoundary (L*blocks) g)) := by
  induction L with
  | zero =>
      simpa only [chain, Nat.zero_mul, liftBoundary] using
        ((RatPolyCoeffEqv.mul_one weight).mul_right g).symm
  | succ L ih =>
      have hh := ((lift_coeff blocks ih).mul_left weight).mul_left kernel
      rw [lift_product, ← liftBoundary_add blocks (L*blocks) g,
        show blocks+L*blocks=(L+1)*blocks by rw [Nat.succ_mul]; omega] at hh
      exact hh.trans (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (by decide)
        (fun
          | 0 => kernel
          | 1 => weight
          | 2 => liftBoundary blocks (chain blocks kernel weight L polyOne)
          | _ => liftBoundary ((L+1)*blocks) g))

private theorem chain_terminal (target blocks L : Nat) (kernel weight g : RatPoly) :
    PaddedPolynomialCoeffEqv target (chain blocks kernel weight L g)
      (polyMul (chain blocks kernel weight L polyOne) (liftBoundary (L*blocks) g)) :=
  .of_coeff (chain_terminal_coeff blocks L kernel weight g)

/-- Exact adjointness of a complete signed multi-time window. The final
one-slice weight is outside each half-open message, once and unchanged. -/
theorem windowMessage_reversal {blocks : Nat} {kernel weight f g p : RatPoly}
    (L : Nat) (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hw : SupportedQuaternionBlocks blocks weight)
    (hs : PaddedPolynomialCoeffEqv (blocks+blocks)
      (reindexQuaternionPolynomial (SU2QuaternionTwoSliceSwap.swap blocks) kernel) kernel)
    (hf : SupportedQuaternionBlocks blocks f) (hg : SupportedQuaternionBlocks blocks g)
    (hp : SupportedQuaternionBlocks ((L+1)*blocks) p) :
    quaternionHaar blocks
        (polyMul weight (polyMul (windowMessage blocks kernel weight L f p) g)) ≈
      quaternionHaar blocks
        (polyMul weight (polyMul f
          (windowMessage blocks kernel weight L g (reversePolynomial blocks L p)))) := by
  let total := (L+1)*blocks
  let C := chain blocks kernel weight L polyOne
  have hroom : blocks≤total := by dsimp [total]; rw [Nat.succ_mul]; omega
  have hC : SupportedQuaternionBlocks total C := chain_supported hk hw L (supported_one blocks)
  have hlf : SupportedQuaternionBlocks total (liftBoundary (L*blocks) f) := by
    simpa only [total, Nat.succ_mul, Nat.add_comm] using lift_supported hf (L*blocks)
  have hlg : SupportedQuaternionBlocks total (liftBoundary (L*blocks) g) := by
    simpa only [total, Nat.succ_mul, Nat.add_comm] using lift_supported hg (L*blocks)
  have hrev : SupportedQuaternionBlocks total (reversePolynomial blocks L p) :=
    reversePolynomial_supported blocks L p
  let q := polyMul (polyMul f p) (polyMul C (liftBoundary (L*blocks) g))
  let q' := polyMul (polyMul g (reversePolynomial blocks L p)) (polyMul C (liftBoundary (L*blocks) f))
  have hq : SupportedQuaternionBlocks total q :=
    supported_polyMul (supported_polyMul (support_mono hf hroom) hp) (supported_polyMul hC hlg)
  have hq' : SupportedQuaternionBlocks total q' :=
    supported_polyMul (supported_polyMul (support_mono hg hroom) hrev) (supported_polyMul hC hlf)
  have hrf : PaddedPolynomialCoeffEqv total (reversePolynomial blocks L f) (liftBoundary (L*blocks) f) := by
    have h := (PaddedPolynomialCoeffEqv.of_prefix
      (reversePolynomial_lift blocks L 0 0 (Nat.zero_le _) f (by simpa using hf))).trans
      (prefix_lift (target:=total) (L*blocks)
        (by simpa using reversePolynomial_supported blocks 0 f) hf (reversePolynomial_zero blocks f hf))
    simpa only [Nat.zero_mul, liftBoundary, Nat.sub_zero] using h
  have hrg : PaddedPolynomialCoeffEqv total
      (reversePolynomial blocks L (liftBoundary (L*blocks) g)) g := by
    have hfirst := PaddedPolynomialCoeffEqv.of_prefix
      (reversePolynomial_lift blocks L L 0 (by omega) g (by simpa using hg))
    simp only [Nat.sub_self, Nat.zero_mul, liftBoundary] at hfirst
    have hlast : PaddedPolynomialCoeffEqv total (reversePolynomial blocks 0 g) g := by
      simpa only [liftBoundary] using
        (prefix_lift (source:=blocks) (target:=total) 0
          (p:=reversePolynomial blocks 0 g) (q:=g)
          (by simpa only [Nat.zero_add, Nat.one_mul] using reversePolynomial_supported blocks 0 g)
          hg (reversePolynomial_zero blocks g hg))
    exact hfirst.trans hlast
  have hpin : PaddedPolynomialCoeffEqv total (reversePolynomial blocks L q) q' := by
    dsimp only [q,q',reversePolynomial]
    rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul,
      reindexQuaternionPolynomial_mul]
    exact ((hrf.mul (PaddedPolynomialCoeffEqv.refl total _)).mul
      ((closedChain_reversal L hk hw hs).mul hrg)).trans
      (.of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 3) (.var 1)) (.mul (.var 2) (.var 0))) (by decide)
        (fun
          | 0 => liftBoundary (L*blocks) f
          | 1 => reversePolynomial blocks L p
          | 2 => C
          | _ => g)))
  have hchange : quaternionHaar total q ≈ quaternionHaar total q' :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_reindex (sliceReverse blocks L) q hq))
      (hpin.haar (reversePolynomial_supported blocks L q) hq')
  have hleft := windowMessage_pairing blocks kernel weight L f p g
  have hright := windowMessage_pairing blocks kernel weight L g (reversePolynomial blocks L p) f
  have hsourceLeft := ((PaddedPolynomialCoeffEqv.refl total (polyMul f p)).mul
    (chain_terminal total blocks L kernel weight g)).haar
      (supported_polyMul (supported_polyMul (support_mono hf hroom) hp) (chain_supported hk hw L hg)) hq
  have hsourceRight := ((PaddedPolynomialCoeffEqv.refl total (polyMul g (reversePolynomial blocks L p))).mul
    (chain_terminal total blocks L kernel weight f)).haar
      (supported_polyMul (supported_polyMul (support_mono hg hroom) hrev) (chain_supported hk hw L hf)) hq'
  have hleftOrder : quaternionHaar blocks
      (polyMul (windowMessage blocks kernel weight L f p) (polyMul weight g)) ≈
      quaternionHaar blocks (polyMul weight (polyMul (windowMessage blocks kernel weight L f p) g)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0=>windowMessage blocks kernel weight L f p | 1=>weight | _=>g))
  have hrightOrder : quaternionHaar blocks
      (polyMul (windowMessage blocks kernel weight L g (reversePolynomial blocks L p)) (polyMul weight f)) ≈
      quaternionHaar blocks (polyMul weight (polyMul f
        (windowMessage blocks kernel weight L g (reversePolynomial blocks L p)))) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
      (fun | 0=>windowMessage blocks kernel weight L g (reversePolynomial blocks L p) | 1=>weight | _=>f))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleftOrder)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
      (Q'.eqv_trans _ _ _ hsourceLeft
        (Q'.eqv_trans _ _ _ hchange
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm hsourceRight)
            (Q'.eqv_trans _ _ _ hright hrightOrder)))))

#print axioms closed_chain
#print axioms reindex_padded
#print axioms reindex_product
#print axioms reverse_range_perm
#print axioms placedProduct_reverse
#print axioms reverse_one_swap
#print axioms chain_terminal_coeff

end YMGap.Continuum.SU2QuaternionHeadWindowReversal

#print axioms YMGap.Continuum.SU2QuaternionHeadWindowReversal.lift_padded
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowReversal.prefix_lift
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowReversal.closedChain_reversal
#print axioms YMGap.Continuum.SU2QuaternionHeadWindowReversal.windowMessage_reversal
