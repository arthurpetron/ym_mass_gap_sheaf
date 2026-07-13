/-
# Explicit finite codes for the exceptional chain carrier

This file unfolds the nested subtraction-free sums in
`connectingChainMajorant` into an explicit finite code space.  A raw chain
code records every recursively chosen next polymer and the terminal
compatible background family.  Pairing it with one further admissible family
gives the exact target code space for

    connectingChainMajorant w qP b1 b2 Γ label * XiR w qP Γ label.

The weighted enumeration is proved equal up to `Q'.eqv` to that product.
Thus a future exceptional-pair encoder has a concrete finite codomain rather
than an informal reference to a nested sum.
-/

import YMGap.Continuum.XiExceptionalWeightedInjection

namespace YMGap.Continuum.XiExceptionalCarrierCode

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiExceptionalWeightedInjection

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Algebra of finite `Q'` list sums -/

theorem qListSum_append (weight : α → Q') :
    ∀ (xs ys : List α),
      qListSum weight (xs ++ ys) ≈
        qListSum weight xs + qListSum weight ys
  | [], ys => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | x :: xs, ys => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (weight x) _ _
          (qListSum_append weight xs ys)) ?_
      exact Q'.eqv_symm
        (Q'.add_assoc_eqv (weight x) (qListSum weight xs)
          (qListSum weight ys))

theorem qListSum_map (weight : β → Q') (f : α → β) :
    ∀ xs : List α,
      qListSum weight (xs.map f) = qListSum (fun x => weight (f x)) xs
  | [] => rfl
  | _ :: xs => by
      simp only [List.map_cons, qListSum_cons]
      rw [qListSum_map weight f xs]

theorem qListSum_eqv_congr (f g : α → Q') :
    ∀ (xs : List α), (∀ x, x ∈ xs → f x ≈ g x) →
      qListSum f xs ≈ qListSum g xs
  | [], _ => Q'.eqv_refl _
  | x :: xs, h =>
      add_eqv_congr_both _ _ _ _
        (h x List.mem_cons_self)
        (qListSum_eqv_congr f g xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem qListSum_flatMap (weight : β → Q') (f : α → List β) :
    ∀ xs : List α,
      qListSum weight (xs.flatMap f) ≈
        qListSum (fun x => qListSum weight (f x)) xs
  | [] => Q'.eqv_refl _
  | x :: xs => by
      simp only [List.flatMap_cons, qListSum_cons]
      refine Q'.eqv_trans _ _ _
        (qListSum_append weight (f x) (xs.flatMap f)) ?_
      exact Q'.add_eqv_congr_left (qListSum weight (f x)) _ _
        (qListSum_flatMap weight f xs)

theorem qListSum_const_mul (a : Q') (weight : α → Q') :
    ∀ xs : List α,
      qListSum (fun x => a * weight x) xs ≈
        a * qListSum weight xs
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | x :: xs => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (a * weight x) _ _
          (qListSum_const_mul a weight xs)) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv a (weight x) (qListSum weight xs))

theorem qListSum_zero : ∀ xs : List α,
    qListSum (fun _ : α => (0 : Q')) xs ≈ 0
  | [] => Q'.eqv_refl _
  | _ :: xs =>
      Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _))
        (qListSum_zero xs)

theorem qListSum_mul_const (weight : α → Q') (a : Q') :
    ∀ xs : List α,
      qListSum (fun x => weight x * a) xs ≈
        qListSum weight xs * a
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv a)
  | x :: xs => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (weight x * a) _ _
          (qListSum_mul_const weight a xs)) ?_
      exact Q'.eqv_symm
        (Q'.add_mul_eqv (weight x) (qListSum weight xs) a)

theorem qListSum_eq_polymerWeightedSum (F : Polymer L → Q') :
    ∀ Γ : List (Polymer L),
      qListSum F Γ = polymerWeightedSum F Γ
  | [] => rfl
  | _ :: Γ => by
      simp only [qListSum_cons, polymerWeightedSum]
      rw [qListSum_eq_polymerWeightedSum F Γ]

/-! ## 2. Zero-weight representation of restricted family sums -/

def admissibleFamilyWeight (w : Q') (q : Polymer L → Bool)
    (label : L.Plaquette → Rep) (B : List (Polymer L)) : Q' :=
  if B.all q && familyCompatibleB B then familyActivity w B label else 0

theorem admissibleFamilyWeight_sum_filter (w : Q')
    (q : Polymer L → Bool) (label : L.Plaquette → Rep) :
    ∀ F : List (List (Polymer L)),
      qListSum (admissibleFamilyWeight w q label) F ≈
        polySum w label (F.filter
          (fun B => B.all q && familyCompatibleB B))
  | [] => Q'.eqv_refl _
  | B :: F => by
      cases hB : B.all q && familyCompatibleB B with
      | true =>
          simp only [qListSum_cons, admissibleFamilyWeight, hB, if_true,
            List.filter_cons, polySum_cons]
          exact Q'.add_eqv_congr_left (familyActivity w B label) _ _
            (admissibleFamilyWeight_sum_filter w q label F)
      | false =>
          simp only [qListSum_cons, admissibleFamilyWeight, hB, if_false,
            List.filter_cons]
          refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
          exact admissibleFamilyWeight_sum_filter w q label F

theorem admissibleFamilyWeight_sum_eqv_XiR (w : Q')
    (q : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    qListSum (admissibleFamilyWeight w q label) (sublists Γ) ≈
      XiR w q Γ label := by
  unfold XiR
  exact admissibleFamilyWeight_sum_filter w q label (sublists Γ)

theorem admissibleFamilyWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (q : Polymer L → Bool) (label : L.Plaquette → Rep)
    (B : List (Polymer L)) :
    (0 : Q') ≤ admissibleFamilyWeight w q label B := by
  unfold admissibleFamilyWeight
  split
  · exact familyActivity_nonneg hw B label
  · exact Q'.le_refl' _

/-! ## 3. Raw recursive chain codes -/

inductive ChainCode (P : Type) : Type
  | terminal (background : List (List P))
  | step (next : List P) (rest : ChainCode P)
deriving DecidableEq

def terminalCodes (Γ : List (Polymer L)) : List (ChainCode L.Plaquette) :=
  (sublists Γ).map ChainCode.terminal

def chainCodes (Γ : List (Polymer L)) : Nat → List (ChainCode L.Plaquette)
  | 0 => terminalCodes Γ
  | fuel + 1 =>
      terminalCodes Γ ++ Γ.flatMap (fun Y =>
        (chainCodes Γ fuel).map (ChainCode.step Y))

def chainCodeWeight (w : Q') (qP b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (X : Polymer L) → (bg : Polymer L → Bool) → ChainCode L.Plaquette → Q'
  | X, bg, .terminal B =>
      if qP X && b2 X then
        activity w X label * admissibleFamilyWeight w
          (fun T => (qP T && bg T) && compatibleB X T) label B
      else 0
  | X, bg, .step Y rest =>
      activity w X label *
        (if qP Y && !(compatibleB X Y) then
          chainCodeWeight w qP b2 Γ label Y
            (fun T => bg T && compatibleB X T) rest
        else 0)

theorem chainCodeWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    ∀ (code : ChainCode L.Plaquette) (X : Polymer L)
      (bg : Polymer L → Bool),
      (0 : Q') ≤ chainCodeWeight w qP b2 Γ label X bg code
  | .terminal B, X, bg => by
      unfold chainCodeWeight
      split
      · exact Q'.mul_nonneg _ _ (activity_nonneg hw X label)
          (admissibleFamilyWeight_nonnegative hw
            (fun T => (qP T && bg T) && compatibleB X T) label B)
      · exact Q'.le_refl' _
  | .step Y rest, X, bg => by
      unfold chainCodeWeight
      apply Q'.mul_nonneg
      · exact activity_nonneg hw X label
      · split
        · exact chainCodeWeight_nonnegative hw qP b2 Γ label rest Y
            (fun T => bg T && compatibleB X T)
        · exact Q'.le_refl' _

theorem terminalCodes_sum_eqv_chainWalkTerminal
    (w : Q') (qP b2 bg : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (X : Polymer L) :
    qListSum (chainCodeWeight w qP b2 Γ label X bg)
        (terminalCodes Γ) ≈
      chainWalkTerminal w qP b2 bg Γ label X := by
  unfold terminalCodes
  rw [qListSum_map]
  unfold chainWalkTerminal
  cases hX : qP X && b2 X with
  | false =>
      simp only [chainCodeWeight, hX, if_false]
      induction sublists Γ with
      | nil => exact Q'.eqv_refl _
      | cons B F ih =>
          simp only [qListSum_cons]
          exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ih
  | true =>
      simp only [chainCodeWeight, hX, if_true]
      refine Q'.eqv_trans _ _ _
        (qListSum_const_mul (activity w X label)
          (admissibleFamilyWeight w
            (fun T => (qP T && bg T) && compatibleB X T) label)
          (sublists Γ)) ?_
      exact Q'.mul_eqv_congr_left (activity w X label) _ _
        (admissibleFamilyWeight_sum_eqv_XiR w
          (fun T => (qP T && bg T) && compatibleB X T) Γ label)

/-! ## 4. The code sum is the recursive chain sum -/

theorem chainCodes_sum_eqv_chainWalkFrom
    (w : Q') (qP b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    ∀ (fuel : Nat) (bg : Polymer L → Bool) (X : Polymer L),
      qListSum (chainCodeWeight w qP b2 Γ label X bg)
          (chainCodes Γ fuel) ≈
        chainWalkFrom w qP b2 Γ label fuel bg X
  | 0, bg, X =>
      terminalCodes_sum_eqv_chainWalkTerminal w qP b2 bg Γ label X
  | fuel + 1, bg, X => by
      let codes := chainCodes Γ fuel
      let nextBg : Polymer L → Bool :=
        fun T => bg T && compatibleB X T
      let choose : Polymer L → Q' := fun Y =>
        if qP Y && !(compatibleB X Y) then
          chainWalkFrom w qP b2 Γ label fuel nextBg Y
        else 0
      have hinner : ∀ Y, Y ∈ Γ →
          qListSum (chainCodeWeight w qP b2 Γ label X bg)
              (codes.map (ChainCode.step Y)) ≈
            activity w X label * choose Y := by
        intro Y _
        rw [qListSum_map]
        cases hY : qP Y && !(compatibleB X Y) with
        | false =>
            simp only [chainCodeWeight, hY, if_false, choose]
            refine Q'.eqv_trans _ _ _
              (qListSum_const_mul (activity w X label)
                (fun _ : ChainCode L.Plaquette => (0 : Q')) codes) ?_
            exact Q'.mul_eqv_congr_left (activity w X label) _ _
              (qListSum_zero codes)
        | true =>
            simp only [chainCodeWeight, hY, if_true, choose]
            refine Q'.eqv_trans _ _ _
              (qListSum_const_mul (activity w X label)
                (chainCodeWeight w qP b2 Γ label Y nextBg) codes) ?_
            exact Q'.mul_eqv_congr_left (activity w X label) _ _
              (chainCodes_sum_eqv_chainWalkFrom w qP b2 Γ label
                fuel nextBg Y)
      have hflat :
          qListSum (chainCodeWeight w qP b2 Γ label X bg)
              (Γ.flatMap (fun Y => codes.map (ChainCode.step Y))) ≈
            activity w X label * polymerWeightedSum choose Γ := by
        refine Q'.eqv_trans _ _ _
          (qListSum_flatMap
            (chainCodeWeight w qP b2 Γ label X bg)
            (fun Y => codes.map (ChainCode.step Y)) Γ) ?_
        refine Q'.eqv_trans _ _ _
          (qListSum_eqv_congr
            (fun Y => qListSum (chainCodeWeight w qP b2 Γ label X bg)
              (codes.map (ChainCode.step Y)))
            (fun Y => activity w X label * choose Y) Γ hinner) ?_
        refine Q'.eqv_trans _ _ _
          (qListSum_const_mul (activity w X label) choose Γ) ?_
        exact Q'.mul_eqv_congr_left (activity w X label) _ _
          (Q'.eqv_of_eq (qListSum_eq_polymerWeightedSum choose Γ))
      unfold chainCodes chainWalkFrom
      refine Q'.eqv_trans _ _ _
        (qListSum_append (chainCodeWeight w qP b2 Γ label X bg)
          (terminalCodes Γ)
          (Γ.flatMap (fun Y => codes.map (ChainCode.step Y)))) ?_
      exact add_eqv_congr_both _ _ _ _
        (terminalCodes_sum_eqv_chainWalkTerminal w qP b2 bg Γ label X)
        hflat

/-! ## 5. Full carrier codes and the external `XiR` factor -/

abbrev CarrierCode (L : Lattice) := Polymer L × ChainCode L.Plaquette

def carrierCodes (Γ : List (Polymer L)) : List (CarrierCode L) :=
  Γ.flatMap (fun X =>
    (chainCodes Γ Γ.length).map (fun code => (X, code)))

def carrierCodeWeight (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (code : CarrierCode L) : Q' :=
  if qP code.1 && b1 code.1 then
    chainCodeWeight w qP b2 Γ label code.1 (fun _ => true) code.2
  else 0

theorem carrierCodeWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) (code : CarrierCode L) :
    (0 : Q') ≤ carrierCodeWeight w qP b1 b2 Γ label code := by
  unfold carrierCodeWeight
  split
  · exact chainCodeWeight_nonnegative hw qP b2 Γ label code.2 code.1
      (fun _ => true)
  · exact Q'.le_refl' _

theorem carrierCodes_sum_eqv_connectingChainMajorant
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    qListSum (carrierCodeWeight w qP b1 b2 Γ label) (carrierCodes Γ) ≈
      connectingChainMajorant w qP b1 b2 Γ label := by
  refine Q'.eqv_trans _ _ _
    (qListSum_flatMap (carrierCodeWeight w qP b1 b2 Γ label)
      (fun X => (chainCodes Γ Γ.length).map (fun code => (X, code))) Γ) ?_
  unfold connectingChainMajorant
  rw [← qListSum_eq_polymerWeightedSum]
  apply qListSum_eqv_congr
  intro X _
  rw [qListSum_map]
  cases hX : qP X && b1 X with
  | false =>
      simp only [carrierCodeWeight, hX, if_false]
      induction chainCodes Γ Γ.length with
      | nil => exact Q'.eqv_refl _
      | cons c cs ih =>
          simp only [qListSum_cons]
          exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ih
  | true =>
      simp only [carrierCodeWeight, hX, if_true]
      exact chainCodes_sum_eqv_chainWalkFrom w qP b2 Γ label Γ.length
        (fun _ => true) X

abbrev CarrierXiCode (L : Lattice) := CarrierCode L × List (Polymer L)

def carrierXiCodes (Γ : List (Polymer L)) : List (CarrierXiCode L) :=
  (sublists Γ).flatMap (fun B =>
    (carrierCodes Γ).map (fun code => (code, B)))

def carrierXiCodeWeight (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (code : CarrierXiCode L) : Q' :=
  carrierCodeWeight w qP b1 b2 Γ label code.1 *
    admissibleFamilyWeight w qP label code.2

theorem carrierXiCodeWeight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) (code : CarrierXiCode L) :
    (0 : Q') ≤ carrierXiCodeWeight w qP b1 b2 Γ label code :=
  Q'.mul_nonneg _ _
    (carrierCodeWeight_nonnegative hw qP b1 b2 Γ label code.1)
    (admissibleFamilyWeight_nonnegative hw qP label code.2)

/-- **Exact finite target representation.** -/
theorem carrierXiCodes_sum_eqv_carrier_mul_XiR
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    qListSum (carrierXiCodeWeight w qP b1 b2 Γ label)
        (carrierXiCodes Γ) ≈
      connectingChainMajorant w qP b1 b2 Γ label *
        XiR w qP Γ label := by
  refine Q'.eqv_trans _ _ _
    (qListSum_flatMap (carrierXiCodeWeight w qP b1 b2 Γ label)
      (fun B => (carrierCodes Γ).map (fun code => (code, B)))
      (sublists Γ)) ?_
  have hinner : ∀ B, B ∈ sublists Γ →
      qListSum (carrierXiCodeWeight w qP b1 b2 Γ label)
          ((carrierCodes Γ).map (fun code => (code, B))) ≈
        connectingChainMajorant w qP b1 b2 Γ label *
          admissibleFamilyWeight w qP label B := by
    intro B _
    rw [qListSum_map]
    refine Q'.eqv_trans _ _ _
      (qListSum_mul_const
        (carrierCodeWeight w qP b1 b2 Γ label)
        (admissibleFamilyWeight w qP label B) (carrierCodes Γ)) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (carrierCodes_sum_eqv_connectingChainMajorant w qP b1 b2 Γ label)
  refine Q'.eqv_trans _ _ _
    (qListSum_eqv_congr
      (fun B => qListSum (carrierXiCodeWeight w qP b1 b2 Γ label)
        ((carrierCodes Γ).map (fun code => (code, B))))
      (fun B => connectingChainMajorant w qP b1 b2 Γ label *
        admissibleFamilyWeight w qP label B)
      (sublists Γ) hinner) ?_
  refine Q'.eqv_trans _ _ _
    (qListSum_const_mul
      (connectingChainMajorant w qP b1 b2 Γ label)
      (admissibleFamilyWeight w qP label) (sublists Γ)) ?_
  exact Q'.mul_eqv_congr_left
    (connectingChainMajorant w qP b1 b2 Γ label) _ _
    (admissibleFamilyWeight_sum_eqv_XiR w qP Γ label)

/-! ## 6. Composition with a concrete exceptional-pair encoder -/

/-- Once an occurrence-distinct exceptional source list is injectively
encoded in the explicit carrier code space with pointwise weight domination,
the finite weighted-injection theorem and the exact code enumeration give
the desired global carrier-times-`XiR` bound. -/
theorem exceptional_qListSum_le_carrier_mul_XiR {Source : Type}
    {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep)
    (source : List Source) (sourceWeight : Source → Q')
    (encode : Source → CarrierXiCode L)
    (hsource : source.Nodup)
    (hmem : ∀ x, x ∈ source → encode x ∈ carrierXiCodes Γ)
    (hinjective : ∀ x, x ∈ source → ∀ y, y ∈ source →
      encode x = encode y → x = y)
    (hterm : ∀ x, x ∈ source →
      sourceWeight x ≤ carrierXiCodeWeight w qP b1 b2 Γ label (encode x)) :
    qListSum sourceWeight source ≤
      connectingChainMajorant w qP b1 b2 Γ label * XiR w qP Γ label := by
  have hsum := qListSum_le_of_injective source (carrierXiCodes Γ)
    sourceWeight (carrierXiCodeWeight w qP b1 b2 Γ label) encode
    hsource hmem hinjective hterm
    (fun code _ => carrierXiCodeWeight_nonnegative hw qP b1 b2 Γ label code)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (carrierXiCodes_sum_eqv_carrier_mul_XiR w qP b1 b2 Γ label))

#print axioms qListSum_append
#print axioms qListSum_flatMap
#print axioms admissibleFamilyWeight_sum_eqv_XiR
#print axioms admissibleFamilyWeight_nonnegative
#print axioms terminalCodes_sum_eqv_chainWalkTerminal
#print axioms chainCodeWeight_nonnegative
#print axioms chainCodes_sum_eqv_chainWalkFrom
#print axioms carrierCodeWeight_nonnegative
#print axioms carrierCodes_sum_eqv_connectingChainMajorant
#print axioms carrierXiCodeWeight_nonnegative
#print axioms carrierXiCodes_sum_eqv_carrier_mul_XiR
#print axioms exceptional_qListSum_le_carrier_mul_XiR

end YMGap.Continuum.XiExceptionalCarrierCode
