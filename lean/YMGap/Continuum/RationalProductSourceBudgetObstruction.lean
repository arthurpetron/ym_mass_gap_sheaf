/-
# Exponential cost of the literal last Haar-source piece in a product model

This is a finite Boolean countermodel to a GENERIC source-budget shortcut,
not an instance of the SU(2) Wilson action and not a Yang--Mills counterexample.
There are M spectator coordinates and one active, unbiased source coordinate.
Every kinetic factor is k(x,y)=1+xy/2; V is the product of a(x)=1+x/2.
For the SAME transfer T, u1=T1 is the product of t(x)=1+x/4 and
f1=T(source spin) is u1 times the source spin divided by two.

The density is exactly nu=V*u1. Its centered source nu*f1 has zero Haar mean.
Integrate the M spectators: the last ordinary-Haar telescope piece is proved
equal to nu*qLast, with qLast an explicit rational function on a finite cube.
Its actual squared weighted norm is (588/335)^M times the squared norm of f1.
Thus a full-family source norm budget must pay for an exponentially expensive
literal summand, even though the initial sourceProbe has one-coordinate support
(the generated observed function does depend on the spectators).

The repository's partition-cleared centeredObservable would be Z*f1 here.
Multiplying both source and test by Z multiplies both squared norms by Z^2;
the displayed ratio is unchanged. No inverse limit or analytic hypothesis is
used. This file proves the last-piece identities and its isolated diagonal
cost; it does NOT claim to formalize the other pieces or the full signed D+2hR.
The actual consumer is the proposed width-independent upper budget behind
BF4ExactSlabFixedSpatialReciprocalSourceBudget / SeedNormBudget. Additional
Wilson-action structure, or a different decomposition, is still required.
-/

import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalProductSourceBudgetObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def half : Q' := ⟨1, 1⟩
def quarter : Q' := ⟨1, 3⟩
def spin : Bool → Q' | false => -1 | true => 1
def a (x : Bool) : Q' := 1 + half * spin x
def t (x : Bool) : Q' := 1 + quarter * spin x
def r (x : Bool) : Q' := a x * t x
def b (x : Bool) : Q' := r x * t x
def bMean : Q' := ⟨21, 15⟩
def c : Bool → Q' | false => ⟨7, 1⟩ | true => ⟨7, 9⟩
def normBase : Q' := ⟨201, 127⟩
def costBase : Q' := ⟨441, 159⟩
def growth : Q' := ⟨588, 334⟩

def mean (f : Bool → Q') : Q' := half * (f false + f true)

/-- M spectators, followed by the distinguished source bit. -/
def Cube : Nat → Type
  | 0 => Bool
  | M+1 => Bool × Cube M

def lastBit : (M : Nat) → Cube M → Bool
  | 0, x => x
  | M+1, x => lastBit M x.2

def haar : (M : Nat) → (Cube M → Q') → Q'
  | 0, f => mean f
  | M+1, f => mean (fun x => haar M (fun y => f (x,y)))

def tensor : (M : Nat) → (Bool → Q') → (Bool → Q') → Cube M → Q'
  | 0, _, v, x => v x
  | M+1, g, v, x => g x.1 * tensor M g v x.2

/-- Ordinary exact rational power, with no quotient or extraction. -/
def power (x : Q') : Nat → Q'
  | 0 => 1
  | M+1 => x * power x M

private theorem mul_congr {x x' y y' : Q'} (hx : x ≈ x') (hy : y ≈ y') :
    x*y ≈ x'*y' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hx)
    (Q'.mul_eqv_congr_left _ _ _ hy)

private theorem add_congr {x x' y y' : Q'} (hx : x ≈ x') (hy : y ≈ y') :
    x+y ≈ x'+y' :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hx)
    (Q'.add_eqv_congr_left _ _ _ hy)

private theorem rearrange (a b c d : Q') : (a*b)*(c*d) ≈ (a*c)*(b*d) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem mean_congr {f g : Bool → Q'} (h : ∀ x, f x ≈ g x) :
    mean f ≈ mean g :=
  Q'.mul_eqv_congr_left _ _ _ (add_congr (h false) (h true))

private theorem mean_scale (q : Q') (f : Bool → Q') :
    mean (fun x => q*f x) ≈ q*mean f :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 3))))
    (.mul (.var 1) (.mul (.var 0) (.add (.var 2) (.var 3))))
    (by decide) (fun | 0 => half | 1 => q | 2 => f false | _ => f true)

private theorem mean_scale_right (q : Q') (f : Bool → Q') :
    mean (fun x => f x*q) ≈ mean f*q :=
  Q'.eqv_trans _ _ _ (mean_congr (fun _ => Q'.mul_comm_eqv _ _))
    (Q'.eqv_trans _ _ _ (mean_scale q f) (Q'.mul_comm_eqv _ _))

private theorem haar_congr : (M : Nat) → {f g : Cube M → Q'} →
    (∀ x, f x ≈ g x) → haar M f ≈ haar M g
  | 0, _, _, h => mean_congr h
  | M+1, _, _, h => mean_congr (fun x => haar_congr M (fun y => h (x,y)))

private theorem haar_scale : (M : Nat) → (q : Q') → (f : Cube M → Q') →
    haar M (fun x => q*f x) ≈ q*haar M f
  | 0, q, f => mean_scale q f
  | M+1, q, f => Q'.eqv_trans _ _ _
      (mean_congr (fun x => haar_scale M q (fun y => f (x,y))))
      (mean_scale q _)

private theorem tensor_congr : (M : Nat) → {g g' v v' : Bool → Q'} →
    (∀ x, g x ≈ g' x) → (∀ x, v x ≈ v' x) →
    ∀ x, tensor M g v x ≈ tensor M g' v' x
  | 0, _, _, _, _, _, hv, x => hv x
  | M+1, _, _, _, _, hg, hv, x => mul_congr (hg x.1) (tensor_congr M hg hv x.2)

private theorem tensor_mul (M : Nat) (g h v z : Bool → Q') :
    ∀ x, tensor M g v x * tensor M h z x ≈
      tensor M (fun s => g s*h s) (fun s => v s*z s) x := by
  induction M with
  | zero => intro x; exact Q'.eqv_refl _
  | succ M ih =>
      intro x
      exact Q'.eqv_trans _ _ _ (rearrange _ _ _ _)
        (Q'.mul_eqv_congr_left _ _ _ (ih x.2))

private theorem power_congr {x y : Q'} (h : x ≈ y) :
    ∀ M, power x M ≈ power y M
  | 0 => Q'.eqv_refl _
  | M+1 => mul_congr h (power_congr h M)

private theorem power_mul (x y : Q') :
    ∀ M, power (x*y) M ≈ power x M * power y M
  | 0 => by change (1 : Q') ≈ 1*1; decide
  | M+1 => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (power_mul x y M))
      (Q'.eqv_symm (rearrange x (power x M) y (power y M)))

private theorem haar_tensor (M : Nat) (g v : Bool → Q') :
    haar M (tensor M g v) ≈ power (mean g) M * mean v := by
  induction M with
  | zero => exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | succ M ih =>
      exact Q'.eqv_trans _ _ _
        (mean_congr (fun x => haar_scale M (g x) (tensor M g v)))
        (Q'.eqv_trans _ _ _ (mean_scale_right (haar M (tensor M g v)) g)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih)
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

private theorem weighted_square (M : Nat) (g v : Bool → Q') :
    haar M (fun x => tensor M r (fun _ => 1) x *
      (tensor M g v x * tensor M g v x)) ≈
    power (mean (fun x => r x*(g x*g x))) M * mean (fun x => v x*v x) := by
  have hp (x : Cube M) : tensor M r (fun _ => 1) x *
      (tensor M g v x * tensor M g v x) ≈
      tensor M (fun s => r s*(g s*g s)) (fun s => v s*v s) x :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (tensor_mul M g g v v x))
      (Q'.eqv_trans _ _ _ (tensor_mul M r (fun s => g s*g s)
        (fun _ => 1) (fun s => v s*v s) x)
        (tensor_congr M (fun _ => Q'.eqv_refl _) (fun s => Q'.one_mul_eqv _) x))
  exact Q'.eqv_trans _ _ _ (haar_congr M hp) (haar_tensor M _ _)

/-! The transfer and its generated orbit, not a supplied density/source pair. -/

def kinetic (x y : Bool) : Q' := 1 + half*(spin x*spin y)

def productKinetic : (M : Nat) → Cube M → Cube M → Q'
  | 0, x, y => kinetic x y
  | M+1, x, y => kinetic x.1 y.1 * productKinetic M x.2 y.2

def potential (M : Nat) : Cube M → Q' := tensor M a (fun _ => 1)

def transfer (M : Nat) (f : Cube M → Q') (y : Cube M) : Q' :=
  haar M (fun x => (potential M x * productKinetic M x y) * f x)

def sourceProbe (M : Nat) : Cube M → Q' := tensor M (fun _ => 1) spin
def unitProbe (M : Nat) : Cube M → Q' := tensor M (fun _ => 1) (fun _ => 1)
def terminal (M : Nat) : Cube M → Q' := tensor M t (fun _ => 1)
def observed (M : Nat) : Cube M → Q' := tensor M t (fun x => half*spin x)
def density (M : Nat) (x : Cube M) : Q' := potential M x * terminal M x
def source (M : Nat) (x : Cube M) : Q' := density M x * observed M x

private theorem transfer_tensor (M : Nat) (g v : Bool → Q') :
    ∀ y, transfer M (tensor M g v) y ≈
      tensor M (fun z => mean (fun x => (a x*kinetic x z)*g x))
        (fun z => mean (fun x => kinetic x z*v x)) y := by
  induction M with
  | zero =>
      intro y
      change mean (fun x => ((1 : Q')*kinetic x y)*v x) ≈
        mean (fun x => kinetic x y*v x)
      exact mean_congr (fun x => Q'.mul_eqv_congr_right
        (1*kinetic x y) (kinetic x y) (v x) (Q'.one_mul_eqv (kinetic x y)))
  | succ M ih =>
      intro y
      have hp (s : Bool) (x : Cube M) :
          ((a s*potential M x)*(kinetic s y.1*productKinetic M x y.2)) *
              (g s*tensor M g v x) ≈
          ((a s*kinetic s y.1)*g s)*
            ((potential M x*productKinetic M x y.2)*tensor M g v x) :=
        poly_identity_of_normal_eq
          (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.var 4) (.var 5)))
          (.mul (.mul (.mul (.var 0) (.var 2)) (.var 4))
            (.mul (.mul (.var 1) (.var 3)) (.var 5)))
          (by decide) (fun
            | 0 => a s
            | 1 => potential M x
            | 2 => kinetic s y.1
            | 3 => productKinetic M x y.2
            | 4 => g s
            | _ => tensor M g v x)
      exact Q'.eqv_trans _ _ _
        (mean_congr (fun s => Q'.eqv_trans _ _ _ (haar_congr M (hp s))
          (haar_scale M ((a s*kinetic s y.1)*g s) _)))
        (Q'.eqv_trans _ _ _ (mean_scale_right (transfer M (tensor M g v) y.2) _)
          (Q'.mul_eqv_congr_left _ _ _ (ih y.2)))

theorem kinetic_bounds (x y : Bool) : half ≤ kinetic x y ∧ kinetic x y ≤ (⟨3,1⟩ : Q') := by
  cases x <;> cases y <;> decide

theorem potential_factor_positive (x : Bool) : (0 : Q') < a x := by
  cases x <;> decide

theorem unitProbe_one (M : Nat) : ∀ x, unitProbe M x ≈ 1 := by
  induction M with
  | zero => intro x; exact Q'.eqv_refl _
  | succ M ih => intro x; exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (ih x.2)

theorem sourceProbe_last (M : Nat) : ∀ x, sourceProbe M x ≈ spin (lastBit M x) := by
  induction M with
  | zero => intro x; exact Q'.eqv_refl _
  | succ M ih => intro x; exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (ih x.2)

theorem transfer_unit (M : Nat) (x : Cube M) : transfer M (unitProbe M) x ≈ terminal M x :=
  Q'.eqv_trans _ _ _ (transfer_tensor M (fun _ => 1) (fun _ => 1) x)
    (tensor_congr M (fun z => by cases z <;> decide) (fun z => by cases z <;> decide) x)

theorem transfer_source (M : Nat) (x : Cube M) : transfer M (sourceProbe M) x ≈ observed M x :=
  Q'.eqv_trans _ _ _ (transfer_tensor M (fun _ => 1) spin x)
    (tensor_congr M (fun z => by cases z <;> decide) (fun z => by cases z <;> decide) x)

theorem density_tensor (M : Nat) (x : Cube M) :
    density M x ≈ tensor M r (fun _ => 1) x :=
  Q'.eqv_trans _ _ _ (tensor_mul M a t (fun _ => 1) (fun _ => 1) x)
    (tensor_congr M (fun _ => Q'.eqv_refl _) (fun _ => by decide) x)

theorem source_tensor (M : Nat) (x : Cube M) :
    source M x ≈ tensor M b (fun y => half*spin y) x :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (density_tensor M x))
    (Q'.eqv_trans _ _ _ (tensor_mul M r t (fun _ => 1) (fun y => half*spin y) x)
      (tensor_congr M (fun _ => Q'.eqv_refl _) (fun _ => Q'.one_mul_eqv _) x))

theorem observed_centered (M : Nat) : haar M (source M) ≈ 0 :=
  Q'.eqv_trans _ _ _ (haar_congr M (source_tensor M))
    (Q'.eqv_trans _ _ _ (haar_tensor M b (fun y => half*spin y))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (show mean (fun y => half*spin y) ≈ 0 by decide))
        (poly_identity_of_normal_eq (.mul (.var 0) (.const 0)) (.const 0)
          (by decide) (fun _ => power (mean b) M))))

/-! The literal last ordinary-Haar telescope piece and its exact conjugate. -/

def integrateSpectators : (M : Nat) → (Cube M → Q') → Bool → Q'
  | 0, f, y => f y
  | M+1, f, y => mean (fun x => integrateSpectators M (fun z => f (x,z)) y)

private theorem integrate_congr : (M : Nat) → {f g : Cube M → Q'} →
    (∀ x, f x ≈ g x) → ∀ y, integrateSpectators M f y ≈ integrateSpectators M g y
  | 0, _, _, h, y => h y
  | M+1, _, _, h, y => mean_congr (fun x => integrate_congr M (fun z => h (x,z)) y)

private theorem integrate_scale : (M : Nat) → (q : Q') → (f : Cube M → Q') →
    ∀ y, integrateSpectators M (fun x => q*f x) y ≈ q*integrateSpectators M f y
  | 0, _, _, _ => Q'.eqv_refl _
  | M+1, q, f, y => Q'.eqv_trans _ _ _
      (mean_congr (fun x => integrate_scale M q (fun z => f (x,z)) y)) (mean_scale q _)

private theorem integrate_tensor (M : Nat) (g v : Bool → Q') :
    ∀ y, integrateSpectators M (tensor M g v) y ≈ power (mean g) M*v y := by
  induction M with
  | zero => intro y; exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | succ M ih =>
      intro y
      exact Q'.eqv_trans _ _ _
        (mean_congr (fun x => integrate_scale M (g x) (tensor M g v) y))
        (Q'.eqv_trans _ _ _ (mean_scale_right (integrateSpectators M (tensor M g v) y) g)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ih y))
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))))

/-- Partial projection through all spectators minus the final total projection. -/
def lastSourcePiece (M : Nat) (x : Cube M) : Q' :=
  integrateSpectators M (source M) (lastBit M x) + -(haar M (source M))

def lastTest (M : Nat) : Cube M → Q' := tensor M c (fun y => half*spin y)

theorem lastSourcePiece_value (M : Nat) (x : Cube M) :
    lastSourcePiece M x ≈ power bMean M*(half*spin (lastBit M x)) := by
  have hp := Q'.eqv_trans _ _ _ (integrate_congr M (source_tensor M) (lastBit M x))
    (Q'.eqv_trans _ _ _ (integrate_tensor M b (fun y => half*spin y) (lastBit M x))
      (Q'.mul_eqv_congr_right _ _ _ (power_congr (show mean b ≈ bMean by decide) M)))
  exact Q'.eqv_trans _ _ _
    (add_congr hp (Q'.neg_eqv_congr _ _ (observed_centered M)))
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0)
      (by decide) (fun _ => power bMean M*(half*spin (lastBit M x))))

private theorem tensor_constant (M : Nat) (q : Q') (v : Bool → Q') :
    ∀ x, tensor M (fun _ => q) v x ≈ power q M*v (lastBit M x) := by
  induction M with
  | zero => intro x; exact Q'.eqv_symm (Q'.one_mul_eqv _)
  | succ M ih =>
      intro x
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ih x.2))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

/-- Exact weighted-source pin; the displayed test is not an assumed inverse. -/
theorem lastTest_source_pin (M : Nat) (x : Cube M) :
    density M x * lastTest M x ≈ lastSourcePiece M x := by
  have hp := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (density_tensor M x))
    (Q'.eqv_trans _ _ _ (tensor_mul M r c (fun _ => 1) (fun y => half*spin y) x)
      (tensor_congr M (fun y => show r y*c y ≈ bMean by cases y <;> decide)
        (fun y => Q'.one_mul_eqv _) x))
  exact Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _ _ _ (tensor_constant M bMean (fun y => half*spin y) x)
      (Q'.eqv_symm (lastSourcePiece_value M x)))

/-! Exact weighted norms, with the growing factor exposed. -/

def weightedNorm (M : Nat) (f : Cube M → Q') : Q' :=
  haar M (fun x => density M x*(f x*f x))

theorem observed_norm (M : Nat) : weightedNorm M (observed M) ≈ quarter*power normBase M :=
  Q'.eqv_trans _ _ _
    (haar_congr M (fun x => Q'.mul_eqv_congr_right _ _ _ (density_tensor M x)))
    (Q'.eqv_trans _ _ _ (weighted_square M t (fun y => half*spin y))
      (Q'.eqv_trans _ _ _
        (mul_congr (power_congr (show mean (fun x => r x*(t x*t x)) ≈ normBase by decide) M)
          (show mean (fun x => (half*spin x)*(half*spin x)) ≈ quarter by decide))
        (Q'.mul_comm_eqv _ _)))

theorem lastTest_norm (M : Nat) : weightedNorm M (lastTest M) ≈ quarter*power costBase M :=
  Q'.eqv_trans _ _ _
    (haar_congr M (fun x => Q'.mul_eqv_congr_right _ _ _ (density_tensor M x)))
    (Q'.eqv_trans _ _ _ (weighted_square M c (fun y => half*spin y))
      (Q'.eqv_trans _ _ _
        (mul_congr (power_congr (show mean (fun x => r x*(c x*c x)) ≈ costBase by decide) M)
          (show mean (fun x => (half*spin x)*(half*spin x)) ≈ quarter by decide))
        (Q'.mul_comm_eqv _ _)))

theorem growth_gt_one : (1 : Q') < growth := by decide

/-- The ACTUAL literal last-source test has exponentially amplified norm. -/
theorem lastTest_norm_amplification (M : Nat) :
    weightedNorm M (lastTest M) ≈ power growth M*weightedNorm M (observed M) := by
  have hp := Q'.eqv_trans _ _ _ (power_congr (show costBase ≈ growth*normBase by decide) M)
    (power_mul growth normBase M)
  exact Q'.eqv_trans _ _ _ (lastTest_norm M)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hp)
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
          (fun | 0 => quarter | 1 => power growth M | _ => power normBase M))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (observed_norm M)))))

/-- Candidate isolated diagonal (1-h)||q_last||^2 with h=1/2.
Identification with an erased-message/family cost is not formalized here. -/
def lastDiagonal (M : Nat) : Q' :=
  haar M (fun x => density M x*((1 + -half)*(lastTest M x*lastTest M x)))

theorem lastDiagonal_amplification (M : Nat) :
    lastDiagonal M ≈ half*(power growth M*weightedNorm M (observed M)) := by
  have hp (x : Cube M) :
      density M x*((1 + -half)*(lastTest M x*lastTest M x)) ≈
      half*(density M x*(lastTest M x*lastTest M x)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (show (1 : Q') + -half ≈ half by decide)))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => density M x | 1 => half | _ => lastTest M x*lastTest M x))
  exact Q'.eqv_trans _ _ _ (haar_congr M hp)
    (Q'.eqv_trans _ _ _ (haar_scale M half _)
      (Q'.mul_eqv_congr_left _ _ _ (lastTest_norm_amplification M)))

#print axioms kinetic_bounds
#print axioms potential_factor_positive
#print axioms unitProbe_one
#print axioms sourceProbe_last
#print axioms transfer_unit
#print axioms transfer_source
#print axioms density_tensor
#print axioms source_tensor
#print axioms observed_centered
#print axioms lastSourcePiece_value
#print axioms lastTest_source_pin
#print axioms observed_norm
#print axioms lastTest_norm
#print axioms growth_gt_one
#print axioms lastTest_norm_amplification
#print axioms lastDiagonal_amplification

end YMGap.Continuum.RationalProductSourceBudgetObstruction
