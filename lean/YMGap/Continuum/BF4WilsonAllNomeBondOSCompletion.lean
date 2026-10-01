/-
# Represented completion of the physical bond-null Wilson sources

Original finite signed Wilson sources carry the actual odd-window bond
distance. Explicit-modulus Cauchy rows are identified by explicit-modulus
asymptotic bond closeness. Their represented completion is isometric to the
quotient of the EXISTING witnessed time-range states by equality of their
underlying original completed vectors. All representative maps and their
Type-valued moduli/range witnesses remain available before either quotient.
No time-zero multiplier, canonical continuum OS root, or new carrier norm is
assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSQuotient

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (difference)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeDistance
  (completedDist completedDist_symm completedDist_triangle completedDist_zero_iff)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (quarter quarter_positive four_quarters)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector
  (State CauchySequence stateSetoid)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization
  (bondForm image image_pairing image_distance denseSequence denseSequence_bound
    denseRows dense_limit)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The genuine odd-window bond seminorm of the difference, before taking
any Cauchy limit. -/
def physicalDist (x y : IntrinsicExpression width) : RC :=
  bondForm hw0 hw1 (difference x y) (difference x y)

theorem physicalDist_image (x y : IntrinsicExpression width) :
    physicalDist hw0 hw1 x y =
      dist (image hw0 hw1 x).val (image hw0 hw1 y).val :=
  (image_distance hw0 hw1 x y).symm

theorem physicalDist_refl (x : IntrinsicExpression width) :
    physicalDist hw0 hw1 x x = RCzero := by
  rw [physicalDist_image]
  exact (completedDist_zero_iff hw0 hw1 _ _).mpr rfl

theorem physicalDist_symm (x y : IntrinsicExpression width) :
    physicalDist hw0 hw1 x y = physicalDist hw0 hw1 y x := by
  rw [physicalDist_image, physicalDist_image]
  exact completedDist_symm hw0 hw1 _ _

theorem physicalDist_triangle (x y z : IntrinsicExpression width) :
    RCle (physicalDist hw0 hw1 x z)
      (RCadd (RCadd (physicalDist hw0 hw1 x y) (physicalDist hw0 hw1 x y))
        (RCadd (physicalDist hw0 hw1 y z) (physicalDist hw0 hw1 y z))) := by
  simp only [physicalDist_image]
  exact completedDist_triangle hw0 hw1 _ _ _

private theorem zero_le_rat (e : Q') (he : (0 : Q') < e) :
    RCle RCzero (rat e) :=
  leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

/-- Every representative row keeps its OWN computed all-tail modulus. -/
structure Rows where
  seq : Nat → IntrinsicExpression width
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ m n,
    modulus e ≤ m → modulus e ≤ n →
      RCle (physicalDist hw0 hw1 (seq m) (seq n)) (rat e)

/-- Explicit asymptotic closeness in the PHYSICAL bond distance, independent
of equality of any already-completed limit. -/
structure Close (X Y : Rows hw0 hw1 (width := width)) where
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
    RCle (physicalDist hw0 hw1 (X.seq n) (Y.seq n)) (rat e)

def closeRefl (X : Rows hw0 hw1 (width := width)) : Close hw0 hw1 X X where
  modulus := X.modulus
  bound := fun e he n hn => X.bound e he n n hn hn

def closeSymm {X Y : Rows hw0 hw1 (width := width)}
    (C : Close hw0 hw1 X Y) : Close hw0 hw1 Y X where
  modulus := C.modulus
  bound := by
    intro e he n hn
    rw [physicalDist_symm]
    exact C.bound e he n hn

def closeTrans {X Y Z : Rows hw0 hw1 (width := width)}
    (C : Close hw0 hw1 X Y) (D : Close hw0 hw1 Y Z) :
    Close hw0 hw1 X Z where
  modulus := fun e => max (C.modulus (quarter e)) (D.modulus (quarter e))
  bound := by
    intro e he n hn
    have hd := quarter_positive he
    have hl := C.bound (quarter e) hd n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hr := D.bound (quarter e) hd n (Nat.le_trans (Nat.le_max_right _ _) hn)
    have h := RCle_trans (physicalDist_triangle hw0 hw1 (X.seq n) (Y.seq n) (Z.seq n))
      (RCadd_le_add (RCadd_le_add hl hl) (RCadd_le_add hr hr))
    rwa [four_quarters] at h

/-- The quotient relation carries a Type-valued modulus witness before
propositional truncation. -/
def rowSetoid : Setoid (Rows hw0 hw1 (width := width)) where
  r X Y := Nonempty (Close hw0 hw1 X Y)
  iseqv := by
    constructor
    · intro X; exact ⟨closeRefl hw0 hw1 X⟩
    · intro X Y h
      rcases h with ⟨C⟩
      exact ⟨closeSymm hw0 hw1 C⟩
    · intro X Y Z h k
      rcases h with ⟨C⟩
      rcases k with ⟨D⟩
      exact ⟨closeTrans hw0 hw1 C D⟩

def BondCompletion : Type := Quotient (rowSetoid hw0 hw1 (width := width))

def SectorQuotient : Type := Quotient (stateSetoid hw0 hw1 (width := width))

/-- Every physical source row has a witnessed row in the ORIGINAL sector. -/
def imageRows (X : Rows hw0 hw1 (width := width)) :
    CauchySequence hw0 hw1 (width := width) where
  seq := fun n => image hw0 hw1 (X.seq n)
  modulus := X.modulus
  bound := by
    intro e he m n hm hn
    exact (physicalDist_image hw0 hw1 (X.seq m) (X.seq n)) ▸
      X.bound e he m n hm hn

/-- Public representative-level map; its returned `State` retains a concrete
original time-range witness. -/
def toSectorRep (X : Rows hw0 hw1 (width := width)) :
    State hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.limit hw0 hw1 (imageRows hw0 hw1 X)

theorem close_limit_eq {X Y : Rows hw0 hw1 (width := width)}
    (C : Close hw0 hw1 X Y) :
    (toSectorRep hw0 hw1 X).val = (toSectorRep hw0 hw1 Y).val := by
  apply BF4WilsonAllNomeTimeSector.limit_unique hw0 hw1
    (imageRows hw0 hw1 X) (toSectorRep hw0 hw1 Y).val
    (fun e => max (C.modulus (quarter e))
      (BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (imageRows hw0 hw1 Y) (quarter e)))
  intro e he n hn
  have hd := quarter_positive he
  have hl := C.bound (quarter e) hd n (Nat.le_trans (Nat.le_max_left _ _) hn)
  rw [physicalDist_image] at hl
  have hr := BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1
    (imageRows hw0 hw1 Y) (quarter e) hd n
    (Nat.le_trans (Nat.le_max_right _ _) hn)
  have h := RCle_trans (completedDist_triangle hw0 hw1
    (image hw0 hw1 (X.seq n)).val (image hw0 hw1 (Y.seq n)).val
      (toSectorRep hw0 hw1 Y).val)
    (RCadd_le_add (RCadd_le_add hl hl) (RCadd_le_add hr hr))
  rwa [four_quarters] at h

/-- Equality of computed limits has a CONSTRUCTED cross-row closeness
modulus; this is what makes the row quotient a genuine completion relation. -/
def closeOfLimitEq {X Y : Rows hw0 hw1 (width := width)}
    (h : (toSectorRep hw0 hw1 X).val = (toSectorRep hw0 hw1 Y).val) :
    Close hw0 hw1 X Y where
  modulus := fun e => max
    (BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (imageRows hw0 hw1 X) (quarter e))
    (BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (imageRows hw0 hw1 Y) (quarter e))
  bound := by
    intro e he n hn
    have hd := quarter_positive he
    have hl := BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1
      (imageRows hw0 hw1 X) (quarter e) hd n
      (Nat.le_trans (Nat.le_max_left _ _) hn)
    have hr := BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1
      (imageRows hw0 hw1 Y) (quarter e) hd n
      (Nat.le_trans (Nat.le_max_right _ _) hn)
    change RCle (dist (image hw0 hw1 (Y.seq n)).val
      (toSectorRep hw0 hw1 Y).val) (rat (quarter e)) at hr
    rw [← h, completedDist_symm] at hr
    rw [physicalDist_image]
    have htri := completedDist_triangle hw0 hw1
      (image hw0 hw1 (X.seq n)).val (toSectorRep hw0 hw1 X).val
      (image hw0 hw1 (Y.seq n)).val
    have hbound := RCle_trans htri
      (RCadd_le_add (RCadd_le_add hl hl) (RCadd_le_add hr hr))
    rwa [four_quarters] at hbound

theorem close_iff_limit_eq (X Y : Rows hw0 hw1 (width := width)) :
    Nonempty (Close hw0 hw1 X Y) ↔
      (toSectorRep hw0 hw1 X).val = (toSectorRep hw0 hw1 Y).val := by
  constructor
  · intro h
    rcases h with ⟨C⟩
    exact close_limit_eq hw0 hw1 C
  · intro h
    exact ⟨closeOfLimitEq hw0 hw1 h⟩

/-- Uniqueness is applied to an ABSTRACT row witness. Its limit construction
is never unfolded while the dense-source row's nested moduli are compared. -/
theorem toSectorRep_eq_of_bound (X : Rows hw0 hw1 (width := width))
    (y : V) (rate : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (dist (image hw0 hw1 (X.seq n)).val y) (rat e)) :
    (toSectorRep hw0 hw1 X).val = y := by
  apply BF4WilsonAllNomeTimeSector.limit_unique hw0 hw1
    (imageRows hw0 hw1 X) y rate
  exact bound

/-- Any supplied physical source sequence with an explicit limit rate forms
a physical bond-Cauchy row. The construction samples no representatives. -/
def rowsOfConvergent (seq : Nat → IntrinsicExpression width) (y : V)
    (rate : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (dist (image hw0 hw1 (seq n)).val y) (rat e)) :
    Rows hw0 hw1 (width := width) where
  seq := seq
  modulus := fun e => rate (quarter e)
  bound := by
    intro e he m n hm hn
    have hd := quarter_positive he
    have hl := bound (quarter e) hd m hm
    have hr := bound (quarter e) hd n hn
    rw [completedDist_symm] at hr
    rw [physicalDist_image]
    have h := RCle_trans
      (completedDist_triangle hw0 hw1 (image hw0 hw1 (seq m)).val y
        (image hw0 hw1 (seq n)).val)
      (RCadd_le_add (RCadd_le_add hl hl) (RCadd_le_add hr hr))
    rwa [four_quarters] at h

/-- The original sector limit of a convergent source row is its supplied
target vector. Keeping the sequence/rate/bound abstract avoids unfolding
their Type-valued witnesses in the specialized consumer. -/
theorem rowsOfConvergent_limit (seq : Nat → IntrinsicExpression width) (y : V)
    (rate : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, rate e ≤ n →
      RCle (dist (image hw0 hw1 (seq n)).val y) (rat e)) :
    (toSectorRep hw0 hw1 (rowsOfConvergent hw0 hw1 seq y rate bound)).val = y := by
  apply toSectorRep_eq_of_bound hw0 hw1
    (rowsOfConvergent hw0 hw1 seq y rate bound) y rate
  intro e he n hn
  exact bound e he n hn

/-- Public representative-level inverse: only the supplied sector state's
own original range witness is sampled. -/
def fromSectorRep (x : State hw0 hw1 (width := width)) :
    Rows hw0 hw1 (width := width) :=
  rowsOfConvergent hw0 hw1 (denseSequence hw0 hw1 x) x.val
    (fun e => e.den) (denseSequence_bound hw0 hw1 x)

theorem fromSectorRep_limit (x : State hw0 hw1 (width := width)) :
    (toSectorRep hw0 hw1 (fromSectorRep hw0 hw1 x)).val = x.val :=
  rowsOfConvergent_limit hw0 hw1 (denseSequence hw0 hw1 x) x.val
    (fun e => e.den) (denseSequence_bound hw0 hw1 x)

/-- The two quotient types retain their own represented data; only equality
of original completed vectors is quotiented on the sector side. -/
def toSector : BondCompletion hw0 hw1 (width := width) →
    SectorQuotient hw0 hw1 (width := width) :=
  Quotient.lift
    (fun X => Quotient.mk (stateSetoid hw0 hw1) (toSectorRep hw0 hw1 X))
    (fun X Y h => Quotient.sound ((close_iff_limit_eq hw0 hw1 X Y).mp h))

def fromSector : SectorQuotient hw0 hw1 (width := width) →
    BondCompletion hw0 hw1 (width := width) :=
  Quotient.lift
    (fun x => Quotient.mk (rowSetoid hw0 hw1) (fromSectorRep hw0 hw1 x))
    (fun x y h => Quotient.sound ((close_iff_limit_eq hw0 hw1
      (fromSectorRep hw0 hw1 x) (fromSectorRep hw0 hw1 y)).mpr (by
        rw [fromSectorRep_limit, fromSectorRep_limit]
        exact h)))

theorem toSector_fromSector (x : SectorQuotient hw0 hw1 (width := width)) :
    toSector hw0 hw1 (fromSector hw0 hw1 x) = x := by
  induction x using Quotient.inductionOn with
  | h a => exact Quotient.sound (fromSectorRep_limit hw0 hw1 a)

theorem fromSector_toSector (X : BondCompletion hw0 hw1 (width := width)) :
    fromSector hw0 hw1 (toSector hw0 hw1 X) = X := by
  induction X using Quotient.inductionOn with
  | h A =>
      exact Quotient.sound ((close_iff_limit_eq hw0 hw1
        (fromSectorRep hw0 hw1 (toSectorRep hw0 hw1 A)) A).mpr
          (fromSectorRep_limit hw0 hw1 (toSectorRep hw0 hw1 A)))

/-- The two completed distances are inherited from their computed ORIGINAL
completed-vector limits. On constant rows, the source distance is exactly
the physical bond form (`constant_distance` below). -/
def bondCompletedDistance : BondCompletion hw0 hw1 (width := width) →
    BondCompletion hw0 hw1 (width := width) → RC :=
  Quotient.lift₂
    (fun X Y => dist (toSectorRep hw0 hw1 X).val (toSectorRep hw0 hw1 Y).val)
    (fun _ _ _ _ h k => by
      dsimp only
      rw [(close_iff_limit_eq hw0 hw1 _ _).mp h,
        (close_iff_limit_eq hw0 hw1 _ _).mp k])

def sectorDistance : SectorQuotient hw0 hw1 (width := width) →
    SectorQuotient hw0 hw1 (width := width) → RC :=
  Quotient.lift₂
    (fun x y => dist x.val y.val)
    (fun _ _ _ _ h k => by
      dsimp only
      rw [h, k])

theorem toSector_isometry (X Y : BondCompletion hw0 hw1 (width := width)) :
    sectorDistance hw0 hw1 (toSector hw0 hw1 X) (toSector hw0 hw1 Y) =
      bondCompletedDistance hw0 hw1 X Y := by
  induction X using Quotient.inductionOn with
  | h A =>
    induction Y using Quotient.inductionOn with
    | h C => rfl

/-- Constant rows embed an actual finite source, with an explicit trivial
Cauchy modulus and no representative choice. -/
def constantRows (x : IntrinsicExpression width) : Rows hw0 hw1 (width := width) where
  seq := fun _ => x
  modulus := fun _ => 0
  bound := by
    intro e he m n hm hn
    rw [physicalDist_refl]
    exact zero_le_rat e he

theorem constantRows_limit (x : IntrinsicExpression width) :
    (toSectorRep hw0 hw1 (constantRows hw0 hw1 x)).val =
      (image hw0 hw1 x).val := by
  apply BF4WilsonAllNomeTimeSector.limit_unique hw0 hw1
    (imageRows hw0 hw1 (constantRows hw0 hw1 x)) (image hw0 hw1 x).val
    (fun _ => 0)
  intro e he n hn
  change RCle (dist (image hw0 hw1 x).val (image hw0 hw1 x).val) (rat e)
  rw [(completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
  exact zero_le_rat e he

def ofSource (x : IntrinsicExpression width) : BondCompletion hw0 hw1 (width := width) :=
  Quotient.mk (rowSetoid hw0 hw1) (constantRows hw0 hw1 x)

/-- The completed distance restricts to the ORIGINAL physical odd-window
bond distance, not to the ambient norm of the raw source. -/
theorem constant_distance (x y : IntrinsicExpression width) :
    bondCompletedDistance hw0 hw1 (ofSource hw0 hw1 x) (ofSource hw0 hw1 y) =
      physicalDist hw0 hw1 x y := by
  change dist (toSectorRep hw0 hw1 (constantRows hw0 hw1 x)).val
    (toSectorRep hw0 hw1 (constantRows hw0 hw1 y)).val = _
  rw [constantRows_limit, constantRows_limit, physicalDist_image]

def bondCompletedInner : BondCompletion hw0 hw1 (width := width) →
    BondCompletion hw0 hw1 (width := width) → RC :=
  Quotient.lift₂
    (fun X Y => B (toSectorRep hw0 hw1 X).val (toSectorRep hw0 hw1 Y).val)
    (fun _ _ _ _ h k => by
      dsimp only
      rw [(close_iff_limit_eq hw0 hw1 _ _).mp h,
        (close_iff_limit_eq hw0 hw1 _ _).mp k])

theorem constant_pairing (x y : IntrinsicExpression width) :
    bondCompletedInner hw0 hw1 (ofSource hw0 hw1 x) (ofSource hw0 hw1 y) =
      bondForm hw0 hw1 x y := by
  change B (toSectorRep hw0 hw1 (constantRows hw0 hw1 x)).val
    (toSectorRep hw0 hw1 (constantRows hw0 hw1 y)).val = _
  rw [constantRows_limit, constantRows_limit]
  exact image_pairing hw0 hw1 x y

#print axioms physicalDist
#print axioms physicalDist_image
#print axioms Rows
#print axioms Close
#print axioms closeTrans
#print axioms rowSetoid
#print axioms imageRows
#print axioms toSectorRep
#print axioms close_limit_eq
#print axioms closeOfLimitEq
#print axioms fromSectorRep
#print axioms toSectorRep_eq_of_bound
#print axioms rowsOfConvergent
#print axioms rowsOfConvergent_limit
#print axioms fromSectorRep_limit
#print axioms toSector
#print axioms fromSector
#print axioms toSector_fromSector
#print axioms fromSector_toSector
#print axioms bondCompletedDistance
#print axioms toSector_isometry
#print axioms constant_distance
#print axioms constant_pairing

end YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
