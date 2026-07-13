/-
# One-node refinement for rational atan Darboux partitions

This is the local common-refinement move.  Inserting `z` into a nonnegative
cell `[x,y]` decreases the left sum and increases the right sum for the
antitone kernel `2/(1+x^2)`.  Iterating this checked move over merged finite
node lists is the remaining endpoint-additivity construction.
-/

import YMGap.Continuum.SemicircleAtanInducedConvergence

namespace YMGap.Continuum.SemicircleAtanPartitionInsertion

open YMGap.Constructive
open YMGap.Continuum.SemicircleAtanInducedGap

def partitionLeftRect (x y : Q') : Q' :=
  (y + -x) * kernelValue x

def partitionRightRect (x y : Q') : Q' :=
  (y + -x) * kernelValue y

private def splitWidthPoly : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.var 1) (.neg (.var 0))) (.var 3))
    (.mul (.add (.var 2) (.neg (.var 1))) (.var 3))

private def coarseWidthPoly : RingNormaliser.PolyExpr :=
  .mul (.add (.var 2) (.neg (.var 0))) (.var 3)

private theorem splitWidth_normal :
    RingNormaliser.normalize splitWidthPoly =
      RingNormaliser.normalize coarseWidthPoly := by decide

private theorem split_width_factor_left (x z y f : Q') :
    (((z + -x) * f) + ((y + -z) * f)).eqv ((y + -x) * f) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    splitWidthPoly coarseWidthPoly splitWidth_normal
    (fun | 0 => x | 1 => z | 2 => y | _ => f)
  simpa [splitWidthPoly, coarseWidthPoly, RingNormaliser.eval] using h

private theorem split_width_factor_right (x z y f : Q') :
    (((z + -x) * f) + ((y + -z) * f)).eqv ((y + -x) * f) :=
  split_width_factor_left x z y f

/-- Inserting a node into a cell decreases its left Darboux contribution. -/
theorem split_left_le_coarse {x z y : Q'}
    (hx0 : (0 : Q') ≤ x) (hxz : x ≤ z) (hzy : z ≤ y) :
    partitionLeftRect x z + partitionLeftRect z y ≤
      partitionLeftRect x y := by
  have hkernel : kernelValue z ≤ kernelValue x :=
    kernelValue_antitone hx0 hxz
  have hwidth : (0 : Q') ≤ y + -z := Q'.sub_nonneg_of_le hzy
  have hmul : (y + -z) * kernelValue z ≤
      (y + -z) * kernelValue x :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hkernel hwidth
  unfold partitionLeftRect
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left ((z + -x) * kernelValue x) _ _ hmul)
    (Q'.le_of_eqv (split_width_factor_left x z y (kernelValue x)))

/-- Inserting a node into a cell increases its right Darboux contribution. -/
theorem coarse_right_le_split {x z y : Q'}
    (hx0 : (0 : Q') ≤ x) (hxz : x ≤ z) (hzy : z ≤ y) :
    partitionRightRect x y ≤
      partitionRightRect x z + partitionRightRect z y := by
  have hz0 : (0 : Q') ≤ z := Q'.le_trans' _ _ _ hx0 hxz
  have hkernel : kernelValue y ≤ kernelValue z :=
    kernelValue_antitone hz0 hzy
  have hwidth : (0 : Q') ≤ z + -x := Q'.sub_nonneg_of_le hxz
  have hmul : (z + -x) * kernelValue y ≤
      (z + -x) * kernelValue z :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hkernel hwidth
  unfold partitionRightRect
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (split_width_factor_right x z y (kernelValue y)))
    (Q'.add_le_add_right _ _ ((y + -z) * kernelValue y) hmul)

/-- Every refined right cell remains below its corresponding refined left
cell. -/
theorem right_le_left {x y : Q'} (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y) :
    partitionRightRect x y ≤ partitionLeftRect x y := by
  have hkernel : kernelValue y ≤ kernelValue x :=
    kernelValue_antitone hx0 hxy
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hkernel
    (Q'.sub_nonneg_of_le hxy)

abbrev PartitionCell := Q' × Q'

def partitionLeftSum : List PartitionCell → Q'
  | [] => 0
  | c :: cs => partitionLeftRect c.1 c.2 + partitionLeftSum cs

def partitionRightSum : List PartitionCell → Q'
  | [] => 0
  | c :: cs => partitionRightRect c.1 c.2 + partitionRightSum cs

private theorem recipPos_eqv_congr {a b : Q'}
    (ha : (0 : Q') < a) (hb : (0 : Q') < b) (hab : a.eqv b) :
    (Q'.recipPos a ha).eqv (Q'.recipPos b hb) := by
  show (Q'.recipPos a ha).num * ((Q'.recipPos b hb).den : Int) =
    (Q'.recipPos b hb).num * ((Q'.recipPos a ha).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_num, Q'.recipPos_den, Q'.recipPos_den]
  simpa only [Int.mul_comm] using hab.symm

theorem kernelValue_eqv_congr {x x' : Q'} (hxx' : x.eqv x') :
    (kernelValue x).eqv (kernelValue x') := by
  have hsquare : (x*x).eqv (x'*x') :=
    Q'.eqv_trans _ (x'*x) _
      (Q'.mul_eqv_congr_right _ _ _ hxx')
      (Q'.mul_eqv_congr_left _ _ _ hxx')
  have hden : ((1 : Q') + x*x).eqv ((1 : Q') + x'*x') :=
    Q'.add_eqv_congr_left 1 _ _ hsquare
  unfold kernelValue Q'.divPos
  exact Q'.mul_eqv_congr_left 2 _ _
    (recipPos_eqv_congr (SemicircleAtanTransformedSqueeze.kernelDen_pos x)
      (SemicircleAtanTransformedSqueeze.kernelDen_pos x') hden)

theorem partitionLeftRect_eqv_congr {x y x' y' : Q'}
    (hx : x.eqv x') (hy : y.eqv y') :
    (partitionLeftRect x y).eqv (partitionLeftRect x' y') := by
  unfold partitionLeftRect
  have hw : (y + -x).eqv (y' + -x') :=
    Q'.add_eqv_congr' hy (Q'.neg_eqv_congr _ _ hx)
  exact Q'.eqv_trans _ ((y' + -x') * kernelValue x) _
    (Q'.mul_eqv_congr_right _ _ _ hw)
    (Q'.mul_eqv_congr_left _ _ _ (kernelValue_eqv_congr hx))

theorem partitionRightRect_eqv_congr {x y x' y' : Q'}
    (hx : x.eqv x') (hy : y.eqv y') :
    (partitionRightRect x y).eqv (partitionRightRect x' y') := by
  unfold partitionRightRect
  have hw : (y + -x).eqv (y' + -x') :=
    Q'.add_eqv_congr' hy (Q'.neg_eqv_congr _ _ hx)
  exact Q'.eqv_trans _ ((y' + -x') * kernelValue y) _
    (Q'.mul_eqv_congr_right _ _ _ hw)
    (Q'.mul_eqv_congr_left _ _ _ (kernelValue_eqv_congr hy))

/-- Cellwise semantic equality, allowing distinct unnormalized `Q'`
representations of the same rational nodes. -/
inductive PartitionEqv : List PartitionCell → List PartitionCell → Prop
  | nil : PartitionEqv [] []
  | cons {x y x' y' : Q'} {cs cs' : List PartitionCell}
      (hx : x.eqv x') (hy : y.eqv y') (hrest : PartitionEqv cs cs') :
      PartitionEqv ((x, y) :: cs) ((x', y') :: cs')

theorem PartitionEqv.leftSum {cells cells' : List PartitionCell}
    (h : PartitionEqv cells cells') :
    (partitionLeftSum cells).eqv (partitionLeftSum cells') := by
  induction h with
  | nil => exact Q'.eqv_refl 0
  | cons hx hy hrest ih =>
      exact Q'.add_eqv_congr'
        (partitionLeftRect_eqv_congr hx hy) ih

theorem PartitionEqv.rightSum {cells cells' : List PartitionCell}
    (h : PartitionEqv cells cells') :
    (partitionRightSum cells).eqv (partitionRightSum cells') := by
  induction h with
  | nil => exact Q'.eqv_refl 0
  | cons hx hy hrest ih =>
      exact Q'.add_eqv_congr'
        (partitionRightRect_eqv_congr hx hy) ih

theorem PartitionEqv.refl (cells : List PartitionCell) :
    PartitionEqv cells cells := by
  induction cells with
  | nil => exact PartitionEqv.nil
  | cons c cs ih =>
      exact PartitionEqv.cons (Q'.eqv_refl c.1) (Q'.eqv_refl c.2) ih

/-- The one-node left refinement inequality remains valid at an arbitrary
cell position in a finite partition list. -/
theorem refine_cell_left (pre post : List PartitionCell) {x z y : Q'}
    (hx0 : (0 : Q') ≤ x) (hxz : x ≤ z) (hzy : z ≤ y) :
    partitionLeftSum
        (pre ++ (x, z) :: (z, y) :: post) ≤
      partitionLeftSum
        (pre ++ (x, y) :: post) := by
  induction pre with
  | nil =>
      change partitionLeftRect x z +
          (partitionLeftRect z y + partitionLeftSum post) ≤
        partitionLeftRect x y + partitionLeftSum post
      have hlocal := split_left_le_coarse hx0 hxz hzy
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.add_assoc_eqv (partitionLeftRect x z)
              (partitionLeftRect z y) (partitionLeftSum post))))
        (Q'.add_le_add_right _ _ _ hlocal)
  | cons c pre ih =>
      change partitionLeftRect c.1 c.2 +
          partitionLeftSum (pre ++ (x, z) :: (z, y) :: post) ≤
        partitionLeftRect c.1 c.2 +
          partitionLeftSum (pre ++ (x, y) :: post)
      exact Q'.add_le_add_left _ _ _ ih

/-- The dual right refinement inequality at an arbitrary cell position. -/
theorem refine_cell_right (pre post : List PartitionCell) {x z y : Q'}
    (hx0 : (0 : Q') ≤ x) (hxz : x ≤ z) (hzy : z ≤ y) :
    partitionRightSum
        (pre ++ (x, y) :: post) ≤
      partitionRightSum
        (pre ++ (x, z) :: (z, y) :: post) := by
  induction pre with
  | nil =>
      change partitionRightRect x y + partitionRightSum post ≤
        partitionRightRect x z +
          (partitionRightRect z y + partitionRightSum post)
      have hlocal := coarse_right_le_split hx0 hxz hzy
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ hlocal)
        (Q'.le_of_eqv
          (Q'.add_assoc_eqv (partitionRightRect x z)
            (partitionRightRect z y) (partitionRightSum post)))
  | cons c pre ih =>
      change partitionRightRect c.1 c.2 +
          partitionRightSum (pre ++ (x, y) :: post) ≤
        partitionRightRect c.1 c.2 +
          partitionRightSum (pre ++ (x, z) :: (z, y) :: post)
      exact Q'.add_le_add_left _ _ _ ih

/-- Constructive finite refinement generated by repeated insertion of an
ordered nonnegative node.  The first argument is the finer partition. -/
inductive CellRefines : List PartitionCell → List PartitionCell → Prop
  | refl (cells : List PartitionCell) : CellRefines cells cells
  | insert (pre post : List PartitionCell) (x z y : Q')
      (hx0 : (0 : Q') ≤ x) (hxz : x ≤ z) (hzy : z ≤ y) :
      CellRefines
        (pre ++ (x, z) :: (z, y) :: post)
        (pre ++ (x, y) :: post)
  | cons (cell : PartitionCell) {fine coarse : List PartitionCell} :
      CellRefines fine coarse → CellRefines (cell :: fine) (cell :: coarse)
  | trans {fine middle coarse : List PartitionCell} :
      CellRefines fine middle → CellRefines middle coarse →
        CellRefines fine coarse

/-- Iterated finite refinement decreases the complete left sum. -/
theorem CellRefines.left_le {fine coarse : List PartitionCell}
    (h : CellRefines fine coarse) :
    partitionLeftSum fine ≤ partitionLeftSum coarse := by
  induction h with
  | refl cells => exact Q'.le_refl' _
  | insert pre post x z y hx0 hxz hzy =>
      exact refine_cell_left pre post hx0 hxz hzy
  | cons cell h ih => exact Q'.add_le_add_left _ _ _ ih
  | trans h₁ h₂ ih₁ ih₂ => exact Q'.le_trans' _ _ _ ih₁ ih₂

/-- Iterated finite refinement increases the complete right sum. -/
theorem CellRefines.right_le {fine coarse : List PartitionCell}
    (h : CellRefines fine coarse) :
    partitionRightSum coarse ≤ partitionRightSum fine := by
  induction h with
  | refl cells => exact Q'.le_refl' _
  | insert pre post x z y hx0 hxz hzy =>
      exact refine_cell_right pre post hx0 hxz hzy
  | cons cell h ih => exact Q'.add_le_add_left _ _ _ ih
  | trans h₁ h₂ ih₁ ih₂ => exact Q'.le_trans' _ _ _ ih₂ ih₁

/-- Every cell in the list has nonnegative ordered endpoints. -/
inductive ValidCells : List PartitionCell → Prop
  | nil : ValidCells []
  | cons (x y : Q') (rest : List PartitionCell)
      (hx0 : (0 : Q') ≤ x) (hxy : x ≤ y) (hrest : ValidCells rest) :
      ValidCells ((x, y) :: rest)

theorem ValidCells.right_le_left {cells : List PartitionCell}
    (h : ValidCells cells) :
    partitionRightSum cells ≤ partitionLeftSum cells := by
  induction h with
  | nil => exact Q'.le_refl' 0
  | cons x y rest hx0 hxy hrest ih =>
      exact Q'.add_le_add
        (YMGap.Continuum.SemicircleAtanPartitionInsertion.right_le_left hx0 hxy) ih

/-- **Abstract common-refinement bracket.**  If one valid finite partition
refines each of two partitions, every right sum of the first coarse partition
is below every left sum of the second. -/
theorem common_refinement_bracket
    {common first second : List PartitionCell}
    (hvalid : ValidCells common)
    (hfirst : CellRefines common first)
    (hsecond : CellRefines common second) :
    partitionRightSum first ≤ partitionLeftSum second := by
  exact Q'.le_trans' _ _ _ hfirst.right_le
    (Q'.le_trans' _ _ _ hvalid.right_le_left hsecond.left_le)

/-- Semantic common-refinement bracket for two independently constructed
merged partitions.  This is the form needed when unnormalized rational nodes
are represented differently but cellwise equivalent. -/
theorem common_refinement_bracket_of_eqv
    {common₁ common₂ first second : List PartitionCell}
    (hvalid : ValidCells common₂)
    (hfirst : CellRefines common₁ first)
    (hsecond : CellRefines common₂ second)
    (heqv : PartitionEqv common₁ common₂) :
    partitionRightSum first ≤ partitionLeftSum second := by
  exact Q'.le_trans' _ _ _ hfirst.right_le
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv.rightSum)
      (Q'.le_trans' _ _ _ hvalid.right_le_left hsecond.left_le))

/-- Cells cut successively at the listed interior nodes. -/
def cutCells (x : Q') : List Q' → Q' → List PartitionCell
  | [], y => [(x, y)]
  | z :: zs, y => (x, z) :: cutCells z zs y

/-- Constructive certificate that a cut list is nonnegative and ordered from
its left endpoint through its right endpoint. -/
def OrderedCuts : Q' → Q' → List Q' → Prop
  | x, y, [] => (0 : Q') ≤ x ∧ x ≤ y
  | x, y, z :: zs => (0 : Q') ≤ x ∧ x ≤ z ∧ OrderedCuts z y zs

private theorem OrderedCuts.left_le_right {y : Q'} :
    ∀ cuts : List Q', ∀ x : Q', OrderedCuts x y cuts → x ≤ y
  | [], _x, h => h.2
  | z :: zs, _x, h =>
      Q'.le_trans' _ _ _ h.2.1 (OrderedCuts.left_le_right zs z h.2.2)

theorem OrderedCuts.validCells {x y : Q'} {cuts : List Q'}
    (h : OrderedCuts x y cuts) : ValidCells (cutCells x cuts y) := by
  induction cuts generalizing x with
  | nil => exact ValidCells.cons x y [] h.1 h.2 ValidCells.nil
  | cons z zs ih =>
      exact ValidCells.cons x z (cutCells z zs y) h.1 h.2.1 (ih h.2.2)

/-- Every ordered finite cut list is an explicit refinement of its enclosing
single cell. -/
theorem OrderedCuts.refines_single {x y : Q'} {cuts : List Q'}
    (h : OrderedCuts x y cuts) :
    CellRefines (cutCells x cuts y) [(x, y)] := by
  induction cuts generalizing x with
  | nil => exact CellRefines.refl _
  | cons z zs ih =>
      have hrest : OrderedCuts z y zs := h.2.2
      exact CellRefines.trans (CellRefines.cons (x, z) (ih hrest))
        (CellRefines.insert [] [] x z y h.1 h.2.1
          (OrderedCuts.left_le_right zs z hrest))

private theorem q_le_total (a b : Q') : a ≤ b ∨ b ≤ a := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int) ∨
    b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  exact Int.le_total _ _

/-- Insert one rational cut into a semantically ordered cut list.  Equal cuts
are retained; they only create a zero-width cell and therefore require no
normalization or quotient choice. -/
def insertCut (z : Q') : List Q' → List Q'
  | [] => [z]
  | w :: ws => if z ≤ w then z :: w :: ws else w :: insertCut z ws

theorem insertCut_ordered {x y z : Q'} {cuts : List Q'}
    (hcuts : OrderedCuts x y cuts) (hxz : x ≤ z) (hzy : z ≤ y) :
    OrderedCuts x y (insertCut z cuts) := by
  induction cuts generalizing x with
  | nil =>
      change (0 : Q') ≤ x ∧ x ≤ z ∧ ((0 : Q') ≤ z ∧ z ≤ y)
      exact ⟨hcuts.1, hxz,
        Q'.le_trans' _ _ _ hcuts.1 hxz, hzy⟩
  | cons w ws ih =>
      by_cases hzw : z ≤ w
      · simp only [insertCut, if_pos hzw]
        exact ⟨hcuts.1, hxz,
          Q'.le_trans' _ _ _ hcuts.1 hxz, hzw, hcuts.2.2⟩
      · have hwz : w ≤ z := by
          rcases q_le_total z w with h | h
          · exact False.elim (hzw h)
          · exact h
        simp only [insertCut, if_neg hzw]
        exact ⟨hcuts.1, hcuts.2.1,
          ih hcuts.2.2 hwz⟩

/-- Inserting one ordered cut gives a genuine finite-cell refinement. -/
theorem insertCut_refines {x y z : Q'} {cuts : List Q'}
    (hcuts : OrderedCuts x y cuts) (hxz : x ≤ z) (hzy : z ≤ y) :
    CellRefines (cutCells x (insertCut z cuts) y) (cutCells x cuts y) := by
  induction cuts generalizing x with
  | nil =>
      change CellRefines [(x, z), (z, y)] [(x, y)]
      exact CellRefines.insert [] [] x z y hcuts.1 hxz hzy
  | cons w ws ih =>
      by_cases hzw : z ≤ w
      · simp only [insertCut, if_pos hzw, cutCells]
        exact CellRefines.insert [] (cutCells w ws y) x z w
          hcuts.1 hxz hzw
      · have hwz : w ≤ z := by
          rcases q_le_total z w with h | h
          · exact False.elim (hzw h)
          · exact h
        simp only [insertCut, if_neg hzw, cutCells]
        exact CellRefines.cons (x, w) (ih hcuts.2.2 hwz)

/-- Every member of a cut list lies in the enclosing interval. -/
def CutsWithin (x y : Q') : List Q' → Prop
  | [] => True
  | z :: zs => x ≤ z ∧ z ≤ y ∧ CutsWithin x y zs

/-- Insert all cuts of the first list into the second list. -/
def mergeCuts : List Q' → List Q' → List Q'
  | [], base => base
  | z :: zs, base => mergeCuts zs (insertCut z base)

theorem mergeCuts_ordered {x y : Q'} :
    ∀ extra base : List Q',
      CutsWithin x y extra → OrderedCuts x y base →
        OrderedCuts x y (mergeCuts extra base)
  | [], base, _hextra, hbase => hbase
  | z :: zs, base, hextra, hbase => by
      exact mergeCuts_ordered zs (insertCut z base) hextra.2.2
        (insertCut_ordered hbase hextra.1 hextra.2.1)

/-- The merged cut list is an explicit refinement of the base partition. -/
theorem mergeCuts_refines_base {x y : Q'} :
    ∀ extra base : List Q',
      CutsWithin x y extra → OrderedCuts x y base →
        CellRefines (cutCells x (mergeCuts extra base) y)
          (cutCells x base y)
  | [], base, _hextra, _hbase => CellRefines.refl _
  | z :: zs, base, hextra, hbase => by
      have hinsertOrdered := insertCut_ordered hbase hextra.1 hextra.2.1
      exact CellRefines.trans
        (mergeCuts_refines_base zs (insertCut z base) hextra.2.2 hinsertOrdered)
        (insertCut_refines hbase hextra.1 hextra.2.1)

/-- The first insertion-order coherence diamond.  Inserting two cuts into an
empty cut list in either order gives cellwise semantically equivalent
partitions, including the case of distinct unnormalized representations of
the same rational cut. -/
theorem insert_two_empty_partition_eqv (x y z w : Q') :
    PartitionEqv
      (cutCells x (insertCut z (insertCut w [])) y)
      (cutCells x (insertCut w (insertCut z [])) y) := by
  by_cases hzw : z ≤ w
  · by_cases hwz : w ≤ z
    · have heq : z.eqv w := by
        show z.num * (w.den : Int) = w.num * (z.den : Int)
        exact Int.le_antisymm hzw hwz
      simpa only [insertCut, if_pos hzw, if_pos hwz, cutCells] using
        (PartitionEqv.cons (Q'.eqv_refl x) heq
          (PartitionEqv.cons heq heq.symm
            (PartitionEqv.cons heq.symm (Q'.eqv_refl y) PartitionEqv.nil)))
    · simp only [insertCut, if_pos hzw, if_neg hwz]
      exact PartitionEqv.refl _
  · have hwz : w ≤ z := by
      rcases q_le_total z w with h | h
      · exact False.elim (hzw h)
      · exact h
    simp only [insertCut, if_neg hzw, if_pos hwz]
    exact PartitionEqv.refl _

/-- Full adjacent-insertion coherence over an arbitrary already ordered base
list.  This is the braid/diamond step used to permute a finite merge history. -/
theorem insert_two_partition_eqv (y z w : Q') :
    ∀ cuts : List Q', ∀ x : Q',
      PartitionEqv
        (cutCells x (insertCut z (insertCut w cuts)) y)
        (cutCells x (insertCut w (insertCut z cuts)) y)
  | [], x => insert_two_empty_partition_eqv x y z w
  | a :: as, x => by
      by_cases hza : z ≤ a
      · by_cases hwa : w ≤ a
        · by_cases hzw : z ≤ w
          · by_cases hwz : w ≤ z
            · have heq : z.eqv w := by
                show z.num * (w.den : Int) = w.num * (z.den : Int)
                exact Int.le_antisymm hzw hwz
              simp only [insertCut, if_pos hza, if_pos hwa,
                if_pos hzw, if_pos hwz, cutCells]
              exact PartitionEqv.cons (Q'.eqv_refl x) heq
                (PartitionEqv.cons heq heq.symm
                  (PartitionEqv.cons heq.symm (Q'.eqv_refl a)
                    (PartitionEqv.refl (cutCells a as y))))
            · simp only [insertCut, if_pos hza, if_pos hwa,
                if_pos hzw, if_neg hwz]
              exact PartitionEqv.refl _
          · have hwz : w ≤ z := by
              rcases q_le_total z w with h | h
              · exact False.elim (hzw h)
              · exact h
            simp only [insertCut, if_pos hza, if_pos hwa,
              if_neg hzw, if_pos hwz]
            exact PartitionEqv.refl _
        · have hn_wz : ¬ w ≤ z := by
            intro hwz
            exact hwa (Q'.le_trans' _ _ _ hwz hza)
          simp only [insertCut, if_neg hwa, if_pos hza, if_neg hn_wz]
          exact PartitionEqv.refl _
      · by_cases hwa : w ≤ a
        · have hn_zw : ¬ z ≤ w := by
            intro hzw
            exact hza (Q'.le_trans' _ _ _ hzw hwa)
          simp only [insertCut, if_pos hwa, if_neg hza, if_neg hn_zw]
          exact PartitionEqv.refl _
        · simp only [insertCut, if_neg hwa, if_neg hza, cutCells]
          exact PartitionEqv.cons (Q'.eqv_refl x) (Q'.eqv_refl a)
            (insert_two_partition_eqv y z w as a)

/-! ## Order-independent finite merge

The local partition diamond above is now lifted to arbitrary finite insertion
histories.  We keep semantic equality at the `Q'` level: two unreduced
rational representatives of the same cut are never identified by structure.
-/

/-- Pointwise semantic equality of rational cut lists. -/
inductive CutListEqv : List Q' → List Q' → Prop
  | nil : CutListEqv [] []
  | cons {x x' : Q'} {xs xs' : List Q'}
      (hx : x.eqv x') (hrest : CutListEqv xs xs') :
      CutListEqv (x :: xs) (x' :: xs')

theorem CutListEqv.refl : ∀ cuts : List Q', CutListEqv cuts cuts
  | [] => CutListEqv.nil
  | x :: xs => CutListEqv.cons (Q'.eqv_refl x) (CutListEqv.refl xs)

theorem CutListEqv.symm {cuts cuts' : List Q'}
    (h : CutListEqv cuts cuts') : CutListEqv cuts' cuts := by
  induction h with
  | nil => exact CutListEqv.nil
  | cons hx hrest ih => exact CutListEqv.cons hx.symm ih

theorem CutListEqv.trans {cuts₁ cuts₂ cuts₃ : List Q'}
    (h₁ : CutListEqv cuts₁ cuts₂) (h₂ : CutListEqv cuts₂ cuts₃) :
    CutListEqv cuts₁ cuts₃ := by
  induction h₁ generalizing cuts₃ with
  | nil =>
      cases h₂
      exact CutListEqv.nil
  | cons hab hrest ih =>
      cases h₂ with
      | cons hbc hrest₂ =>
          exact CutListEqv.cons (Q'.eqv_trans _ _ _ hab hbc)
            (ih hrest₂)

private theorem le_transport_eqv {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') (hab : a ≤ b) : a' ≤ b' :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv ha)
    (Q'.le_trans' _ _ _ hab (Q'.le_of_eqv hb))

/-- Orderedness transports across semantic changes of the two enclosing
endpoints; interior rational representatives are untouched. -/
theorem OrderedCuts.congr_endpoints {x x' y y' : Q'} {cuts : List Q'}
    (hcuts : OrderedCuts x y cuts) (hx : x.eqv x') (hy : y.eqv y') :
    OrderedCuts x' y' cuts := by
  induction cuts generalizing x x' with
  | nil =>
      exact ⟨le_transport_eqv (Q'.eqv_refl 0) hx hcuts.1,
        le_transport_eqv hx hy hcuts.2⟩
  | cons z zs ih =>
      exact ⟨le_transport_eqv (Q'.eqv_refl 0) hx hcuts.1,
        le_transport_eqv hx (Q'.eqv_refl z) hcuts.2.1,
        ih hcuts.2.2 (Q'.eqv_refl z)⟩

/-- Concatenate an ordered `[x,r]` mesh with an ordered `[r',y]` mesh when
the two join representatives are semantically equal. -/
theorem OrderedCuts.append_join {x r r' y : Q'} {second : List Q'} :
    ∀ first : List Q', OrderedCuts x r first → OrderedCuts r' y second →
      r.eqv r' → OrderedCuts x y (first ++ r' :: second)
  | [], hfirst, hsecond, hjoin =>
      ⟨hfirst.1,
        le_transport_eqv (Q'.eqv_refl x) hjoin hfirst.2,
        hsecond⟩
  | _z :: zs, hfirst, hsecond, hjoin =>
      ⟨hfirst.1, hfirst.2.1,
        OrderedCuts.append_join zs hfirst.2.2 hsecond hjoin⟩

/-- Cutting at a join node turns cut-list concatenation into cell-list
concatenation exactly. -/
theorem cutCells_append_join (r y : Q') (second : List Q') :
    ∀ first : List Q', ∀ x : Q',
      cutCells x (first ++ r :: second) y =
        cutCells x first r ++ cutCells r second y
  | [], _x => rfl
  | z :: zs, x => by
      change (x, z) :: cutCells z (zs ++ r :: second) y =
        (x, z) :: (cutCells z zs r ++ cutCells r second y)
      rw [cutCells_append_join r y second zs z]

theorem partitionLeftSum_append : ∀ first second : List PartitionCell,
    (partitionLeftSum (first ++ second)).eqv
      (partitionLeftSum first + partitionLeftSum second)
  | [], second => by
      change (partitionLeftSum second).eqv ((0 : Q') + partitionLeftSum second)
      rw [Q'.zero_add']
      exact Q'.eqv_refl _
  | c :: cs, second => by
      change (partitionLeftRect c.1 c.2 +
          partitionLeftSum (cs ++ second)).eqv
        ((partitionLeftRect c.1 c.2 + partitionLeftSum cs) +
          partitionLeftSum second)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (partitionLeftSum_append cs second))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv (partitionLeftRect c.1 c.2)
            (partitionLeftSum cs) (partitionLeftSum second)))

theorem partitionRightSum_append : ∀ first second : List PartitionCell,
    (partitionRightSum (first ++ second)).eqv
      (partitionRightSum first + partitionRightSum second)
  | [], second => by
      change (partitionRightSum second).eqv ((0 : Q') + partitionRightSum second)
      rw [Q'.zero_add']
      exact Q'.eqv_refl _
  | c :: cs, second => by
      change (partitionRightRect c.1 c.2 +
          partitionRightSum (cs ++ second)).eqv
        ((partitionRightRect c.1 c.2 + partitionRightSum cs) +
          partitionRightSum second)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (partitionRightSum_append cs second))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv (partitionRightRect c.1 c.2)
            (partitionRightSum cs) (partitionRightSum second)))

theorem partitionLeftSum_join_eqv (x r y : Q')
    (first second : List Q') :
    (partitionLeftSum (cutCells x (first ++ r :: second) y)).eqv
      (partitionLeftSum (cutCells x first r) +
        partitionLeftSum (cutCells r second y)) := by
  rw [cutCells_append_join r y second first x]
  exact partitionLeftSum_append _ _

theorem partitionRightSum_join_eqv (x r y : Q')
    (first second : List Q') :
    (partitionRightSum (cutCells x (first ++ r :: second) y)).eqv
      (partitionRightSum (cutCells x first r) +
        partitionRightSum (cutCells r second y)) := by
  rw [cutCells_append_join r y second first x]
  exact partitionRightSum_append _ _

/-- Insertion respects semantic equality of both the inserted cut and the
already constructed cut list. -/
theorem insertCut_eqv_congr {z z' : Q'} (hz : z.eqv z') :
    ∀ {cuts cuts' : List Q'}, CutListEqv cuts cuts' →
      CutListEqv (insertCut z cuts) (insertCut z' cuts')
  | [], [], CutListEqv.nil =>
      CutListEqv.cons hz CutListEqv.nil
  | w :: ws, w' :: ws', CutListEqv.cons hw hrest => by
      by_cases hzw : z ≤ w
      · have hz'w' : z' ≤ w' := le_transport_eqv hz hw hzw
        simp only [insertCut, if_pos hzw, if_pos hz'w']
        exact CutListEqv.cons hz (CutListEqv.cons hw hrest)
      · have hn_z'w' : ¬ z' ≤ w' := by
          intro hz'w'
          exact hzw (le_transport_eqv hz.symm hw.symm hz'w')
        simp only [insertCut, if_neg hzw, if_neg hn_z'w']
        exact CutListEqv.cons hw (insertCut_eqv_congr hz hrest)

/-- The adjacent insertion braid at cut-list level. -/
theorem insert_two_cutListEqv (z w : Q') :
    ∀ cuts : List Q',
      CutListEqv
        (insertCut z (insertCut w cuts))
        (insertCut w (insertCut z cuts))
  | [] => by
      by_cases hzw : z ≤ w
      · by_cases hwz : w ≤ z
        · have heq : z.eqv w := by
            show z.num * (w.den : Int) = w.num * (z.den : Int)
            exact Int.le_antisymm hzw hwz
          simp only [insertCut, if_pos hzw, if_pos hwz]
          exact CutListEqv.cons heq
            (CutListEqv.cons heq.symm CutListEqv.nil)
        · simp only [insertCut, if_pos hzw, if_neg hwz]
          exact CutListEqv.refl _
      · have hwz : w ≤ z := by
          rcases q_le_total z w with h | h
          · exact False.elim (hzw h)
          · exact h
        simp only [insertCut, if_neg hzw, if_pos hwz]
        exact CutListEqv.refl _
  | a :: as => by
      by_cases hza : z ≤ a
      · by_cases hwa : w ≤ a
        · by_cases hzw : z ≤ w
          · by_cases hwz : w ≤ z
            · have heq : z.eqv w := by
                show z.num * (w.den : Int) = w.num * (z.den : Int)
                exact Int.le_antisymm hzw hwz
              simp only [insertCut, if_pos hza, if_pos hwa,
                if_pos hzw, if_pos hwz]
              exact CutListEqv.cons heq
                (CutListEqv.cons heq.symm (CutListEqv.refl _))
            · simp only [insertCut, if_pos hza, if_pos hwa,
                if_pos hzw, if_neg hwz]
              exact CutListEqv.refl _
          · have hwz : w ≤ z := by
              rcases q_le_total z w with h | h
              · exact False.elim (hzw h)
              · exact h
            simp only [insertCut, if_pos hza, if_pos hwa,
              if_neg hzw, if_pos hwz]
            exact CutListEqv.refl _
        · have hn_wz : ¬ w ≤ z := by
            intro hwz
            exact hwa (Q'.le_trans' _ _ _ hwz hza)
          simp only [insertCut, if_neg hwa, if_pos hza, if_neg hn_wz]
          exact CutListEqv.refl _
      · by_cases hwa : w ≤ a
        · have hn_zw : ¬ z ≤ w := by
            intro hzw
            exact hza (Q'.le_trans' _ _ _ hzw hwa)
          simp only [insertCut, if_pos hwa, if_neg hza, if_neg hn_zw]
          exact CutListEqv.refl _
        · simp only [insertCut, if_neg hwa, if_neg hza]
          exact CutListEqv.cons (Q'.eqv_refl a)
            (insert_two_cutListEqv z w as)

/-- Applying the same remaining insertion history to semantically equal base
lists preserves their equality. -/
theorem mergeCuts_eqv_base (extra : List Q') {base base' : List Q'}
    (hbase : CutListEqv base base') :
    CutListEqv (mergeCuts extra base) (mergeCuts extra base') := by
  induction extra generalizing base base' with
  | nil => exact hbase
  | cons z zs ih =>
      exact ih (insertCut_eqv_congr (Q'.eqv_refl z) hbase)

/-- Finite insertion histories depend only on their permutation, up to
semantic equality of unreduced rational cuts. -/
theorem mergeCuts_perm_eqv (base : List Q') :
    ∀ {first second : List Q'}, first.Perm second →
      CutListEqv (mergeCuts first base) (mergeCuts second base)
  | _, _, List.Perm.nil => CutListEqv.refl _
  | _, _, List.Perm.cons _ h =>
      mergeCuts_perm_eqv (insertCut _ base) h
  | _, _, List.Perm.swap a b rest =>
      mergeCuts_eqv_base rest (insert_two_cutListEqv a b base)
  | _, _, List.Perm.trans h₁ h₂ =>
      CutListEqv.trans (mergeCuts_perm_eqv base h₁)
        (mergeCuts_perm_eqv base h₂)

theorem mergeCuts_append (first second base : List Q') :
    mergeCuts (first ++ second) base =
      mergeCuts second (mergeCuts first base) := by
  induction first generalizing base with
  | nil => rfl
  | cons z zs ih => exact ih (insertCut z base)

/-- Right-to-left insertion sort, used only to expose the canonical replay of
an already ordered cut list. -/
def sortCuts : List Q' → List Q'
  | [] => []
  | z :: zs => insertCut z (sortCuts zs)

theorem mergeCuts_reverse_eq_sortCuts : ∀ cuts : List Q',
    mergeCuts cuts.reverse [] = sortCuts cuts
  | [] => rfl
  | z :: zs => by
      rw [List.reverse_cons, sortCuts]
      rw [mergeCuts_append, mergeCuts_reverse_eq_sortCuts zs]
      rfl

theorem sortCuts_eq_of_ordered {x y : Q'} :
    ∀ cuts : List Q', OrderedCuts x y cuts → sortCuts cuts = cuts
  | [], _h => rfl
  | z :: zs, h => by
      have hrest : OrderedCuts z y zs := h.2.2
      rw [sortCuts, sortCuts_eq_of_ordered zs hrest]
      cases zs with
      | nil => rfl
      | cons w ws =>
          simp only [insertCut, if_pos hrest.2.1]

private theorem list_perm_refl : ∀ xs : List Q', xs.Perm xs
  | [] => List.Perm.nil
  | x :: xs => List.Perm.cons x (list_perm_refl xs)

private theorem list_perm_reverse : ∀ xs : List Q', xs.Perm xs.reverse
  | [] => List.Perm.nil
  | x :: xs => by
      rw [List.reverse_cons]
      have hmove : (x :: xs.reverse).Perm (xs.reverse ++ [x]) := by
        simpa only [List.append_nil] using
          (List.perm_middle (l₁ := xs.reverse) (a := x) (l₂ := [])).symm
      exact List.Perm.trans
        (List.Perm.cons x (list_perm_reverse xs))
        hmove

/-- Replaying an already ordered list from the empty history recovers it
semantically.  Equal unreduced cuts may be reordered, but not normalized. -/
theorem mergeCuts_replay_ordered {x y : Q'} {cuts : List Q'}
    (hcuts : OrderedCuts x y cuts) :
    CutListEqv (mergeCuts cuts []) cuts := by
  have hperm := mergeCuts_perm_eqv ([] : List Q') (list_perm_reverse cuts)
  rw [mergeCuts_reverse_eq_sortCuts,
    sortCuts_eq_of_ordered cuts hcuts] at hperm
  exact hperm

/-- Pointwise cut equality induces cellwise partition equality. -/
theorem cutCells_eqv_congr {x x' y y' : Q'} {cuts cuts' : List Q'}
    (hx : x.eqv x') (hy : y.eqv y') (hcuts : CutListEqv cuts cuts') :
    PartitionEqv (cutCells x cuts y) (cutCells x' cuts' y') := by
  induction hcuts generalizing x x' with
  | nil => exact PartitionEqv.cons hx hy PartitionEqv.nil
  | cons hz hrest ih =>
      exact PartitionEqv.cons hx hz (ih hz)

/-- A merged base can be represented as the single concatenated insertion
history, up to semantic cut equality. -/
theorem mergeCuts_history_eqv {x y : Q'} (extra : List Q')
    {base : List Q'} (hbase : OrderedCuts x y base) :
    CutListEqv (mergeCuts extra base)
      (mergeCuts (base ++ extra) []) := by
  rw [mergeCuts_append]
  exact (mergeCuts_eqv_base extra (mergeCuts_replay_ordered hbase)).symm

private theorem list_perm_append_comm :
    ∀ first second : List Q', (first ++ second).Perm (second ++ first)
  | [], second => by
      simpa only [List.nil_append, List.append_nil] using list_perm_refl second
  | x :: xs, second => by
      exact List.Perm.trans
        (List.Perm.cons x (list_perm_append_comm xs second))
        (List.perm_middle (l₁ := second) (a := x) (l₂ := xs)).symm

/-- Merging two ordered cut lists is commutative up to pointwise semantic
equality, including arbitrary unreduced representatives. -/
theorem mergeCuts_comm_eqv {x y : Q'} {first second : List Q'}
    (hfirst : OrderedCuts x y first) (hsecond : OrderedCuts x y second) :
    CutListEqv (mergeCuts first second) (mergeCuts second first) := by
  exact CutListEqv.trans (mergeCuts_history_eqv first hsecond)
    (CutListEqv.trans
      (mergeCuts_perm_eqv ([] : List Q')
        (list_perm_append_comm second first))
      (mergeCuts_history_eqv second hfirst).symm)

private theorem CutsWithin.weaken_left {x z y : Q'} (hxz : x ≤ z) :
    ∀ cuts : List Q', CutsWithin z y cuts → CutsWithin x y cuts
  | [], _h => trivial
  | _w :: ws, h =>
      ⟨Q'.le_trans' _ _ _ hxz h.1, h.2.1,
        CutsWithin.weaken_left hxz ws h.2.2⟩

theorem OrderedCuts.cutsWithin {x y : Q'} {cuts : List Q'}
    (h : OrderedCuts x y cuts) : CutsWithin x y cuts := by
  induction cuts generalizing x with
  | nil => trivial
  | cons z zs ih =>
      have hrest : OrderedCuts z y zs := h.2.2
      exact ⟨h.2.1, OrderedCuts.left_le_right zs z hrest,
        CutsWithin.weaken_left h.2.1 zs (ih hrest)⟩

/-- Fully constructive common-refinement bracket for any two ordered rational
meshes on the same nonnegative interval. -/
theorem ordered_partitions_common_bracket {x y : Q'}
    {first second : List Q'}
    (hfirst : OrderedCuts x y first) (hsecond : OrderedCuts x y second) :
    partitionRightSum (cutCells x first y) ≤
      partitionLeftSum (cutCells x second y) := by
  have hfirstWithin := hfirst.cutsWithin
  have hsecondWithin := hsecond.cutsWithin
  have hcommonOrdered :=
    mergeCuts_ordered first second hfirstWithin hsecond
  have hrefFirst :=
    mergeCuts_refines_base second first hsecondWithin hfirst
  have hrefSecond :=
    mergeCuts_refines_base first second hfirstWithin hsecond
  have heqv : PartitionEqv
      (cutCells x (mergeCuts second first) y)
      (cutCells x (mergeCuts first second) y) :=
    cutCells_eqv_congr (Q'.eqv_refl x) (Q'.eqv_refl y)
      (mergeCuts_comm_eqv hsecond hfirst)
  exact common_refinement_bracket_of_eqv
    hcommonOrdered.validCells hrefFirst hrefSecond heqv

/-- Common-refinement bracket when the two enclosing endpoints use distinct
but semantically equal rational representatives. -/
theorem ordered_partitions_common_bracket_of_endpoints
    {x x' y y' : Q'} {first second : List Q'}
    (hfirst : OrderedCuts x y first) (hsecond : OrderedCuts x' y' second)
    (hx : x.eqv x') (hy : y.eqv y') :
    partitionRightSum (cutCells x first y) ≤
      partitionLeftSum (cutCells x' second y') := by
  have hfirst' : OrderedCuts x' y' first :=
    hfirst.congr_endpoints hx hy
  have heqv : PartitionEqv (cutCells x first y) (cutCells x' first y') :=
    cutCells_eqv_congr hx hy (CutListEqv.refl first)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv.rightSum)
    (ordered_partitions_common_bracket hfirst' hsecond)

end YMGap.Continuum.SemicircleAtanPartitionInsertion

#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.split_left_le_coarse
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.coarse_right_le_split
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.right_le_left
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.refine_cell_left
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.refine_cell_right
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.CellRefines.left_le
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.CellRefines.right_le
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.common_refinement_bracket
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.common_refinement_bracket_of_eqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.PartitionEqv.leftSum
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.PartitionEqv.rightSum
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.OrderedCuts.refines_single
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.insertCut_ordered
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.insertCut_refines
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.mergeCuts_ordered
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.mergeCuts_refines_base
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.insert_two_empty_partition_eqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.insert_two_partition_eqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.insert_two_cutListEqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.mergeCuts_perm_eqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.mergeCuts_comm_eqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.ordered_partitions_common_bracket
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.OrderedCuts.append_join
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.partitionLeftSum_join_eqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.partitionRightSum_join_eqv
#print axioms YMGap.Continuum.SemicircleAtanPartitionInsertion.ordered_partitions_common_bracket_of_endpoints
