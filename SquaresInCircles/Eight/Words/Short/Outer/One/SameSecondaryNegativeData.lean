module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameDiagonal
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryData

/-!
# Eight squares: the actual negative-half same-sign secondary contact

Both the target and angle motions increase the original source contact
coordinate. The source and target labels retain their literal reflected
coefficients throughout the motions.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)
open SecondWord (U W)

def contact (B x : ℝ) : ℝ :=
  1/2+(1/2-arc B)*Real.cos x+(1/2+B)*Real.sin x
def speed (B x : ℝ) : ℝ :=
  (arc B-1/2)*Real.sin x+(B+1/2)*Real.cos x
def K (B x : ℝ) : ℝ := ratio B*Real.cos x+Real.sin x
def Domain (B x : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ contact B x∈Icc 0 outerDiagonal
def cost (r : Row) (B x : ℝ) : ℝ :=
  Real.pi/2-x+c r+target r (contact B x)+targetCost r B
def first (r : Row) (B x : ℝ) : ℝ := -1+slope r (contact B x)*speed B x
def targetFirst (r : Row) (B x : ℝ) : ℝ := slope r (contact B x)*K B x-targetSlope r B

lemma contact_angle_hasDerivAt (B x : ℝ) : HasDerivAt (contact B) (speed B x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul (1/2-arc B)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (1/2+B))
  convert h using 1
  · funext y; simp only [contact,Pi.add_apply]
  · simp only [speed]; ring

lemma speed_hasDerivAt (B x : ℝ) : HasDerivAt (speed B) (1/2-contact B x) x := by
  have h := ((Real.hasDerivAt_sin x).const_mul (arc B-1/2)).add
    ((Real.hasDerivAt_cos x).const_mul (B+1/2))
  convert h using 1
  · funext y; simp only [speed,Pi.add_apply]
  · simp only [contact]; ring

lemma contact_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun B => contact B x) (K B x) B := by
  have h := ((((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_sub (1/2)).mul_const
    (Real.cos x)).const_add (1/2)).add
      (((hasDerivAt_id B).const_add (1/2)).mul_const (Real.sin x))
  convert h using 1
  · funext y; simp only [contact,Pi.add_apply,id_eq]
  · simp only [K]; ring

lemma K_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) : 0<K B x := by
  have ht := positive_trig hx
  have hp := mul_pos (SameContact.ratio_pos (SameContact.outer_domain hB))
    (show 0<Real.cos x by linarith [ht.1])
  dsimp [K]
  linarith [ht.2.2.1]

lemma contact_target_monotone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun B => contact B x) (Icc 0 outerDiagonal) := monoOn_of_hasDeriv_nonneg
  (fun B hB => (contact_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
  (fun B hB => contact_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
  (fun B hB => (K_positive (Ioo_subset_Icc_self hB) hx).le)

lemma speed_positive {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 (7/10)) :
    0<speed B x := by
  have ht := positive_trig hx
  have hA := (outer_bounds (SameContact.arc_state hB)).1
  have h1 := mul_nonneg (show 0≤arc B-1/2 by linarith [outer_endpoint_bounds.2.2.1]) ht.2.2.1
  have h2 := mul_pos (show 0<B+1/2 by linarith [hB.1])
    (show 0<Real.cos x by linarith [ht.1])
  dsimp [speed]
  linarith

lemma contact_angle_monotone {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    MonotoneOn (contact B) (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun x _ => (contact_angle_hasDerivAt B x).continuousAt.continuousWithinAt)
  (fun x _ => contact_angle_hasDerivAt B x)
  (fun x hx => (speed_positive hB (Ioo_subset_Icc_self hx)).le)

lemma cost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (cost r B) (first r B x) x := by
  have h := ((((hasDerivAt_id x).neg).const_add (Real.pi/2+c r)).add
    ((Secondary.source_hasDerivAt r hd.2.2).comp x (contact_angle_hasDerivAt B x))).add_const
      (targetCost r B)
  convert h using 1
  · funext y; simp only [cost,Pi.add_apply,Pi.neg_apply,Function.comp_apply,id_eq]; ring
  · simp only [first]

lemma cost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => cost r B x) (targetFirst r B x) B := by
  have h := (((Secondary.source_hasDerivAt r hd.2.2).comp B
    (contact_target_hasDerivAt hd.1 x)).const_add (Real.pi/2-x+c r)).add
      (targetCost_hasDerivAt r hd.1)
  convert h using 1
  · funext y; simp only [cost,Pi.add_apply,Function.comp_apply]
  · simp only [targetFirst]; ring

lemma diagonal_contact (x : ℝ) : contact outerDiagonal x=Diagonal.joinContact x := by
  rw [contact,SameContact.arc_diagonal,Diagonal.joinContact]
  ring

lemma diagonal_contact_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<contact outerDiagonal x := by
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩
  have hm := contact_angle_monotone hdiag (show (0:ℝ)∈Icc 0 (7/10) by norm_num) hx hx.1
  norm_num [contact,SameContact.arc_diagonal] at hm
  rw [contact,SameContact.arc_diagonal]
  linarith [outer_endpoint_bounds.2.2.2]

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative
