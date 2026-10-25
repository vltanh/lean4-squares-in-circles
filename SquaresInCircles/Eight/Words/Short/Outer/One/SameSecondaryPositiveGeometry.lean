module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePositiveGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryData

/-!
# Eight squares: the initial same-sign secondary contact strip

The independent arc bound confines a possible low value to this one
strip. The original contact has only the zero-source and diagonal-target
coordinate boundaries. Its stationary angular derivative is positive
throughout the strip.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio)
open SecondWord (U W)

def strip : ℝ := 27/250
def contact (B x : ℝ) : ℝ :=
  1/2+(1/2-arc B)*Real.cos x+(1/2-B)*Real.sin x
def D (B x : ℝ) : ℝ := W B*Real.cos x-U B*Real.sin x
def K (B x : ℝ) : ℝ := ratio B*Real.cos x-Real.sin x
def contactAngle (B x : ℝ) : ℝ := Real.cos x-Real.sin x-D B x
def Domain (B x : ℝ) : Prop := B∈Icc 0 outerDiagonal ∧ x∈Icc 0 strip ∧ 0≤contact B x
def cost (r : Row) (B x : ℝ) : ℝ :=
  Real.pi/2+x+c r+target r (contact B x)+targetCost r B
def first (r : Row) (B x : ℝ) : ℝ := 1+slope r (contact B x)*contactAngle B x
def targetFirst (r : Row) (B x : ℝ) : ℝ := slope r (contact B x)*K B x-targetSlope r B
def transport (r : Row) (B x : ℝ) : ℝ :=
  1-H r B*(1-(Real.cos x-Real.sin x)/D B x)

lemma angle_full {x : ℝ} (hx : x∈Icc 0 strip) : x∈Icc 0 (7/10) :=
  ⟨hx.1,by dsimp [strip] at hx; linarith [hx.2]⟩

lemma strip_trig {x : ℝ} (hx : x∈Icc 0 strip) :
    (497/500:ℝ)<Real.cos x ∧ 0≤Real.sin x ∧ Real.sin x≤27/250 ∧
      (177/200:ℝ)<Real.cos x-Real.sin x := by
  have hc := Same.Positive.near_cos hx
  have ht := positive_trig (angle_full hx)
  have hs : Real.sin x≤27/250 := ht.2.2.2.2.1.trans hx.2
  exact ⟨hc,ht.2.2.1,hs,by linarith⟩

lemma D_bounds {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 strip) :
    (29/100:ℝ)<D B x ∧ D B x<(7/5:ℝ) := by
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have hs := outer_bounds (SameContact.arc_state hB)
  have hU : 0≤U B ∧ U B<(383/200:ℝ) := by
    dsimp [U]
    constructor <;> linarith [hs.1,hs.2.1,ShortOuterZero.fine_axial_bounds.2,outer_endpoint_bounds.2.2.1]
  have hV : (1/2:ℝ)≤W B ∧ W B<(7/5:ℝ) := by
    dsimp [W]
    constructor <;> linarith [hB.1,hB.2,outer_endpoint_bounds.2.2.2]
  have hlo := mul_le_mul hV.1 ht.1.le (by norm_num) (by linarith : 0≤W B)
  have hsub := mul_le_mul hU.2.le ht.2.2.1 ht.2.1 (by norm_num)
  have hupper := mul_le_mul_of_nonneg_left hf.2.1 (by linarith : 0≤W B)
  have hnonneg := mul_nonneg hU.1 ht.2.1
  dsimp [D]
  constructor <;> nlinarith

lemma K_identity {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) : U B*K B x=D B x := by
  have hU : arc B+1/2≠0 := (SecondWord.U_positive (SecondWord.outer_domain hB)).ne'
  have h1 : (arc B+1/2)*((B+1/2)/(arc B+1/2))=B+1/2 := mul_div_cancel₀ _ hU
  simp only [K,D,ratio,U,W]
  linear_combination Real.cos x*h1

lemma H_identity {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (r : Row) :
    targetSlope r B*U B=H r B := by
  have hU : arc B+1/2≠0 := (SecondWord.U_positive (SecondWord.outer_domain hB)).ne'
  have h1 : (arc B+1/2)*((B+1/2)/(arc B+1/2))=B+1/2 := mul_div_cancel₀ _ hU
  simp only [targetSlope,H,ratio,U,W]
  linear_combination p r*h1

lemma contact_target_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun B => contact B x) (K B x) B := by
  have h := ((((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_sub (1/2)).mul_const
    (Real.cos x)).const_add (1/2)).add
      (((hasDerivAt_id B).const_sub (1/2)).mul_const (Real.sin x))
  convert h using 1
  · funext y; simp only [contact,Pi.add_apply,id_eq]
  · simp only [K]; ring

lemma contact_target_monotone {x : ℝ} (hx : x∈Icc 0 strip) :
    MonotoneOn (fun B => contact B x) (Icc 0 outerDiagonal) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro B hB
    exact (contact_target_hasDerivAt hB x).continuousAt.continuousWithinAt
  · intro B hB
    exact contact_target_hasDerivAt (Ioo_subset_Icc_self hB) x
  · intro B hB
    have hBi := Ioo_subset_Icc_self hB
    have hh := K_identity (x := x) hBi
    have hU := SecondWord.U_positive (SecondWord.outer_domain hBi)
    have hD := (D_bounds hBi hx).1
    nlinarith

lemma contact_zero_target {x : ℝ} (hx : x∈Icc 0 strip) : contact 0 x<0 := by
  have ht := strip_trig hx
  have ha := ShortOuterZero.fine_axial_bounds
  have hp := mul_le_mul
    (show (914575671/1000000000:ℝ)≤outerAxial-1/2 by linarith [ha.1])
    ht.1.le (by norm_num) (by linarith [ha.1] : 0≤outerAxial-1/2)
  norm_num [contact,SameContact.arc_zero]
  nlinarith [ht.2.2.1]

lemma contact_target_diagonal {x : ℝ} (hx : x∈Icc 0 strip) :
    0<contact outerDiagonal x ∧ contact outerDiagonal x<outerDiagonal := by
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have hsum : 1≤Real.cos x+Real.sin x ∧ Real.cos x+Real.sin x≤277/250 :=
    ⟨by linarith [hf.2.2.2.2.2],by linarith [hf.2.1,ht.2.2.1]⟩
  have hupper := mul_le_mul (show outerDiagonal-1/2≤(2/5:ℝ) by linarith [outer_endpoint_bounds.2.2.2])
    hsum.2 (by linarith [hsum.1]) (by norm_num)
  have hlower := mul_le_mul_of_nonneg_left hsum.1
    (show 0≤outerDiagonal-1/2 by linarith [outer_endpoint_bounds.2.2.1])
  rw [contact,SameContact.arc_diagonal]
  constructor <;> nlinarith [outer_endpoint_bounds.2.2.1]

lemma source_mem {B x : ℝ} (hd : Domain B x) : contact B x∈Icc 0 outerDiagonal := by
  have hm := contact_target_monotone hd.2.1 hd.1
    (show outerDiagonal∈Icc 0 outerDiagonal from ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩) hd.1.2
  exact ⟨hd.2.2,hm.trans (contact_target_diagonal hd.2.1).2.le⟩

lemma target_positive {B x : ℝ} (hd : Domain B x) : 0<B := by
  by_contra! hbad
  have he : B=0 := le_antisymm hbad hd.1.1
  subst B
  linarith [contact_zero_target hd.2.1,hd.2.2]

lemma contact_angle_hasDerivAt (B x : ℝ) :
    HasDerivAt (contact B) (contactAngle B x) x := by
  have h := (((Real.hasDerivAt_cos x).const_mul (1/2-arc B)).const_add (1/2)).add
    ((Real.hasDerivAt_sin x).const_mul (1/2-B))
  convert h using 1
  · funext y; simp only [contact,Pi.add_apply]
  · simp only [contactAngle,D,U,W]; ring

lemma cost_angle_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (cost r B) (first r B x) x := by
  have h := (((hasDerivAt_id x).const_add (Real.pi/2+c r)).add
    ((Secondary.source_hasDerivAt r (source_mem hd)).comp x
      (contact_angle_hasDerivAt B x))).add_const (targetCost r B)
  convert h using 1
  · funext y; simp only [cost,Pi.add_apply,Function.comp_apply,id_eq]; ring
  · simp only [first]

lemma cost_target_hasDerivAt (r : Row) {B x : ℝ} (hd : Domain B x) :
    HasDerivAt (fun B => cost r B x) (targetFirst r B x) B := by
  have h := (((Secondary.source_hasDerivAt r (source_mem hd)).comp B
    (contact_target_hasDerivAt hd.1 x)).const_add (Real.pi/2+x+c r)).add
      (targetCost_hasDerivAt r hd.1)
  convert h using 1
  · funext y; simp only [cost,Pi.add_apply,Function.comp_apply]
  · simp only [targetFirst]; ring

lemma first_continuousAt (r : Row) {B x : ℝ} (hd : Domain B x) : ContinuousAt (first r B) x := by
  have hs := (slope_hasDerivAt r (source_mem hd)).continuousAt.comp (x := x)
    (contact_angle_hasDerivAt B x).continuousAt
  have ha : ContinuousAt (contactAngle B) x := by
    have : contactAngle B=fun y => Real.cos y-Real.sin y-(W B*Real.cos y-U B*Real.sin y) := rfl
    rw [this]; fun_prop
  exact continuousAt_const.add (hs.mul ha)

lemma transport_lower (r : Row) {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) (hx : x∈Icc 0 strip) :
    (33/100:ℝ)<transport r B x := by
  have hD := D_bounds hB hx
  have hH := H_upper r hB
  have hHpos := H_positive r hB
  have htr := (strip_trig hx).2.2.2
  have hDpos : 0<D B x := by linarith [hD.1]
  have he : transport r B x*D B x=D B x-H r B*(D B x-(Real.cos x-Real.sin x)) := by
    simp only [transport]
    field_simp
  refine lt_of_mul_lt_mul_right ?_ hDpos.le
  rw [he]
  by_cases hdelta : D B x-(Real.cos x-Real.sin x)≤0
  · have hh := mul_nonpos_of_nonneg_of_nonpos hHpos.le hdelta
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hH.le (le_of_not_ge hdelta)
    nlinarith

lemma stationary_first (r : Row) {B x : ℝ} (hd : Domain B x)
    (hstat : targetFirst r B x=0) : first r B x=transport r B x := by
  have hU := SecondWord.U_positive (SecondWord.outer_domain hd.1)
  have hD := (D_bounds hd.1 hd.2.1).1
  have hK := K_identity (x := x) hd.1
  have hH := H_identity hd.1 r
  have hs : slope r (contact B x)*D B x=H r B := by
    dsimp [targetFirst] at hstat
    linear_combination -slope r (contact B x)*hK+U B*hstat+hH
  dsimp [first,contactAngle,transport]
  field_simp [show D B x≠0 by linarith]
  linear_combination (Real.cos x-Real.sin x-D B x)*hs

lemma initial_lower (r : Row) {B : ℝ} (hd : Domain B 0) :
    (8981/10000:ℝ)<cost r B 0 := by
  have hs := SameContact.arc_state (source_mem hd)
  have ht := SameContact.arc_state hd.1
  have he : contact B 0+arc B=1 := by norm_num [contact]; ring
  have hh := Secondary.aligned_original r hs ht he.ge
  have hc := original_cost r hs ht
  dsimp [cost]
  nlinarith only [hh,hc]

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive
