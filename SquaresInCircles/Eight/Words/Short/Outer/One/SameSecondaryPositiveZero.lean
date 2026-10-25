module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryDiagonalData
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePositiveGeometry

/-!
# Eight squares: the moving zero-source boundary of the secondary strip

The original target circle supplies an explicit rotating coordinate.
Its derivative is precisely the same positive transport derivative as
an interior stationary target.
-/

section
/-!
## Literal reflection and source slopes for the same-sign secondary owners

Reflection exchanges the two already defined role functions. This is
the literal adjacent-label identity; no sign of a selected vertex is
changed in the cycle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc ratio ratioD)
open SecondWord (U W)

def targetCost (r : Row) (B : ℝ) : ℝ := p r*arc B-q r*B
def slope (r : Row) (b : ℝ) : ℝ := t r+P r*ratio b
def targetSlope (r : Row) (B : ℝ) : ℝ := q r+p r*ratio B
def H (r : Row) (B : ℝ) : ℝ := q r*U B+p r*W B

lemma slope_eq (r : Row) (b : ℝ) : slope r b=targetD r b := by dsimp [slope,targetD]; ring
lemma slope_bounds (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    0<slope r b ∧ slope r b<(6/5:ℝ) := by
  have hpos := targetD_positive r hb
  have hr := SecondWord.outer_ratio_bounds hb
  rw [←slope_eq] at hpos
  refine ⟨hpos,?_⟩
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg
    (coefficient_bounds r).2.2.2.2.1 (by linarith [hr.1] : 0≤ratio b)
  have ht : t r≤11336/10000 := by fin_cases r <;> norm_num [t]
  dsimp only [slope]
  linarith

lemma targetSlope_positive (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    0<targetSlope r B := by
  have hp := mul_nonneg (coefficient_bounds r).1
    (SameContact.ratio_pos (SameContact.outer_domain hB)).le
  dsimp [targetSlope]
  have hq : 0<q r := by fin_cases r <;> norm_num [q]
  linarith

lemma targetCost_hasDerivAt (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    HasDerivAt (targetCost r) (-targetSlope r B) B := by
  convert ((SameContact.arc_hasDerivAt (SameContact.outer_domain hB)).const_mul (p r)).sub
    ((hasDerivAt_id B).const_mul (q r)) using 1
  · funext y; simp only [targetCost,Pi.sub_apply,id_eq]
  · simp only [targetSlope]; ring

lemma targetCost_antitone (r : Row) : AntitoneOn (targetCost r) (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun _ hB => (targetCost_hasDerivAt r hB).continuousAt.continuousWithinAt)
    (fun _ hB => targetCost_hasDerivAt r (Ioo_subset_Icc_self hB))
    (fun _ hB => neg_nonpos.mpr (targetSlope_positive r (Ioo_subset_Icc_self hB)).le)

lemma source_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (target r) (slope r b) b := by
  rw [slope_eq]
  exact Same.target_hasDerivAt r hb

lemma slope_hasDerivAt (r : Row) {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    HasDerivAt (slope r) (P r*ratioD b) b := by
  convert ((SameContact.ratio_hasDerivAt (SameContact.outer_domain hb)).const_mul (P r)).const_add
    (t r) using 1
  · funext y; simp only [slope]

lemma original_cost (r : Row) {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    target r b+targetCost r B= -P r*a+t r*b+p r*A-q r*B := by
  rw [target,targetCost,(SameContact.actual_arc hs).1,(SameContact.actual_arc ht).1]
  ring

lemma aligned_original (r : Row) {a b A B : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : 1≤b+A) :
    (8981/10000:ℝ)<Real.pi/2+c r-P r*a+t r*b+p r*A-q r*B := by
  have hh := Same.aligned_original r ht hs (by linarith)
  linarith

lemma H_positive (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : 0<H r B := by
  have hU := SecondWord.U_positive (SecondWord.outer_domain hB)
  have hmain := mul_pos (show 0<q r by fin_cases r <;> norm_num [q]) hU
  have hother := mul_nonneg (coefficient_bounds r).1 (show 0≤W B by dsimp [W]; linarith [hB.1])
  dsimp [H]
  linarith

lemma H_upper (r : Row) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : H r B<(91/50:ℝ) := by
  have hc := SecondWord.UW_circle (SecondWord.outer_domain hB)
  have hnonneg := sq_nonneg (q r*W B-p r*U B)
  have hid : (H r B)^2+(q r*W B-p r*U B)^2=Q0*((q r)^2+(p r)^2) := by
    dsimp [H]
    linear_combination ((q r)^2+(p r)^2)*hc
  by_cases hlast : r=2
  · subst r
    have ha := (outer_bounds (SameContact.arc_state hB)).2.1
    have ha0 := ShortOuterZero.fine_axial_bounds.2
    norm_num [H,p,q,U]
    linarith
  · have hr : r=0 ∨ r=1 := by fin_cases r <;> simp_all
    rcases hr with rfl | rfl <;> norm_num [p,q,Q0] at hid ⊢ <;> nlinarith

lemma independent_floor (r : Row) :
    (39747/50000:ℝ)<Real.pi/2+c r-P r*outerAxial+(p r-q r)*outerDiagonal := by
  have ha := ShortOuterZero.fine_axial_bounds
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hp := pi_hand_enclosure.1
  fin_cases r <;> norm_num [c,p,q,P] <;> linarith

lemma independent_lower (r : Row) {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    (39747/50000:ℝ)+x<Real.pi/2+x+c r-P r*a+t r*b+p r*A-q r*B := by
  have hb : b∈Icc 0 outerDiagonal := ⟨hs.1,(outer_bounds hs).2.2.2.1⟩
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hzero : (0:ℝ)∈Icc 0 outerDiagonal := ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal := ⟨hzero.2,le_rfl⟩
  have hsrc := target_monotone r hzero hb hb.1
  have htar := targetCost_antitone r hB hdiag hB.2
  rw [target,SameContact.arc_zero] at hsrc
  rw [targetCost,SameContact.arc_diagonal] at htar
  have hh := original_cost r hs ht
  have hf := independent_floor r
  linarith

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary
end
end
end

section
/-!
## The actual negative-half same-sign secondary contact

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
  (fun _ hB => (contact_target_hasDerivAt hB x).continuousAt.continuousWithinAt)
  (fun _ hB => contact_target_hasDerivAt (Ioo_subset_Icc_self hB) x)
  (fun _ hB => (K_positive (Ioo_subset_Icc_self hB) hx).le)

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
  (fun _ hx => (speed_positive hB (Ioo_subset_Icc_self hx)).le)

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
end
end
end

section
/-!
## The initial same-sign secondary contact strip

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive.Zero
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open SecondWord (U W)

def Z (x : ℝ) : ℝ := 1/2+Real.cos x+Real.sin x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Z x*Real.cos x-Y x*Real.sin x
def vertical (x : ℝ) : ℝ := Z x*Real.sin x+Y x*Real.cos x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-(Real.cos x-Real.sin x)/Y x
def value (r : Row) (x : ℝ) : ℝ :=
  Real.pi/2+x+c r+target r 0+targetCost r (height x)
def first (r : Row) (x : ℝ) : ℝ :=
  1-targetSlope r (height x)*horizontal x*factor x

lemma radical_data {x : ℝ} (hx : x∈Icc 0 strip) :
    0<Y x ∧ (Y x)^2+(Z x)^2=Q0 := by
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have hz : (3/2:ℝ)≤Z x ∧ Z x≤201/125 := by
    dsimp [Z]
    constructor <;> linarith [hf.2.2.2.2.2,hf.2.1,ht.2.2.1]
  have hr : 0<Q0-(Z x)^2 := by norm_num [Q0]; nlinarith
  exact ⟨Real.sqrt_pos.mpr hr,by dsimp [Y]; linarith [Real.sq_sqrt hr.le]⟩

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (Real.cos x-Real.sin x) x := by
  have h := ((Real.hasDerivAt_cos x).const_add (1/2)).add (Real.hasDerivAt_sin x)
  convert h using 1
  · funext y; simp only [Z,Pi.add_apply]
  · ring

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt Y (-Z x*(Real.cos x-Real.sin x)/Y x) x := by
  have hy := radical_data hx
  have hr : Q0-(Z x)^2≠0 := by nlinarith [hy.1,hy.2]
  have h := (((Z_hasDerivAt x).pow 2).const_sub Q0).sqrt hr
  convert h using 1
  · rfl
  change _=-(((2:ℕ):ℝ)*Z x^(2-1)*(Real.cos x-Real.sin x))/(2*Y x)
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
  field_simp

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt height (horizontal x*factor x) x := by
  have hy := (radical_data hx).1
  have h := (((Z_hasDerivAt x).mul (Real.hasDerivAt_sin x)).add
    ((Y_hasDerivAt hx).mul (Real.hasDerivAt_cos x))).sub_const (1/2)
  convert h using 1
  · funext y; simp only [height,vertical,Pi.add_apply,Pi.mul_apply]
  · simp only [horizontal,factor]; field_simp; ring

lemma original_coordinates {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 strip)
    (he : 1/2+(1/2-A)*Real.cos x+(1/2-B)*Real.sin x=0) :
    horizontal x=A+1/2 ∧ vertical x=B+1/2 := by
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hD := (D_bounds hB hx).1
  have hD' : 0<(B+1/2)*Real.cos x-(A+1/2)*Real.sin x := by
    dsimp [D,U,W] at hD
    rw [(SameContact.actual_arc ht).1] at hD
    linarith
  have hZ : Z x=(A+1/2)*Real.cos x+(B+1/2)*Real.sin x := by
    dsimp [Z]
    linarith
  have hcircle : ((B+1/2)*Real.cos x-(A+1/2)*Real.sin x)^2+(Z x)^2=Q0 := by
    rw [hZ]
    linear_combination ht.2.2+
      ((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=(B+1/2)*Real.cos x-(A+1/2)*Real.sin x := by
    have hr := radical_data hx
    nlinarith [hr.1,hr.2]
  constructor
  · dsimp [horizontal]
    rw [hZ,hY]
    linear_combination (A+1/2)*(Real.sin_sq_add_cos_sq x)
  · dsimp [vertical]
    rw [hZ,hY]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

lemma exists_target {x : ℝ} (hx : x∈Icc 0 strip) :
    ∃B,B∈Icc 0 outerDiagonal ∧ contact B x=0 := by
  have hc : Continuous (fun B => contact B x) := by dsimp [contact,arc]; fun_prop
  exact intermediate_value_Icc (show (0:ℝ)≤outerDiagonal by linarith [outer_endpoint_bounds.2.2.1])
    hc.continuousOn (show (0:ℝ)∈Icc (contact 0 x) (contact outerDiagonal x) from
      ⟨(contact_zero_target hx).le,(contact_target_diagonal hx).1.le⟩)

lemma physical {x : ℝ} (hx : x∈Icc 0 strip) :
    height x∈Icc 0 outerDiagonal ∧ contact (height x) x=0 ∧ U (height x)=horizontal x := by
  obtain ⟨B,hB,he⟩ := exists_target hx
  have hh := original_coordinates (SameContact.arc_state hB) hx (by simpa [contact] using he)
  have hheight : height x=B := by dsimp [height]; linarith [hh.2]
  rw [hheight]
  exact ⟨hB,he,by dsimp [U]; linarith [hh.1]⟩

lemma actual_height {B x : ℝ} (hd : Domain B x) (he : contact B x=0) : height x=B := by
  have hh := original_coordinates (SameContact.arc_state hd.1) hd.2.1 (by simpa [contact] using he)
  dsimp [height]
  linarith [hh.2]

lemma actual_D {x : ℝ} (hx : x∈Icc 0 strip) : D (height x) x=Y x := by
  have hp := physical hx
  dsimp [D,W]
  rw [hp.2.2]
  dsimp [height,horizontal,vertical]
  linear_combination Y x*(Real.sin_sq_add_cos_sq x)

lemma value_cost {x : ℝ} (hx : x∈Icc 0 strip) (r : Row) : value r x=cost r (height x) x := by
  dsimp [value,cost]
  rw [(physical hx).2.1]

lemma first_transport {x : ℝ} (hx : x∈Icc 0 strip) (r : Row) :
    first r x=transport r (height x) x := by
  have hp := physical hx
  have hH := H_identity hp.1 r
  rw [hp.2.2] at hH
  dsimp [first,factor,transport]
  rw [actual_D hx]
  nlinarith only [congrArg (fun z : ℝ => z*(1-(Real.cos x-Real.sin x)/Y x)) hH]

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) (r : Row) :
    HasDerivAt (value r) (first r x) x := by
  have h := ((hasDerivAt_id x).const_add (Real.pi/2+c r+target r 0)).add
    ((targetCost_hasDerivAt r (physical hx).1).comp x (height_hasDerivAt hx))
  convert h using 1
  · funext y; simp only [value,Pi.add_apply,Function.comp_apply,id_eq]; ring
  · simp only [first]; ring

theorem value_lower (r : Row) {x : ℝ} (hx : x∈Icc 0 strip) : (8981/10000:ℝ)<value r x := by
  have hm : MonotoneOn (value r) (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (value_hasDerivAt hy r).continuousAt.continuousWithinAt)
    (fun y hy => value_hasDerivAt (Ioo_subset_Icc_self hy) r)
    (fun y hy => by
      rw [first_transport (Ioo_subset_Icc_self hy)]
      linarith [transport_lower r (physical (Ioo_subset_Icc_self hy)).1 (Ioo_subset_Icc_self hy)])
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  have hp := physical h0
  have hv := initial_lower r (show Domain (height 0) 0 from ⟨hp.1,h0,hp.2.1.ge⟩)
  rw [←value_cost h0 r] at hv
  exact hv.trans_le (hm h0 hx hx.1)

theorem original_lower (r : Row) {B x : ℝ} (hd : Domain B x) (he : contact B x=0) :
    (8981/10000:ℝ)<cost r B x := by
  have hh := value_lower r hd.2.1
  rw [value_cost hd.2.1 r,actual_height hd he] at hh
  exact hh

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Positive.Zero
end
end
end
