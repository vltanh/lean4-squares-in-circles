module

public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryNegativeData
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryPositiveGeometry

/-!
# Eight squares: the actual initial contact strip for the first secondary row

The contact is the original negative-half separator. Its feasible
targets exceed 0.35; the stationary angular derivative is the exact
transport formula (21), positive on the entire strip.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport
open SameContact (arc ratio)
open SecondWord (U W)

def strip : ℝ := 3/100
def Domain (B x : ℝ) : Prop := B∈Icc 0 outerDiagonal ∧ x∈Icc 0 strip ∧ 0≤contact B x
def D (B x : ℝ) : ℝ := W B*Real.cos x+U B*Real.sin x
def transport (B x : ℝ) : ℝ := -1+H 0 B*(1-Real.sin x/D B x)

lemma angle_full {x : ℝ} (hx : x∈Icc 0 strip) : x∈Icc 0 (7/10) :=
  ⟨hx.1,by dsimp [strip] at hx; linarith [hx.2]⟩

lemma strip_trig {x : ℝ} (hx : x∈Icc 0 strip) :
    (1999/2000:ℝ)<Real.cos x ∧ 0≤Real.sin x ∧ Real.sin x≤3/100 := by
  have hm := cos_anti (angle_full hx) (show (3/100:ℝ)∈Icc 0 (7/10) by norm_num) hx.2
  have hcap := HighOrderTaylor.C18_le_cos (show (0:ℝ)≤3/100 by norm_num)
  have hpoly : (1999/2000:ℝ)<HighOrderTaylor.C18 (3/100) := by
    norm_num [HighOrderTaylor.C18,HighOrderTaylor.C16,HighOrderTaylor.C14,
      HighOrderTaylor.C12,cos10,cos8]
  have ht := positive_trig (angle_full hx)
  exact ⟨hpoly.trans_le (hcap.trans hm),ht.2.2.1,ht.2.2.2.2.1.trans hx.2⟩

lemma fixed_contact_negative : contact (7/20) strip<0 := by
  have hB : (7/20:ℝ)∈Icc 0 outerDiagonal :=
    ⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hstate := SameContact.arc_state hB
  have hc := hstate.2.2
  have hA : (5/4:ℝ)<arc (7/20) := by
    norm_num [Q0] at hc
    nlinarith [hstate.1,hstate.2.1]
  have ht := strip_trig (show strip∈Icc 0 strip by norm_num [strip])
  have hp : (3/4:ℝ)*(1999/2000)<(arc (7/20)-1/2)*Real.cos strip := by
    gcongr <;> linarith
  dsimp [contact]
  nlinarith

lemma contact_target_diagonal {x : ℝ} (hx : x∈Icc 0 strip) :
    0<contact outerDiagonal x ∧ contact outerDiagonal x<outerDiagonal := by
  have ht := strip_trig hx
  have hd := ShortMixedZero.fine_diagonal_bounds
  have hfirst : (399/1000:ℝ)*(1999/2000)<(outerDiagonal-1/2)*Real.cos x := by
    gcongr <;> linarith
  have hlast := mul_le_mul
    (show outerDiagonal+1/2≤(7/5:ℝ) by linarith) ht.2.2 ht.2.1 (by norm_num)
  refine ⟨diagonal_contact_positive (angle_full hx),?_⟩
  rw [contact,SameContact.arc_diagonal]
  nlinarith

lemma source_strict_upper {B x : ℝ} (hd : Domain B x) : contact B x<outerDiagonal := by
  have hm := contact_target_monotone (angle_full hd.2.1) hd.1
    (show outerDiagonal∈Icc 0 outerDiagonal from
      ⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩) hd.1.2
  exact hm.trans_lt (contact_target_diagonal hd.2.1).2

lemma source_mem {B x : ℝ} (hd : Domain B x) : contact B x∈Icc 0 outerDiagonal :=
  ⟨hd.2.2,(source_strict_upper hd).le⟩

lemma wide_domain {B x : ℝ} (hd : Domain B x) : Negative.Domain B x :=
  ⟨hd.1,angle_full hd.2.1,source_mem hd⟩

lemma target_lower {B x : ℝ} (hd : Domain B x) : (7/20:ℝ)<B := by
  by_contra! hbad
  have hB : (7/20:ℝ)∈Icc 0 outerDiagonal :=
    ⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hm := contact_target_monotone (angle_full hd.2.1) hd.1 hB hbad
  have ha := contact_angle_monotone hB (angle_full hd.2.1)
    (show strip∈Icc 0 (7/10) by norm_num [strip]) hd.2.1.2
  linarith [fixed_contact_negative,hd.2.2]

lemma D_lower {B x : ℝ} (hd : Domain B x) : (849/1000:ℝ)<D B x := by
  have hB := target_lower hd
  have ht := strip_trig hd.2.1
  have hmain : (17/20:ℝ)*(1999/2000)<W B*Real.cos x := by
    have hW : (17/20:ℝ)<W B := by dsimp [W]; linarith
    have hc := ht.1
    gcongr
  have hrest := mul_nonneg (SecondWord.U_positive (SameContact.outer_domain hd.1)).le ht.2.1
  dsimp [D]
  nlinarith

lemma H_lower {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (97207/100000:ℝ)*(1399/1000)<H 0 B := by
  have hend : (q 0+p 0)*outerDiagonal≤q 0*outerAxial := by
    have hd := ShortMixedZero.fine_diagonal_bounds
    have ha := ShortOuterZero.fine_axial_bounds
    norm_num [q,p]
    linarith
  have hm := outer_concave_lower (SameContact.arc_state hB)
    (show 0≤q 0 by norm_num [q]) hend (le_refl ((q 0+p 0)*outerDiagonal))
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [H,U,W]
  norm_num [p,q] at hm ⊢
  linarith

lemma K_identity {B x : ℝ} (hB : B∈Icc 0 outerDiagonal) : U B*K B x=D B x := by
  have hU := SecondWord.U_positive (SameContact.outer_domain hB)
  have hr : U B*ratio B=W B := mul_div_cancel₀ (W B) hU.ne'
  simp only [K,D]
  linear_combination Real.cos x*hr

lemma H_identity {B : ℝ} (hB : B∈Icc 0 outerDiagonal) : targetSlope 0 B*U B=H 0 B :=
  Secondary.Positive.H_identity hB 0

lemma speed_identity (B x : ℝ) : Negative.speed B x=D B x-Real.sin x := by
  dsimp [Negative.speed,D,U,W]
  ring

lemma transport_positive {B x : ℝ} (hd : Domain B x) : 0<transport B x := by
  have hD := D_lower hd
  have hH := H_lower hd.1
  have ht := strip_trig hd.2.1
  have hdiff : 0<D B x-Real.sin x := by linarith [ht.2.2]
  have hm := mul_lt_mul_of_pos_right hH hdiff
  have hl : D B x<(97207/100000:ℝ)*(1399/1000)*(D B x-Real.sin x) := by
    nlinarith [ht.2.2]
  have he : transport B x*D B x= -D B x+H 0 B*(D B x-Real.sin x) := by
    dsimp [transport]
    field_simp [show D B x≠0 by linarith]
  have hp : 0<transport B x*D B x := by linarith
  exact (mul_pos_iff_of_pos_right (by linarith : 0<D B x)).mp hp

lemma stationary_first {B x : ℝ} (hd : Domain B x) (hstat : targetFirst 0 B x=0) :
    Negative.first 0 B x=transport B x := by
  have hK := K_identity (x:=x) hd.1
  have hH := H_identity hd.1
  have hs : slope 0 (contact B x)*D B x=H 0 B := by
    dsimp [targetFirst] at hstat
    linear_combination -slope 0 (contact B x)*hK+U B*hstat+hH
  dsimp [Negative.first,transport]
  rw [speed_identity]
  field_simp [show D B x≠0 by linarith [D_lower hd]]
  linear_combination (D B x-Real.sin x)*hs

lemma first_continuousAt {B x : ℝ} (hd : Domain B x) :
    ContinuousAt (Negative.first 0 B) x := by
  have hs := (slope_hasDerivAt 0 (source_mem hd)).continuousAt.comp (x := x)
    (contact_angle_hasDerivAt B x).continuousAt
  have ht : ContinuousAt (Negative.speed B) x := by
    show ContinuousAt (fun y => (arc B-1/2)*Real.sin y+(B+1/2)*Real.cos y) x
    fun_prop
  exact continuousAt_const.add (hs.mul ht)

lemma diagonal_first_positive {x : ℝ} (hx : x∈Icc 0 strip) :
    0<Negative.first 0 outerDiagonal x := by
  have hD : Domain outerDiagonal x :=
    ⟨⟨by linarith [outer_endpoint_bounds.2.2.1],le_rfl⟩,hx,(contact_target_diagonal hx).1.le⟩
  have hr := (SecondWord.outer_ratio_bounds (source_mem hD)).2.1
  have ht := strip_trig hx
  have hsl : (80213/100000:ℝ)≤ slope 0 (contact outerDiagonal x) := by
    norm_num [slope,t,P]
    linarith
  have hmain : (1399/1000:ℝ)*(1999/2000)<(outerDiagonal+1/2)*Real.cos x := by
    have hd := ShortMixedZero.fine_diagonal_bounds
    gcongr <;> linarith
  have hother := mul_nonneg (show 0≤outerDiagonal-1/2 by
    linarith [outer_endpoint_bounds.2.2.1]) ht.2.1
  have hspeed : (1399/1000:ℝ)*(1999/2000)<Negative.speed outerDiagonal x := by
    rw [Negative.speed,SameContact.arc_diagonal]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hsl (speed_positive hD.1 (angle_full hx)).le
  dsimp [Negative.first]
  nlinarith

lemma initial_lower {B : ℝ} (hd : Domain B 0) : (8981/10000:ℝ)<Negative.cost 0 B 0 := by
  have hs := SameContact.arc_state (source_mem hd)
  have ht := SameContact.arc_state hd.1
  have he : contact B 0+arc B=1 := by norm_num [contact]; ring
  have hh := Secondary.aligned_original 0 hs ht he.ge
  have hc := Secondary.original_cost 0 hs ht
  dsimp [Negative.cost]
  nlinarith only [hh,hc]

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip
