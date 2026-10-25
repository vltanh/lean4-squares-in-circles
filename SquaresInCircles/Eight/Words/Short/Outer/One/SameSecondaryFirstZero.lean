module

public import SquaresInCircles.Eight.Words.Short.Outer.One.OppositeFiveUpperPrimary
public import SquaresInCircles.Eight.Words.Short.Outer.One.SamePositiveGeometry
public import SquaresInCircles.Eight.Words.Short.Outer.One.SameSecondaryPositiveZero
public import SquaresInCircles.Eight.Words.Short.Outer.Zero.SameCap

/-!
# Eight squares: the zero-source boundary of the first negative secondary strip

The target coordinates come from the exact original target circle.
Their derivative gives precisely transport formula (21), so this whole
boundary increases from its aligned endpoint.
-/

section
/-!
## The single multiplier for the first negative secondary owner

The multiplier is exactly 0.94. The source endpoint support and the
full-circle target support retain the actual original weak separator.
The norm decreases on the whole angle interval and its exact curvature
identity makes the support derivative decreasing.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstNorm
open CommonQuarter CorePairGeometry Arithmetic WrongWordCircleSupport

def weight : ℝ := 47/50
abbrev radius := RoleFour.radius
def normA : ℝ := (p 0)^2+(q 0)^2+weight^2
def normB : ℝ := -2*weight*p 0
def normC : ℝ := -2*weight*q 0
def N (x : ℝ) : ℝ := CircularNorm.norm normA normB normC x
def value (x : ℝ) : ℝ :=
  Real.pi/2-x+c 0-P 0*outerAxial+(weight-p 0+q 0)/2+weight*Real.cos x-radius*N x
def first (x : ℝ) : ℝ :=
  -1-weight*Real.sin x-radius*CircularNorm.d1 normA normB normC x
def second (x : ℝ) : ℝ :=
  -weight*Real.cos x-radius*CircularNorm.d2 normA normB normC x

lemma energy_identity (x : ℝ) : CircularNorm.energy normA normB normC x=
    (p 0-weight*Real.cos x)^2+(-q 0+weight*Real.sin x)^2 := by
  dsimp [CircularNorm.energy,normA,normB,normC]
  linear_combination -weight^2*(Real.sin_sq_add_cos_sq x)

lemma energy_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    0<CircularNorm.energy normA normB normC x := by
  have hX : p 0-weight*Real.cos x<0 := by
    norm_num [p,weight]
    linarith [(positive_trig hx).1]
  rw [energy_identity]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_neg hX) (sq_nonneg _)

lemma norm_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : 0<N x :=
  CircularNorm.norm_pos (energy_positive hx)

lemma norm_sq {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    (N x)^2=(p 0)^2+(q 0)^2+weight^2-2*weight*(p 0*Real.cos x+q 0*Real.sin x) := by
  have hh := CircularNorm.norm_sq (energy_positive hx).le
  convert hh using 1 <;> dsimp [N,CircularNorm.energy,normA,normB,normC]
  ring

lemma norm_slope_negative {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    CircularNorm.d1 normA normB normC x<0 := by
  have ht := positive_trig hx
  have hs : CircularNorm.slope normB normC x<0 := by
    norm_num [CircularNorm.slope,normB,normC,weight,p,q]
    linarith [ht.1,ht.2.2.2.1]
  exact div_neg_of_neg_of_pos hs (mul_pos (by norm_num) (norm_positive hx))

lemma norm_antitone : AntitoneOn N (Icc 0 (7/10)) := antiOn_of_hasDeriv_nonpos
  (fun _ hx => (CircularNorm.norm_hasDerivAt (energy_positive hx)).continuousAt.continuousWithinAt)
  (fun _ hx => CircularNorm.norm_hasDerivAt (energy_positive (Ioo_subset_Icc_self hx)))
  (fun _ hx => (norm_slope_negative (Ioo_subset_Icc_self hx)).le)

lemma norm_upper {x : ℝ} (hx : x∈Icc 0 (7/10)) : N x<(153/125:ℝ) := by
  have h0 : (0:ℝ)∈Icc 0 (7/10) := by norm_num
  have hsq := norm_sq h0
  have hn0 : N 0<(153/125:ℝ) := by
    norm_num [p,q,weight] at hsq
    nlinarith [norm_positive h0]
  exact (norm_antitone h0 hx hx.1).trans_lt hn0

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt value (first x) x := by
  convert (((((hasDerivAt_id x).neg).const_add
    (Real.pi/2+c 0-P 0*outerAxial+(weight-p 0+q 0)/2)).add
      ((Real.hasDerivAt_cos x).const_mul weight)).sub
        ((CircularNorm.norm_hasDerivAt (energy_positive hx)).const_mul radius)) using 1
  · funext y; simp only [value,N,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq]; ring
  · simp only [first]; ring

lemma first_hasDerivAt {x : ℝ} (hx : x∈Icc 0 (7/10)) : HasDerivAt first (second x) x := by
  convert ((((Real.hasDerivAt_sin x).const_mul weight).neg).const_add (-1)).sub
    ((CircularNorm.d1_hasDerivAt (energy_positive hx)).const_mul radius) using 1
  · funext y; simp only [first,Pi.sub_apply,Pi.neg_apply]; ring
  · simp only [second]; ring

lemma curvature {x : ℝ} (hx : x∈Icc 0 (7/10)) : second x< -(11/100:ℝ) := by
  have hnorm := CircularNorm.curvature_lower (energy_positive hx)
    (show normB^2+normC^2≤normA^2 by norm_num [normA,normB,normC,weight,p,q])
  have hmul := mul_le_mul_of_nonneg_left hnorm RoleFour.radius_positive.le
  have hrN : radius*N x<(1978788/1000000:ℝ)*(153/125) :=
    (mul_le_mul_of_nonneg_right RoleFour.radius_upper.le (norm_positive hx).le).trans_lt
      (mul_lt_mul_of_pos_left (norm_upper hx) (by norm_num))
  have hmul' : -radius*N x/4≤radius*CircularNorm.d2 normA normB normC x := by
    simp only [N]; linarith
  have hc := (positive_trig hx).1
  simp only [second,weight]
  linarith

lemma first_antitone : AntitoneOn first (Icc 0 (7/10)) := antiOn_of_hasDeriv_nonpos
  (fun x hx => (first_hasDerivAt hx).continuousAt.continuousWithinAt)
  (fun x hx => first_hasDerivAt (Ioo_subset_Icc_self hx))
  (fun x hx => by linarith [curvature (Ioo_subset_Icc_self hx)])

lemma source_endpoint_gap : (2/625:ℝ)<(-P 0+t 0-weight)*outerDiagonal+P 0*outerAxial := by
  have hd := ShortMixedZero.fine_diagonal_bounds
  have ha := ShortOuterZero.fine_axial_bounds
  norm_num [P,t,weight]
  linarith

lemma source_support {a b : ℝ} (hs : OuterState a b) :
    -P 0*outerAxial≤-P 0*a+(t 0-weight)*b := by
  apply outer_concave_lower hs (show 0≤-P 0 by norm_num [P]) le_rfl
  linarith [source_endpoint_gap]

lemma norm_coefficients (x : ℝ) :
    Real.sqrt ((p 0-weight*Real.cos x)^2+(-q 0+weight*Real.sin x)^2)=N x := by
  unfold N CircularNorm.norm
  rw [energy_identity]

theorem original_support {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    value x≤Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  have hmargin := mul_le_mul_of_nonneg_left hm (show 0≤weight by norm_num [weight])
  have hsource := source_support hs
  have htarget := ShortOuterZero.Opposite.Positive.Cap.full_circle_lower
    (X:=p 0-weight*Real.cos x) (Y:=-q 0+weight*Real.sin x) ht
  rw [norm_coefficients] at htarget
  dsimp [value]
  nlinarith only [hmargin,hsource,htarget]

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstNorm
end
end
end

section
/-!
## The two fixed support comparisons for the first secondary row

The exact norm is substituted only at 0.7 and 0.03. The whole-interval
curvature proof then propagates positivity of the derivative and the
lower bound from 0.03 to every later angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstNorm
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)
open SecondWord.OppositeThree.ReferenceAlgebra (rootThree rootStep)

def energyBox (x : ℝ) (hx : 0≤x) : Interval (CircularNorm.energy normA normB normC x) :=
  (((Interval.point normA).add ((Interval.point normB).mul (cosBox x hx))).add
    ((Interval.point normC).mul (sinBox x hx)))
def normBox (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo) : Interval (N x) :=
  rootThree (energyBox x hx) (6/5) (by norm_num) hr
def radiusBox : Interval radius := rootThree (Interval.point Q0) 2 (by norm_num)
  (by norm_num [Interval.point,Q0])
def slopeBox (x : ℝ) (hx : 0≤x) : Interval (CircularNorm.slope normB normC x) :=
  (((Interval.point (-normB)).mul (sinBox x hx))).add
    ((Interval.point normC).mul (cosBox x hx))
def firstBox (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo)
    (hn : 0<(normBox x hx hr).lo) : Interval (first x) := by
  let denominator := (Interval.point 2).mul (normBox x hx hr)
  have hden : 0<denominator.lo := Interval.mul_lo_pos (by norm_num [Interval.point]) hn
  exact (((Interval.point (-1)).sub ((Interval.point weight).mul (sinBox x hx))).sub
    (radiusBox.mul ((slopeBox x hx).div denominator hden)))
def valueBox (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo) : Interval (value x) := by
  let V₀ := ((RoleFour.piBox.mul (Interval.point (1/2))).sub (Interval.point x)).add
    (Interval.point (c 0))
  let V₁ := (V₀.sub ((Interval.point (P 0)).mul RoleFour.aBox)).add
    (Interval.point ((weight-p 0+q 0)/2))
  let V₂ := V₁.add ((Interval.point weight).mul (cosBox x hx))
  convert V₂.sub (radiusBox.mul (normBox x hx hr)) using 1
  dsimp [value]
  ring

local macro "first_secondary_norm_reference" : tactic => `(tactic|
  norm_num [energyBox,normBox,radiusBox,slopeBox,firstBox,valueBox,normA,normB,normC,
    weight,RoleFour.piBox,RoleFour.aBox,SecondWord.SameZero.PJ.Reference.sinBox,
    SecondWord.SameZero.PJ.Reference.cosBox,rootThree,rootStep,
    Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,Interval.mul,
    Interval.square,Interval.div,Interval.inv,HighOrderTaylor.S17,HighOrderTaylor.S15,
    HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C18,HighOrderTaylor.C16,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,Q0,c,p,q,P,t])

lemma final_first : (3/50:ℝ)<first (7/10) := by
  have hr : 0≤(energyBox (7/10) (by norm_num)).lo := by first_secondary_norm_reference
  have hn : 0<(normBox (7/10) (by norm_num) hr).lo := by first_secondary_norm_reference
  have hlo : (3/50:ℝ)<(firstBox (7/10) (by norm_num) hr hn).lo := by
    first_secondary_norm_reference
  exact hlo.trans_le (firstBox (7/10) (by norm_num) hr hn).mem.1

private lemma r87_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl

private lemma r87_value_eq (x : ℝ) : value x=Real.pi*(1/2)-x+c 0-P 0*outerAxial+
    (weight-p 0+q 0)/2+weight*Real.cos x-radius*N x := by
  simp only [value]; ring
private lemma r87_valueBox_lo (x : ℝ) (hx : 0≤x) (hr : 0≤(energyBox x hx).lo) :
    (valueBox x hx hr).lo=(((((((RoleFour.piBox.mul (Interval.point (1/2))).sub
      (Interval.point x)).add (Interval.point (c 0))).sub
        ((Interval.point (P 0)).mul RoleFour.aBox)).add
          (Interval.point ((weight-p 0+q 0)/2))).add
            ((Interval.point weight).mul (cosBox x hx))).sub
              (radiusBox.mul (normBox x hx hr))).lo := by
  dsimp only [valueBox]
  exact r87_mpr_lo (r87_value_eq x) _ _

lemma initial_reference : (89929/100000:ℝ)<value (3/100) := by
  have hr : 0≤(energyBox (3/100) (by norm_num)).lo := by first_secondary_norm_reference
  have hlo : (89929/100000:ℝ)<(valueBox (3/100) (by norm_num) hr).lo := by
    rw [r87_valueBox_lo]
    first_secondary_norm_reference
  exact hlo.trans_le (valueBox (3/100) (by norm_num) hr).mem.1

lemma first_positive {x : ℝ} (hx : x∈Icc 0 (7/10)) : (3/50:ℝ)<first x :=
  final_first.trans_le (first_antitone hx (show (7/10:ℝ)∈Icc 0 (7/10) by norm_num) hx.2)

lemma value_monotone : MonotoneOn value (Icc 0 (7/10)) := monoOn_of_hasDeriv_nonneg
  (fun x hx => (value_hasDerivAt hx).continuousAt.continuousWithinAt)
  (fun x hx => value_hasDerivAt (Ioo_subset_Icc_self hx))
  (fun x hx => by linarith [first_positive (Ioo_subset_Icc_self hx)])

theorem original_later {a b A B x : ℝ} (hs : OuterState a b) (ht : OuterState A B)
    (hx : x∈Icc (3/100:ℝ) (7/10))
    (hm : (1+Real.cos x+Real.sin x)/2≤b+A*Real.cos x-B*Real.sin x) :
    (89929/100000:ℝ)<Real.pi/2-x+c 0-P 0*a+t 0*b+p 0*A-q 0*B := by
  have hv := value_monotone (show (3/100:ℝ)∈Icc 0 (7/10) by norm_num)
    (show x∈Icc 0 (7/10) from ⟨by linarith [hx.1],hx.2⟩) hx.1
  exact initial_reference.trans_le (hv.trans (original_support hs ht hm))

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstNorm
end
end
end

section
/-!
## The actual initial contact strip for the first secondary row

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip.Zero
open CommonQuarter CorePairGeometry Arithmetic
open SameContact (arc)
open SecondWord (U W)

def Z (x : ℝ) : ℝ := 1/2+Real.cos x
def Y (x : ℝ) : ℝ := Real.sqrt (Q0-(Z x)^2)
def horizontal (x : ℝ) : ℝ := Z x*Real.cos x+Y x*Real.sin x
def vertical (x : ℝ) : ℝ := Y x*Real.cos x-Z x*Real.sin x
def height (x : ℝ) : ℝ := vertical x-1/2
def factor (x : ℝ) : ℝ := 1-Real.sin x/Y x
def value (x : ℝ) : ℝ := Real.pi/2-x+c 0+target 0 0+targetCost 0 (height x)
def first (x : ℝ) : ℝ := -1+targetSlope 0 (height x)*horizontal x*factor x

lemma radical_data {x : ℝ} (hx : x∈Icc 0 strip) :
    0<Y x ∧ (Y x)^2+(Z x)^2=Q0 := by
  have ht := strip_trig hx
  have hf := positive_trig (angle_full hx)
  have hz : 0<Z x ∧ Z x≤3/2 := by dsimp [Z]; constructor <;> linarith [ht.1,hf.2.1]
  have hr : 0<Q0-(Z x)^2 := by norm_num [Q0]; nlinarith
  exact ⟨Real.sqrt_pos.mpr hr,by dsimp [Y]; linarith [Real.sq_sqrt hr.le]⟩

lemma Z_hasDerivAt (x : ℝ) : HasDerivAt Z (-Real.sin x) x :=
  (Real.hasDerivAt_cos x).const_add (1/2)

lemma Y_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt Y (Z x*Real.sin x/Y x) x := by
  have hy := radical_data hx
  have hr : Q0-(Z x)^2≠0 := by nlinarith [hy.1,hy.2]
  have h := (((Z_hasDerivAt x).pow 2).const_sub Q0).sqrt hr
  convert h using 1
  · rfl
  change _=-(((2:ℕ):ℝ)*Z x^(2-1)*(-Real.sin x))/(2*Y x)
  simp only [Nat.cast_ofNat,show (2:ℕ)-1=1 from rfl,pow_one]
  field_simp

lemma height_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) :
    HasDerivAt height (-horizontal x*factor x) x := by
  have hy := (radical_data hx).1
  have h := (((Y_hasDerivAt hx).mul (Real.hasDerivAt_cos x)).sub
    ((Z_hasDerivAt x).mul (Real.hasDerivAt_sin x))).sub_const (1/2)
  convert h using 1
  · funext y; simp only [height,vertical,Pi.sub_apply,Pi.mul_apply]
  · simp only [horizontal,factor]; field_simp; ring

lemma original_coordinates {A B x : ℝ} (ht : OuterState A B) (hx : x∈Icc 0 strip)
    (he : 1/2+(1/2-A)*Real.cos x+(1/2+B)*Real.sin x=0) :
    horizontal x=A+1/2 ∧ vertical x=B+1/2 := by
  let T : ℝ := (A+1/2)*Real.sin x+(B+1/2)*Real.cos x
  have htr := strip_trig hx
  have hT : 0<T := by
    have hs := mul_nonneg (show 0≤A+1/2 by linarith [ht.1,ht.2.1]) htr.2.1
    have hc := mul_pos (show 0<B+1/2 by linarith [ht.1])
      (show 0<Real.cos x by linarith [htr.1])
    dsimp [T]
    linarith
  have hZ : Z x=(A+1/2)*Real.cos x-(B+1/2)*Real.sin x := by dsimp [Z]; linarith
  have hcircle : T^2+(Z x)^2=Q0 := by
    rw [hZ]
    dsimp [T]
    linear_combination ht.2.2+((A+1/2)^2+(B+1/2)^2)*(Real.sin_sq_add_cos_sq x)
  have hY : Y x=T := by
    have hr := radical_data hx
    nlinarith [hr.1,hr.2]
  constructor
  · dsimp [horizontal]
    rw [hY,hZ]
    dsimp [T]
    linear_combination (A+1/2)*(Real.sin_sq_add_cos_sq x)
  · dsimp [vertical]
    rw [hY,hZ]
    dsimp [T]
    linear_combination (B+1/2)*(Real.sin_sq_add_cos_sq x)

lemma exists_target {x : ℝ} (hx : x∈Icc 0 strip) :
    ∃B,B∈Icc 0 outerDiagonal ∧ contact B x=0 := by
  have hB : (7/20:ℝ)∈Icc 0 outerDiagonal :=
    ⟨by norm_num,by linarith [outer_endpoint_bounds.2.2.1]⟩
  have hm := contact_angle_monotone hB (angle_full hx)
    (show strip∈Icc 0 (7/10) by norm_num [strip]) hx.2
  have hc : Continuous (fun B => contact B x) := by dsimp [contact,arc]; fun_prop
  obtain ⟨B,hB',he⟩ := intermediate_value_Icc hB.2 hc.continuousOn
    (show (0:ℝ)∈Icc (contact (7/20) x) (contact outerDiagonal x) from
      ⟨(hm.trans_lt fixed_contact_negative).le,(contact_target_diagonal hx).1.le⟩)
  exact ⟨B,⟨hB.1.trans hB'.1,hB'.2⟩,he⟩

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

lemma value_cost {x : ℝ} (hx : x∈Icc 0 strip) : value x=Negative.cost 0 (height x) x := by
  dsimp [value,Negative.cost]
  rw [(physical hx).2.1]

lemma first_transport {x : ℝ} (hx : x∈Icc 0 strip) : first x=transport (height x) x := by
  have hp := physical hx
  have hH := H_identity hp.1
  rw [hp.2.2] at hH
  dsimp [first,factor,transport]
  rw [actual_D hx]
  nlinarith only [congrArg (fun z : ℝ => z*(1-Real.sin x/Y x)) hH]

lemma value_hasDerivAt {x : ℝ} (hx : x∈Icc 0 strip) : HasDerivAt value (first x) x := by
  have h := (((hasDerivAt_id x).neg).const_add (Real.pi/2+c 0+target 0 0)).add
    ((targetCost_hasDerivAt 0 (physical hx).1).comp x (height_hasDerivAt hx))
  convert h using 1
  · funext y; simp only [value,Pi.add_apply,Pi.neg_apply,Function.comp_apply,id_eq]; ring
  · simp only [first]; ring

theorem value_lower {x : ℝ} (hx : x∈Icc 0 strip) : (8981/10000:ℝ)<value x := by
  have hm : MonotoneOn value (Icc 0 strip) := monoOn_of_hasDeriv_nonneg
    (fun y hy => (value_hasDerivAt hy).continuousAt.continuousWithinAt)
    (fun y hy => value_hasDerivAt (Ioo_subset_Icc_self hy))
    (fun y hy => by
      have hys := Ioo_subset_Icc_self hy
      have hp := physical hys
      rw [first_transport hys]
      exact (transport_positive (show Domain (height y) y from ⟨hp.1,hys,hp.2.1.ge⟩)).le)
  have h0 : (0:ℝ)∈Icc 0 strip := by norm_num [strip]
  have hp := physical h0
  have hv := initial_lower (show Domain (height 0) 0 from ⟨hp.1,h0,hp.2.1.ge⟩)
  rw [←value_cost h0] at hv
  exact hv.trans_le (hm h0 hx hx.1)

theorem original_lower {B x : ℝ} (hd : Domain B x) (he : contact B x=0) :
    (8981/10000:ℝ)<Negative.cost 0 B x := by
  have hh := value_lower hd.2.1
  rw [value_cost hd.2.1,actual_height hd he] at hh
  exact hh

end SquaresInCircles.Eight.ShortOuterOne.Same.Secondary.Negative.FirstStrip.Zero
end
end
end
