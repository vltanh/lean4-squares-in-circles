module

public import SquaresInCircles.Eight.Frames.Pair.Shape
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetGeometry
public import SquaresInCircles.Eight.Words.Second.Mixed.Zero.OppositeTargetReferenceAlgebra
public import SquaresInCircles.Eight.Words.Second.Outer.PointProducts
public import SquaresInCircles.Eight.Words.Short.Mixed.ZeroCoreNegative

/-!
# Eight squares: the full nonnegative-angle target-secondary half

The original weak target projection gives a
single transverse-sum loss, using only the primary core bound.  J and L
use their aligned reserves.  P uses its aligned minimum for angles at
least `.06`; below that angle, the same owner forces its actual outer
coordinate above `.435` and yields the stronger aligned reserve.
-/

section
/-!
## Named scalar references for the opposite mixed zero rows

Every radical enclosure below follows from
two rational square comparisons at one named coordinate.  The values
and slopes are direct substitutions in the literal role polynomials.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.References
open CommonQuarter CorePairGeometry Arithmetic GeneralReference

lemma six_mem : (3/5:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
lemma minimum_mem : (1027/1250:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)

lemma L_six : (47/50:ℝ)<aligned 2 (3/5) ∧ alignedD 2 (3/5)<0 ∧
    (1/2:ℝ)<LLabel.d2 (3/5) := by
  have hr := shifted_chart_reference (outer_domain six_mem)
    (l := (164487081559616/100000000000000:ℝ))
    (u := (164487081559617/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label LLabel six_mem ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,LLabel,Q0] at hh
  norm_num [aligned,alignedD,c,g,F,LLabel]
  exact ⟨by linarith [hh.1],by linarith [hh.2.2.2.1],by linarith [hh.2.2.2.2.1]⟩

lemma L_minimum : (9010079/10000000:ℝ)<aligned 2 (1027/1250) ∧
    |alignedD 2 (1027/1250)|<(1/10000:ℝ) := by
  have hr := shifted_chart_reference (outer_domain minimum_mem)
    (l := (147274350787908/100000000000000:ℝ))
    (u := (147274350787909/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label LLabel minimum_mem ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,LLabel,Q0] at hh
  norm_num [aligned,alignedD,c,g,F,LLabel]
  exact ⟨by linarith [hh.1],abs_lt.mpr ⟨by linarith [hh.2.2.1],by linarith [hh.2.2.2.1]⟩⟩

lemma J_small_slope : 1<JLabel.d1 (3/20) := by
  have hb : (3/20:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (186898368104165/100000000000000:ℝ))
    (u := (186898368104166/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label JLabel hb ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,JLabel,Q0] at hh ⊢
  linarith [hh.2.2.1]

lemma P_target : (463/500:ℝ)<aligned 1 (87/200) := by
  have hb : (87/200:ℝ)∈Icc 0 outerDiagonal := Asymmetric.rational_outer_mem (by norm_num)
  have hr := shifted_chart_reference (outer_domain hb)
    (l := (174395384113227/100000000000000:ℝ))
    (u := (174395384113228/100000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [W,Q0]) (by norm_num [W,Q0])
  have hh := GeneralReference.label PLabel hb ⟨le_rfl,le_rfl⟩
    ⟨hr.1.le,hr.2.le⟩ (by norm_num) (by norm_num)
  norm_num [valueLo,valueHi,firstLo,firstHi,secondLo,secondHi,
    lo,hi,rlo,rhi,dlo,dhi,PLabel,Q0] at hh
  norm_num [aligned,c,g,F,PLabel]
  linarith [hh.1]

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.References
end
end
end

section
/-!
## Complete aligned bounds for the three mixed zero rows

J is concave and P increases.  The initial L
arc has a convex derivative ending negative, and the remaining arc has
uniform positive curvature.  A single exact value-and-slope reference
then controls its minimum on that entire remaining arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic

lemma J_aligned_endpoints : (1801/2000:ℝ)<aligned 0 0 ∧
    (1801/2000:ℝ)<aligned 0 outerDiagonal := by
  constructor
  · change (1801/2000:ℝ)<125/100000+(103981/100000)*(1-0)+J 0
    rw [J_zero]
    linarith [outer_endpoint_bounds.2.1]
  · have hd := ShortMixedZero.fine_diagonal_bounds
    have hs : (449607/500000:ℝ)^2<outerDiagonal^2 := by
      nlinarith [hd.1]
    change (1801/2000:ℝ)<125/100000+(103981/100000)*(1-outerDiagonal)+J outerDiagonal
    rw [J_diagonal]
    nlinarith [hd.1,hd.2]

lemma J_aligned {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1801/2000:ℝ)<aligned 0 B := by
  have hc : ConcaveOn ℝ (Icc 0 outerDiagonal) (aligned 0) :=
    concave_of_deriv2 (fun t ht => aligned_hasDerivAt 0 ht)
      (fun t ht => alignedD_hasDerivAt 0 ht)
      (fun t ht => by norm_num [F]; linarith [J_second_upper ht])
  exact concave_gt_of_endpoints hc hB J_aligned_endpoints.1 J_aligned_endpoints.2

lemma P_aligned_monotone : MonotoneOn (aligned 1) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun t ht => (aligned_hasDerivAt 1 ht).continuousAt.continuousWithinAt)
    (fun t ht => aligned_hasDerivAt 1 (Ioo_subset_Icc_self ht))
    (fun t ht => by
      norm_num [alignedD,F,g]
      linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1])

lemma P_aligned {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (17033/20000:ℝ)≤aligned 1 B := by
  have hh := P_aligned_monotone outer_zero_mem hB hB.1
  have hz : aligned 1 0=(17033/20000:ℝ) := by
    norm_num [aligned,c,g,F,RoleLabel.outer,RoleLabel.eval,PLabel]
  rw [hz] at hh
  exact hh

lemma P_aligned_late {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (hcut : (87/200:ℝ)≤B) :
    (463/500:ℝ)<aligned 1 B :=
  References.P_target.trans_le (P_aligned_monotone
    (Asymmetric.rational_outer_mem (by norm_num)) hB hcut)

lemma L_aligned_early {B : ℝ} (hB : B∈Icc (0:ℝ) (3/5)) :
    (901/1000:ℝ)<aligned 2 B := by
  have hdom {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) : t∈Icc 0 outerDiagonal :=
    ⟨ht.1,ht.2.trans References.six_mem.2⟩
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (3/5)) (fun t => -alignedD 2 t) :=
    concave_of_deriv2
      (fun t ht => (alignedD_hasDerivAt 2 (hdom ht)).neg)
      (fun t ht => (LLabel.d2_hasDerivAt (outer_domain (hdom ht))).neg)
      (fun t ht => neg_nonpos.mpr (L_third_positive (hdom ht)).le)
  have hh := endpoint_minimum_of_convex_derivative hB
    (fun t ht => aligned_hasDerivAt 2 (hdom ht)) hc References.L_six.2.1.le
  have hz : (901/1000:ℝ)<aligned 2 0 := by
    norm_num [aligned,c,g,F,LLabel,RoleLabel.outer,RoleLabel.eval]
  exact (lt_min hz (by linarith [References.L_six.1])).trans_le hh

lemma L_aligned_curvature {B : ℝ} (hB : B∈Icc (3/5:ℝ) outerDiagonal) :
    (1/2:ℝ)<LLabel.d2 B :=
  References.L_six.2.2.trans_le (L_second_monotone References.six_mem
    ⟨by linarith [hB.1],hB.2⟩ hB.1)

lemma L_aligned_tangent {B : ℝ} (hB : B∈Icc (3/5:ℝ) outerDiagonal) :
    aligned 2 (1027/1250)+alignedD 2 (1027/1250)*(B-1027/1250)+
      (1/4)*(B-1027/1250)^2≤aligned 2 B := by
  convert curvature_tangent (κ := (1/2:ℝ)) hB
    (show (1027/1250:ℝ)∈Icc (3/5:ℝ) outerDiagonal from
      ⟨by norm_num,References.minimum_mem.2⟩)
    (fun t ht => aligned_hasDerivAt 2 ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => alignedD_hasDerivAt 2 ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => (L_aligned_curvature ht).le) using 1
  ring

lemma L_aligned_late {B : ℝ} (hB : B∈Icc (3/5:ℝ) outerDiagonal) :
    (901/1000:ℝ)<aligned 2 B := by
  have ht := L_aligned_tangent hB
  have hs := abs_lt.mp References.L_minimum.2
  have hp := mul_pos (show 0<alignedD 2 (1027/1250)+1/10000 by linarith [hs.1])
    (show 0<(1/10000:ℝ)-alignedD 2 (1027/1250) by linarith [hs.2])
  have hq := sq_nonneg ((B-1027/1250)/2+alignedD 2 (1027/1250))
  nlinarith [References.L_minimum.1]

lemma L_aligned {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (901/1000:ℝ)<aligned 2 B := by
  by_cases he : B≤3/5
  · exact L_aligned_early ⟨hB.1,he⟩
  · exact L_aligned_late ⟨by linarith,hB.2⟩

lemma high_aligned (r : Row) (hr : r≠1) {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1801/2000:ℝ)<aligned r B := by
  fin_cases r
  · exact J_aligned hB
  · exact (hr rfl).elim
  · have h := L_aligned hB
    change (1801/2000:ℝ)<aligned 2 B
    linarith

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite
end
end
end

section
/-!
## Continuous supports for the original source-secondary owner

The positive- and negative-angle supports
are obtained by subtracting the literal core slope times the original
weak margin.  The auxiliary sum estimates concern the same original
core and outer coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Source
open CommonQuarter CorePairGeometry Arithmetic

def positive (r : Row) (A B x : ℝ) : ℝ := x+c r+(F r).outer B+
  g r*(1/2+(1/2-B)*Real.cos x+(1/2-A)*Real.sin x)
def positiveD (r : Row) (A B x : ℝ) : ℝ :=
  1-g r*((A-1/2)*Real.cos x-(B-1/2)*Real.sin x)
def negative (r : Row) (A B x : ℝ) : ℝ := -x+c r+(F r).outer B+
  g r*(1/2+(1/2-B)*Real.cos x+(A+1/2)*Real.sin x)
def negativeD (r : Row) (A B x : ℝ) : ℝ :=
  -1+g r*((B-1/2)*Real.sin x+(A+1/2)*Real.cos x)

lemma positive_hasDerivAt (r : Row) (A B x : ℝ) :
    HasDerivAt (positive r A B) (positiveD r A B x) x := by
  have h : HasDerivAt (positive r A B)
      (1+g r*((1/2-B)*(-Real.sin x)+(1/2-A)*Real.cos x)) x :=
    (((hasDerivAt_id' (x:=x)).add_const (c r)).add_const ((F r).outer B)).fun_add
      (((((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).fun_add
        ((Real.hasDerivAt_sin x).const_mul (1/2-A))).const_mul (g r))
  exact h.congr_deriv (by simp only [positiveD]; ring)

lemma negative_hasDerivAt (r : Row) (A B x : ℝ) :
    HasDerivAt (negative r A B) (negativeD r A B x) x := by
  have h : HasDerivAt (negative r A B)
      (-1+g r*((1/2-B)*(-Real.sin x)+(A+1/2)*Real.cos x)) x :=
    (((hasDerivAt_id' (x:=x)).fun_neg.add_const (c r)).add_const ((F r).outer B)).fun_add
      (((((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).fun_add
        ((Real.hasDerivAt_sin x).const_mul (A+1/2))).const_mul (g r))
  exact h.congr_deriv (by simp only [negativeD]; ring)

lemma initial_positive (r : Row) (A B : ℝ) : positive r A B 0=aligned r B := by
  simp only [positive,aligned,Real.sin_zero,Real.cos_zero]
  ring

lemma initial_negative (r : Row) (A B : ℝ) : negative r A B 0=aligned r B := by
  simp only [negative,aligned,Real.sin_zero,Real.cos_zero]
  ring

lemma outer_sum_axial {A B : ℝ} (ht : OuterState A B) : outerAxial≤A+B := by
  have hA : 0≤A := ht.1.trans ht.2.1
  have hprod := mul_nonneg hA ht.1
  have hAx : 0≤outerAxial := by linarith [outer_endpoint_bounds.1]
  by_contra! hn
  have hs := mul_pos (show 0<outerAxial-(A+B) by linarith)
    (show 0<outerAxial+(A+B)+1 by linarith [ht.1])
  nlinarith [ht.2.2,axial_circle]

lemma outer_sum_late {A B : ℝ} (ht : OuterState A B) (hB : (3/20:ℝ)≤B) :
    (3/2:ℝ)<A+B := by
  have hA : (3/20:ℝ)≤A := hB.trans ht.2.1
  have hprod := mul_nonneg (show 0≤A-3/20 by linarith) (show 0≤B-3/20 by linarith)
  by_contra! hn
  have hs := pow_le_pow_left₀ (show 0≤A+B by linarith) hn 2
  have hc := ht.2.2
  norm_num [Q0] at hc
  nlinarith

lemma harmonic_norm (r : Row) {A B : ℝ}
    (hr : r=2 ∨ (r=0 ∧ (3/20:ℝ)≤B)) (ht : OuterState A B) :
    (g r*(A-1/2))^2+(-g r*(B-1/2))^2<1 := by
  have he : (g r*(A-1/2))^2+(-g r*(B-1/2))^2=
      (g r)^2*(Q0-2*(A+B)) := by
    linear_combination (g r)^2*ht.2.2
  rw [he]
  rcases hr with rfl | ⟨rfl,hB⟩
  · have hh := outer_sum_axial ht
    norm_num [g,Q0]
    linarith [fine_outer_endpoint_bounds.1]
  · have hh := outer_sum_late ht hB
    norm_num [g,Q0]
    linarith

lemma positive_derivative (r : Row) {A B x : ℝ}
    (hr : r=2 ∨ (r=0 ∧ (3/20:ℝ)≤B)) (ht : OuterState A B) :
    0<positiveD r A B x := by
  have hh := FramePairCalculus.harmonic_projection_lt_one (x := x)
    (A:=-g r*(B-1/2)) (B:=g r*(A-1/2)) (by linarith [harmonic_norm r hr ht])
  simp only [positiveD]
  linarith

lemma negative_derivative (r : Row) (hr : r≠1) {A B x : ℝ}
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (8/25)) :
    0<negativeD r A B x := by
  have hp : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have tr := positive_trig hp
  have hA : (1399/1000:ℝ)<A+1/2 := by
    linarith [(outer_bounds ht).1,fine_outer_endpoint_bounds.2]
  have hsquare := pow_le_pow_left₀ hx.1 hx.2 2
  have hcos : (593/625:ℝ)≤Real.cos x := by
    linarith [Real.one_sub_sq_div_two_le_cos (x:=x)]
  have hAc := mul_le_mul hA.le hcos (by norm_num : (0:ℝ)≤593/625)
    (by linarith : 0≤A+1/2)
  have hBs := mul_nonneg ht.1 tr.2.2.1
  have hsi : Real.sin x≤(8/25:ℝ) := tr.2.2.2.2.1.trans hx.2
  simp only [negativeD]
  rcases (show r=0 ∨ r=2 by fin_cases r <;> simp_all) with rfl | rfl <;>
    norm_num [g] <;> linarith

lemma positive_lower (r : Row) {A B x : ℝ}
    (hr : r=2 ∨ (r=0 ∧ (3/20:ℝ)≤B))
    (ht : OuterState A B) (hx : x∈Icc 0 (7/10)) :
    (1801/2000:ℝ)<positive r A B x := by
  have hm : MonotoneOn (positive r A B) (Icc 0 (7/10)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t _ => (positive_hasDerivAt r A B t).continuousAt.continuousWithinAt)
      (fun t _ => positive_hasDerivAt r A B t)
      (fun t _ => (positive_derivative r hr ht).le)
  have hh := hm (by norm_num) hx hx.1
  rw [initial_positive] at hh
  have hr1 : r≠1 := by rcases hr with rfl | ⟨rfl,_⟩ <;> decide
  exact (high_aligned r hr1 ⟨ht.1,(outer_bounds ht).2.2.2.1⟩).trans_le hh

lemma negative_lower (r : Row) (hr : r≠1) {A B x : ℝ}
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (8/25)) :
    (1801/2000:ℝ)<negative r A B x := by
  have hm : MonotoneOn (negative r A B) (Icc (0:ℝ) (8/25)) :=
    monoOn_of_hasDeriv_nonneg
      (fun t _ => (negative_hasDerivAt r A B t).continuousAt.continuousWithinAt)
      (fun t _ => negative_hasDerivAt r A B t)
      (fun t ht' => (negative_derivative r hr ht (Ioo_subset_Icc_self ht')).le)
  have hh := hm (by norm_num) hx hx.1
  rw [initial_negative] at hh
  exact (high_aligned r hr ⟨ht.1,(outer_bounds ht).2.2.2.1⟩).trans_le hh

lemma J_small_line {B : ℝ} (hB : B∈Icc (0:ℝ) (3/20)) : J 0+B≤J B := by
  let f : ℝ → ℝ := fun t => J t-t
  have hdom {t : ℝ} (ht : t∈Icc (0:ℝ) (3/20)) : t∈Icc 0 outerDiagonal :=
    Asymmetric.rational_outer_mem ⟨ht.1,by linarith [ht.2]⟩
  have hd {t : ℝ} (ht : t∈Icc (0:ℝ) (3/20)) : HasDerivAt f (JLabel.d1 t-1) t :=
    (JLabel.outer_hasDerivAt (outer_domain (hdom ht))).sub (hasDerivAt_id t)
  have hm : MonotoneOn f (Icc (0:ℝ) (3/20)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun t ht => (hd ht).continuousAt.continuousWithinAt
    · exact fun t ht => hd (Ioo_subset_Icc_self ht)
    · intro t ht
      have hh := J_first_antitone (hdom (Ioo_subset_Icc_self ht))
        (hdom (by norm_num)) ht.2.le
      linarith [References.J_small_slope]
  have hh := hm (by norm_num) hB hB.1
  dsimp [f] at hh
  linarith

lemma J_small_positive {A B x : ℝ} (ht : OuterState A B)
    (hB : B≤3/20) (hx : x∈Icc 0 (7/10)) :
    (17953/20000:ℝ)<positive 0 A B x := by
  have tr := positive_trig hx
  have hJ := J_small_line ⟨ht.1,hB⟩
  rw [J_zero] at hJ
  have hA := mul_le_mul_of_nonneg_right (outer_bounds ht).2.1 tr.2.2.1
  have hAx := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le tr.2.2.1
  have hsquare := pow_le_pow_left₀ hx.1 hx.2 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=x)
  have hsin := Real.sin_le hx.1
  have hBcos := mul_nonneg ht.1 (sub_nonneg.mpr tr.2.1)
  have hlinear := mul_nonneg (show 0≤1-(103981/100000:ℝ)*(283/200-1/2) by norm_num) hx.1
  change (17953/20000:ℝ)<x+125/100000+J B+
    (103981/100000)*(1/2+(1/2-B)*Real.cos x+(1/2-A)*Real.sin x)
  linarith [outer_endpoint_bounds.2.1]

lemma P_line {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1239/50000:ℝ)+(773/1000)*B≤P B := by
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) :
      HasDerivAt (fun y => P y-(773/1000)*y) (PLabel.d1 t-773/1000) t := by
    have h := (PLabel.outer_hasDerivAt (outer_domain ht)).fun_sub
      ((hasDerivAt_id' (x:=t)).const_mul (773/1000:ℝ))
    rw [mul_one] at h
    exact h
  have hm : MonotoneOn (fun y => P y-(773/1000)*y) (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1])
  have hh := hm outer_zero_mem hB hB.1
  have hz : P 0-(773/1000)*0=(1239/50000:ℝ) := by
    norm_num [P,RoleLabel.outer,RoleLabel.eval,PLabel]
  simp only at hh
  rw [hz] at hh
  linarith

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Source
end
end
end

section
/-!
## All three opposite mixed zero rows with their original source owner

The P row is paid directly by the sum of the
two original transverse coordinates.  J and L use the continuous
supports and aligned bounds.  The negative-angle geometric cap is
derived from the same weak owner before it is used analytically.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Source
open CommonQuarter CorePairGeometry Arithmetic

lemma positive_sum {b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    1-(109/100)*x≤b+B := by
  have tr := positive_trig hx
  have hA := mul_le_mul_of_nonneg_right (outer_bounds ht).2.1 tr.2.2.1
  have hAx := mul_le_mul_of_nonneg_right outer_endpoint_bounds.2.1.le tr.2.2.1
  have hB := mul_nonneg ht.1 (sub_nonneg.mpr tr.2.1)
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=x)
  have hsin := Real.sin_le hx.1
  have hquad := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  linarith

lemma negative_sum {b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (8/25))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    1+(259/200)*x≤b+B := by
  have tr := positive_trig (show x∈Icc 0 (7/10) from ⟨hx.1,by linarith [hx.2]⟩)
  have hA : (899/1000:ℝ)≤A := by
    linarith [(outer_bounds ht).1,fine_outer_endpoint_bounds.2]
  have hAs := mul_le_mul_of_nonneg_right hA tr.2.2.1
  have hB := mul_nonneg ht.1 (sub_nonneg.mpr tr.2.1)
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=x)
  have hsin := Real.sin_ge_sub_cube hx.1
  have hquad := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hsquare := pow_le_pow_left₀ hx.1 hx.2 2
  have hcube := mul_le_mul_of_nonneg_right hsquare hx.1
  linarith

lemma P_positive {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)<x+c 1+g 1*b+(F 1).outer B := by
  have hsum := positive_sum ht hx hm
  have hP := P_line ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hb : b<(559/1000:ℝ) := by
    linarith [(CoreAngleEndpoint.state_bounds hs).2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  change (17953/20000:ℝ)<x+19555/100000+(63132/100000)*b+P B
  nlinarith [hx.1]

lemma P_negative {a b A B x : ℝ} (hs : CoreState a b) (ht : OuterState A B)
    (hx : x∈Icc (0:ℝ) (8/25))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)< -x+c 1+g 1*b+(F 1).outer B := by
  have hsum := negative_sum ht hx hm
  have hP := P_line ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hb : b<(559/1000:ℝ) := by
    linarith [(CoreAngleEndpoint.state_bounds hs).2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
  change (17953/20000:ℝ)< -x+19555/100000+(63132/100000)*b+P B
  nlinarith [hx.1]

theorem positive_original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b+A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  by_cases hP : r=1
  · subst r
    exact P_positive hs ht hx hm
  · have hsep := mul_nonneg (slope_bounds r).1.le (sub_nonneg.mpr hm)
    have he : positive r A B x≤x+c r+g r*b+(F r).outer B := by
      dsimp [positive]
      nlinarith only [hsep]
    by_cases hJ : r=0 ∧ B≤3/20
    · obtain ⟨rfl,hB⟩ := hJ
      exact (J_small_positive ht hB hx).trans_le he
    · have hr : r=2 ∨ (r=0 ∧ (3/20:ℝ)≤B) := by
        fin_cases r <;> simp_all
        linarith
      exact (by linarith [positive_lower r hr ht hx] :
        (17953/20000:ℝ)<positive r A B x).trans_le he

theorem negative_original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤b-A*Real.sin x+B*Real.cos x) :
    (17953/20000:ℝ)< -x+c r+g r*b+(F r).outer B := by
  have hcap := ShortMixedZero.CoreContact.original_angle_cut hs ht hx hm
  have hsmall : x∈Icc (0:ℝ) (8/25) := ⟨hx.1,by simpa [ShortMixedZero.CoreContact.cap] using hcap.le⟩
  by_cases hP : r=1
  · subst r
    exact P_negative hs ht hsmall hm
  · have hsep := mul_nonneg (slope_bounds r).1.le (sub_nonneg.mpr hm)
    have hl := negative_lower r hP ht hsmall
    dsimp [negative] at hl
    nlinarith only [hl,hsep]

theorem original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : |x|≤7/10)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  have hm' : pairWidth x≤b+A*Real.sin x+B*Real.cos x := by
    norm_num [Eight.forwardMargin] at hm
    linarith
  by_cases hp : 0≤x
  · have hx' : x∈Icc 0 (7/10) := ⟨hp,(abs_le.mp hx).2⟩
    have hw := signed_width hx
    rw [abs_of_nonneg (positive_trig hx').2.2.1] at hw
    apply positive_original r hs ht hx'
    rw [hw] at hm'
    linarith
  · have hx' : -x∈Icc 0 (7/10) := ⟨by linarith,by linarith [(abs_le.mp hx).1]⟩
    have hsin : Real.sin x≤0 := by
      have hh := (positive_trig hx').2.2.1
      simpa only [Real.sin_neg,neg_nonneg] using hh
    have hw := signed_width hx
    rw [abs_of_nonpos hsin] at hw
    have hh := negative_original r hs ht hx' (by
      rw [hw] at hm'
      simp only [Real.sin_neg,Real.cos_neg,mul_neg,sub_neg_eq_add]
      linarith)
    simpa only [neg_neg] using hh

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Source
end
end
end

section
/-!
## The two first-feasible corner references

These are the fixed `.41` J comparison and
the `.377` L comparison from §§8.2 and 10.3 of the written proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.BoundaryReferences
open CommonQuarter CorePairGeometry Arithmetic
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra Target.ReferenceAlgebra

local macro "boundary_reference" : tactic => `(tactic|
  norm_num [coreBox,outerBox,sinBox,cosBox,outerLabelBox,inverseBox,boundaryBox,
    labelBox,coordinate,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    F,c,g,JLabel,LLabel,Q0,cap])

private lemma r94_mpr_lo {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).lo = S.lo := by subst e; rfl
private lemma r94_mpr_hi {x y : ℝ} (e : x = y) (h : Interval x = Interval y) (S : Interval y) :
    (Eq.mpr h S).hi = S.hi := by subst e; rfl

private lemma r94_coordinate_eq {y : ℝ} : ShortOuterOne.SameContact.arc y = U y-1/2 := by
  dsimp [U]; ring
private lemma r94_coordinate_lo {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).lo = (Y.sub (Interval.point (1/2))).lo :=
  r94_mpr_lo r94_coordinate_eq (congrArg _ r94_coordinate_eq) _
private lemma r94_coordinate_hi {y : ℝ} (Y : Interval (U y)) :
    (coordinate Y).hi = (Y.sub (Interval.point (1/2))).hi :=
  r94_mpr_hi r94_coordinate_eq (congrArg _ r94_coordinate_eq) _

private lemma r94_label_eq (H : RoleLabel) {y : ℝ} :
    H.outer y = H.c+H.p*(ShortOuterOne.SameContact.arc y)+H.q*y+H.r*y^2+
      H.s*(ShortOuterOne.SameContact.arc y*y) := by
  dsimp [RoleLabel.outer,RoleLabel.eval]; ring
private lemma r94_labelBox_lo (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).lo = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).lo :=
  r94_mpr_lo (r94_label_eq H) (congrArg _ (r94_label_eq H)) _
private lemma r94_labelBox_hi (H : RoleLabel) {y : ℝ} (Y : Interval y) (X : Interval (U y)) :
    (labelBox H Y X).hi = (((((Interval.point H.c).add ((Interval.point H.p).mul (coordinate X))).add
      ((Interval.point H.q).mul Y)).add ((Interval.point H.r).mul Y.square)).add
        ((Interval.point H.s).mul ((coordinate X).mul Y))).hi :=
  r94_mpr_hi (r94_label_eq H) (congrArg _ (r94_label_eq H)) _

private lemma r94_U_diagonal : U outerDiagonal=outerDiagonal+1/2 := by
  rw [U,ShortOuterOne.SameContact.arc_diagonal]

/-- The outer coordinate box at the diagonal, with explicit endpoints. -/
private def r94_UBox : Interval (U outerDiagonal) :=
  ⟨outerBox.lo+1/2,outerBox.hi+1/2,by
    rw [r94_U_diagonal]; exact ⟨by linarith [outerBox.mem.1],by linarith [outerBox.mem.2]⟩⟩

private lemma r94_interval_eq {x : ℝ} (I J : Interval x) (h1 : I.lo=J.lo) (h2 : I.hi=J.hi) :
    I=J := by
  cases I; cases J; simp_all

private lemma r94_outerLabelBox_eq (r : Row) :
    outerLabelBox r=labelBox (F r) outerBox r94_UBox := by
  unfold outerLabelBox
  dsimp only
  congr 1
  apply r94_interval_eq
  · rw [r94_mpr_lo r94_U_diagonal]; rfl
  · rw [r94_mpr_hi r94_U_diagonal]; rfl

private lemma r94_outerLabelBox_lo (r : Row) :
    (outerLabelBox r).lo=(labelBox (F r) outerBox r94_UBox).lo := by
  rw [r94_outerLabelBox_eq]
private lemma r94_outerLabelBox_hi (r : Row) :
    (outerLabelBox r).hi=(labelBox (F r) outerBox r94_UBox).hi := by
  rw [r94_outerLabelBox_eq]
private lemma r94_UBox_lo : r94_UBox.lo=outerBox.lo+1/2 := rfl
private lemma r94_UBox_hi : r94_UBox.hi=outerBox.hi+1/2 := rfl

attribute [local simp ↓] r94_coordinate_lo r94_coordinate_hi r94_labelBox_lo r94_labelBox_hi
  r94_outerLabelBox_lo r94_outerLabelBox_hi r94_UBox_lo r94_UBox_hi

lemma J_first :
    (4528/5000:ℝ)< -(41/100)+c 0+J outerDiagonal+g 0/2 ∧
    (8999/10000:ℝ)< -cap+c 0+J outerDiagonal+g 0*(5249/10000) ∧
    (5249/10000:ℝ)< inverse CoreAngleEndpoint.diagonal outerDiagonal (41/100) := by
  let V₀ := (((Interval.point (-(41/100:ℝ))).add (Interval.point (c 0))).add
    (outerLabelBox 0)).add (Interval.point (g 0/2))
  let V₁ := (((Interval.point (-cap)).add (Interval.point (c 0))).add
    (outerLabelBox 0)).add (Interval.point (g 0*(5249/10000)))
  have hc : 0<(cosBox (41/100) (by norm_num)).lo := by boundary_reference
  let I := inverseBox coreBox outerBox (sinBox (41/100) (by norm_num))
    (cosBox (41/100) (by norm_num)) hc
  have h0 : (4528/5000:ℝ)<V₀.lo := by dsimp only [V₀]; boundary_reference
  have h1 : (8999/10000:ℝ)<V₁.lo := by dsimp only [V₁]; boundary_reference
  have hI : (5249/10000:ℝ)<I.lo := by dsimp only [I]; boundary_reference
  exact ⟨h0.trans_le V₀.mem.1,h1.trans_le V₁.mem.1,hI.trans_le I.mem.1⟩

lemma L_first : (1126/1250:ℝ)<boundary 2 CoreAngleEndpoint.diagonal outerDiagonal (377/1000) ∧
    0<(Real.sin (377/1000))^2-g 2*(outerDiagonal-1/2)*Real.sin (377/1000)+
      g 2*(CoreAngleEndpoint.diagonal+1/2)-1 ∧
    (9/25:ℝ)<Real.sin (377/1000) ∧
    1/2+(13/12)*Real.sin (377/1000)<outerDiagonal := by
  have hc : 0<(cosBox (377/1000) (by norm_num)).lo := by boundary_reference
  let V := boundaryBox 2 coreBox (by norm_num : (0:ℝ)≤377/1000) hc
  let S := sinBox (377/1000) (by norm_num)
  let N := ((S.square.sub (((Interval.point (g 2)).mul
    (outerBox.sub (Interval.point (1/2)))).mul S)).add
      ((Interval.point (g 2)).mul (coreBox.add (Interval.point (1/2))))).sub
        (Interval.point 1)
  let J := (Interval.point (1/2)).add ((Interval.point (13/12)).mul S)
  have hv : (1126/1250:ℝ)<V.lo := by dsimp only [V]; boundary_reference
  have hn : (0:ℝ)<N.lo := by dsimp only [N,S]; boundary_reference
  have hs : (9/25:ℝ)<S.lo := by dsimp only [S]; boundary_reference
  have hj : J.hi<outerBox.lo := by dsimp only [J,S]; boundary_reference
  exact ⟨hv.trans_le V.mem.1,hn.trans_le N.mem.1,hs.trans_le S.mem.1,
    J.mem.2.trans_lt (hj.trans_le outerBox.mem.1)⟩

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.Target.BoundaryReferences
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.TargetPositive
open CommonQuarter CorePairGeometry Arithmetic

lemma transverse_sum {a b B x : ℝ} (hs : CoreState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤a*Real.sin x+b*Real.cos x+B) :
    1-x/12-x^2/4≤b+B ∧ 1-(31/120)*x≤b+B := by
  have tr := positive_trig hx
  have hc := CoreAngleEndpoint.state_bounds hs
  have ha := mul_le_mul_of_nonneg_right hc.2.1 tr.2.2.1
  have hb := mul_nonneg hc.2.2.1 (sub_nonneg.mpr tr.2.1)
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=x)
  have hsin := Real.sin_le hx.1
  have hquad := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  constructor <;> linarith

theorem original_projection (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : (1+Real.sin x+Real.cos x)/2≤a*Real.sin x+b*Real.cos x+B) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  have hsum := transverse_sum hs hx hm
  have hB : B∈Icc 0 outerDiagonal := ⟨ht.1,(outer_bounds ht).2.2.2.1⟩
  have hslope : 0<1-(31/120)*g r := by
    have hg := slope_bounds r
    linarith [hg.2]
  have hpay := mul_le_mul_of_nonneg_left hsum.2 (slope_bounds r).1.le
  have hbound : aligned r B+(1-(31/120)*g r)*x≤
      x+c r+g r*b+(F r).outer B := by
    dsimp [aligned]
    nlinarith only [hpay]
  by_cases hP : r=1
  · subst r
    by_cases hlarge : (3/50:ℝ)≤x
    · have hxpay := mul_le_mul_of_nonneg_left hlarge hslope.le
      have hl := P_aligned hB
      have hg : g 1=63132/100000 := rfl
      rw [hg] at hbound hxpay ⊢
      linarith
    · have hb : b<(559/1000:ℝ) := by
        linarith [(CoreAngleEndpoint.state_bounds hs).2.2.2.2,CoreAngleEndpoint.diagonal_bounds.2]
      have hsquare := pow_le_pow_left₀ hx.1 (le_of_not_ge hlarge) 2
      have htarget : (87/200:ℝ)≤B := by linarith [hsum.1]
      have hl := P_aligned_late hB htarget
      have hnon := mul_nonneg hslope.le hx.1
      linarith
  · have hl := high_aligned r hP hB
    have hnon := mul_nonneg hslope.le hx.1
    linarith

theorem original (r : Row) {a b A B x : ℝ}
    (hs : CoreState a b) (ht : OuterState A B) (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B 1 (-1) x) :
    (17953/20000:ℝ)<x+c r+g r*b+(F r).outer B := by
  have hangle : |x|≤7/10 := abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have hw : pairWidth x=(1+Real.sin x+Real.cos x)/2 := by
    rw [signed_width hangle,abs_of_nonneg (positive_trig hx).2.2.1]
    ring
  apply original_projection r hs ht hx
  norm_num [Eight.forwardMargin] at hm
  rw [hw] at hm
  linarith

end SquaresInCircles.Eight.SecondWord.MixedZero.Opposite.TargetPositive
end
end
end
