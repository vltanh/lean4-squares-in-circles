module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeAligned

/-!
# Continuous supports for the original source-secondary owner

Uncompiled source draft.  The positive- and negative-angle supports
are obtained by subtracting the literal core slope times the original
weak margin.  The auxiliary sum estimates concern the same original
core and outer coordinates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Source
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
  convert ((((hasDerivAt_id x).add_const (c r)).add_const ((F r).outer B)).add
    (((((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
      ((Real.hasDerivAt_sin x).const_mul (1/2-A))).const_mul (g r)))
    using 1 <;> dsimp [positive,positiveD] <;> ring

lemma negative_hasDerivAt (r : Row) (A B x : ℝ) :
    HasDerivAt (negative r A B) (negativeD r A B x) x := by
  convert (((((hasDerivAt_id x).neg).add_const (c r)).add_const ((F r).outer B)).add
    (((((Real.hasDerivAt_cos x).const_mul (1/2-B)).const_add (1/2)).add
      ((Real.hasDerivAt_sin x).const_mul (A+1/2))).const_mul (g r)))
    using 1 <;> dsimp [negative,negativeD] <;> ring

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
    (show 0<outerAxial+(A+B)+1 by linarith)
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
  have hh := FramePairCalculus.harmonic_projection_lt_one (x := x) (harmonic_norm r hr ht)
  dsimp [positiveD]
  nlinarith

lemma negative_derivative (r : Row) (hr : r≠1) {A B x : ℝ}
    (ht : OuterState A B) (hx : x∈Icc (0:ℝ) (8/25)) :
    0<negativeD r A B x := by
  have hp : x∈Icc 0 (7/10) := ⟨hx.1,by linarith [hx.2]⟩
  have tr := positive_trig hp
  have hA : (1399/1000:ℝ)<A+1/2 := by
    linarith [(outer_bounds ht).1,fine_outer_endpoint_bounds.2]
  have hsquare := pow_le_pow_left₀ hx.1 hx.2 2
  have hcos : (593/625:ℝ)≤Real.cos x := by linarith [cos_lower_two hx.1]
  have hAc := mul_le_mul hA.le hcos (by norm_num : (0:ℝ)≤593/625)
    (by linarith : 0≤A+1/2)
  have hBs := mul_nonneg ht.1 tr.2.2.1
  have hsi : Real.sin x≤(8/25:ℝ) := tr.2.2.2.2.1.trans hx.2
  dsimp [negativeD]
  fin_cases r <;> norm_num [g] at hr ⊢ <;> nlinarith

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
  have hcos := cos_lower_two hx.1
  have hsin := Real.sin_le hx.1
  have hBcos := mul_nonneg ht.1 (sub_nonneg.mpr tr.2.1)
  have hlinear := mul_nonneg (show 0≤1-(103981/100000:ℝ)*(283/200-1/2) by norm_num) hx.1
  change (17953/20000:ℝ)<x+125/100000+J B+
    (103981/100000)*(1/2+(1/2-B)*Real.cos x+(1/2-A)*Real.sin x)
  nlinarith [outer_endpoint_bounds.2.1]

lemma P_line {B : ℝ} (hB : B∈Icc 0 outerDiagonal) :
    (1239/50000:ℝ)+(773/1000)*B≤P B := by
  let f : ℝ → ℝ := fun t => P t-(773/1000)*t
  have hd {t : ℝ} (ht : t∈Icc 0 outerDiagonal) : HasDerivAt f (PLabel.d1 t-773/1000) t :=
    (PLabel.outer_hasDerivAt (outer_domain ht)).sub ((hasDerivAt_id t).const_mul (773/1000))
  have hm : MonotoneOn f (Icc 0 outerDiagonal) :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd ht).continuousAt.continuousWithinAt)
      (fun t ht => hd (Ioo_subset_Icc_self ht))
      (fun t ht => by linarith [(P_first_bounds (Ioo_subset_Icc_self ht)).1])
  have hh := hm outer_zero_mem hB hB.1
  have hz : f 0=(1239/50000:ℝ) := by
    norm_num [f,P,RoleLabel.outer,RoleLabel.eval,PLabel]
  rw [hz] at hh
  dsimp [f] at hh
  linarith

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Source
