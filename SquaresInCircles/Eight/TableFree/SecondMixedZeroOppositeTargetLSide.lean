module

public import SquaresInCircles.Eight.TableFree.SecondMixedZeroOppositeTargetCorner

/-!
# The uniform L side-loss estimate

Uncompiled source draft.  This is §4.2 of the table-free replacement:
complete one square in the angle derivative, integrate the resulting
uniform lower slope, then use the single aligned tangent parabola.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.LSide
open CommonQuarter CorePairGeometry Arithmetic

def n (B : ℝ) : ℝ := (13/12)*g 2-1-(g 2)^2*(B-1/2)^2/4
def K (B : ℝ) : ℝ :=
  9010079/10000000-(1/10000)*(B-1027/1250)+(1/4)*(B-1027/1250)^2+(273/500)*n B
def K₁ (B : ℝ) : ℝ :=
  -(1/10000)+(1/2)*(B-1027/1250)-(273/1000)*(g 2)^2*(B-1/2)

lemma slope_lower {B x : ℝ} (hx : x∈angles) :
    n B/(Real.cos x)^2≤boundary₁ 2 (7/12) B x := by
  have hden : 0<(Real.cos x)^2 := sq_pos_of_pos (by linarith [(cosine_bounds hx).1])
  have hn : n B≤(Real.sin x)^2-g 2*(B-1/2)*Real.sin x+g 2*((7/12:ℝ)+1/2)-1 := by
    dsimp [n]
    nlinarith [sq_nonneg (Real.sin x-g 2*(B-1/2)/2)]
  apply (div_le_div_iff₀ hden hden).2
  exact mul_le_mul_of_nonneg_right hn hden.le

lemma negative_late {B : ℝ} (hB : (1/2:ℝ)≤B) (hn : n B<0) : (21/25:ℝ)<B := by
  by_contra! hu
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hB)
    (show B-1/2≤(17/50:ℝ) by linarith) 2
  norm_num [n,g] at hn
  nlinarith

lemma nonnegative_case {B x : ℝ} (hB : B∈Icc (1/2:ℝ) outerDiagonal)
    (hx : x∈angles) (hn : 0≤n B) : (17953/20000:ℝ)<boundary 2 (7/12) B x := by
  have hm : MonotoneOn (boundary 2 (7/12) B) angles :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (boundary_hasDerivAt 2 (7/12) B ht).continuousAt.continuousWithinAt)
      (fun t ht => boundary_hasDerivAt 2 (7/12) B (Ioo_subset_Icc_self ht))
      (fun t ht => (div_nonneg hn (sq_nonneg (Real.cos t))).trans
        (slope_lower (Ioo_subset_Icc_self ht)))
  have hh := hm (by norm_num [angles,cap]) hx hx.1
  rw [boundary_zero] at hh
  linarith [L_aligned ⟨by linarith [hB.1],hB.2⟩]

lemma negative_slope {B x : ℝ} (hx : x∈angles) (hn : n B<0) :
    n B/(81/100)≤boundary₁ 2 (7/12) B x := by
  have hc := (cosine_bounds hx).2
  have hden : 0<(Real.cos x)^2 := by linarith
  have hh : n B/(81/100)≤n B/(Real.cos x)^2 := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<81/100) hden).2
    exact mul_le_mul_of_nonpos_left hc.le hn.le
  exact hh.trans (slope_lower hx)

lemma uniform_loss {B x : ℝ} (hx : x∈angles) (hn : n B<0) :
    aligned 2 B+(273/500)*n B<boundary 2 (7/12) B x := by
  let E : ℝ→ℝ := fun t => boundary 2 (7/12) B t-(n B/(81/100))*t
  have hd (t : ℝ) (ht : t∈angles) :
      HasDerivAt E (boundary₁ 2 (7/12) B t-n B/(81/100)) t :=
    (boundary_hasDerivAt 2 (7/12) B ht).sub ((hasDerivAt_id t).const_mul (n B/(81/100)))
  have hm : MonotoneOn E angles :=
    monoOn_of_hasDeriv_nonneg
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => hd t (Ioo_subset_Icc_self ht))
      (fun t ht => sub_nonneg.mpr (negative_slope (Ioo_subset_Icc_self ht) hn))
  have hh := hm (by norm_num [angles,cap]) hx hx.1
  have h0 : E 0=aligned 2 B := by simp only [E,mul_zero,sub_zero,boundary_zero]
  rw [h0] at hh
  have hcoef : x/(81/100)<(273/500:ℝ) := by
    dsimp [cap] at hx
    linarith [hx.2]
  have hp := mul_lt_mul_of_neg_right hcoef hn
  dsimp [E] at hh
  nlinarith

lemma aligned_tangent {B : ℝ} (hB : B∈Icc (21/25:ℝ) outerDiagonal) :
    9010079/10000000-(1/10000)*(B-1027/1250)+(1/4)*(B-1027/1250)^2<aligned 2 B := by
  have ht := L_aligned_tangent ⟨by linarith [hB.1],hB.2⟩
  have hs := (abs_lt.mp References.L_minimum.2).1
  have hp := mul_pos (show 0<alignedD 2 (1027/1250)+1/10000 by linarith)
    (show 0<B-1027/1250 by linarith [hB.1])
  nlinarith [References.L_minimum.1]

lemma K_hasDerivAt (B : ℝ) : HasDerivAt K (K₁ B) B := by
  have hn : HasDerivAt n (-(g 2)^2*(B-1/2)/2) B := by
    convert (((((hasDerivAt_id B).sub_const (1/2)).pow 2).const_mul ((g 2)^2/4)).
      const_sub ((13/12)*g 2-1)) using 1 <;> dsimp [n] <;> ring
  convert (((((hasDerivAt_id B).sub_const (1027/1250)).const_mul (1/10000)).
    const_sub (9010079/10000000)).add
      ((((hasDerivAt_id B).sub_const (1027/1250)).pow 2).const_mul (1/4))).add
        (hn.const_mul (273/500)) using 1 <;> dsimp [K,K₁] <;> ring

lemma K_first_negative {B : ℝ} (hB : B∈Icc (21/25:ℝ) (9/10)) : K₁ B<0 := by
  norm_num [K₁,g]
  linarith [hB.2]

lemma K_lower {B : ℝ} (hB : B∈Icc (21/25:ℝ) (9/10)) : (17953/20000:ℝ)<K B := by
  have hm : AntitoneOn K (Icc (21/25:ℝ) (9/10)) :=
    antiOn_of_hasDeriv_nonpos
      (fun t _ => (K_hasDerivAt t).continuousAt.continuousWithinAt)
      (fun t _ => K_hasDerivAt t)
      (fun t ht => (K_first_negative (Ioo_subset_Icc_self ht)).le)
  have hh := hm hB (by norm_num) hB.2
  have he : (17953/20000:ℝ)<K (9/10) := by norm_num [K,n,g]
  exact he.trans_le hh

lemma boundary_lower {B x : ℝ} (hB : B∈Icc (1/2:ℝ) outerDiagonal) (hx : x∈angles) :
    (17953/20000:ℝ)<boundary 2 (7/12) B x := by
  by_cases hn : 0≤n B
  · exact nonnegative_case hB hx hn
  · have hneg : n B<0 := lt_of_not_ge hn
    have hlate := negative_late hB.1 hneg
    have ht := aligned_tangent ⟨hlate.le,hB.2⟩
    have hk := K_lower ⟨hlate.le,by linarith [hB.2,outer_endpoint_bounds.2.2.2]⟩
    have hl := uniform_loss hx hneg
    dsimp [K] at hk
    linarith

lemma side {x b : ℝ} (hx : x∈angles) (hb : b∈Icc (0:ℝ) (1/2))
    (hf : contact (7/12) b x≤outerDiagonal) : (17953/20000:ℝ)<sideCost 2 x b := by
  rw [side_as_boundary 2 hx]
  exact boundary_lower ⟨side_contact_lower hx hb,hf⟩ hx

end SquaresInCircles.Eight.TableFree.SecondWord.MixedZero.Opposite.Target.LSide
