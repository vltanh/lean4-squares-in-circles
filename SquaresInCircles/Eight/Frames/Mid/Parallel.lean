module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Core.MidGeometry

/-!
# Eight squares: the complete middle/middle opposite-sign transverse contact region

The exact parallel minimum is extended to the entire square of middle
coordinates by the two actual marker slopes.  The original separating
margin then controls the distance from the parallel line.  This avoids
an implicit contact curve, minimizer switches, and any angular partition.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameMidParallel
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameCoreArc
open FramePairCalculus FrameCoreMidGeometry

def parallelValue : ℝ := M b2+M (1-b2)
def parallelSum (b : ℝ) : ℝ := M b+M (1-b)
def cost (b B x : ℝ) : ℝ :=
  x-(9/50)*periodicFrameCost x+M b+M B
def margin (b B x : ℝ) : ℝ :=
  b+A B*Real.sin x+B*Real.cos x-pairWidth x

theorem complement_bounds : b1<1-b2 ∧ 1-b2<b2 := by
  constructor <;> linarith [b1_bounds.2,b2_bounds.1,b2_bounds.2]

theorem complement_mem : 1-b2∈Icc b1 b2 :=
  ⟨complement_bounds.1.le,complement_bounds.2.le⟩

theorem reflected_mem {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    b∈Icc b1 b2 ∧ 1-b∈Icc b1 b2 := by
  refine ⟨⟨complement_bounds.1.le.trans hb.1,hb.2⟩,?_,?_⟩
  · linarith [hb.2,complement_bounds.1]
  · linarith [hb.1]

theorem Md_lower {b : ℝ} (hb : b∈Icc b1 b2) : (69/100:ℝ)<Md b := by
  have hh := slope_mid_bounds hb
  dsimp [Md,p,q]
  linarith

theorem Md_deriv {b : ℝ} (hb : b∈Icc b1 b2) :
    HasDerivAt Md (p*FrameCircleArc.Add b) b := by
  have hh := ((Ad_hasDerivAt ⟨b1_mem.1.trans hb.1,hb.2.trans b2_mem.2⟩
    ).const_mul p).const_add q
  convert hh using 1
  funext y
  simp only [Md,Ad,FrameLowArc.slope]
  ring

theorem marker_growth_lower {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (horder : b≤B) :
    (69/100)*(B-b)≤M B-M b := by
  have hm : MonotoneOn (fun z => M z-(69/100)*z) (Icc b1 b2) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact ((M_deriv hz).sub ((hasDerivAt_id z).const_mul (69/100))).continuousAt.continuousWithinAt
    · intro z hz
      exact (M_deriv (Ioo_subset_Icc_self hz)).sub
        ((hasDerivAt_id z).const_mul (69/100))
    · intro z hz
      linarith [Md_lower (Ioo_subset_Icc_self hz)]
  have hh := hm hb hB horder
  linarith

theorem marker_growth_upper {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (horder : b≤B) :
    M B-M b≤(449/500)*(B-b) := by
  have hm : MonotoneOn (fun z => (449/500)*z-M z) (Icc b1 b2) := by
    apply monoOn_of_hasDeriv_nonneg
    · intro z hz
      exact (((hasDerivAt_id z).const_mul (449/500)).sub (M_deriv hz)).continuousAt.continuousWithinAt
    · intro z hz
      exact ((hasDerivAt_id z).const_mul (449/500)).sub
        (M_deriv (Ioo_subset_Icc_self hz))
    · intro z hz
      linarith [(Md_bounds (Ioo_subset_Icc_self hz)).2]
  have hh := hm hb hB horder
  linarith

theorem parallelSum_deriv {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    HasDerivAt parallelSum (Md b-Md (1-b)) b := by
  have hh := reflected_mem hb
  have hr : HasDerivAt (fun z : ℝ => 1-z) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub 1
  have h := (M_deriv hh.1).fun_add ((M_deriv hh.2).comp b hr)
  convert h using 1
  · funext y
    simp only [parallelSum,Function.comp_apply]
  · ring

theorem parallelSum_second {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    HasDerivAt (fun z => Md z-Md (1-z)) (p*FrameCircleArc.Add b+p*FrameCircleArc.Add (1-b)) b := by
  have hh := reflected_mem hb
  have hr : HasDerivAt (fun z : ℝ => 1-z) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub 1
  have h := (Md_deriv hh.1).fun_sub ((Md_deriv hh.2).comp b hr)
  convert h using 1
  · funext y
    simp only [Function.comp_apply]
  · ring

theorem parallelSum_concave : ConcaveOn ℝ (Icc (1-b2) b2) parallelSum := by
  apply concave_of_deriv2 (fun b hb => parallelSum_deriv hb)
    (fun b hb => parallelSum_second hb)
  intro b hb
  have hh := reflected_mem hb
  have h1 := Add_negative ⟨b1_mem.1.trans hh.1.1,hh.1.2.trans b2_mem.2⟩
  have h2 := Add_negative ⟨b1_mem.1.trans hh.2.1,hh.2.2.trans b2_mem.2⟩
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by norm_num [p]) h1.le)
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num [p]) h2.le)

theorem parallel_minimum {b : ℝ} (hb : b∈Icc (1-b2) b2) :
    parallelValue≤M b+M (1-b) := by
  have hh := parallelSum_concave.min_le_of_mem_Icc
    ⟨le_rfl,complement_bounds.2.le⟩ ⟨complement_bounds.2.le,le_rfl⟩ hb
  have hleft : parallelSum (1-b2)=parallelValue := by
    simp [parallelSum,parallelValue,add_comm]
  have hright : parallelSum b2=parallelValue := rfl
  rw [hleft,hright,min_self] at hh
  exact hh

theorem complement_primary_lower : (303904031/250000000:ℝ)<A (1-b2) := by
  have hc := A_circle
    ⟨b1_mem.1.trans complement_mem.1,complement_mem.2.trans b2_mem.2⟩
  have ha := A_mid_bounds complement_mem
  have hb : 0≤(1-b2)+1/2 := by linarith [b2_bounds.2]
  have hbU : (1-b2)+1/2≤3/2-(3/7)*(59962803/50000000:ℝ) := by
    dsimp [b2]
    linarith [a2_bounds.1]
  have hsB := pow_le_pow_left₀ hb hbU 2
  by_contra! hbad
  have hsA := pow_le_pow_left₀ (show 0≤A (1-b2)+1/2 by linarith [ha.1,a2_bounds.1])
    (show A (1-b2)+1/2≤(303904031/250000000:ℝ)+1/2 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem parallelValue_lower : (22281/25000:ℝ)<parallelValue := by
  have ha := complement_primary_lower
  have he : parallelValue=2*cM+q+p*(a2+A (1-b2)) := by
    dsimp [parallelValue,M]
    rw [A_b2]
    ring
  rw [he]
  dsimp [cM,p,q]
  linarith [a2_bounds.1]

/-- A global lower support below the parallel contact line. -/
theorem sum_below_parallel {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (hsum : b+B≤1) :
    parallelValue-(449/500)*(1-b-B)≤M b+M B := by
  by_cases hB0 : 1-b2≤B
  · have hB' : B∈Icc (1-b2) b2 := ⟨hB0,hB.2⟩
    have href := (reflected_mem hB').2
    have hg := marker_growth_upper hb href (by linarith)
    have he := parallel_minimum hB'
    linarith
  · have hg1 := marker_growth_upper hb ⟨b1_lt_b2.le,le_rfl⟩ hb.2
    have hg2 := marker_growth_upper hB complement_mem (lt_of_not_ge hB0).le
    dsimp [parallelValue]
    linarith

/-- A global lower support above the parallel contact line. -/
theorem sum_above_parallel {b B : ℝ} (hb : b∈Icc b1 b2)
    (hB : B∈Icc b1 b2) (hsum : 1≤b+B) :
    parallelValue+(69/100)*(b+B-1)≤M b+M B := by
  have hB' : B∈Icc (1-b2) b2 := ⟨by linarith [hb.2],hB.2⟩
  have href := (reflected_mem hB').2
  have hg := marker_growth_lower href hb (by linarith)
  have he := parallel_minimum hB'
  linarith

theorem positive_deficit {b B x : ℝ} (hB : B∈Icc b1 b2)
    (hx : x∈Icc (0:ℝ) (8/25)) (hm : 0≤ margin b B x) :
    1-b-B≤(20679/25000)*x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hxq
  have hb := middle_bounds hB
  have hs := Real.sin_le hx.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hA := mul_le_mul_of_nonneg_right
    (show A B-1/2≤799/1000 by linarith [hb.2.2.2]) ht.1
  have hB' := mul_le_mul_of_nonneg_right
    (show 1/2-B≤22/125 by linarith [hb.1])
    (show 0≤1-Real.cos x by linarith [ht.2.2.2])
  have hx2 := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  dsimp [margin] at hm
  rw [(first_width hxq).1] at hm
  linarith

theorem positive_region {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (0:ℝ) (8/25)) (hm : 0≤ margin b B x) :
    parallelValue≤cost b B x := by
  have hd := positive_deficit hB hx hm
  have hsum : parallelValue-(449/500)*(20679/25000)*x≤M b+M B := by
    by_cases hs : b+B≤1
    · have hh := sum_below_parallel hb hB hs
      linarith
    · have hh := sum_above_parallel hb hB (lt_of_not_ge hs).le
      linarith [hx.1]
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,FrameLowPair.pi_lower]⟩
  have hcharge : (9/50)*periodicFrameCost x≤(9/100)*x := by
    rw [(first_width hxq).2]
    linarith [Real.sin_le hx.1,Real.cos_le_one x]
  dsimp [cost]
  linarith [hx.1]

theorem negative_surplus {b B z : ℝ} (hB : B∈Icc b1 b2)
    (hz : z∈Icc (0:ℝ) (1/20)) (hm : 0≤ margin b B (-z)) :
    (169/100)*z≤b+B-1 := by
  have hzq : z∈Icc 0 (Real.pi/2) :=
    ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hzq
  have hb := middle_bounds hB
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hA := mul_le_mul_of_nonneg_right
    (show (1699/1000:ℝ)≤A B+1/2 by linarith [hb.2.2.1]) ht.1
  have hB' := mul_le_mul_of_nonneg_right
    (show -(22/125:ℝ)≤B-1/2 by linarith [hb.1])
    (show 0≤1-Real.cos z by linarith [ht.2.2.2])
  have hz2 := mul_nonneg hz.1 (sub_nonneg.mpr hz.2)
  have hzsq := pow_le_pow_left₀ hz.1 hz.2 2
  have hz3 := mul_le_mul_of_nonneg_right hzsq hz.1
  dsimp [margin,pairWidth] at hm
  simp only [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg ht.1,
    abs_of_nonneg ht.2.2.1] at hm
  nlinarith

theorem negative_region {b B z : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hz : z∈Icc (0:ℝ) (1/20)) (hm : 0≤ margin b B (-z)) :
    parallelValue≤cost b B (-z) := by
  have hd := negative_surplus hB hz hm
  have hsum : 1≤b+B := by linarith [hz.1]
  have hs := sum_above_parallel hb hB hsum
  have hzq : z∈Icc 0 (Real.pi/2) :=
    ⟨hz.1,by linarith [hz.2,FrameLowPair.pi_lower]⟩
  have ht := FrameLowPair.quadrant hzq
  have hcharge : (9/50)*periodicFrameCost (-z)≤(9/100)*z := by
    dsimp [periodicFrameCost]
    simp only [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg ht.1,
      abs_of_nonneg ht.2.2.1]
    linarith [Real.sin_le hz.1,Real.cos_le_one z]
  dsimp [cost]
  linarith [hz.1]

/-- The full original contact strip, including both signs of its angle. -/
theorem contact_strip {b B x : ℝ} (hb : b∈Icc b1 b2) (hB : B∈Icc b1 b2)
    (hx : x∈Icc (-(1/20:ℝ)) (8/25)) (hm : 0≤ margin b B x) :
    (557/625:ℝ)<cost b B x := by
  have hh : parallelValue≤cost b B x := by
    by_cases hp : 0≤x
    · exact positive_region hb hB ⟨hp,hx.2⟩ hm
    · have hz : -x∈Icc (0:ℝ) (1/20) := ⟨by linarith,by linarith [hx.1]⟩
      simpa only [neg_neg] using negative_region hb hB hz (by simpa using hm)
  exact (lt_trans (by norm_num) parallelValue_lower).trans_le hh

end SquaresInCircles.Eight.FrameMidParallel
