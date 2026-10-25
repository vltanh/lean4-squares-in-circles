module

public import SquaresInCircles.Eight.Frames.Low.HighParallel

/-!
# Eight squares: explicit quarter-contact calculus with the original high target fixed

The continued source coordinate lies in `[-.25,.13]` throughout the
strip.  Its marker has derivative between `.95` and `1.09` there.
The positive-angle contact cost increases.  At negative angles it
decreases whenever the target primary coordinate is at most `1.03`;
the remaining target arc has a separate strict marker reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowHighQuarterCalculus
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameLowHighParallelCalculus FrameLowHighParallelBounds

def sourceDomain : Set ℝ := Icc (-(1/4:ℝ)) (13/100)
def cost (positive : Bool) (B x : ℝ) : ℝ :=
  x-(9/50)*(FrameLowHighParallelCalculus.width positive x-1)+L (height positive (A B) x)+G (A B)
def costD (positive : Bool) (B x : ℝ) : ℝ :=
  1-(9/50)*widthD positive x-Ld (height positive (A B) x)*P positive (A B) x

theorem height_eq (positive : Bool) {B : ℝ} (hB : B∈Icc b2 c0) (x : ℝ) :
    height positive (A B) x=FrameLowHighParallelCalculus.width positive x-B*Real.sin x-A B*Real.cos x := by
  rw [height,extended_involution (high_extended hB)]

theorem width_bounds (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    1≤FrameLowHighParallelCalculus.width positive x ∧ FrameLowHighParallelCalculus.width positive x≤101/100 := by
  have hlo : 1≤FrameLowHighParallelCalculus.width positive x := by rw [width_eq positive hx]; exact FrameCoreArc.width_one_le x
  have ht := trig_small positive hx
  refine ⟨hlo,?_⟩
  cases positive <;> dsimp [FrameLowHighParallelCalculus.width] <;> linarith [ht.1,ht.2.1,ht.2.2.2.1]

theorem height_domain (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) : height positive (A B) x∈sourceDomain := by
  have ht := trig_small positive hx
  have hw := width_bounds positive hx
  have ha := high_bounds hB
  have hBn : 0≤B := b2_mem.1.trans hB.1
  have hAn : 0≤A B := by linarith [ha.2.2.1]
  have hBsU := mul_le_mul_of_nonneg_left ht.2.1 hBn
  have hBsL := mul_le_mul_of_nonneg_left ht.1 hBn
  have hAcU := mul_le_mul_of_nonneg_left ht.2.2.2.1 hAn
  have hAcL := mul_le_mul
    (show (899/1000:ℝ)≤A B by linarith [ha.2.2.1]) ht.2.2.1
    (by norm_num : (0:ℝ)≤4999/5000) hAn
  rw [height_eq positive hB]
  constructor <;> nlinarith [ha.2.1,ha.2.2.2]

theorem source_derivative_bounds {z : ℝ} (hz : z∈sourceDomain) :
    (19/20:ℝ)<Ld z ∧ Ld z<109/100 := by
  have he : z∈extendedDomain := ⟨hz.1,by linarith [hz.2]⟩
  have hc := extended_circle he
  have hp := extended_shift_pos he
  have hsq := pow_le_pow_left₀ (show 0≤z+1/2 by linarith [hz.1])
    (show z+1/2≤63/100 by linarith [hz.2]) 2
  have hA : (15/8:ℝ)<A z+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hr0 : 0≤ slope z := div_nonneg (by linarith [hz.1]) hp.le
  have hrU : slope z<42/125 := by
    apply (div_lt_iff₀ hp).2
    linarith [hz.2]
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  constructor <;> linarith

theorem source_label_monotone : MonotoneOn L (Icc (-(1/4:ℝ)) b1) := by
  have he z (hz : z∈Icc (-(1/4:ℝ)) b1) : z∈extendedDomain :=
    ⟨hz.1,by linarith [hz.2,b1_bounds.2]⟩
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (extended_L_deriv (he z hz)).continuousAt.continuousWithinAt
  · exact fun z hz => extended_L_deriv (he z (Ioo_subset_Icc_self hz))
  · intro z hz
    have hr := extended_slope_monotone (he z (Ioo_subset_Icc_self hz))
      (low_extended (show b1∈Icc 0 b1 from ⟨b1_mem.1,le_rfl⟩)) hz.2.le
    have hbound := slope_bounds (show b1∈Icc 0 b1 from ⟨b1_mem.1,le_rfl⟩)
    dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
    linarith

theorem cost_deriv (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) : HasDerivAt (cost positive B) (costD positive B x) x := by
  have hz := height_domain positive hB hx
  have he : height positive (A B) x∈extendedDomain := ⟨hz.1,by linarith [hz.2]⟩
  have h := (((hasDerivAt_id' x).fun_sub
    (((width_deriv positive x).sub_const 1).const_mul (9/50))).fun_add
      ((extended_L_deriv he).comp x (height_deriv positive (A B) x))).add_const (G (A B))
  refine h.congr_deriv ?_
  simp only [costD]
  ring

theorem positive_derivative {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain true) : 0<costD true B x := by
  have ht := trig_small true hx
  have hw := widthD_bounds true hx
  have hd := source_derivative_bounds (height_domain true hB hx)
  have hBc := mul_le_mul_of_nonneg_left ht.2.2.2.1 (b2_mem.1.trans hB.1)
  have hAs := mul_nonneg (by linarith [(A_high_bounds hB).1,c0_bounds.1] : 0≤A B) ht.2.2.2.2
  have hp : P true (A B) x≤4101/10000 := by
    rw [P,extended_involution (high_extended hB)]
    linarith [hB.2,c0_bounds.2,hw.1]
  have hm0 := mul_le_mul_of_nonneg_left hp (by linarith [hd.1] : 0≤Ld (height true (A B) x))
  have hm1 := mul_le_mul_of_nonneg_right hd.2.le (by norm_num : (0:ℝ)≤4101/10000)
  dsimp [costD]
  nlinarith [hw.2]

theorem high_transverse_lower {B : ℝ} (hB : B∈Icc b2 c0)
    (hcap : A B≤103/100) : (3/4:ℝ)<B := by
  have hc := extended_circle (high_extended hB)
  have hA := extended_shift_pos (high_extended hB)
  have hAsq := pow_le_pow_left₀ hA.le (show A B+1/2≤153/100 by linarith) 2
  by_contra! hbad
  have hBsq := pow_le_pow_left₀ (by linarith [hB.1,b2_bounds.1] : 0≤B+1/2)
    (show B+1/2≤5/4 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem negative_derivative {B x : ℝ} (hB : B∈Icc b2 c0)
    (hcap : A B≤103/100) (hx : x∈angleDomain false) : costD false B x<0 := by
  have ht := trig_small false hx
  have hw := widthD_bounds false hx
  have hd := source_derivative_bounds (height_domain false hB hx)
  have hBlarge := high_transverse_lower hB hcap
  have hBc := mul_le_mul hBlarge.le ht.2.2.1 (by norm_num : (0:ℝ)≤4999/5000)
    (by linarith : 0≤B)
  have hAs := mul_nonpos_of_nonneg_of_nonpos
    (by linarith [(A_high_bounds hB).1,c0_bounds.1] : 0≤A B) ht.2.2.2.2
  have hp : (4959/4000:ℝ)≤P false (A B) x := by
    rw [P,extended_involution (high_extended hB)]
    linarith [hw.2]
  have hm := mul_le_mul hd.1.le hp (by norm_num : (0:ℝ)≤4959/4000)
    (by linarith [hd.1] : 0≤Ld (height false (A B) x))
  dsimp [costD]
  nlinarith [hw.1]

theorem G_monotone : MonotoneOn G extendedDomain := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun z hz => (G_deriv hz).continuousAt.continuousWithinAt
  · exact fun z hz => G_deriv (Ioo_subset_Icc_self hz)
  · intro z hz
    have hr : 0≤ FrameLowArc.slope z := div_nonneg
      (by linarith [hz.1])
      (extended_shift_pos (Ioo_subset_Icc_self hz)).le
    dsimp [Gd,FrameHighArc.u,FrameHighArc.v]
    linarith

theorem G_reference : (229/250:ℝ)<G (103/100) := by
  have he : (103/100:ℝ)∈extendedDomain := by constructor <;> norm_num [extendedDomain]
  have hc := extended_circle he
  have hp := extended_shift_pos he
  have hA : A (103/100)<151/200 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤251/200)
      (show (251/200:ℝ)≤A (103/100)+1/2 by linarith) 2
    norm_num [Q0] at hc
    nlinarith
  dsimp [G,FrameHighArc.u,FrameHighArc.v]
  linarith [Arithmetic.pi_hand_enclosure.1,diagonal_precise.2]

theorem target_chart {B : ℝ} (hB : B∈Icc b2 c0) : A B∈extendedDomain := by
  have hh := A_high_bounds hB
  constructor <;> linarith [hh.1,hh.2,c0_bounds.1,a2_bounds.2]

end SquaresInCircles.Eight.FrameLowHighQuarterCalculus
