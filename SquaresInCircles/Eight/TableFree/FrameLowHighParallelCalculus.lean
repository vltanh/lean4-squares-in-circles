module

public import SquaresInCircles.Eight.TableFree.FrameLowHighExtendedAligned
public import SquaresInCircles.Eight.TableFree.FrameLowHighGeometry

/-!
# Explicit source-contact calculus in the parallel strip

At a fixed original target, contact determines the source transverse
coordinate explicitly.  The circle markers are evaluated on slightly
enlarged scalar domains.  All derivative signs below are proved from
the actual target arc and the displayed source-coordinate bounds.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowHighParallelCalculus
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus

def angleDomain (positive : Bool) : Set ℝ :=
  if positive then Icc (0:ℝ) (1/50) else Icc (-(1/50:ℝ)) 0
def width (positive : Bool) (x : ℝ) : ℝ :=
  if positive then (1+Real.sin x+Real.cos x)/2 else (1-Real.sin x+Real.cos x)/2
def widthD (positive : Bool) (x : ℝ) : ℝ :=
  if positive then (Real.cos x-Real.sin x)/2 else (-Real.cos x-Real.sin x)/2
def height (positive : Bool) (B x : ℝ) : ℝ :=
  width positive x-A B*Real.sin x-B*Real.cos x
def P (positive : Bool) (B x : ℝ) : ℝ :=
  A B*Real.cos x-B*Real.sin x-widthD positive x

theorem width_deriv (positive : Bool) (x : ℝ) :
    HasDerivAt (width positive) (widthD positive x) x := by
  cases positive
  · convert ((((Real.hasDerivAt_sin x).neg).const_add 1).add
      (Real.hasDerivAt_cos x)).div_const 2 using 1 <;> dsimp [width,widthD] <;> ring
  · convert (((Real.hasDerivAt_sin x).const_add 1).add
      (Real.hasDerivAt_cos x)).div_const 2 using 1 <;> dsimp [width,widthD] <;> ring

theorem height_deriv (positive : Bool) (B x : ℝ) :
    HasDerivAt (height positive B) (-P positive B x) x := by
  convert ((width_deriv positive x).sub ((Real.hasDerivAt_sin x).const_mul (A B))).sub
    ((Real.hasDerivAt_cos x).const_mul B) using 1 <;> dsimp [height,P] <;> ring

theorem trig_small (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    -(1/50:ℝ)≤Real.sin x ∧ Real.sin x≤1/50 ∧
      (4999/5000:ℝ)≤Real.cos x ∧ Real.cos x≤1 ∧
        (if positive then 0≤Real.sin x else Real.sin x≤0) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hcu := Real.cos_le_one x
  cases positive with
  | false =>
      have hz : -x∈Icc (0:ℝ) (1/50) := by
        dsimp [angleDomain] at hx
        constructor <;> linarith [hx.1,hx.2]
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
        (by linarith [hz.2,FrameLowPair.pi_lower])
      have hsu := Real.sin_le_self hz.1
      have hsq := pow_le_pow_left₀ hz.1 hz.2 2
      simp only [Real.sin_neg,neg_sq] at hs hsu hsq
      simp only [Bool.false_eq_true,ite_false]
      repeat' constructor <;> nlinarith [hz.2]
  | true =>
      have hz : x∈Icc (0:ℝ) (1/50) := by simpa [angleDomain] using hx
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
        (by linarith [hz.2,FrameLowPair.pi_lower])
      have hsu := Real.sin_le_self hz.1
      have hsq := pow_le_pow_left₀ hz.1 hz.2 2
      simp only [ite_true]
      repeat' constructor <;> nlinarith [hz.2]

theorem width_eq (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    width positive x=pairWidth x := by
  have ht := trig_small positive hx
  cases positive
  · simp [width,pairWidth,abs_of_nonpos ht.2.2.2.2,
      abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos x)]
  · simp [width,pairWidth,abs_of_nonneg ht.2.2.2.2,
      abs_of_nonneg (by linarith [ht.2.2.1] : 0≤Real.cos x)]

theorem widthD_bounds (positive : Bool) {x : ℝ} (hx : x∈angleDomain positive) :
    if positive then (4899/10000:ℝ)≤widthD positive x ∧ widthD positive x≤1/2
    else -(1/2:ℝ)≤widthD positive x ∧ widthD positive x≤-(4899/10000:ℝ) := by
  have ht := trig_small positive hx
  cases positive <;> dsimp [widthD] at * <;> constructor <;> linarith

theorem P_positive (positive : Bool) {B x : ℝ} (hB : B∈Icc 0 c0)
    (hx : x∈angleDomain positive) : 0<P positive B x := by
  have ht := trig_small positive hx
  have hw := widthD_bounds positive hx
  have hA := A_bounds hB
  have hAc := mul_le_mul
    (show (899/1000:ℝ)≤A B by linarith [hA.1,c0_bounds.1]) ht.2.2.1
    (by norm_num : (0:ℝ)≤4999/5000) (by linarith [hA.1,c0_bounds.1] : 0≤A B)
  have hBs := mul_le_mul_of_nonneg_left ht.2.1 hB.1
  have hBup : B≤9/10 := by linarith [hB.2,c0_bounds.2]
  dsimp [P]
  cases positive <;> dsimp at hw <;> nlinarith

theorem height_antitone (positive : Bool) {B : ℝ} (hB : B∈Icc 0 c0) :
    AntitoneOn (height positive B) (angleDomain positive) := by
  cases positive <;> dsimp [angleDomain]
  all_goals apply antiOn_of_hasDeriv_nonpos
  all_goals try exact fun x _ => (height_deriv _ B x).continuousAt.continuousWithinAt
  all_goals try exact fun x _ => height_deriv _ B x
  all_goals intro x hx
  all_goals have hh := P_positive _ hB (Ioo_subset_Icc_self hx)
  all_goals linarith

@[simp] theorem height_zero (positive : Bool) (B : ℝ) : height positive B 0=1-B := by
  cases positive <;> simp [height,width]

theorem low_derivative_bounds {b : ℝ} (hb : b∈Icc (0:ℝ) (7/20)) :
    (89/100:ℝ)<Ld b ∧ Ld b<109/100 := by
  have hd : b∈extendedDomain := by constructor <;> linarith [hb.1,hb.2]
  have hc := extended_circle hd
  have hp := extended_shift_pos hd
  have hbsq := pow_le_pow_left₀ (by linarith [hb.1] : 0≤b+1/2)
    (show b+1/2≤17/20 by linarith [hb.2]) 2
  have hA : (89/50:ℝ)<A b+1/2 := by
    by_contra! hbad
    have hh := pow_le_pow_left₀ hp.le hbad 2
    norm_num [Q0] at hc
    nlinarith
  have hr0 : 0≤slope b := div_nonneg (by linarith [hb.1]) hp.le
  have hrU : slope b<12/25 := by
    apply (div_lt_iff₀ hp).2
    linarith [hb.2,hA]
  dsimp [Ld,FrameLowArc.u,FrameLowArc.v]
  constructor <;> linarith

theorem high_derivative_bounds {b : ℝ} (hb : b∈Icc (16/25:ℝ) (93/100)) :
    (39/50:ℝ)<Hd b ∧ Hd b<99/100 := by
  have hd : b∈extendedDomain := by constructor <;> linarith [hb.1,hb.2]
  have hc := extended_circle hd
  have hp := extended_shift_pos hd
  have hbL : (57/50:ℝ)≤b+1/2 := by linarith [hb.1]
  have hbU : b+1/2≤143/100 := by linarith [hb.2]
  have hsqL := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤57/50) hbL 2
  have hsqU := pow_le_pow_left₀ (by linarith [hbL] : 0≤b+1/2) hbU 2
  have hA : (34/25:ℝ)<A b+1/2 ∧ A b+1/2<81/50 := by
    constructor
    · by_contra! hbad
      have hh := pow_le_pow_left₀ hp.le hbad 2
      norm_num [Q0] at hc
      nlinarith
    · by_contra! hbad
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤81/50) hbad 2
      norm_num [Q0] at hc
      nlinarith
  have hrL : (7/10:ℝ)<slope b := by
    apply (lt_div_iff₀ hp).2
    linarith [hA.2,hbL]
  have hrU : slope b<143/136 := by
    apply (div_lt_iff₀ hp).2
    linarith [hA.1,hbU]
  dsimp [Hd,FrameHighArc.u,FrameHighArc.v]
  constructor <;> linarith

theorem low_label_monotone : MonotoneOn L (Icc (0:ℝ) (7/20)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (extended_L_deriv (by constructor <;> linarith [hb.1,hb.2])).continuousAt.continuousWithinAt
  · intro b hb
    exact extended_L_deriv (by constructor <;> linarith [hb.1,hb.2])
  · exact fun b hb => (low_derivative_bounds (Ioo_subset_Icc_self hb)).1.le

theorem high_label_monotone : MonotoneOn H (Icc (16/25:ℝ) (93/100)) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact (extended_H_deriv (by constructor <;> linarith [hb.1,hb.2])).continuousAt.continuousWithinAt
  · intro b hb
    exact extended_H_deriv (by constructor <;> linarith [hb.1,hb.2])
  · exact fun b hb => (high_derivative_bounds (Ioo_subset_Icc_self hb)).1.le

theorem low_target_primary_upper {B : ℝ} (hB : B∈Icc 0 b1)
    (hBl : (717/10000:ℝ)<B) : A B<279/200 := by
  have hc := A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤5717/10000)
    (show (5717/10000:ℝ)≤B+1/2 by linarith) 2
  by_contra! hbad
  have hA := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤379/200)
    (show (379/200:ℝ)≤A B+1/2 by linarith) 2
  norm_num [Q0] at hc
  nlinarith

theorem high_target_P (positive : Bool) {B x : ℝ} (hB : B∈Icc b2 c0)
    (hx : x∈angleDomain positive) :
    if positive then P positive B x<711/1000 else (69/50:ℝ)<P positive B x := by
  have ht := trig_small positive hx
  have hw := widthD_bounds positive hx
  have hA := high_bounds hB
  have hB0 : 0≤B := b2_mem.1.trans hB.1
  cases positive with
  | false =>
      have hAc := mul_le_mul
        (show (899/1000:ℝ)≤A B by linarith [hA.2.2.1]) ht.2.2.1
        (by norm_num : (0:ℝ)≤4999/5000) (by linarith [hA.2.2.1] : 0≤A B)
      have hBs := mul_nonpos_of_nonneg_of_nonpos hB0 ht.2.2.2.2
      dsimp [P] at *
      linarith
  | true =>
      have hAc := mul_le_mul_of_nonneg_left ht.2.2.2.1 (by linarith [hA.2.2.1] : 0≤A B)
      have hBs := mul_nonneg hB0 ht.2.2.2.2
      dsimp [P] at *
      linarith

theorem low_target_P (positive : Bool) {B x : ℝ} (hB : B∈Icc 0 b1)
    (hBl : positive=true → (717/10000:ℝ)<B) (hx : x∈angleDomain positive) :
    if positive then P positive B x<453/500 else (177/100:ℝ)<P positive B x := by
  have ht := trig_small positive hx
  have hw := widthD_bounds positive hx
  have hA := A_low_bounds hB
  cases positive with
  | false =>
      have hAc := mul_le_mul
        (show (129/100:ℝ)≤A B by linarith [hA.1,a1_precise.1]) ht.2.2.1
        (by norm_num : (0:ℝ)≤4999/5000) (by linarith [hA.1,a1_precise.1] : 0≤A B)
      have hBs := mul_nonpos_of_nonneg_of_nonpos hB.1 ht.2.2.2.2
      dsimp [P] at *
      linarith
  | true =>
      have hAu := low_target_primary_upper hB (hBl rfl)
      have hAc := mul_le_mul_of_nonneg_left ht.2.2.2.1 (by linarith [hA.1,a1_precise.1] : 0≤A B)
      have hBs := mul_nonneg hB.1 ht.2.2.2.2
      dsimp [P] at *
      linarith

end SquaresInCircles.Eight.TableFree.FrameLowHighParallelCalculus
