module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperAligned

/-!
# Both high-source primary target signs below the quarter turn

The original weak margin bounds one explicit contact height.  On
the full angle interval `[-.4,0]` this height decreases to its aligned
value, and its cost has strictly negative derivative.  The continued
upper marker supplies a scalar comparison even when the contact
passes below the intrinsic diagonal; no physical recoding is used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryNegative
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus
open FrameHighLowPrimaryGeometry FrameHighLowUpperAligned

def domain : Set ℝ := Icc (-(2/5:ℝ)) 0
def W (x : ℝ) : ℝ := (1-Real.sin x+Real.cos x)/2
def height (k : Bool) (B x : ℝ) : ℝ :=
  W x-A B*Real.sin x+sign k*B*Real.cos x
def P (k : Bool) (B x : ℝ) : ℝ :=
  (A B+1/2)*Real.cos x+(1/2+sign k*B)*Real.sin x
def F (k : Bool) (B x : ℝ) : ℝ :=
  x-(9/50)*(W x-1)+G (height k B x)-sign k*L B
def Fd (k : Bool) (B x : ℝ) : ℝ :=
  1+(9/100)*(Real.cos x+Real.sin x)-Gd (height k B x)*P k B x

theorem width_actual {x : ℝ} (hx : x∈domain) :
    W x=pairWidth x ∧ W x-1=periodicFrameCost x := by
  have hh := negative_width
    (show x∈Icc (-(54/125:ℝ)) 0 from ⟨by linarith [hx.1],hx.2⟩)
  constructor
  · simpa [W] using hh.1.symm
  · rw [hh.2]
    dsimp [W]
    ring

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    -(2/5:ℝ)≤Real.sin x ∧ Real.sin x≤0 ∧ (23/25:ℝ)≤Real.cos x := by
  have hz : -x∈Icc (0:ℝ) (2/5) := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,FrameLowPair.pi_lower])
  have hu := Real.sin_le hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hz.1 hz.2 2
  simp only [Real.sin_neg,neg_sq] at hs hu hsq
  refine ⟨?_,?_,?_⟩ <;> linarith [hz.2]

theorem height_deriv (k : Bool) (B x : ℝ) :
    HasDerivAt (height k B) (-P k B x) x := by
  have hw := (((Real.hasDerivAt_sin x).const_sub 1).fun_add (Real.hasDerivAt_cos x)).div_const 2
  have h := (hw.fun_sub ((Real.hasDerivAt_sin x).const_mul (A B))).fun_add
    ((Real.hasDerivAt_cos x).const_mul (sign k*B))
  exact h.congr_deriv (by simp only [P]; ring)

@[simp] theorem height_zero (k : Bool) (B : ℝ) : height k B 0=1+sign k*B := by
  simp [height,W]

theorem P_lower (k : Bool) {B x : ℝ} (hB : B∈Icc 0 b1) (hx : x∈domain) :
    (33/25:ℝ)<P k B x := by
  have ht := trig_bounds hx
  have hA := A_low_bounds hB
  have hAc := mul_le_mul
    (show (899/500:ℝ)≤A B+1/2 by linarith [hA.1,a1_precise.1]) ht.2.2
    (by norm_num : (0:ℝ)≤23/25) (by linarith [hA.1,a1_precise.1] : 0≤A B+1/2)
  have hcoef : 0≤1/2+sign k*B ∧ 1/2+sign k*B≤33/40 := by
    cases k <;> dsimp [sign] <;> constructor <;> linarith [hB.1,hB.2,b1_bounds.2]
  have hprod := mul_le_mul hcoef.2
    (show -Real.sin x≤2/5 by linarith [ht.1])
    (by linarith [ht.2.1] : 0≤-Real.sin x) (by norm_num : (0:ℝ)≤33/40)
  dsimp [P]
  nlinarith

theorem height_antitone (k : Bool) {B : ℝ} (hB : B∈Icc 0 b1) :
    AntitoneOn (height k B) domain := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (height_deriv k B x).continuousAt.continuousWithinAt
  · exact fun x _ => height_deriv k B x
  · intro x hx
    linarith [P_lower k hB (Ioo_subset_Icc_self hx)]

theorem contact_le (k : Bool) {z B x : ℝ} (hx : x∈domain)
    (hm : 0≤upperMargin k z B x) : height k B x≤z := by
  dsimp [height,upperMargin] at *
  rw [(width_actual hx).1]
  linarith

theorem contact_domain (k : Bool) {z B x t : ℝ}
    (hz : z∈sourceDomain) (hB : B∈Icc 0 b1) (hx : x∈domain)
    (hm : 0≤upperMargin k z B x) (ht : t∈Icc x 0) :
    height k B t∈lowerDomain := by
  have htd : t∈domain := ⟨hx.1.trans ht.1,ht.2⟩
  have hzero := height_antitone k hB htd
    (show (0:ℝ)∈domain by constructor <;> norm_num [domain]) ht.2
  have hstart := height_antitone k hB hx htd ht.1
  rw [height_zero] at hzero
  have hweak := contact_le k hx hm
  constructor
  · cases k <;> dsimp [sign] at hzero <;> linarith [hB.1,hB.2,b1_bounds.2]
  · linarith [hz.2]

theorem F_deriv (k : Bool) {B x : ℝ} (hz : height k B x∈lowerDomain) :
    HasDerivAt (F k B) (Fd k B x) x := by
  have hw := (((Real.hasDerivAt_sin x).const_sub 1).fun_add (Real.hasDerivAt_cos x)).div_const 2
  have h := (((hasDerivAt_id' x).fun_sub ((hw.sub_const 1).const_mul (9/50))).fun_add
    ((G_deriv (lower_extended hz)).comp x (height_deriv k B x))).sub_const (sign k*L B)
  exact h.congr_deriv (by simp only [Fd]; ring)

theorem Fd_negative (k : Bool) {B x : ℝ} (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hz : height k B x∈lowerDomain) : Fd k B x<0 := by
  have hp := P_lower k hB hx
  have hg := lower_Gd hz
  have hm := mul_le_mul hg.le hp.le (by norm_num : (0:ℝ)≤33/25)
    (by linarith : 0≤Gd (height k B x))
  dsimp [Fd]
  linarith [(trig_bounds hx).2.1,Real.cos_le_one x]

theorem move_to_zero (k : Bool) {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : x∈domain) (hm : 0≤upperMargin k z B x) :
    F k B 0≤F k B x := by
  have ha : AntitoneOn (F k B) (Icc x 0) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun t ht => (F_deriv k (contact_domain k hz hB hx hm ht)).continuousAt.continuousWithinAt
    · exact fun t ht => F_deriv k (contact_domain k hz hB hx hm (Ioo_subset_Icc_self ht))
    · intro t ht
      exact (Fd_negative k hB ⟨hx.1.trans ht.1.le,ht.2.le⟩
        (contact_domain k hz hB hx hm (Ioo_subset_Icc_self ht))).le
  exact ha ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2

theorem weak_separator (k : Bool) {z B x : ℝ} (hz : z∈sourceDomain)
    (hB : B∈Icc 0 b1) (hx : x∈domain) (hm : 0≤upperMargin k z B x) :
    (8833/10000:ℝ)<upperCost k z B x := by
  have hzero := contact_domain k hz hB hx hm (show (0:ℝ)∈Icc x 0 from ⟨hx.2,le_rfl⟩)
  rw [height_zero] at hzero
  have hF0 : F k B 0=G (1+sign k*B)-sign k*L B := by
    simp only [F,height_zero,W,Real.sin_zero,Real.cos_zero]; ring
  have haligned : (8833/10000:ℝ)<F k B 0 := by
    rw [hF0]
    cases k
    · have hh := negative_aligned hB
      have he : (1:ℝ)+sign false*B=1-B := by simp only [sign]; norm_num; ring
      rw [he]
      simp only [sign]
      norm_num
      linarith
    · have he : (1:ℝ)+sign true*B=1+B := by simp [sign]
      rw [he] at hzero ⊢
      have hh := positive_aligned hB hzero.2
      simp only [sign]
      norm_num
      linarith
  have hpath := move_to_zero k hz hB hx hm
  have hcontact := contact_domain k hz hB hx hm ⟨le_rfl,hx.2⟩
  have hG := FrameLowHighQuarterCalculus.G_monotone (lower_extended hcontact)
    (source_extended hz) (contact_le k hx hm)
  have hcomparison : F k B x≤upperCost k z B x := by
    dsimp only [F,upperCost]
    rw [(width_actual hx).2]
    linarith
  exact haligned.trans_le (hpath.trans hcomparison)

end SquaresInCircles.Eight.TableFree.FrameHighLowPrimaryNegative
