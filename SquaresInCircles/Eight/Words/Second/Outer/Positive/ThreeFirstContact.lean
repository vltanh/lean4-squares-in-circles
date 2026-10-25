module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeData

/-!
# Eight squares: actual least-source contacts for the first positive edge-three axis

The source coordinate comes directly from the original weak separator.
The cost has a strictly concave first derivative on every closed
physical contact interval.  The derivative formulas below keep the
actual source and target circle coordinates throughout.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.FirstContact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

def source (B φ : ℝ) : ℝ := 1/2+(1-U B)*Real.sin φ+W B*Real.cos φ
def sourceFirst (B φ : ℝ) : ℝ := ratio B*Real.sin φ+Real.cos φ
def sourceSecond (B φ : ℝ) : ℝ := ratioD B*Real.sin φ
def sourceThird (B φ : ℝ) : ℝ := ratioDD B*Real.sin φ
def cost (B φ : ℝ) : ℝ := φ+V (source B φ)-L B
def first (B φ : ℝ) : ℝ := VLabel.d1 (source B φ)*sourceFirst B φ-LLabel.d1 B
def second (B φ : ℝ) : ℝ :=
  VLabel.d2 (source B φ)*(sourceFirst B φ)^2+
    VLabel.d1 (source B φ)*sourceSecond B φ-LLabel.d2 B
def third (B φ : ℝ) : ℝ :=
  VLabel.d3 (source B φ)*(sourceFirst B φ)^3+
    3*VLabel.d2 (source B φ)*sourceFirst B φ*sourceSecond B φ+
    VLabel.d1 (source B φ)*sourceThird B φ-LLabel.d3 B

def Domain (B φ : ℝ) : Prop :=
  B∈Icc 0 outerDiagonal ∧ source B φ∈Icc 0 outerDiagonal ∧ Lower φ

lemma source_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => source t φ) (sourceFirst B φ) B := by
  have hd := (((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hB)).add_const
    (1/2)).const_sub 1).mul_const (Real.sin φ)).const_add (1/2)).add
    (((hasDerivAt_id' B).add_const (1/2)).mul_const (Real.cos φ))
  convert hd using 1
  · funext t
    simp only [source,U,W,Pi.add_apply]
  · dsimp only [sourceFirst]
    ring

lemma sourceFirst_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => sourceFirst t φ) (sourceSecond B φ) B := by
  convert ((ShortOuterOne.SameContact.ratio_hasDerivAt (outer_domain hB)).mul_const
    (Real.sin φ)).add_const (Real.cos φ) using 1 <;>
    dsimp [sourceFirst,sourceSecond]

lemma sourceSecond_hasDerivAt {B : ℝ} (hB : B∈Icc 0 outerDiagonal) (φ : ℝ) :
    HasDerivAt (fun t => sourceSecond t φ) (sourceThird B φ) B := by
  exact (ShortOuterOne.SameContact.ratioD_hasDerivAt (outer_domain hB)).mul_const
    (Real.sin φ)

lemma cost_hasDerivAt {B φ : ℝ} (h : Domain B φ) :
    HasDerivAt (fun t => cost t φ) (first B φ) B := by
  have hv := (VLabel.outer_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  convert (hv.const_add φ).sub (LLabel.outer_hasDerivAt (outer_domain h.1)) using 1
  · funext t
    simp only [cost,V,L,Pi.sub_apply,Function.comp_apply]
  · rfl

lemma first_hasDerivAt {B φ : ℝ} (h : Domain B φ) :
    HasDerivAt (fun t => first t φ) (second B φ) B := by
  have hv := (VLabel.d1_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  convert (hv.mul (sourceFirst_hasDerivAt h.1 φ)).sub
    (LLabel.d1_hasDerivAt (outer_domain h.1)) using 1
  · funext t
    simp only [first,Pi.sub_apply,Pi.mul_apply,Function.comp_apply]
  · simp only [second,Function.comp_apply]
    ring

lemma second_hasDerivAt {B φ : ℝ} (h : Domain B φ) :
    HasDerivAt (fun t => second t φ) (third B φ) B := by
  have hv2 := (VLabel.d2_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  have hv1 := (VLabel.d1_hasDerivAt (outer_domain h.2.1)).comp B
    (source_hasDerivAt h.1 φ)
  convert ((hv2.mul ((sourceFirst_hasDerivAt h.1 φ).pow 2)).add
    (hv1.mul (sourceSecond_hasDerivAt h.1 φ))).sub
      (LLabel.d2_hasDerivAt (outer_domain h.1)) using 1
  · funext t
    simp only [second,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,
      Function.comp_apply]
  · simp only [third,Function.comp_apply,Pi.pow_apply]
    ring

lemma sourceFirst_positive {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    0<sourceFirst B φ := by
  have ht := lower_trig hφ
  have hp := mul_pos (ShortOuterOne.SameContact.ratio_pos (outer_domain hB))
    (show 0<Real.sin φ by linarith [ht.1])
  dsimp [sourceFirst]
  linarith [ht.2.2.1]

lemma sourceSecond_positive {B φ : ℝ} (hB : B∈Icc 0 outerDiagonal) (hφ : Lower φ) :
    0<sourceSecond B φ :=
  mul_pos (outer_ratio_bounds hB).2.2.1 (by linarith [(lower_trig hφ).1])

lemma third_negative {B φ : ℝ} (h : Domain B φ) : third B φ<0 := by
  have hv3 := V_third_negative h.2.1
  have hv2 : VLabel.d2 (source B φ)<0 := by linarith [V_second_upper h.2.1]
  have hp := sourceFirst_positive h.1 h.2.2
  have hq := sourceSecond_positive h.1 h.2.2
  have hfirst := mul_neg_of_neg_of_pos hv3 (pow_pos hp 3)
  have hsecond := mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num : (0:ℝ)<3) hv2) hp) hq
  have hs := lower_trig h.2.2
  have hd := (outer_ratio_bounds h.1).2.2.1
  have hDD := ratioDD_positive h.1
  have hDcap := outer_ratioDD_comparison h.1
  have hthird : 0≤ sourceThird B φ ∧ sourceThird B φ≤ratioDD B := by
    dsimp [sourceThird]
    exact ⟨mul_nonneg hDD.le (by linarith [hs.1]),
      by simpa using mul_le_mul_of_nonneg_left hs.2.1 hDD.le⟩
  have hv1 : 0≤VLabel.d1 (source B φ) := by
    linarith [(V_first_bounds h.2.1).1]
  have hprod := mul_le_mul (V_first_upper h.2.1).le
    (hthird.2.trans hDcap.le) hthird.1 (by norm_num : (0:ℝ)≤1061/1000)
  have hBprod := mul_nonneg h.1.1 hDD.le
  have hL : (284163/50000)*ratioD B≤LLabel.d3 B := by
    norm_num [RoleLabel.d3,LLabel]
    nlinarith
  dsimp [third]
  norm_num at hprod
  nlinarith

lemma original_cut {a b A B φ : ℝ} (ht : OuterState A B) (hφ : Lower φ)
    (hm : 0≤Eight.forwardMargin 0 a b A B 1 1 φ) : source B φ≤b := by
  have hh := lower_source_secondary_cut hφ hm
  dsimp [source,U,W]
  rw [(ShortOuterOne.SameContact.actual_arc ht).1]
  linarith

lemma source_at_quarter (B : ℝ) : source B (Real.pi/2)=1-arc B := by
  simp [source,U,W]
  ring

lemma source_monotone {φ : ℝ} (hφ : Lower φ) :
    MonotoneOn (fun B => source B φ) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun B hB => (source_hasDerivAt hB φ).continuousAt.continuousWithinAt)
    (fun B hB => source_hasDerivAt (Ioo_subset_Icc_self hB) φ)
    (fun B hB => (sourceFirst_positive (Ioo_subset_Icc_self hB) hφ).le)

end SquaresInCircles.Eight.SecondWord.PositiveThree.FirstContact
