module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Core.Arc
public import SquaresInCircles.Eight.Frames.Low.Pair

/-!
# Eight squares: whole-interval calculus for the original frame-pair supports

The derivative endpoint principle allows an initial convex part followed
by a concave part without selecting an angular mesh or a critical point.
The trigonometric helpers retain the complete first and second quadrants.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FramePairCalculus

theorem endpoint_minimum_of_concave_derivative {f d : ℝ → ℝ} {l u x : ℝ}
    (hx : x∈Icc l u) (hd : ∀t∈Icc l u,HasDerivAt f (d t) t)
    (hc : ConcaveOn ℝ (Icc l u) d) (hl : 0≤d l) :
    min (f l) (f u)≤f x := by
  have hlu : l≤u := hx.1.trans hx.2
  by_cases hdx : 0≤d x
  · have hm : MonotoneOn f (Icc l x) := by
      apply monoOn_of_hasDeriv_nonneg
      · exact fun t ht => (hd t ⟨ht.1,ht.2.trans hx.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨ht.1.le,ht.2.le.trans hx.2⟩
      · intro t ht
        have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hlu⟩ hx ⟨ht.1.le,ht.2.le⟩
        exact (le_min hl hdx).trans hh
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)
  · have hm : AntitoneOn f (Icc x u) := by
      apply antiOn_of_hasDeriv_nonpos
      · exact fun t ht => (hd t ⟨hx.1.trans ht.1,ht.2⟩).continuousAt.continuousWithinAt
      · exact fun t ht => hd t ⟨hx.1.trans ht.1.le,ht.2.le⟩
      · intro t ht
        by_contra! hdt
        have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hlu⟩
          ⟨hx.1.trans ht.1.le,ht.2.le⟩ ⟨hx.1,ht.1.le⟩
        exact hdx ((le_min hl hdt.le).trans hh)
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)

theorem sin_concave {l u : ℝ} (hl : 0≤l) (hu : u≤Real.pi) :
    ConcaveOn ℝ (Icc l u) Real.sin := by
  apply concave_of_deriv2 (fun x _ => Real.hasDerivAt_sin x)
    (fun x _ => Real.hasDerivAt_cos x)
  intro x hx
  exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi (hl.trans hx.1) (hx.2.trans hu))

theorem sin_endpoint_lower {l u x m : ℝ} (hl : 0≤l) (hu : u≤Real.pi)
    (hx : x∈Icc l u) (hL : m<Real.sin l) (hU : m<Real.sin u) : m<Real.sin x :=
  concave_gt_of_endpoints (sin_concave hl hu) hx hL hU

theorem harmonic_projection_lt_one {A B x : ℝ} (h : A^2+B^2<1) :
    A*Real.sin x+B*Real.cos x<1 :=
  FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<1) (by simpa using h) x

theorem negative_div_lower {a A b B : ℝ} (hA : A≤a) (hA0 : A≤0)
    (hB : 0<B) (hb : B≤b) : A/B≤a/b := by
  have hb0 : 0<b := hB.trans_le hb
  apply (div_le_div_iff₀ hB hb0).2
  have hm := mul_le_mul_of_nonpos_left hb hA0
  have hn := mul_le_mul_of_nonneg_right hA hB.le
  nlinarith

theorem first_width {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    pairWidth x=(1+Real.sin x+Real.cos x)/2 ∧
      periodicFrameCost x=(Real.sin x+Real.cos x-1)/2 := by
  have hh := FrameLowPair.quadrant hx
  simp [pairWidth,periodicFrameCost,abs_of_nonneg hh.1,abs_of_nonneg hh.2.2.1,add_comm]

theorem second_signs {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    0≤Real.sin x ∧ Real.cos x≤0 := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [hx.1,Real.pi_pos]) hx.2
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0≤Real.pi/2) hx.2 hx.1
  simpa only [Real.cos_pi_div_two] using And.intro hs hc

theorem second_width {x : ℝ} (hx : x∈Icc (Real.pi/2) Real.pi) :
    pairWidth x=(1+Real.sin x-Real.cos x)/2 ∧
      periodicFrameCost x=(Real.sin x-Real.cos x-1)/2 := by
  have hh := second_signs hx
  simp only [pairWidth,periodicFrameCost,abs_of_nonneg hh.1,abs_of_nonpos hh.2]
  constructor <;> ring

theorem negative_width {x : ℝ} (hx : x∈Icc (-(54/125:ℝ)) 0) :
    pairWidth x=(1-Real.sin x+Real.cos x)/2 ∧
      periodicFrameCost x=(-Real.sin x+Real.cos x-1)/2 := by
  have hx' : -x∈Icc 0 (Real.pi/2) :=
    ⟨by linarith [hx.2],by linarith [hx.1,FrameLowPair.pi_lower]⟩
  have hh := FrameLowPair.quadrant hx'
  simp only [Real.sin_neg,Real.cos_neg] at hh
  simp only [pairWidth,periodicFrameCost,abs_of_nonpos (by linarith [hh.1] : Real.sin x≤0),
    abs_of_nonneg hh.2.2.1]
  constructor <;> ring

end SquaresInCircles.Eight.FramePairCalculus
