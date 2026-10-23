module

public import SquaresInCircles.Eight.ExactFamily.CriticalDifferentiation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The actual radical coordinates on the terminal rectangle

Uncompiled reconstruction.  Every bound below concerns the successive
positive circle roots themselves.  The radius and position range is one
rectangle, and each root enclosure follows by positive squaring.  The
trigonometric bounds likewise concern the actual angle `arctan h`.
No stationarity equation, fitted coordinate, or root-cover hypothesis is
used in these primitive estimates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryPrimitives
open ExactFamily.FiveCornerGeometry

/-- Positive interval arithmetic used only for the displayed continuous
algebraic comparisons. -/
theorem product_bounds {x y a b c d : ℝ}
    (hx : x∈Icc a b) (hy : y∈Icc c d) (ha : 0≤a) (hc : 0≤c) :
    x*y∈Icc (a*c) (b*d) := by
  exact ⟨mul_le_mul hx.1 hy.1 hc (le_trans ha hx.1),
    mul_le_mul hx.2 hy.2 (le_trans hc hy.1) (le_trans ha (le_trans hx.1 hx.2))⟩

theorem quotient_bounds {x y a b c d : ℝ}
    (hx : x∈Icc a b) (hy : y∈Icc c d) (ha : 0≤a) (hc : 0<c) :
    x/y∈Icc (a/d) (b/c) := by
  have hdp : 0<d := lt_of_lt_of_le hc (le_trans hy.1 hy.2)
  have hyp : 0<y := lt_of_lt_of_le hc hy.1
  have hbp : 0≤b := le_trans ha (le_trans hx.1 hx.2)
  constructor
  · apply (le_div_iff₀ hyp).2
    calc
      (a/d)*y ≤ (a/d)*d := mul_le_mul_of_nonneg_left hy.2 (div_nonneg ha hdp.le)
      _ = a := div_mul_cancel₀ a hdp.ne'
      _ ≤ x := hx.1
  · apply (div_le_iff₀ hyp).2
    calc
      x ≤ b := hx.2
      _ = (b/c)*c := (div_mul_cancel₀ b hc.ne').symm
      _ ≤ (b/c)*y := mul_le_mul_of_nonneg_left hy.1 (div_nonneg hbp hc.le)

theorem square_bounds {x a b : ℝ} (hx : x∈Icc a b) (ha : 0≤a) :
    x^2∈Icc (a^2) (b^2) := by
  exact ⟨square_mono_nonneg ha hx.1,
    square_mono_nonneg (le_trans ha hx.1) hx.2⟩

theorem cube_bounds {x a b : ℝ} (hx : x∈Icc a b) (ha : 0≤a) :
    x^3∈Icc (a^3) (b^3) := by
  have hh := product_bounds (square_bounds hx ha) hx (sq_nonneg a) ha
  simpa only [← pow_succ] using hh

theorem sqrt_bounds {x a b l r : ℝ} (hx : x∈Icc l r)
    (ha : 0≤a) (hb : 0≤b) (hl : a^2<l) (hr : r<b^2) :
    Real.sqrt x∈Ioo a b :=
  sqrt_between ha hb (lt_of_lt_of_le hl hx.1) (lt_of_le_of_lt hx.2 hr)

structure RadicalBounds (q u : ℝ) : Prop where
  r_lower : 1741/1000<lowerRight q u
  r_upper : lowerRight q u<353/200
  U_lower : 1641/1000<topRight q u
  U_upper : topRight q u<1671/1000
  V_lower : 1329/1000<topLeft q u
  V_upper : topLeft q u<1359/1000
  Y_lower : 719/500<topHeight q u
  Y_upper : topHeight q u<1467/1000
  v_lower : 533/1000<lowerHeight q u
  v_upper : lowerHeight q u<281/500
  w_lower : 1897/1000<lowerLeft q u
  w_upper : lowerLeft q u<953/500

/-- One successive-square calculation for the full terminal rectangle. -/
theorem radical_bounds {q u : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50)) : RadicalBounds q u := by
  have hu2 := square_bounds hu (by norm_num)
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hl2 := square_bounds hl (by norm_num)
  have hr : lowerRight q u∈Ioo (1741/1000:ℝ) (353/200) := by
    apply sqrt_bounds (l:=15159/5000) (r:=124583/40000)
      (show q-u^2∈Icc (15159/5000:ℝ) (124583/40000) from
        ⟨by linarith [hq.1,hu2.2],by linarith [hq.2,hu2.1]⟩) <;> norm_num
  have hU : topRight q u∈Ioo (1641/1000:ℝ) (1671/1000) := by
    apply sqrt_bounds (l:=4311/1600) (r:=349/125)
      (show q-(2-u)^2∈Icc (4311/1600:ℝ) (349/125) from
        ⟨by linarith [hq.1,hl2.2],by linarith [hq.2,hl2.1]⟩) <;> norm_num
  have hV : topLeft q u∈Ioo (1329/1000:ℝ) (1359/1000) := by
    dsimp [topLeft]
    exact ⟨by linarith [hU.2],by linarith [hU.1]⟩
  have hV2 := square_bounds ⟨hV.1.le,hV.2.le⟩ (by norm_num)
  have hY : topHeight q u∈Ioo (719/500:ℝ) (1467/1000) := by
    apply sqrt_bounds (l:=2068519/1000000) (r:=2149359/1000000)
      (show q-topLeft q u^2∈Icc (2068519/1000000:ℝ) (2149359/1000000) from
        ⟨by linarith [hq.1,hV2.2],by linarith [hq.2,hV2.1]⟩) <;> norm_num
  have hv : lowerHeight q u∈Ioo (533/1000:ℝ) (281/500) := by
    dsimp [lowerHeight]
    exact ⟨by linarith [hY.2],by linarith [hY.1]⟩
  have hv2 := square_bounds ⟨hv.1.le,hv.2.le⟩ (by norm_num)
  have hw : lowerLeft q u∈Ioo (1897/1000:ℝ) (953/500) := by
    apply sqrt_bounds (l:=899889/250000) (r:=3631511/1000000)
      (show q-lowerHeight q u^2∈Icc (899889/250000:ℝ) (3631511/1000000) from
        ⟨by linarith [hq.1,hv2.2],by linarith [hq.2,hv2.1]⟩) <;> norm_num
  exact ⟨hr.1,hr.2,hU.1,hU.2,hV.1,hV.2,hY.1,hY.2,hv.1,hv.2,hw.1,hw.2⟩

theorem RadicalBounds.r {q u : ℝ} (h : RadicalBounds q u) :
    lowerRight q u∈Icc (1741/1000:ℝ) (353/200) := ⟨h.r_lower.le,h.r_upper.le⟩
theorem RadicalBounds.U {q u : ℝ} (h : RadicalBounds q u) :
    topRight q u∈Icc (1641/1000:ℝ) (1671/1000) := ⟨h.U_lower.le,h.U_upper.le⟩
theorem RadicalBounds.V {q u : ℝ} (h : RadicalBounds q u) :
    topLeft q u∈Icc (1329/1000:ℝ) (1359/1000) := ⟨h.V_lower.le,h.V_upper.le⟩
theorem RadicalBounds.Y {q u : ℝ} (h : RadicalBounds q u) :
    topHeight q u∈Icc (719/500:ℝ) (1467/1000) := ⟨h.Y_lower.le,h.Y_upper.le⟩
theorem RadicalBounds.v {q u : ℝ} (h : RadicalBounds q u) :
    lowerHeight q u∈Icc (533/1000:ℝ) (281/500) := ⟨h.v_lower.le,h.v_upper.le⟩
theorem RadicalBounds.w {q u : ℝ} (h : RadicalBounds q u) :
    lowerLeft q u∈Icc (1897/1000:ℝ) (953/500) := ⟨h.w_lower.le,h.w_upper.le⟩

theorem RadicalBounds.smoothDomain {q u : ℝ} (h : RadicalBounds q u)
    (hq : q<4) (hu : 0≤u) : SmoothDomain q u := by
  have hr : 0<lowerRight q u := by linarith [h.r_lower]
  have hU : 0<topRight q u := by linarith [h.U_lower]
  have hY : 0<topHeight q u := by linarith [h.Y_lower]
  have hw : 0<lowerLeft q u := by linarith [h.w_lower]
  have hr2 : 0<q-u^2 := Real.sqrt_pos.mp hr
  have hU2 : 0<q-(2-u)^2 := Real.sqrt_pos.mp hU
  have hY2 : 0<q-topLeft q u^2 := Real.sqrt_pos.mp hY
  have hw2 : 0<q-lowerHeight q u^2 := Real.sqrt_pos.mp hw
  exact ⟨⟨hu,by linarith,by linarith,by linarith,by linarith⟩,hq,hr,hU,hY,hw⟩

def cosine (h : ℝ) : ℝ := Real.cos (Real.arctan h)
def sine (h : ℝ) : ℝ := Real.sin (Real.arctan h)

theorem cosine_pos (h : ℝ) : 0<cosine h :=
  Real.cos_pos_of_mem_Ioo (Real.arctan_mem_Ioo h)

theorem sine_eq (h : ℝ) : sine h=h*cosine h := by
  rw [sine,cosine,Real.sin_arctan,Real.cos_arctan]
  ring

theorem unit (h : ℝ) : cosine h^2+sine h^2=1 := by
  dsimp [cosine,sine]
  nlinarith [Real.sin_sq_add_cos_sq (Real.arctan h)]

structure TrigBounds (h : ℝ) : Prop where
  c_lower : 2467/2500<cosine h
  c_upper : cosine h<9951/10000
  s_lower : 199/2000<sine h
  s_upper : sine h<81/500

theorem trig_bounds {h : ℝ} (hh : h∈Icc (1/10:ℝ) (41/250)) : TrigBounds h := by
  let D : ℝ := Real.sqrt (1+h^2)
  have hrad : 0<1+h^2 := by positivity
  have hD : 0<D := Real.sqrt_pos.mpr hrad
  have hD2 : D^2=1+h^2 := Real.sq_sqrt hrad.le
  have hh2 := square_bounds hh (by norm_num)
  have hDb : D∈Ioo (10000/9951:ℝ) (2500/2467) := by
    apply sqrt_bounds (l:=101/100) (r:=64181/62500)
      (show 1+h^2∈Icc (101/100:ℝ) (64181/62500) from
        ⟨by linarith [hh2.1],by linarith [hh2.2]⟩) <;> norm_num
  have hc : (2467/2500:ℝ)<cosine h ∧ cosine h<9951/10000 := by
    change (2467/2500:ℝ)<Real.cos (Real.arctan h) ∧
      Real.cos (Real.arctan h)<9951/10000
    rw [Real.cos_arctan]
    constructor
    · apply (lt_div_iff₀ hD).2
      linarith [hDb.2]
    · apply (div_lt_iff₀ hD).2
      linarith [hDb.1]
  have hsL : (199/2000:ℝ)*D<h := by
    by_contra! hbad
    have hsq := square_mono_nonneg (by linarith [hh.1] : 0≤h) hbad
    nlinarith [hh2.1]
  have hsU : h<(81/500:ℝ)*D := by
    by_contra! hbad
    have hsq := square_mono_nonneg (by positivity : 0≤(81/500:ℝ)*D) hbad
    nlinarith [hh2.2]
  refine ⟨hc.1,hc.2,?_,?_⟩
  · change (199/2000:ℝ)<Real.sin (Real.arctan h)
    rw [Real.sin_arctan]
    exact (lt_div_iff₀ hD).2 hsL
  · change Real.sin (Real.arctan h)<81/500
    rw [Real.sin_arctan]
    exact (div_lt_iff₀ hD).2 hsU

theorem TrigBounds.c {h : ℝ} (hT : TrigBounds h) :
    cosine h∈Icc (2467/2500:ℝ) (9951/10000) := ⟨hT.c_lower.le,hT.c_upper.le⟩
theorem TrigBounds.s {h : ℝ} (hT : TrigBounds h) :
    sine h∈Icc (199/2000:ℝ) (81/500) := ⟨hT.s_lower.le,hT.s_upper.le⟩

end SquaresInCircles.Eight.TableFree.StationaryPrimitives
