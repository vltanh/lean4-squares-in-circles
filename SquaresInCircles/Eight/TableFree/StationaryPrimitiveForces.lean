module

public import SquaresInCircles.Eight.TableFree.StationaryPrimitives

/-!
# Force primitives of the actual stationary-position family

Uncompiled reconstruction.  These estimates are substitutions into the
one radical rectangle, before any stationary equation is imposed.  In
particular the position derivatives and the two corner components are
the original nested-circle formulas, not auxiliary interval variables.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.StationaryPrimitives
open ExactFamily.FiveCornerGeometry

structure ForceBounds (q u h : ℝ) : Prop where
  p_lower : 287/500<slopeRatio q u
  p_upper : slopeRatio q u<637/1000
  a_lower : 599/1000<positionA q (cosine h) (sine h) u
  a_upper : positionA q (cosine h) (sine h) u<7/10
  b_lower : 291/500<positionb q (cosine h) (sine h) u
  b_upper : positionb q (cosine h) (sine h) u<133/200
  k1_lower : 1327/1000<firstComponent q (cosine h) (sine h) u
  k1_upper : firstComponent q (cosine h) (sine h) u<711/500
  k2_lower : 1379/1000<secondComponent q (cosine h) (sine h) u
  k2_upper : secondComponent q (cosine h) (sine h) u<147/100
  E_lower : 469/500< -secondTilt q (cosine h) (sine h) u
  E_upper : -secondTilt q (cosine h) (sine h) u<993/1000

theorem force_bounds_of_primitives {q u h : ℝ}
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hr : RadicalBounds q u) (ht : TrigBounds h) : ForceBounds q u h := by
  have hl : 2-u∈Icc (53/50:ℝ) (221/200) := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  have hnum := product_bounds hl hr.V (by norm_num) (by norm_num)
  have hden := product_bounds hr.U hr.Y (by norm_num) (by norm_num)
  have hp0 := quotient_bounds hnum hden (by norm_num) (by norm_num)
  have hp : slopeRatio q u∈Ioo (287/500:ℝ) (637/1000) := by
    dsimp [slopeRatio]
    exact ⟨by linarith [hp0.1],by linarith [hp0.2]⟩
  have hcu := product_bounds ht.c hu (by norm_num) (by norm_num)
  have hcur := quotient_bounds hcu hr.r (by norm_num) (by norm_num)
  have ha : positionA q (cosine h) (sine h) u∈Ioo (599/1000:ℝ) (7/10) := by
    dsimp [positionA]
    exact ⟨by linarith [ht.s_lower,hcur.1],by linarith [ht.s_upper,hcur.2]⟩
  have hsv := product_bounds ht.s hr.v (by norm_num) (by norm_num)
  have hsvw := quotient_bounds hsv hr.w (by norm_num) (by norm_num)
  have hB : positionB q (cosine h) (sine h) u∈
      Icc ((2467/2500:ℝ)+(199/2000)*(533/1000)/(953/500))
        ((9951/10000:ℝ)+(81/500)*(281/500)/(1897/1000)) := by
    dsimp [positionB]
    exact ⟨by linarith [ht.c_lower,hsvw.1],by linarith [ht.c_upper,hsvw.2]⟩
  have hb0 := product_bounds ⟨hp.1.le,hp.2.le⟩ hB (by norm_num) (by norm_num)
  have hb : positionb q (cosine h) (sine h) u∈Ioo (291/500:ℝ) (133/200) := by
    dsimp [positionb]
    exact ⟨by linarith [hb0.1],by linarith [hb0.2]⟩
  have hrm : lowerRight q u-1∈Icc (741/1000:ℝ) (153/200) :=
    ⟨by linarith [hr.r_lower],by linarith [hr.r_upper]⟩
  have hcrm := product_bounds ht.c hrm (by norm_num) (by norm_num)
  have hsu := product_bounds ht.s hu (by norm_num) (by norm_num)
  have hk1 : firstComponent q (cosine h) (sine h) u∈Ioo (1327/1000:ℝ) (711/500) := by
    dsimp [firstComponent]
    exact ⟨by linarith [hcrm.2,hsu.1],by linarith [hcrm.1,hsu.2]⟩
  have hwm : lowerLeft q u-1∈Icc (897/1000:ℝ) (453/500) :=
    ⟨by linarith [hr.w_lower],by linarith [hr.w_upper]⟩
  have hcv := product_bounds ht.c hr.v (by norm_num) (by norm_num)
  have hswm := product_bounds ht.s hwm (by norm_num) (by norm_num)
  have hk2 : secondComponent q (cosine h) (sine h) u∈Ioo (1379/1000:ℝ) (147/100) := by
    dsimp [secondComponent]
    exact ⟨by linarith [hcv.1,hswm.2],by linarith [hcv.2,hswm.1]⟩
  have hcwm := product_bounds ht.c hwm (by norm_num) (by norm_num)
  have hE : -secondTilt q (cosine h) (sine h) u∈Ioo (469/500:ℝ) (993/1000) := by
    dsimp [secondTilt]
    exact ⟨by linarith [hcwm.1,hsv.1],by linarith [hcwm.2,hsv.2]⟩
  exact ⟨hp.1,hp.2,ha.1,ha.2,hb.1,hb.2,hk1.1,hk1.2,hk2.1,hk2.2,hE.1,hE.2⟩

theorem force_bounds {q u h : ℝ}
    (hq : q∈Icc (19577/5000:ℝ) (9789/2500))
    (hu : u∈Icc (179/200:ℝ) (47/50))
    (hh : h∈Icc (1/10:ℝ) (41/250)) : ForceBounds q u h :=
  force_bounds_of_primitives hu (radical_bounds hq hu) (trig_bounds hh)

theorem ForceBounds.p {q u h : ℝ} (hf : ForceBounds q u h) :
    slopeRatio q u∈Icc (287/500:ℝ) (637/1000) := ⟨hf.p_lower.le,hf.p_upper.le⟩
theorem ForceBounds.a {q u h : ℝ} (hf : ForceBounds q u h) :
    positionA q (cosine h) (sine h) u∈Icc (599/1000:ℝ) (7/10) :=
  ⟨hf.a_lower.le,hf.a_upper.le⟩
theorem ForceBounds.b {q u h : ℝ} (hf : ForceBounds q u h) :
    positionb q (cosine h) (sine h) u∈Icc (291/500:ℝ) (133/200) :=
  ⟨hf.b_lower.le,hf.b_upper.le⟩
theorem ForceBounds.k1 {q u h : ℝ} (hf : ForceBounds q u h) :
    firstComponent q (cosine h) (sine h) u∈Icc (1327/1000:ℝ) (711/500) :=
  ⟨hf.k1_lower.le,hf.k1_upper.le⟩
theorem ForceBounds.k2 {q u h : ℝ} (hf : ForceBounds q u h) :
    secondComponent q (cosine h) (sine h) u∈Icc (1379/1000:ℝ) (147/100) :=
  ⟨hf.k2_lower.le,hf.k2_upper.le⟩
theorem ForceBounds.E {q u h : ℝ} (hf : ForceBounds q u h) :
    -secondTilt q (cosine h) (sine h) u∈Icc (469/500:ℝ) (993/1000) :=
  ⟨hf.E_lower.le,hf.E_upper.le⟩

end SquaresInCircles.Eight.TableFree.StationaryPrimitives
