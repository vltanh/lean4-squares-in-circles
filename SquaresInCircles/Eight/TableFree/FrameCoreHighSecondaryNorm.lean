module

public import SquaresInCircles.Eight.TableFree.FrameCoreHighHighSecondary
public import SquaresInCircles.Eight.TableFree.CircularNorm

/-!
# The two actual rotating norms in the core/high transverse support

Every norm is positive on the whole real line.  The exact circle identity
provides the global lower curvature bound; on the final first-quadrant
interval the positive-target norm has positive curvature itself.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreHighSecondaryNorm
open FramePair FrameCircleArc FrameHighArc FramePairCalculus
open FrameMidArc (g)

def E : ℝ := g^2+u^2+v^2
def B : ℝ := -2*g*v
def C (j : Bool) : ℝ := -2*g*sign j*u
def N (j : Bool) (x : ℝ) : ℝ := CircularNorm.norm E B (C j) x
def Nd (j : Bool) (x : ℝ) : ℝ := CircularNorm.d1 E B (C j) x
def Ndd (j : Bool) (x : ℝ) : ℝ := CircularNorm.d2 E B (C j) x

theorem energy_positive (j : Bool) (x : ℝ) : 0<CircularNorm.energy E B (C j) x := by
  have ht : sign j*u*Real.sin x+v*Real.cos x<(7/10:ℝ) := by
    apply FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<7/10)
    cases j <;> norm_num [sign,u,v]
  have hg := mul_lt_mul_of_pos_left ht (show 0<2*g by norm_num [g])
  dsimp [CircularNorm.energy,E,B,C,g,u,v] at *
  nlinarith

theorem N_pos (j : Bool) (x : ℝ) : 0<N j x := CircularNorm.norm_pos (energy_positive j x)
theorem N_sq (j : Bool) (x : ℝ) : (N j x)^2=CircularNorm.energy E B (C j) x :=
  CircularNorm.norm_sq (energy_positive j x).le
theorem N_deriv (j : Bool) (x : ℝ) : HasDerivAt (N j) (Nd j x) x :=
  CircularNorm.norm_hasDerivAt (energy_positive j x)
theorem Nd_deriv (j : Bool) (x : ℝ) : HasDerivAt (Nd j) (Ndd j x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive j x)

theorem N_upper (j : Bool) (x : ℝ) : N j x<g+7/10 := by
  have ht : -sign j*u*Real.sin x-v*Real.cos x<(7/10:ℝ) := by
    have hh := FrameCoreArc.projection_lt (a := -sign j*u) (b := -v)
      (by norm_num : (0:ℝ)<7/10)
      (by cases j <;> norm_num [sign,u,v]) x
    nlinarith
  have hN := N_sq j x
  have hp := N_pos j x
  have hg := mul_lt_mul_of_pos_left ht (show 0<2*g by norm_num [g])
  dsimp [CircularNorm.energy,E,B,C,g,u,v] at *
  nlinarith

theorem curvature_lower (j : Bool) (x : ℝ) : -(N j x)/4≤Ndd j x := by
  apply CircularNorm.curvature_lower (energy_positive j x)
  cases j <;> norm_num [E,B,C,sign,g,u,v]

theorem curvature_work (j : Bool) (x : ℝ) : -R*Ndd j x<(9/10:ℝ) := by
  have hc := curvature_lower j x
  have hR := radius_bound
  have hRN : R*N j x<radiusUpper*(g+7/10) :=
    mul_lt_mul'' hR (N_upper j x) R_pos.le (N_pos j x).le
  have hh := mul_le_mul_of_nonneg_left hc R_pos.le
  norm_num [radiusUpper,g] at hRN
  linarith

theorem trig_seven_fifths :
    (197/200:ℝ)<Real.sin (7/5:ℝ) ∧ Real.sin (7/5:ℝ)<493/500 ∧
      (169/1000:ℝ)<Real.cos (7/5:ℝ) ∧ Real.cos (7/5:ℝ)<17/100 := by
  have hsL := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤7/5 by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (show (0:ℝ)≤7/5 by norm_num)
  have hcL := HighOrderTaylor.C14_le_cos (show (0:ℝ)≤7/5 by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (show (0:ℝ)≤7/5 by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,
    HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at *
  refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem positive_first_trig {x : ℝ} (hx : x∈Icc (7/5:ℝ) (Real.pi/2)) :
    (197/200:ℝ)<Real.sin x ∧ 0≤Real.cos x ∧ Real.cos x<17/100 := by
  have ht := FrameLowPair.quadrant ⟨by linarith [hx.1],hx.2⟩
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(7/5:ℝ)) hx.2 hx.1
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤7/5)
    (by linarith [hx.2,Real.pi_pos]) hx.1
  exact ⟨by linarith [trig_seven_fifths.1],ht.2.2.1,
    by linarith [trig_seven_fifths.2.2.2]⟩

theorem positive_norm_monotone : MonotoneOn (N true) (Icc (7/5:ℝ) (Real.pi/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv true x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv true x
  · intro x hx
    have ht := positive_first_trig (Ioo_subset_Icc_self hx)
    dsimp [Nd,CircularNorm.d1,CircularNorm.slope,B,C,sign]
    apply div_nonneg
    · norm_num [g,u,v]
      nlinarith
    · exact mul_nonneg (by norm_num) (N_pos true x).le

theorem positive_quarter_norm : N true (Real.pi/2)=FrameCoreHighNorm.n 1 := by
  dsimp [N,CircularNorm.norm,CircularNorm.energy,E,B,C,FrameCoreHighNorm.n,
    FrameCoreHighNorm.energy,sign]
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,add_zero]
  congr 1
  ring

theorem positive_norm_curvature {x : ℝ} (hx : x∈Icc (7/5:ℝ) (Real.pi/2)) : 0<Ndd true x := by
  have hN := positive_norm_monotone hx
    ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ hx.2
  rw [positive_quarter_norm] at hN
  have hNu : N true x<(641/1000:ℝ) := by linarith [FrameCoreHighNorm.n_one_bounds.2]
  have hNp := N_pos true x
  have hN2 : (N true x)^2<(641/1000:ℝ)^2 := by nlinarith
  have hD : (641/1000:ℝ)^2<g^2-u^2-v^2 := by norm_num [g,u,v]
  have hnum : (N true x)^4<(g^2-u^2-v^2)^2 := by nlinarith [sq_nonneg (N true x)]
  have hid := CircularNorm.curvature_identity (energy_positive true x)
  have he : E^2-B^2-(C true)^2=(g^2-u^2-v^2)^2 := by
    dsimp [E,B,C,sign]
    ring
  rw [he] at hid
  change Ndd true x+N true x/4=(g^2-u^2-v^2)^2/(4*(N true x)^3) at hid
  have hdiv : N true x/4<(g^2-u^2-v^2)^2/(4*(N true x)^3) := by
    apply (lt_div_iff₀ (by positivity : 0<4*(N true x)^3)).2
    nlinarith only [hnum]
  linarith

theorem norm_endpoints :
    N false 0<(223/250:ℝ) ∧ N false (6/5)<63/40 ∧
      N true (7/5)<67/125 ∧ N true (5/2)<63/50 := by
  have h0 := N_sq false 0
  have hp0 := N_pos false 0
  have h12 := N_sq false (6/5)
  have hp12 := N_pos false (6/5)
  have ht12 := FrameCoreMidScalars.trig_six_fifths
  have h14 := N_sq true (7/5)
  have hp14 := N_pos true (7/5)
  have ht14 := trig_seven_fifths
  have h25 := N_sq true (5/2)
  have hp25 := N_pos true (5/2)
  have ht25 := FrameCoreHighCorePrimary.trig_endpoints
  dsimp [CircularNorm.energy,E,B,C,sign,g,u,v] at h0 h12 h14 h25
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,add_zero] at h0
  refine ⟨?_,?_,?_,?_⟩
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h0]; norm_num)
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h12]; norm_num; linarith [ht12.2.1,ht12.2.2.1])
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h14]; norm_num; linarith [ht14.1,ht14.2.2.1])
  · exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h25]; norm_num; linarith [ht25.2.2.2.1,ht25.2.2.2.2])

end SquaresInCircles.Eight.TableFree.FrameCoreHighSecondaryNorm
