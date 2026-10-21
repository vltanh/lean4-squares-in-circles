module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperSupport

/-!
# The constant upper-high support on the entire short interval

The actual rotating-circle norm has positive radicand and second
derivative greater than `1/6`.  The complete support is consequently
strictly concave.  Two rational Taylor and squared-root comparisons
prove its endpoint values, with no sampled intermediate states.
Uncompiled source draft of HAND_LOW_HIGH_SCALAR_REPLACEMENTS §1.1.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperConstant
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FramePairCalculus FrameHighLowPrimaryGeometry
open FrameHighLowUpperSupport

def domain : Set ℝ := Icc (2/25:ℝ) (11/100)
def normA : ℝ := FrameLowArc.u^2+FrameLowArc.v^2+K^2
def normB : ℝ := -2*K*FrameLowArc.v
def normC : ℝ := 2*K*FrameLowArc.u
def Nd (x : ℝ) : ℝ := CircularNorm.d1 normA normB normC x
def Ndd (x : ℝ) : ℝ := CircularNorm.d2 normA normB normC x
def Fd (x : ℝ) : ℝ := 1+(K-9/100)*Real.cos x+(9/100)*Real.sin x-R*Nd x
def Fdd (x : ℝ) : ℝ := -(K-9/100)*Real.sin x+(9/100)*Real.cos x-R*Ndd x
def endpoint (j : Bool) : ℝ := if j then 11/100 else 2/25
def normBound (j : Bool) : ℝ := if j then 526764919/1000000000 else 12459003/25000000

theorem energy_eq (x : ℝ) : CircularNorm.energy normA normB normC x=energy K x := by
  dsimp [CircularNorm.energy,normA,normB,normC,energy]
  ring

theorem norm_eq (x : ℝ) : CircularNorm.norm normA normB normC x=N K x := by
  rw [CircularNorm.norm,energy_eq]
  rfl

theorem trig_bounds {x : ℝ} (hx : x∈domain) :
    0≤Real.sin x ∧ Real.sin x≤11/100 ∧ (19879/20000:ℝ)≤Real.cos x ∧ Real.cos x≤1 := by
  have hx0 : 0≤x := by linarith [hx.1]
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx0
    (by linarith [hx.2,FrameLowPair.pi_lower])
  have hu := Real.sin_le_self hx0
  have hc := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsq := pow_le_pow_left₀ hx0 hx.2 2
  exact ⟨hs,by linarith [hx.2],by nlinarith,Real.cos_le_one x⟩

theorem energy_positive {x : ℝ} (hx : x∈domain) :
    0<CircularNorm.energy normA normB normC x := by
  have hs := (trig_bounds hx).1
  have hf : 0<FrameLowArc.u+K*Real.sin x := by dsimp [FrameLowArc.u,K]; nlinarith
  rw [energy_eq,energy_squares]
  nlinarith [sq_pos_of_pos hf,sq_nonneg (FrameLowArc.v-K*Real.cos x)]

theorem N_positive {x : ℝ} (hx : x∈domain) : 0<N K x := by
  simpa only [norm_eq] using CircularNorm.norm_pos (energy_positive hx)

theorem N_upper {x : ℝ} (hx : x∈domain) : N K x<53/100 := by
  have ht := trig_bounds hx
  have he := N_square K x
  have hn := N_nonneg K x
  by_contra! hbad
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤53/100) hbad 2
  norm_num [energy,K,FrameLowArc.u,FrameLowArc.v] at he
  nlinarith

theorem determinant_lower : (9/50:ℝ)<normA^2-normB^2-normC^2 := by
  norm_num [normA,normB,normC,K,FrameLowArc.u,FrameLowArc.v]

theorem Ndd_lower {x : ℝ} (hx : x∈domain) : (1/6:ℝ)<Ndd x := by
  have hp := N_positive hx
  have hu := N_upper hx
  have hc := CircularNorm.curvature_identity (energy_positive hx)
  rw [norm_eq] at hc
  have hcube := pow_le_pow_left₀ hp.le hu.le 3
  have hratio : (3/10:ℝ)<(normA^2-normB^2-normC^2)/(4*(N K x)^3) := by
    apply (lt_div_iff₀ (by positivity : 0<4*(N K x)^3)).2
    nlinarith [determinant_lower]
  dsimp [Ndd]
  linarith

theorem N_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt (N K) (Nd x) x := by
  convert CircularNorm.norm_hasDerivAt (energy_positive hx) using 1
  ext t
  exact (norm_eq t).symm

theorem Nd_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt Nd (Ndd x) x :=
  CircularNorm.d1_hasDerivAt (energy_positive hx)

theorem F_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt (F K) (Fd x) x := by
  convert (((((hasDerivAt_id x).add_const
    (9/100+Real.pi/4+FrameLowArc.u*a0+(FrameLowArc.u+FrameLowArc.v)/2+(1/2-c0)*K)).add
      ((Real.hasDerivAt_sin x).const_mul (K-9/100))).sub
        ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((N_deriv hx).const_mul R)) using 1
  all_goals dsimp [F,Fd]; ring

theorem Fd_deriv {x : ℝ} (hx : x∈domain) : HasDerivAt Fd (Fdd x) x := by
  convert (((((Real.hasDerivAt_cos x).const_mul (K-9/100)).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub ((Nd_deriv hx).const_mul R)) using 1
  all_goals dsimp [Fd,Fdd]; ring

theorem curvature_negative {x : ℝ} (hx : x∈domain) : Fdd x<0 := by
  have ht := trig_bounds hx
  have hd := Ndd_lower hx
  have hproduct := mul_le_mul
    (show (197/100:ℝ)≤R by linarith [radius_precise.1]) hd.le
    (by norm_num : (0:ℝ)≤1/6) R_pos.le
  have hsin := mul_nonneg (show 0≤K-9/100 by norm_num [K]) ht.1
  dsimp [Fdd]
  nlinarith [ht.2.2.2]

theorem concave : ConcaveOn ℝ domain (F K) :=
  concave_of_deriv2 (fun x hx => F_deriv hx) (fun x hx => Fd_deriv hx)
    (fun x hx => (curvature_negative hx).le)

theorem endpoint_norm (j : Bool) : N K (endpoint j)<normBound j := by
  have hx : 0≤endpoint j := by cases j <;> norm_num [endpoint]
  have hs := HighOrderTaylor.sin_le_S13 hx
  have hc := HighOrderTaylor.C14_le_cos hx
  have he := N_square K (endpoint j)
  by_contra! hbad
  have hsq := pow_le_pow_left₀
    (show 0≤normBound j by cases j <;> norm_num [normBound]) hbad 2
  cases j <;> norm_num [endpoint,normBound,energy,K,FrameLowArc.u,FrameLowArc.v,
    HighOrderTaylor.S13,HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,
    Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,Arithmetic.cos8] at hs hc he hsq
  all_goals nlinarith

theorem endpoint_lower (j : Bool) : (8833/10000:ℝ)<F K (endpoint j) := by
  have hx : 0≤endpoint j := by cases j <;> norm_num [endpoint]
  have hs := HighOrderTaylor.S11_le_sin hx
  have hc := HighOrderTaylor.cos_le_C12 hx
  have hn := endpoint_norm j
  have hRN := mul_le_mul radius_precise.2.le hn.le (N_nonneg K (endpoint j))
    (by norm_num : (0:ℝ)≤494696877/250000000)
  have ha := a0_precise.1
  have hdiag := diagonal_precise.2
  have hpi := Arithmetic.pi_hand_enclosure.1
  cases j <;> norm_num [F,endpoint,normBound,K,FrameLowArc.u,FrameLowArc.v,
    HighOrderTaylor.S11,HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at hs hc hRN ⊢
  all_goals nlinarith

theorem lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F K x :=
  concave_gt_of_endpoints concave hx
    (by simpa [endpoint] using endpoint_lower false)
    (by simpa [endpoint] using endpoint_lower true)

theorem weak_separator {z B x : ℝ} (hz : z∈sourceDomain) (hB : B∈Icc 0 b1)
    (hx : x∈domain) (hm : 0≤upperMargin true z B x) :
    (8833/10000:ℝ)<upperCost true z B x := by
  exact (lower hx).trans_le (circle_support
    (show K∈Icc 0 K from ⟨by norm_num [K],le_rfl⟩) hz hB
    ⟨by linarith [hx.1],by linarith [hx.2,FrameLowPair.pi_lower]⟩ hm)

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperConstant
