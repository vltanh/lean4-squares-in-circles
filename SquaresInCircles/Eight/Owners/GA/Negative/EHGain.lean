module

public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds

/-!
# Eight squares: the small and far negative-EH gains

The far multiplier is `1.005`. The H zero-angle support loss is bounded by integrating its radial
derivative (`radial_derivative`, `radial_support_loss`); the resulting allowance is `.00022`
(`far_actual_gain`). No EH witness and no neighboring witness changes.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEH
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

abbrev v : ℝ := 1/10
abbrev u : ℝ := 1/4
abbrev p : ℝ := 201/200
abbrev epsilon : ℝ := 1/200
abbrev K : ℝ := 13/12
abbrev beta : ℝ := 82/125
def g (s : ℝ) : ℝ := K*Real.sin s-beta*(1-Real.cos s)
def gD (s : ℝ) : ℝ := K*Real.cos s-beta*Real.sin s
def gDD (s : ℝ) : ℝ := -K*Real.sin s-beta*Real.cos s
def G (s : ℝ) : ℝ := p*g s-11/50000
def GD (s : ℝ) : ℝ := p*gD s

theorem g_hasDerivAt (s : ℝ) : HasDerivAt g (gD s) s := by
  have h : HasDerivAt (fun s => K*Real.sin s-beta*(1-Real.cos s))
      (K*Real.cos s-beta*(- -Real.sin s)) s :=
    ((Real.hasDerivAt_sin s).const_mul K).sub
      (((Real.hasDerivAt_cos s).const_sub 1).const_mul beta)
  exact h.congr_deriv (by dsimp [gD]; ring)
theorem gD_hasDerivAt (s : ℝ) : HasDerivAt gD (gDD s) s := by
  have h : HasDerivAt (fun s => K*Real.cos s-beta*Real.sin s)
      (K*(-Real.sin s)-beta*Real.cos s) s :=
    ((Real.hasDerivAt_cos s).const_mul K).sub ((Real.hasDerivAt_sin s).const_mul beta)
  exact h.congr_deriv (by dsimp [gDD]; ring)
theorem G_hasDerivAt (s : ℝ) : HasDerivAt G (GD s) s := by
  exact ((g_hasDerivAt s).const_mul p).sub_const (11/50000)

theorem g_concave : ConcaveOn ℝ (Icc 0 frameCap) g := by
  apply concave_of_deriv2 (fun s _ => g_hasDerivAt s) (fun s _ => gD_hasDerivAt s)
  intro s hs
  have ht := transport_trig hs
  dsimp [gDD,K,beta]
  nlinarith [ht.1,ht.2.2.1]
theorem G_concave : ConcaveOn ℝ (Icc 0 frameCap) G := by
  apply concave_of_deriv2 (fun s _ => G_hasDerivAt s)
    (fun s _ => (gD_hasDerivAt s).const_mul p)
  intro s hs
  have ht := transport_trig hs
  dsimp [p,gDD,K,beta]
  nlinarith [ht.1,ht.2.2.1]

theorem gD_antitone : AntitoneOn gD (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun s _ => (gD_hasDerivAt s).continuousAt.continuousWithinAt)
    (fun s _ => gD_hasDerivAt s)
  intro s hs
  have ht := transport_trig (Ioo_subset_Icc_self hs)
  dsimp [gDD,K,beta]
  nlinarith [ht.1,ht.2.2.1]

theorem small_slope {s : ℝ} (hs : s∈Icc 0 v) : (253/250:ℝ)<gD s := by
  have hsf : s∈Icc 0 frameCap := ⟨hs.1,by dsimp [v,frameCap] at *; linarith [hs.2]⟩
  have hm := gD_antitone hsf (by norm_num [v,frameCap]) hs.2
  have ht := PositiveTD.Certificate.taylor_bounds (show v∈Icc 0 frameCap by norm_num [v,frameCap])
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (by norm_num : (0:ℝ)≤K)
  have hsin := mul_le_mul_of_nonneg_left ht.2.2.1 (by norm_num : (0:ℝ)≤beta)
  have he : (253/250:ℝ)<K*Polynomial.aeval v PositiveTD.Certificate.C10-
      beta*Polynomial.aeval v PositiveTD.Certificate.S9 := by
    norm_num [K,beta,v,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,
      PositiveTD.Certificate.S9,PositiveTD.Certificate.S5]
  dsimp only [gD] at hm ⊢
  simp only [K,beta] at hm hcos hsin he ⊢
  linarith

theorem far_slope {s : ℝ} (hs : s∈Icc v u) : (8917/10000:ℝ)<GD s := by
  have hsf : s∈Icc 0 frameCap :=
    ⟨le_trans (by norm_num [v]) hs.1,by dsimp [u,frameCap] at *; linarith [hs.2]⟩
  have hm := gD_antitone hsf (by norm_num [u,frameCap]) hs.2
  have ht := PositiveTD.Certificate.taylor_bounds (show u∈Icc 0 frameCap by norm_num [u,frameCap])
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (by norm_num : (0:ℝ)≤K)
  have hsin := mul_le_mul_of_nonneg_left ht.2.2.1 (by norm_num : (0:ℝ)≤beta)
  have he : (8917/10000:ℝ)<p*(K*Polynomial.aeval u PositiveTD.Certificate.C10-
      beta*Polynomial.aeval u PositiveTD.Certificate.S9) := by
    norm_num [K,beta,p,u,PositiveTD.Certificate.C10,PositiveTD.Certificate.C4,
      PositiveTD.Certificate.S9,PositiveTD.Certificate.S5]
  dsimp only [GD,gD] at hm ⊢
  simp only [p,K,beta] at hm hcos hsin he ⊢
  linarith

theorem small_actual_gain {b s : ℝ} (hb : b∈Icc 0 (39/250:ℝ))
    (hs : s∈Icc 0 frameCap) :
    g s≤edgeWidth s-1+(7/12)*Real.sin s-b*(1-Real.cos s) := by
  have hm := mul_le_mul_of_nonneg_right hb.2 (sub_nonneg.mpr (Real.cos_le_one s))
  rw [edgeWidth_positive_formula hs]
  dsimp [g,K,beta]
  nlinarith

theorem far_cosine {s : ℝ} (hs : s∈Icc v u) : p*Real.cos s<1 := by
  have hm := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : (0:ℝ)≤v) (by dsimp [u] at hs; linarith [hs.2,Real.pi_gt_three]) hs.1
  have ht := PositiveTD.Certificate.taylor_bounds (show v∈Icc 0 frameCap by norm_num [v,frameCap])
  have he : p*Polynomial.aeval v PositiveTD.Certificate.C12<1 := by
    norm_num [p,v,PositiveTD.Certificate.C12,PositiveTD.Certificate.C10,
      PositiveTD.Certificate.C4]
  dsimp [p] at ⊢ he
  linarith [ht.2.2.2.2.2]

theorem radial_derivative {k r : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5)) (hr : r∈Icc 1 p) :
    R*r/Real.sqrt (r^2+k^2)<17/10 := by
  have hn : 0<Real.sqrt (r^2+k^2) := Real.sqrt_pos.mpr (by nlinarith [hr.1])
  have hn2 := Real.sq_sqrt (show 0≤r^2+k^2 by positivity)
  have hr2 : r^2≤p^2 := by nlinarith [hr.1,hr.2]
  have hk2 : (3/5:ℝ)^2≤k^2 := by nlinarith [hk.1]
  have hR2 : (R*r)^2=qCap*r^2 := by rw [mul_pow,radius_sq]
  have hh : (R*r)^2<((17/10)*Real.sqrt (r^2+k^2))^2 := by
    rw [hR2,mul_pow,hn2]
    norm_num [p,qCap] at hr2 ⊢
    nlinarith
  apply (div_lt_iff₀ hn).2
  nlinarith [mul_nonneg (Real.sqrt_nonneg qCap) (show 0≤r by linarith [hr.1])]

theorem radial_support_loss {k : ℝ} (hk : k∈Icc (3/5:ℝ) (4/5)) :
    R*(Real.sqrt (p^2+k^2)-Real.sqrt (1+k^2))≤(17/10)*epsilon := by
  have hd (r : ℝ) (hr : r∈Icc 1 p) :
      HasDerivAt (fun r => R*Real.sqrt (r^2+k^2)) (R*r/Real.sqrt (r^2+k^2)) r := by
    have hn : 0<r^2+k^2 := by nlinarith [hr.1]
    have h2 : HasDerivAt (fun r : ℝ => r^2+k^2) (2*r) r := by
      simpa using ((hasDerivAt_id r).pow 2).add_const (k^2)
    have hs : 0<Real.sqrt (r^2+k^2) := Real.sqrt_pos.mpr hn
    have hh : HasDerivAt (fun r => R*Real.sqrt (r^2+k^2))
        (R*(1/(2*Real.sqrt (r^2+k^2))*(2*r))) r :=
      ((Real.hasDerivAt_sqrt hn.ne').comp r h2).const_mul R
    exact hh.congr_deriv (by field_simp)
  have hm : MonotoneOn (fun r => (17/10)*r-R*Real.sqrt (r^2+k^2)) (Icc 1 p) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun r hr =>
        (((hasDerivAt_id r).const_mul (17/10)).sub (hd r hr)).continuousAt.continuousWithinAt)
      (fun r hr =>
        ((hasDerivAt_id r).const_mul (17/10)).sub (hd r (Ioo_subset_Icc_self hr)))
    intro r hr
    linarith [radial_derivative hk (Ioo_subset_Icc_self hr)]
  have hh := hm (by norm_num [p] : (1:ℝ)∈Icc 1 p) (by norm_num [p] : p∈Icc 1 p)
    (by norm_num [p] : (1:ℝ)≤p)
  simp only [one_pow] at hh
  have he : R*(Real.sqrt (p^2+k^2)-Real.sqrt (1+k^2)) =
      R*Real.sqrt (p^2+k^2)-R*Real.sqrt (1+k^2) := by ring
  rw [he]
  norm_num only [p,epsilon] at hh ⊢
  linarith

theorem far_actual_gain {b k s : ℝ} (hb : b∈Icc 0 (39/250:ℝ))
    (hk : k∈Icc (3/5:ℝ) (4/5)) (hs : s∈Icc v u) :
    G s≤p*edgeWidth s-1+p*(7/12)*Real.sin s-(1-p*Real.cos s)*b-
      (fullSupport p k-fullSupport 1 k) := by
  have hsf : s∈Icc 0 frameCap :=
    ⟨le_trans (by norm_num [v]) hs.1,by dsimp [u,frameCap] at *; linarith [hs.2]⟩
  have hm := mul_le_mul_of_nonneg_left hb.2 (by linarith [far_cosine hs] : 0≤1-p*Real.cos s)
  have hsupport := radial_support_loss hk
  rw [edgeWidth_positive_formula hsf]
  dsimp [G,g,fullSupport,K,beta,p,epsilon] at ⊢ hsupport hm
  norm_num only [one_pow]
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeEH
