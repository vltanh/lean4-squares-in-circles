module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import SquaresInCircles.Eight.Arithmetic.Taylor
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.GA.Positive.TDScalarBounds
public import SquaresInCircles.Eight.Owners.GA.Secant.Gain
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support

/-!
# Eight squares: the large-A negative-DE secant correction

For `c = 1.193` the sorted D support changes from the diagonal to the full circle when
`sec n = c`. Both smooth correction branches have derivative at least `M = 1.045` on their domains
(`diagonal_derivative_lower`, `interior_derivative_lower`). The transition is found by the
intermediate value theorem, and the two branches agree there by the equality of the full and the
diagonal supports (`correction_lower`). No endpoint correction or derivative reserve is a
hypothesis.
-/

section
/-!
## The small and far negative-EH gains

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
end
end
end

section
/-!
## Removing far-EH same-block saturation with its original charge

The two
identities retain both original positive and negative masses. Their
strict numerical reserves are weakened to closed inequalities, so the
zero-mass cases are included in the same theorem statements.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEH.SameBlock
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem short_trig {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) :
    (33/40:ℝ)<Real.cos t ∧ Real.sin t<113/200 ∧
      (47/50)*t≤Real.sin t := by
  have hb := trig_bracket (l:=0) (u:=(3/5:ℝ)) (by norm_num)
    (by linarith [Real.pi_gt_three]) ht
  have hs := sin_lower_seven ht.1
  have ht2 : t^2≤(3/5:ℝ)^2 := by nlinarith [ht.1,ht.2]
  have ht3 : t^3≤(9/25)*t := by nlinarith [mul_le_mul_of_nonneg_right ht2 ht.1]
  have hh : 0≤t^5*(42-t^2) := mul_nonneg (pow_nonneg ht.1 5) (by linarith)
  norm_num at hb
  exact ⟨by linarith [hb.2.2.1],by linarith [hb.2.1],by nlinarith⟩

theorem short_cosine_loss {t : ℝ} (ht : t∈Icc (0:ℝ) (3/5)) :
    1-Real.cos t≤(31/100)*Real.sin t := by
  have hd (x : ℝ) : HasDerivAt (fun x => (31/100)*Real.sin x+Real.cos x-1)
      ((31/100)*Real.cos x-Real.sin x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (31/100)).add
      (Real.hasDerivAt_cos x)).sub_const 1 using 1
  have hdd (x : ℝ) : HasDerivAt (fun x => (31/100)*Real.cos x-Real.sin x)
      (-(31/100)*Real.sin x-Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (31/100)).sub
      (Real.hasDerivAt_sin x) using 1
    ring
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (3/5))
      (fun x => (31/100)*Real.sin x+Real.cos x-1) := by
    apply concave_of_deriv2 (fun x _ => hd x) (fun x _ => hdd x)
    intro x hx
    have hs := (transport_trig (show x∈Icc 0 frameCap by
      exact ⟨hx.1,by norm_num [frameCap]; linarith [hx.2]⟩)).2.2.1
    linarith [(short_trig hx).1]
  have he : 0≤(31/100)*Real.sin (3/5:ℝ)+Real.cos (3/5:ℝ)-1 := by
    have hs := sin_lower_seven (show (0:ℝ)≤3/5 by norm_num)
    have hh := cos_lower_six (show (0:ℝ)≤3/5 by norm_num)
    norm_num at hs hh
    linarith
  have hh := hc.min_le_of_mem_Icc (by norm_num) (by norm_num) ht
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,zero_add,sub_self,min_eq_left he] at hh
  linarith

theorem cap_phi : (1409/1000:ℝ)<PositiveAngularEnvelope.phi frameCap ∧
    (3/25:ℝ)<Real.cos frameCap-Real.sin frameCap := by
  have hb := trig_bracket (l:=0) (u:=frameCap) (by norm_num [frameCap])
    (by dsimp [frameCap]; linarith [Real.pi_gt_three])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  norm_num [frameCap] at hb
  exact ⟨OrdinaryAngleConcavity.phi_cap_lower,by linarith [hb.2.2.1,hb.2.1]⟩

def phiD (t : ℝ) : ℝ := Real.cos t-Real.sin t
theorem phi_derivative (t : ℝ) : HasDerivAt PositiveAngularEnvelope.phi (phiD t) t :=
  ((Real.hasDerivAt_cos t).fun_add (Real.hasDerivAt_sin t)).congr_deriv
    (by dsimp only [phiD]; ring)
theorem phiD_derivative (t : ℝ) : HasDerivAt phiD (-PositiveAngularEnvelope.phi t) t :=
  ((Real.hasDerivAt_cos t).fun_sub (Real.hasDerivAt_sin t)).congr_deriv
    (by dsimp only [PositiveAngularEnvelope.phi]; ring)

theorem phiD_antitone : AntitoneOn phiD (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
    (fun t _ => (phiD_derivative t).continuousAt.continuousWithinAt)
    (fun t _ => phiD_derivative t)
  intro t ht
  have hh := transport_trig (Ioo_subset_Icc_self ht)
  dsimp [PositiveAngularEnvelope.phi]
  linarith [hh.1,hh.2.2.1]

theorem phi_difference {P N : ℝ} (hN : 0≤N) (hNP : N≤P)
    (hP : P≤frameCap) :
    PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) := by
  have hNcap : N≤frameCap := hNP.trans hP
  have hd (x : ℝ) : HasDerivAt
      (fun x => PositiveAngularEnvelope.phi x-PositiveAngularEnvelope.phi (x-N))
      (phiD x-phiD (x-N)) x :=
    (phi_derivative x).fun_sub (HasDerivAt.comp_sub_const x N (phi_derivative (x-N)))
  have hm : AntitoneOn
      (fun x => PositiveAngularEnvelope.phi x-PositiveAngularEnvelope.phi (x-N))
      (Icc N frameCap) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    intro x hx
    have hh := phiD_antitone
      (show x-N∈Icc 0 frameCap from ⟨by linarith [hx.1],by linarith [hx.2]⟩)
      (show x∈Icc 0 frameCap from ⟨by linarith [hx.1],hx.2.le⟩)
      (by linarith)
    linarith
  exact hm ⟨hNP,hP⟩ ⟨hNcap,le_rfl⟩ hP

theorem negative_reserve {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) :
    (4/125)*P≤ mixedBlock R a b P N-V R a b (N-P) := by
  have ha0 : 0≤a := by linarith
  have hNs : N∈Icc (0:ℝ) (3/5) := ⟨hP.trans hPN,hN⟩
  have hPs : P∈Icc (0:ℝ) (3/5) := ⟨hP,hPN.trans hN⟩
  have hNP : N-P∈Icc (0:ℝ) N := ⟨by linarith,by linarith⟩
  have hcos : Real.cos N≤Real.cos (N-P) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hNP.1
      (by linarith [Real.pi_gt_three]) hNP.2
  have hcoef := mul_le_mul_of_nonpos_right hab (sub_nonpos.mpr hcos)
  have hc := short_trig hNs
  have hs := short_trig hPs
  have hfirst : 0≤(1-(5/3)*Real.cos N)*(Real.cos P-1) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith [hc.1])
      (sub_nonpos.mpr (Real.cos_le_one P))
  have hsin : 0≤Real.sin P := by linarith [hs.2.2]
  have hsecond : (329/10000)*P≤a*(1-(5/3)*Real.sin N)*Real.sin P := by
    have hfactor : (7/120:ℝ)≤1-(5/3)*Real.sin N := by linarith [hc.2.1]
    have hprod := mul_le_mul ha hfactor (by norm_num : (0:ℝ)≤7/120) ha0
    have hprod' := mul_le_mul hprod hs.2.2
      (by positivity : (0:ℝ)≤(47/50)*P) (by positivity : (0:ℝ)≤a*(1-(5/3)*Real.sin N))
    nlinarith only [hprod']
  have hid : mixedBlock R a b P N-V R a b (N-P)=
      a*(PositiveAngularEnvelope.phi P-1)+b*(Real.cos N-Real.cos (N-P)) := by
    dsimp only [mixedBlock,V]
    rw [show -(N-P)=P-N by ring]
    ring
  have htrig : PositiveAngularEnvelope.phi P-1+(5/3)*(Real.cos N-Real.cos (N-P))=
      (1-(5/3)*Real.cos N)*(Real.cos P-1)+
        (1-(5/3)*Real.sin N)*Real.sin P := by
    rw [Real.cos_sub]
    dsimp only [PositiveAngularEnvelope.phi]
    ring
  have htrig' := congrArg (fun x : ℝ => a*x) htrig
  rw [hid]
  nlinarith [mul_nonneg ha0 hfirst]

theorem positive_reserve {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hN : 0≤N) (hNP : N≤P)
    (hP : P≤frameCap) (hNs : N≤3/5) :
    (11/500)*N≤ mixedBlock R a b P N-U R a b (P-N) := by
  have ha0 : 0≤a := by linarith
  have hn : N∈Icc (0:ℝ) (3/5) := ⟨hN,hNs⟩
  have hs := short_trig hn
  have hsin : 0≤Real.sin N := by linarith [hs.2.2]
  have hloss := short_cosine_loss hn
  have hcos := Real.cos_le_one N
  have hcoef := mul_le_mul_of_nonpos_right hab (by linarith : Real.cos N-1≤0)
  have hdiff := mul_le_mul_of_nonneg_left (phi_difference hN hNP hP) ha0
  have hc := cap_phi
  have hcap : (11/500)*N≤a*(PositiveAngularEnvelope.phi frameCap-
      PositiveAngularEnvelope.phi (frameCap-N)+(5/3)*(Real.cos N-1)) := by
    have hid : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)+
        (5/3)*(Real.cos N-1)=
        (PositiveAngularEnvelope.phi frameCap-5/3)*(1-Real.cos N)+
          (Real.cos frameCap-Real.sin frameCap)*Real.sin N := by
      dsimp only [PositiveAngularEnvelope.phi]
      rw [Real.cos_sub,Real.sin_sub]
      ring
    have hfirst := mul_le_mul_of_nonneg_right hc.1.le (by linarith : 0≤1-Real.cos N)
    have hsecond := mul_le_mul_of_nonneg_right hc.2.le hsin
    have hl : (11/300)*N≤PositiveAngularEnvelope.phi frameCap-
        PositiveAngularEnvelope.phi (frameCap-N)+(5/3)*(Real.cos N-1) := by
      rw [hid]
      nlinarith
    have hm := mul_le_mul ha hl (by positivity : (0:ℝ)≤(11/300)*N) ha0
    nlinarith only [hm]
  have hid : mixedBlock R a b P N-U R a b (P-N)=
      a*(PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N))+
        b*(Real.cos N-1) := by
    dsimp only [mixedBlock,U]
    ring
  rw [hid]
  nlinarith only [hcap,hdiff,hcoef]

theorem negative_charged {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hP : 0≤P) (hPN : P≤N) (hN : N≤3/5) :
    V R a b (N-P)≤ mixedBlock R a b P N-epsilon*P := by
  have hh := negative_reserve ha hab hP hPN hN
  dsimp [epsilon]
  nlinarith

theorem positive_charged {a b P N : ℝ} (ha : (3/5:ℝ)≤a)
    (hab : b≤(5/3)*a) (hN : 0≤N) (hNP : N≤P)
    (hP : P≤frameCap) (hNs : N≤3/5) :
    U R a b (P-N)-epsilon*(P-N)≤ mixedBlock R a b P N-epsilon*P := by
  have hh := positive_reserve ha hab hN hNP hP hNs
  dsimp [epsilon]
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeEH.SameBlock
end
end
end

section
/-!
## The secant gains of a negative core-E primary

The DE estimate keeps the reserve `1/390` after the angular charge `21/20` (`de_gain_lower`). The
EH estimate keeps `1/625` after the charge `103/100` (`eh_gain_lower`); it includes the change of
the H circle norm itself, not only its tangent and secant lower model.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeESecant
open Arithmetic

def K : ℝ := 13/12

def gain (b s : ℝ) : ℝ :=
  (K*Real.sin s-b*(1-Real.cos s))/Real.cos s

def gainD (b s : ℝ) : ℝ := (K-b*Real.sin s)/Real.cos s^2

def gainDD (b s : ℝ) : ℝ :=
  (2*K*Real.sin s-b*(1+Real.sin s^2))/Real.cos s^3

theorem cos_pos {s : ℝ} (hs : s∈Icc 0 frameCap) : 0<Real.cos s :=
  transport_cos_pos (by rw [abs_of_nonneg hs.1]; exact hs.2)

theorem gain_secant (b : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    gain b s=K*Real.tan s-b*(1/Real.cos s-1) := by
  rw [Real.tan_eq_sin_div_cos]
  dsimp [gain]
  field_simp [(cos_pos hs).ne']

@[simp] theorem gain_zero (b : ℝ) : gain b 0=0 := by simp [gain]

theorem gain_hasDerivAt (b : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt (gain b) (gainD b s) s := by
  have hc := (cos_pos hs).ne'
  have hd := (((Real.hasDerivAt_sin s).const_mul K).sub
    (((Real.hasDerivAt_cos s).const_sub 1).const_mul b)).div
      (Real.hasDerivAt_cos s) hc
  convert hd using 1
  · rfl
  · dsimp [gainD]
    field_simp [hc]
    nlinarith only [congrArg (fun z : ℝ => K*z) (Real.sin_sq_add_cos_sq s)]

theorem gainD_hasDerivAt (b : ℝ) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt (gainD b) (gainDD b s) s := by
  have hc := (cos_pos hs).ne'
  have hd := (((Real.hasDerivAt_sin s).const_mul b).const_sub K).div
    ((Real.hasDerivAt_cos s).pow 2) (pow_ne_zero 2 hc)
  convert hd using 1
  · rfl
  · dsimp [gainDD]
    field_simp [hc]
    linear_combination b*(Real.sin_sq_add_cos_sq s)

theorem gain_antitone_coefficient {b c s : ℝ} (hbc : b≤c)
    (hs : s∈Icc 0 frameCap) : gain c s≤gain b s := by
  have hcos := Real.cos_le_one s
  have hp := mul_le_mul_of_nonneg_right hbc (by linarith : 0≤1-Real.cos s)
  exact div_le_div_of_nonneg_right (by linarith) (cos_pos hs).le

/-- The polynomial is the DE reserve multiplied by the cosine and divided by its angle. Its
negative high powers are bounded on the whole interval. -/
def dePolynomial (s : ℝ) : ℝ :=
  1/30-s/5+(31/90)*s^2+(1/60)*s^3-(5/144)*s^4-(1/1800)*s^5+
    ((21/20)/720-K/5040)*s^6-((21/20)/40320)*s^8

theorem dePolynomial_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (1/390:ℝ)≤dePolynomial s := by
  have h2 : s^2≤(7/10:ℝ)^2 := pow_le_pow_left₀ hs.1 hs.2 2
  have h3 : s^3≤(7/10:ℝ)^3 := pow_le_pow_left₀ hs.1 hs.2 3
  have h6 : s^6≤(7/10:ℝ)^6 := pow_le_pow_left₀ hs.1 hs.2 6
  have h4 : s^4≤(7/10:ℝ)^2*s^2 := by
    calc s^4=s^2*s^2 := by ring
         _≤(7/10:ℝ)^2*s^2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg s)
  have h5 : s^5≤(7/10:ℝ)^3*s^2 := by
    calc s^5=s^3*s^2 := by ring
         _≤(7/10:ℝ)^3*s^2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg s)
  have h8 : s^8≤(7/10:ℝ)^6*s^2 := by
    calc s^8=s^6*s^2 := by ring
         _≤(7/10:ℝ)^6*s^2 := mul_le_mul_of_nonneg_right h6 (sq_nonneg s)
  have hquadratic : (1/390:ℝ)≤1/30-s/5+(13/40)*s^2 := by
    nlinarith [sq_nonneg (s-(4/13:ℝ))]
  have hpoly : 1/30-s/5+(13/40)*s^2≤dePolynomial s := by
    dsimp [dePolynomial,K]
    nlinarith only [h4,h5,h8,pow_nonneg hs.1 3,pow_nonneg hs.1 6,sq_nonneg s]
  exact hquadratic.trans hpoly

theorem de_cosine_reserve {s : ℝ} (hs : s∈Icc 0 frameCap) :
    s/390≤K*Real.sin s+(2/5)*(Real.cos s-1)-(21/20)*s*Real.cos s := by
  have hsin : sin7 s≤Real.sin s := sin_lower_seven hs.1
  have hcos := cos_lower_six hs.1
  have hupper := cos_le_cos8 hs.1
  have h1 := mul_le_mul_of_nonneg_left hsin (by norm_num [K] : 0≤K)
  have h2 := mul_le_mul_of_nonneg_left hcos (by norm_num : (0:ℝ)≤2/5)
  have h3 := mul_le_mul_of_nonneg_left hupper
    (mul_nonneg (by norm_num : (0:ℝ)≤21/20) hs.1)
  have he : K*sin7 s+(2/5)*(1-s^2/2+s^4/24-s^6/720-1)-
      (21/20)*s*cos8 s=s*dePolynomial s := by
    dsimp [sin7,cos8,dePolynomial,K]
    ring
  have hp := mul_le_mul_of_nonneg_left (dePolynomial_lower hs) hs.1
  nlinarith only [h1,h2,h3,he,hp]

theorem de_gain_lower {b s : ℝ} (hb : b≤2/5)
    (hs : s∈Icc 0 frameCap) :
    ((21/20:ℝ)+1/390)*s≤gain b s := by
  have hbase : ((21/20:ℝ)+1/390)*s≤gain (2/5) s := by
    have hres := de_cosine_reserve hs
    have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one s)
      (div_nonneg hs.1 (by norm_num : (0:ℝ)≤390))
    dsimp [gain]
    apply (le_div_iff₀ (cos_pos hs)).2
    nlinarith only [hres,hm]
  exact hbase.trans (gain_antitone_coefficient hb hs)

theorem de_secant_range {s : ℝ} (hs : s∈Icc 0 frameCap) :
    1≤1/Real.cos s ∧ 1/Real.cos s≤327/250 := by
  have ht := transport_trig hs
  have hc := cos_pos hs
  constructor
  · apply (le_div_iff₀ hc).2
    simpa using Real.cos_le_one s
  · apply (div_le_iff₀ hc).2
    linarith [ht.1]

theorem eh_short_subset {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    s∈Icc 0 frameCap := ⟨hs.1,by dsimp [frameCap]; linarith [hs.2]⟩

theorem eh_secant_range {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    1≤1/Real.cos s ∧ 1/Real.cos s≤1033/1000 := by
  have hc := cos_pos (eh_short_subset hs)
  have ht := trig_bracket (l := 0) (u := (1/4:ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hs
  constructor
  · apply (le_div_iff₀ hc).2
    simpa using Real.cos_le_one s
  · apply (div_le_iff₀ hc).2
    norm_num at ht
    linarith [ht.2.2.1]

/-- The lower EH model is concave up to the EH cutoff `1/4`. -/
theorem eh_gain_curvature {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    gainDD (29/50) s≤0 := by
  have hsupper : Real.sin s≤1/4 := (Real.sin_le hs.1).trans hs.2
  have hnum : 2*K*Real.sin s-(29/50)*(1+Real.sin s^2)≤-(23/600:ℝ) := by
    dsimp [K]
    nlinarith [sq_nonneg (Real.sin s)]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (pow_nonneg (cos_pos (eh_short_subset hs)).le 3)

theorem eh_cap_gain :
    ((103/100:ℝ)+1/625)*(1/4)≤gain (29/50) (1/4) := by
  have hsin := sin_lower_seven (by norm_num : (0:ℝ)≤1/4)
  have hcos := cos_lower_six (by norm_num : (0:ℝ)≤1/4)
  have hmul := mul_le_mul_of_nonneg_left hcos
    (by norm_num : (0:ℝ)≤29/50-(103/100)*(1/4))
  have hs := mul_le_mul_of_nonneg_left hsin (by norm_num [K] : 0≤K)
  have hres : (1/2500:ℝ)<
      K*Real.sin (1/4)+(29/50-(103/100)*(1/4))*Real.cos (1/4)-29/50 := by
    norm_num [K] at hs hmul ⊢
    linarith
  have hc := cos_pos (eh_short_subset (by norm_num : (1/4:ℝ)∈Icc 0 (1/4)))
  dsimp [gain]
  apply (le_div_iff₀ hc).2
  nlinarith [Real.cos_le_one (1/4:ℝ)]

theorem eh_model_gain_lower {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    ((103/100:ℝ)+1/625)*s≤gain (29/50) s := by
  let f : ℝ→ℝ := fun t => gain (29/50) t-((103/100:ℝ)+1/625)*t
  have hconc : ConcaveOn ℝ (Icc 0 (1/4:ℝ)) f := by
    apply concave_of_deriv2
      (f' := fun t => gainD (29/50) t-((103/100:ℝ)+1/625))
      (f'' := gainDD (29/50))
    · intro t ht
      have h1 := (gain_hasDerivAt (29/50) (eh_short_subset ht)).sub
        ((hasDerivAt_id t).const_mul ((103/100:ℝ)+1/625))
      simp only [id,mul_one] at h1
      exact h1
    · intro t ht
      exact (gainD_hasDerivAt (29/50) (eh_short_subset ht)).sub_const _
    · exact fun t ht => eh_gain_curvature ht
  have hmin := concave_endpoint_reserve (f := f) (k := 0) (by norm_num) hs
    (by simpa using hconc)
  have h0 : f 0=0 := by simp [f]
  have hcap : 0≤f (1/4) := by dsimp [f]; linarith [eh_cap_gain]
  have hmin0 : 0 ≤ min (f 0) (f (1/4)) := le_min (by rw [h0]) hcap
  have hfs : 0≤f s := by
    simp only [zero_div,zero_mul,add_zero] at hmin
    exact hmin0.trans hmin
  dsimp [f] at hfs
  linarith

/-- The positive-square comparison that bounds the change of the H norm. -/
theorem eh_root_slope {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    Real.sqrt qCap*u≤(79/50)*Real.sqrt (u^2+(39/50:ℝ)^2) := by
  have hu0 : 0≤u := by linarith [hu.1]
  have hu2 : u^2≤(1033/1000:ℝ)^2 := pow_le_pow_left₀ hu0 hu.2 2
  have hp : 0≤u^2+(39/50:ℝ)^2 := by positivity
  have hsq := Real.sq_sqrt hp
  have hR := Real.sq_sqrt (by norm_num [qCap] : 0≤qCap)
  have htarget : qCap*u^2<(79/50:ℝ)^2*(u^2+(39/50:ℝ)^2) := by
    dsimp [qCap]
    nlinarith only [hu2]
  have hleft := mul_nonneg (Real.sqrt_nonneg qCap) hu0
  have hright : 0≤(79/50)*Real.sqrt (u^2+(39/50:ℝ)^2) := by positivity
  rw [← sq_le_sq₀ hleft hright,mul_pow,hR,mul_pow,hsq]
  exact htarget.le

theorem eh_root_difference {u : ℝ} (hu : u∈Icc 1 (1033/1000:ℝ)) :
    Real.sqrt qCap*(Real.sqrt (u^2+(39/50:ℝ)^2)-
      Real.sqrt (1+(39/50:ℝ)^2))≤(79/50)*(u-1) := by
  let r := Real.sqrt (u^2+(39/50:ℝ)^2)
  let r0 := Real.sqrt (1+(39/50:ℝ)^2)
  have hr : r^2=u^2+(39/50:ℝ)^2 := Real.sq_sqrt (by positivity)
  have hr0 : r0^2=1+(39/50:ℝ)^2 := Real.sq_sqrt (by norm_num)
  have hsum : 0<r+r0 := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
    (Real.sqrt_pos.mpr (by norm_num))
  have h1 := eh_root_slope hu
  have h0 := eh_root_slope (u := 1) (by norm_num)
  simp only [one_pow,mul_one] at h0
  have hbound : Real.sqrt qCap*(u+1)≤(79/50)*(r+r0) := by
    dsimp [r,r0]
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound (sub_nonneg.mpr hu.1)
  have hid : Real.sqrt qCap*(r-r0)*(r+r0)=Real.sqrt qCap*(u+1)*(u-1) := by
    have he : (r-r0)*(r+r0)=(u+1)*(u-1) := by nlinarith only [hr,hr0]
    rw [mul_assoc,he]
    ring
  have hgoal : Real.sqrt qCap*(r-r0)*(r+r0)≤(79/50)*(u-1)*(r+r0) := by
    rw [hid]
    linarith only [hm]
  exact le_of_mul_le_mul_right hgoal hsum

/-- The gain of the H norm, with its secant multiplier, is bounded below. -/
theorem eh_gain_lower {s : ℝ} (hs : s∈Icc 0 (1/4:ℝ)) :
    ((103/100:ℝ)+1/625)*s≤ secantGain qCap (39/50) s := by
  have hmodel := eh_model_gain_lower hs
  have hsec := eh_secant_range hs
  have hnorm := eh_root_difference hsec
  have hformula := secantGain_eq_secant_expression qCap (39/50)
    (cos_pos (eh_short_subset hs))
  have hgain := gain_secant (29/50) (eh_short_subset hs)
  dsimp [K] at hgain
  nlinarith only [hmodel,hnorm,hformula,hgain]

end SquaresInCircles.Eight.GlobalGA.NegativeESecant
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
open Secondary

abbrev k : ℝ := 717/1000
abbrev l : ℝ := 457/500
abbrev c : ℝ := 1193/1000
abbrev M : ℝ := 209/200
abbrev K : ℝ := 13/12
abbrev beta : ℝ := 82/125

def secant (s : ℝ) : ℝ := 1/Real.cos s

def dCorrection (s : ℝ) : ℝ :=
  (secant s-1)/2+K*Real.tan s-
    (clippedSupport (secant s) c-clippedSupport 1 c)

def fullCorrection (s : ℝ) : ℝ :=
  secantGain qCap c s+diagonalSupport 1 c-fullSupport 1 c

theorem secant_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt secant (Real.sin s/Real.cos s^2) s := by
  have h := (hasDerivAt_const s (1:ℝ)).div (Real.hasDerivAt_cos s)
    (NegativeESecant.cos_pos hs).ne'
  exact h.congr_deriv (by ring)

theorem secant_monotone : MonotoneOn secant (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (secant_hasDerivAt hs).continuousAt.continuousWithinAt)
    (fun s hs => secant_hasDerivAt (Ioo_subset_Icc_self hs))
  intro s hs
  exact div_nonneg (transport_trig (Ioo_subset_Icc_self hs)).2.2.1 (sq_nonneg _)

theorem secant_range {s : ℝ} (hs : s∈Icc 0 frameCap) : secant s∈Icc 1 (327/250:ℝ) :=
  NegativeESecant.de_secant_range hs

theorem correction_diagonal {s : ℝ} (hs : s∈Icc 0 frameCap) (hc : secant s≤c) :
    dCorrection s=NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s := by
  rw [dCorrection,clippedSupport,ite_eq_left hc]
  have h1 : (1:ℝ)≤c := by norm_num [c]
  rw [clippedSupport,ite_eq_left h1,NegativeESecant.gain_secant _ hs]
  dsimp [diagonalSupport,NegativeESecant.K,K,secant]
  ring

theorem correction_full {s : ℝ} (hs : s∈Icc 0 frameCap) (hc : c≤ secant s) :
    dCorrection s=fullCorrection s := by
  have hsupport : clippedSupport (secant s) c=fullSupport (secant s) c := by
    by_cases he : secant s≤c
    · have heq : secant s=c := le_antisymm he hc
      have hsum : 0≤ secant s+c := by
        dsimp [c] at hc ⊢
        linarith
      rw [clippedSupport,ite_eq_left he,full_at_diagonal heq hsum]
    · simp [clippedSupport,he]
  have h1 : (1:ℝ)≤c := by norm_num [c]
  rw [dCorrection,hsupport,clippedSupport,ite_eq_left h1,fullCorrection,
    secantGain_eq_secant_expression qCap c (NegativeESecant.cos_pos hs)]
  dsimp [fullSupport,diagonalSupport,secant,K]
  norm_num
  ring

theorem diagonal_derivative_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    M≤NegativeESecant.gainD (GlobalGA.Secondary.diagonal-1/2) s := by
  have ht := transport_trig hs
  have hd := mul_le_mul_of_nonneg_right
    (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) ht.2.2.1
  dsimp [NegativeESecant.gainD,NegativeESecant.K,M]
  apply (le_div_iff₀ (sq_pos_of_pos (NegativeESecant.cos_pos hs))).2
  nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s-(40/209:ℝ))]

theorem diagonal_gain_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    M*s≤NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s := by
  have h := derivative_reserve
    (f := NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2))
    (df := NegativeESecant.gainD (GlobalGA.Secondary.diagonal-1/2)) (k := M)
    (fun z hz => (NegativeESecant.gain_hasDerivAt _ hz).continuousAt.continuousWithinAt)
    (fun z hz => NegativeESecant.gain_hasDerivAt _ (Ioo_subset_Icc_self hz))
    (fun z hz => diagonal_derivative_lower (Ioo_subset_Icc_self hz))
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hs hs.1
  simpa using h

theorem interior_sine_lower {s : ℝ} (hs : s∈Icc 0 frameCap) (hc : c≤ secant s) :
    (1/2:ℝ)<Real.sin s := by
  have ht := transport_trig hs
  have hcos := NegativeESecant.cos_pos hs
  have hprod : c*Real.cos s≤1 := (le_div_iff₀ hcos).1 hc
  have hprod0 : 0≤c*Real.cos s := mul_nonneg (by norm_num [c]) hcos.le
  have hprod2 := pow_le_pow_left₀ hprod0 hprod 2
  by_contra! hsin
  have hsin2 := pow_le_pow_left₀ ht.2.2.1 hsin 2
  dsimp [c] at hprod2
  nlinarith [Real.sin_sq_add_cos_sq s]

theorem interior_root_ratio {s : ℝ} (hs : s∈Icc 0 frameCap) :
    Real.sqrt qCap/Real.sqrt (gainRadicand c s)<147/100 := by
  have ht := transport_trig hs
  have hcos2 : (7648/10000:ℝ)^2≤Real.cos s^2 :=
    pow_le_pow_left₀ (by norm_num) ht.1.le 2
  have hr := gainRadicand_pos c s
  have hroot := Real.sqrt_pos.mpr hr
  have hroot2 := Real.sq_sqrt hr.le
  have hcompare : qCap<(147/100:ℝ)^2*gainRadicand c s := by
    dsimp [gainRadicand,c,qCap]
    nlinarith only [hcos2]
  apply (div_lt_iff₀ hroot).2
  have hq0 : (0:ℝ)≤qCap := by norm_num [qCap]
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [mul_pow,Real.sq_sqrt hq0,hroot2]
  linarith

theorem interior_derivative_lower {s : ℝ} (hs : s∈Icc 0 frameCap)
    (hc : c≤ secant s) : M≤ secantGainDeriv qCap c s := by
  have ht := transport_trig hs
  have hsin := interior_sine_lower hs hc
  have hr := interior_root_ratio hs
  have hm := mul_le_mul_of_nonneg_right hr.le ht.2.2.1
  have hunit := Real.sin_sq_add_cos_sq s
  have he : Real.sqrt qCap*Real.sin s/Real.sqrt (gainRadicand c s)=
      (Real.sqrt qCap/Real.sqrt (gainRadicand c s))*Real.sin s := by ring
  dsimp [secantGainDeriv]
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos (NegativeESecant.cos_pos hs))).2
  dsimp [M]
  nlinarith [sq_nonneg (Real.sin s-(1/2:ℝ))]

theorem fullCorrection_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt fullCorrection (secantGainDeriv qCap c s) s :=
  ((secantGain_hasDerivAt qCap c (NegativeESecant.cos_pos hs).ne').add_const (diagonalSupport 1 c)).sub_const (fullSupport 1 c)

/-- Each derivative is used only on its side of the switch of the sorted support. -/
theorem correction_lower {s : ℝ} (hs : s∈Icc 0 frameCap) : M*s≤dCorrection s := by
  by_cases hc : secant s≤c
  · rw [correction_diagonal hs hc]
    exact diagonal_gain_lower hs
  · have hs0 : (0:ℝ) ≤ s := hs.1
    have hcont : ContinuousOn secant (Icc 0 s) := by
      intro z hz
      exact (secant_hasDerivAt ⟨hz.1,hz.2.trans hs.2⟩).continuousAt.continuousWithinAt
    obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hs0 hcont
      (show c∈Icc (secant 0) (secant s) by
        constructor
        · norm_num [secant,c]
        · exact (lt_of_not_ge hc).le)
    have hti : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hs.2⟩
    have htransition : NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) t=
        fullCorrection t := by
      rw [← correction_diagonal hti hte.le,correction_full hti hte.ge]
    have hlower : M*t≤fullCorrection t := by
      rw [← htransition]
      exact diagonal_gain_lower hti
    have hmono (z : ℝ) (hz : z∈Ioo t s) : c≤ secant z := by
      rw [← hte]
      exact secant_monotone hti ⟨ht.1.trans hz.1.le,hz.2.le.trans hs.2⟩ hz.1.le
    have hderiv := derivative_reserve (f := fullCorrection)
      (df := secantGainDeriv qCap c) (k := M)
      (fun z hz => (fullCorrection_hasDerivAt
        ⟨ht.1.trans hz.1,hz.2.trans hs.2⟩).continuousAt.continuousWithinAt)
      (fun z hz => fullCorrection_hasDerivAt ⟨ht.1.trans hz.1.le,hz.2.le.trans hs.2⟩)
      (fun z hz => interior_derivative_lower
        ⟨ht.1.trans hz.1.le,hz.2.le.trans hs.2⟩ (hmono z hz))
      (show t∈Icc t s from ⟨le_rfl,ht.2⟩)
      (show s∈Icc t s from ⟨ht.2,le_rfl⟩) ht.2
    rw [correction_full hs (lt_of_not_ge hc).le]
    linarith

/-- The geometry of D gives the correction bound directly; the diagonal baseline is kept as it
is. -/
theorem actual_correction_lower {q s : ℝ} {D : SignedPoint}
    (hsort : D.Sorted) (hy : 0≤D.y) (hc : D.Contained q) (hq : q≤qCap)
    (hs : s∈Icc 0 frameCap) :
    M*s≤(secant s-1)/2+K*Real.tan s-
      (secant s*D.a+c*D.y-clippedSupport 1 c) := by
  have hsec := secant_range hs
  have hsupport := actual_clipped_support (f := secant s) (g := c)
    hsort hy hc hq (by dsimp [c]; linarith [hsec.1])
  have hgain := correction_lower hs
  dsimp [dCorrection] at hgain
  simp only [c,K,M] at hgain hsupport ⊢
  linarith only [hgain,hsupport]

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
end
end
end
