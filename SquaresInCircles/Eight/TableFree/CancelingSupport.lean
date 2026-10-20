module

public import SquaresInCircles.Eight.TableFree.NegativePrimaryEntry
public import SquaresInCircles.Eight.TableFree.ContactContinuation

/-!
# The continuous H-circle bound in the canceling negative-primary transport

Uncompiled draft. A single harmonic concavity argument gives the two
intrinsic endpoint supports. This is the same whole-arc support bound as
Sections 4--5 of the canceling companion, without introducing interval data.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace CancelingSupport

abbrev p₀ : ℝ := 763/1000
abbrev t₀ : ℝ := 13/50

def m (h : ℝ) : ℝ := Real.sin h+Real.cos h

def n (h : ℝ) : ℝ := Real.cos h-Real.sin h

def S (a b h : ℝ) : ℝ := (a-1/2)*Real.sin h+(b-1/2)*Real.cos h

def U (a b h : ℝ) : ℝ := (a-1/2)*Real.cos h-(b-1/2)*Real.sin h

def tail (D : ℝ) : ℝ := Real.sqrt (qCap-(301/125-D)^2)-3/25

def tailDerivative (D : ℝ) : ℝ :=
  (301/125-D)/Real.sqrt (qCap-(301/125-D)^2)

theorem circle_identity (a b h : ℝ) :
    (S a b h+m h)^2+(U a b h+n h)^2=(a+1/2)^2+(b+1/2)^2 := by
  unfold S U m n
  have hu := Real.sin_sq_add_cos_sq h
  linear_combination ((a+1/2)^2+(b+1/2)^2)*hu

theorem endpoint_trig :
    176/125 < m (7/10) ∧ 3/25 < n (7/10) := by
  have hc := cos_lower_six (show (0:ℝ)≤7/10 by norm_num)
  have hs := sin_lower_seven (show (0:ℝ)≤7/10 by norm_num)
  have hs' := sin_upper_five (show (0:ℝ)≤7/10 by norm_num)
  constructor <;> unfold m n <;> norm_num at hc hs hs' ⊢ <;> linarith

/-- The lower envelope of the shifted circle cost is a positive harmonic.
Its minimum lies at an endpoint of the one full arc. -/
theorem support_endpoint {d u h : ℝ}
    (hd : 0≤d) (hu : 0≤u) (hh : h∈Icc 0 (7/10 : ℝ)) :
    min ((d+1)^2+(u+1)^2)
      ((d+m (7/10))^2+(u+n (7/10))^2) ≤
        (d+m h)^2+(u+n h)^2 := by
  let H : ℝ → ℝ := fun x => (d+u)*Real.cos x+(d-u)*Real.sin x
  have hH : ConcaveOn ℝ (Icc 0 (7/10 : ℝ)) H := by
    apply harmonic_concave
    intro x hx
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hx
    have hfirst := mul_nonneg hd (show 0≤Real.cos x+Real.sin x by linarith)
    have hsecond := mul_nonneg hu (sub_nonneg.mpr hsc.le)
    nlinarith
  have hend := hH.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)
    (show (7/10:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num) hh
  have hid (x : ℝ) : (d+m x)^2+(u+n x)^2=d^2+u^2+2+2*H x := by
    unfold m n H
    linear_combination 2*Real.sin_sq_add_cos_sq x
  rw [hid h,hid (7/10)]
  have hid0 : (d+1)^2+(u+1)^2=d^2+u^2+2+2*H 0 := by
    simp [H]
    ring
  rw [hid0]
  rw [min_le_iff] at hend ⊢
  rcases hend with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem tail_domain {D : ℝ} (hD : D∈Icc (1/2) p₀) :
    0<qCap-(301/125-D)^2 ∧
    0<Real.sqrt (qCap-(301/125-D)^2) ∧
    Real.sqrt (qCap-(301/125-D)^2)<11/10 := by
  have hL : (329/200 : ℝ)≤301/125-D ∧ 301/125-D≤2385/1250 := by
    constructor <;> dsimp [p₀] at hD <;> linarith [hD.1,hD.2]
  have hnonneg : 0≤301/125-D := by linarith [hL.1]
  have hsq := pow_le_pow_left₀ hnonneg hL.2 2
  have hroot : 0<qCap-(301/125-D)^2 := by
    dsimp [qCap]; norm_num at hsq; linarith
  have hsqrt := Real.sqrt_pos.mpr hroot
  have he := Real.sq_sqrt hroot.le
  have hlower := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤329/200) hL.1 2
  refine ⟨hroot,hsqrt,?_⟩
  dsimp [qCap] at he
  nlinarith

theorem tail_upper {D : ℝ} (hD : D∈Icc (1/2) p₀) : tail D<49/50 := by
  have h := (tail_domain hD).2.2
  unfold tail
  linarith

theorem tail_hasDerivAt {D : ℝ} (hD : D∈Icc (1/2) p₀) :
    HasDerivAt tail (tailDerivative D) D := by
  have hr := (tail_domain hD).1
  have hh := ((hasDerivAt_const D qCap).sub
    (((hasDerivAt_const D (301/125 : ℝ)).sub (hasDerivAt_id D)).pow 2)).sqrt hr.ne'
  convert hh.sub_const (3/25) using 1
  · rfl
  · unfold tailDerivative
    field_simp [(tail_domain hD).2.1.ne']
    ring

theorem tail_derivative_lower {D : ℝ} (hD : D∈Icc (1/2) p₀) :
    7/5<tailDerivative D := by
  obtain ⟨hr,hs0,hs⟩ := tail_domain hD
  have hlower : (329/200 : ℝ)≤301/125-D := by
    dsimp [p₀] at hD; linarith [hD.2]
  unfold tailDerivative
  rw [lt_div_iff₀ hs0]
  nlinarith

/-- The two support branches hold for the actual H circle at a feasible
contact. No monotonicity of a sampled support envelope is assumed. -/
theorem actual_H_branches {a b D h q : ℝ}
    (hD : D∈Icc (1/2) p₀) (hh : h∈Icc 0 (7/10 : ℝ))
    (hcircle : (a+1/2)^2+(b+1/2)^2≤q) (hq : q≤qCap)
    (hfeasible : 1≤D+S a b h) :
    U a b h<11/20 ∨ U a b h≤tail D := by
  by_cases hu : U a b h<0
  · exact Or.inl (by linarith)
  have hu0 : 0≤U a b h := le_of_not_gt hu
  have hd0 : 0≤1-D := by dsimp [p₀] at hD; linarith [hD.2]
  have hm0 : 0≤m h := by
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hh
    unfold m
    linarith
  have hS : 1-D≤S a b h := by linarith
  have hSq := pow_le_pow_left₀ (add_nonneg hd0 hm0)
    (add_le_add_right hS (m h)) 2
  have htotal : (1-D+m h)^2+(U a b h+n h)^2≤qCap := by
    have hid := circle_identity a b h
    linarith
  have hend := support_endpoint hd0 hu0 hh
  have hmin := hend.trans htotal
  rw [min_le_iff] at hmin
  rcases hmin with h0 | h1
  · left
    have hDhi : D≤763/1000 := hD.2
    dsimp [qCap] at h0
    by_contra! hU
    nlinarith [sq_nonneg (D-763/1000),sq_nonneg (U a b h-11/20)]
  · right
    have hm := endpoint_trig.1
    have hn := endpoint_trig.2
    have hMs : (301/125-D)^2≤(1-D+m (7/10))^2 := by
      apply pow_le_pow_left₀
      · dsimp [p₀] at hD; linarith [hD.2]
      · linarith
    have hNs : (U a b h+3/25)^2≤(U a b h+n (7/10))^2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    obtain ⟨hr,hs0,hs⟩ := tail_domain hD
    have he := Real.sq_sqrt hr.le
    unfold tail
    nlinarith

theorem quarter_tangent {x : ℝ} (hx : x∈Icc 0 (1/4 : ℝ)) :
    0≤Real.tan x ∧ Real.tan x<13/50 := by
  have hb := trig_bracket (l := 0) (u := (1/4 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hx
  have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_three])
  rw [Real.tan_eq_sin_div_cos]
  refine ⟨div_nonneg hs hc.le,?_⟩
  rw [div_lt_iff₀ hc]
  have hr : (1/4 : ℝ)-(1/4 : ℝ)^3/6+(1/4 : ℝ)^5/120 <
      (13/50 : ℝ)*(1-(1/4 : ℝ)^2/2+(1/4 : ℝ)^4/24-(1/4 : ℝ)^6/720) := by norm_num
  nlinarith [hb.2.1,hb.2.2.1]

def correlated (P x : ℝ) : ℝ :=
  PrimaryCap.value P x*Real.tan x+tail (PrimaryCap.value P x)

def correlatedDerivative (P x : ℝ) : ℝ :=
  PrimaryCap.value P x*(1+(Real.tan x)^2)+
    PrimaryCap.derivative P x*(Real.tan x+tailDerivative (PrimaryCap.value P x))

theorem correlated_hasDerivAt {P x : ℝ}
    (hx : x∈Icc 0 (1/4 : ℝ))
    (hD : PrimaryCap.value P x∈Icc (1/2) p₀) :
    HasDerivAt (correlated P) (correlatedDerivative P x) x := by
  have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
  have hd := PrimaryCap.value_hasDerivAt P x hc.ne'
  have ht := Real.hasDerivAt_tan hc.ne'
  have hh := (hd.mul ht).add ((tail_hasDerivAt hD).comp x hd)
  convert hh using 1
  · rfl
  · unfold correlatedDerivative
    have hu : 1/(Real.cos x)^2=1+(Real.tan x)^2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hc.ne']
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [hu]
    ring

theorem correlated_derivative_negative {P x : ℝ}
    (hx : x∈Icc 0 (1/4 : ℝ))
    (hD : PrimaryCap.value P x∈Icc (1/2) p₀) :
    correlatedDerivative P x < -(417/1000) := by
  obtain ⟨ht0,ht⟩ := quarter_tangent hx
  have hD0 : 0≤PrimaryCap.value P x := by linarith [hD.1]
  have hp := mul_le_mul hD.2 ht.le ht0 (by norm_num : (0:ℝ)≤p₀)
  have hc := transport_cos_pos (by rw [abs_of_nonneg hx.1]; linarith [hx.2])
  have hd := PrimaryCap.derivative_rewrite P x hc.ne'
  have hDprime : PrimaryCap.derivative P x < -(22/25) := by
    unfold PrimaryCap.K at hd
    norm_num [p₀] at hp
    linarith
  have htSq := pow_le_pow_left₀ ht0 ht.le 2
  have hterm : PrimaryCap.value P x*(1+(Real.tan x)^2)<163/200 := by
    have hh := mul_le_mul hD.2 (by linarith : 1+(Real.tan x)^2≤1+(13/50 : ℝ)^2)
      (by positivity) (by norm_num : (0:ℝ)≤p₀)
    norm_num [p₀] at hh
    linarith
  have hf := tail_derivative_lower hD
  have hpos : 7/5<Real.tan x+tailDerivative (PrimaryCap.value P x) := by linarith
  have hprod : PrimaryCap.derivative P x*(Real.tan x+tailDerivative (PrimaryCap.value P x)) <
      -(22/25 : ℝ)*(7/5) := by
    have h1 := mul_lt_mul_of_pos_right hDprime (by linarith : 0<Real.tan x+tailDerivative (PrimaryCap.value P x))
    have h2 := mul_lt_mul_of_neg_left hpos (by norm_num : -(22/25 : ℝ)<0)
    exact h1.trans h2
  unfold correlatedDerivative
  linarith

theorem correlated_upper {P z x : ℝ}
    (hP : 1/2<P ∧ P<p₀) (hz : z∈Icc 0 (1/4 : ℝ))
    (hcap : 1/2≤PrimaryCap.value P z) (hx : x∈Icc 0 z) :
    correlated P x<49/50 := by
  have hPwide : 0≤P ∧ P≤183/200 := by
    dsimp [p₀] at hP; constructor <;> linarith [hP.1,hP.2]
  have hD (y : ℝ) (hy : y∈Icc 0 z) :
      PrimaryCap.value P y∈Icc (1/2) p₀ := by
    have hywide : y∈Icc 0 (7/10 : ℝ) := ⟨hy.1,by linarith [hy.2,hz.2]⟩
    have hzwide : z∈Icc 0 (7/10 : ℝ) := ⟨hz.1,by linarith [hz.2]⟩
    have hanti := (PrimaryCap.value_strictAnti hPwide).antitoneOn hywide hzwide hy.2
    have hupper := PrimaryCap.value_le_position hPwide hywide
    exact ⟨hcap.trans hanti,hupper.trans hP.2.le⟩
  have hanti : AntitoneOn (correlated P) (Icc 0 z) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro y hy
      exact (correlated_hasDerivAt ⟨hy.1,hy.2.trans hz.2⟩ (hD y hy)).continuousAt.continuousWithinAt
    · intro y hy
      exact correlated_hasDerivAt ⟨hy.1.le,hy.2.le.trans hz.2⟩ (hD y (Ioo_subset_Icc_self hy))
    · intro y hy
      have hh := correlated_derivative_negative
        ⟨hy.1.le,hy.2.le.trans hz.2⟩ (hD y (Ioo_subset_Icc_self hy))
      linarith
  have hle := hanti ⟨le_rfl,hz.1⟩ hx hx.1
  have hzero : correlated P 0=tail P := by simp [correlated]
  rw [hzero] at hle
  exact hle.trans_lt (tail_upper ⟨hP.1.le,hP.2.le⟩)

end CancelingSupport
end SquaresInCircles.Eight.TableFree