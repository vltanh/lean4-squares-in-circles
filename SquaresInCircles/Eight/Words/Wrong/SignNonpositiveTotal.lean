module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Endpoint.Principles
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: wrong-sign HG0/GA1 pairs with nonpositive total

The comparison point is on the flat core and strictly inside the same q-circle; the original H
and A states do not move. The final HG slack has a uniform positive reserve, including zero
paired total and `yG = 0` (`replacement_slack`, `wrong_sign_nonpositive_total_transport`).

The scalar statements use the whole intervals. The single auxiliary `F` has negative third
derivative (`dddF_negative`), hence negative second derivative, on `[0,1/3]` (`F_concave`). Only
its two endpoints are evaluated (`F_zero_reserve`, `F_third_reserve`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace WrongSign

abbrev L : ℝ := 447/800
abbrev K : ℝ := 13/12
abbrev κ : ℝ := 847/800
abbrev ℓ : ℝ := 21/200

def width (x : ℝ) : ℝ := (1+Real.cos x+Real.sin x)/2

def wrongTarget (x : ℝ) : ℝ := 2/5-Real.cos x/2+(183/200)*Real.sin x

def wrongTargetDerivative (x : ℝ) : ℝ := Real.sin x/2+(183/200)*Real.cos x

theorem wrongTarget_hasDeriv (x : ℝ) :
    HasDerivAt wrongTarget (wrongTargetDerivative x) x := by
  have h := ((hasDerivAt_const x (2/5 : ℝ)).fun_sub
    ((Real.hasDerivAt_cos x).div_const 2)).fun_add
    ((Real.hasDerivAt_sin x).const_mul (183/200))
  exact h.congr_deriv (by unfold wrongTargetDerivative; ring)

theorem wrongTarget_increasing : StrictMonoOn wrongTarget (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve (k := 1/2)
  · exact fun x _ => (wrongTarget_hasDeriv x).continuousAt.continuousWithinAt
  · intro x hx
    exact wrongTarget_hasDeriv x
  · norm_num
  · intro x hx
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse (Ioo_subset_Icc_self hx)
    unfold wrongTargetDerivative
    nlinarith

theorem wrongTarget_at_cut : wrongTarget ℓ < 0 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := (21/200 : ℝ))
  have hs := sin_upper_five (x := (21/200 : ℝ)) (by norm_num)
  dsimp [wrongTarget,ℓ]
  norm_num at hc hs ⊢
  linarith

/-- A wrong weak G sign forces a positive HG error separated from zero. -/
theorem positive_error_cut {bH aG g v : ℝ}
    (hb : bH<9/10) (ha : aG<283/200) (hg : 0≤g)
    (hv : v∈Icc 0 (7/10 : ℝ))
    (h : width v ≤ bH+aG*Real.sin v-g*Real.cos v) : ℓ<v := by
  obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse hv
  have hprod := mul_nonneg hg (show 0≤Real.cos v by linarith)
  have hA := mul_le_mul_of_nonneg_right ha.le hs0
  have hf : 0<wrongTarget v := by
    dsimp [wrongTarget,width] at h ⊢
    nlinarith
  by_contra! hv'
  have hm := wrongTarget_increasing.monotoneOn hv
    (show ℓ∈Icc 0 (7/10 : ℝ) by norm_num [ℓ]) hv'
  linarith [wrongTarget_at_cut]

def pairExcess (s v : ℝ) : ℝ :=
  width v+width (v+s)-2+L*(Real.sin (v+s)-Real.sin v)

def pairExcessDerivative (s v : ℝ) : ℝ :=
  -(L-1/2)*Real.cos v+κ*Real.cos (v+s)-
    (Real.sin v+Real.sin (v+s))/2

def spanDemand (s : ℝ) : ℝ := κ*Real.sin s-(1-Real.cos s)/2

def spanDemandDerivative (s : ℝ) : ℝ := κ*Real.cos s-Real.sin s/2

theorem pairExcess_hasDeriv (s v : ℝ) :
    HasDerivAt (pairExcess s) (pairExcessDerivative s v) v := by
  have hw : ∀ x : ℝ, HasDerivAt width ((Real.cos x-Real.sin x)/2) x := by
    intro x
    have h := (((Real.hasDerivAt_cos x).const_add 1).fun_add (Real.hasDerivAt_sin x)).div_const 2
    exact h.congr_deriv (by ring)
  have ha : HasDerivAt (fun x => x+s) 1 v := (hasDerivAt_id' v).add_const s
  have hs := (Real.hasDerivAt_sin (v+s)).comp v ha
  have h := (((hw v).fun_add ((hw (v+s)).comp v ha)).sub_const 2).fun_add
    ((hs.fun_sub (Real.hasDerivAt_sin v)).const_mul L)
  exact h.congr_deriv (by unfold pairExcessDerivative L κ; ring)

theorem pairExcessDerivative_pos {s v : ℝ}
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10) :
    53341/500000 < pairExcessDerivative s v := by
  obtain ⟨hc,hc1,hsi0,hsi,hsc⟩ := transport_trig ⟨hv,by linarith⟩
  obtain ⟨hC,hC1,hS0,hS,hSC⟩ := transport_trig ⟨by linarith,hvs⟩
  unfold pairExcessDerivative L κ
  nlinarith

theorem pairExcess_lower {s v : ℝ}
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10) :
    spanDemand s ≤ pairExcess s v := by
  have hm : MonotoneOn (pairExcess s) (Icc 0 (7/10-s)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (pairExcess_hasDeriv s x).continuousAt.continuousWithinAt
    · intro x hx
      exact pairExcess_hasDeriv s x
    · intro x hx
      have h := pairExcessDerivative_pos hs hx.1.le (by linarith [hx.2])
      linarith
  have h := hm (show (0:ℝ)∈Icc 0 (7/10-s) by constructor <;> linarith)
    (show v∈Icc 0 (7/10-s) by constructor <;> linarith) hv
  have h0 : pairExcess s 0=spanDemand s := by
    simp only [pairExcess,width,spanDemand,zero_add,Real.cos_zero,Real.sin_zero,L,κ]
    ring
  rw [h0] at h
  exact h

theorem spanDemand_hasDeriv (s : ℝ) :
    HasDerivAt spanDemand (spanDemandDerivative s) s := by
  have h := ((Real.hasDerivAt_sin s).const_mul κ).fun_sub
    (((hasDerivAt_const s (1:ℝ)).fun_sub (Real.hasDerivAt_cos s)).div_const 2)
  exact h.congr_deriv (by unfold spanDemandDerivative; ring)

theorem spanDemand_increasing : StrictMonoOn spanDemand (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve (k := 2/5)
  · exact fun x _ => (spanDemand_hasDeriv x).continuousAt.continuousWithinAt
  · intro x hx
    exact spanDemand_hasDeriv x
  · norm_num
  · intro x hx
    obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse (Ioo_subset_Icc_self hx)
    unfold spanDemandDerivative κ
    nlinarith

theorem spanDemand_at_third : 63/200 < spanDemand (1/3) := by
  have hs := sin_lower_seven (x := (1/3 : ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (1/3 : ℝ)) (by norm_num)
  unfold spanDemand κ
  norm_num at hs hc ⊢
  linarith

/-- The span cut uses the original two witnesses, before moving G. -/
theorem original_pair_bounds {H G A : SignedPoint} {s v : ℝ}
    (hH : H.y<9/10) (hA : A.a<283/200) (hG : L≤G.a)
    (hg : 0≤G.y) (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10)
    (hHG : width v ≤ H.y+G.a*Real.sin v-G.y*Real.cos v)
    (hGA : width (v+s) ≤ A.a-G.a*Real.sin (v+s)+G.y*Real.cos (v+s)) :
    11/10 < A.a ∧ s<1/3 := by
  have hsine : Real.sin v ≤ Real.sin (v+s) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_gt_three]) (by linarith)
  have hcos : Real.cos (v+s) ≤ Real.cos v :=
    Real.cos_le_cos_of_nonneg_of_le_pi hv
      (by linarith [Real.pi_gt_three]) (by linarith)
  have hprodA := mul_nonneg (show 0≤G.a by dsimp [L] at hG; linarith)
    (sub_nonneg.mpr hsine)
  have hprodG := mul_nonneg hg (sub_nonneg.mpr hcos)
  have hWv : 1≤width v := by
    show 1≤(1+Real.cos v+Real.sin v)/2
    rw [← edgeWidth_positive_formula ⟨hv,by linarith⟩]
    exact edgeWidth_ge_one v
  have hWz : 1≤width (v+s) := by
    show 1≤(1+Real.cos (v+s)+Real.sin (v+s))/2
    rw [← edgeWidth_positive_formula ⟨by linarith,hvs⟩]
    exact edgeWidth_ge_one (v+s)
  have hlarge : 11/10<A.a := by nlinarith
  refine ⟨hlarge,?_⟩
  have hprodL := mul_nonneg (sub_nonneg.mpr hG) (sub_nonneg.mpr hsine)
  have hpair : 2+pairExcess s v ≤ H.y+A.a := by
    dsimp [pairExcess]
    nlinarith
  have hspan := pairExcess_lower hs hv hvs
  by_contra! hs'
  have hm := spanDemand_increasing.monotoneOn
    (show (1/3:ℝ)∈Icc 0 (7/10 : ℝ) by norm_num)
    (show s∈Icc 0 (7/10 : ℝ) by constructor <;> linarith) hs'
  linarith [spanDemand_at_third]

def coefficient (z : ℝ) : ℝ := (L-1/2)*Real.cos z+Real.sin z/2-K

def error (z s : ℝ) : ℝ :=
  Real.cos s*(Real.sin z+Real.cos z-1)+coefficient z*Real.sin s

def errorDerivative (z s : ℝ) : ℝ :=
  (Real.cos s+Real.sin s/2)*Real.cos z-
    (Real.cos s+(L-1/2)*Real.sin s)*Real.sin z

theorem error_hasDeriv (z s : ℝ) :
    HasDerivAt (fun x => error x s) (errorDerivative z s) z := by
  have h := ((((Real.hasDerivAt_sin z).fun_add (Real.hasDerivAt_cos z)).sub_const 1).const_mul
    (Real.cos s)).fun_add
      ((((Real.hasDerivAt_cos z).const_mul (L-1/2)).fun_add
        ((Real.hasDerivAt_sin z).div_const 2)).sub_const K |>.mul_const (Real.sin s))
  exact h.congr_deriv (by unfold errorDerivative; ring)

theorem error_increasing {s : ℝ} (hs : s∈Icc 0 (1/3 : ℝ)) :
    StrictMonoOn (fun z => error z s) (Icc 0 (7/10 : ℝ)) := by
  apply strict_increase_of_reserve (k := 1/20)
  · exact fun z _ => (error_hasDeriv z s).continuousAt.continuousWithinAt
  · intro z hz
    exact error_hasDeriv z s
  · norm_num
  · intro z hz
    obtain ⟨hc,hc1,hsi0,hsi,hsc⟩ := transport_trig (Ioo_subset_Icc_self hz)
    obtain ⟨hC,hS0,hS⟩ := transport_trig_coarse
      (show s∈Icc 0 (7/10 : ℝ) by constructor <;> linarith [hs.1,hs.2])
    have hfirst : 3/4 ≤ Real.cos s+(L-1/2)*Real.sin s := by
      dsimp [L]
      nlinarith
    have hgap : 0 ≤ (1-L)*Real.sin s := mul_nonneg (by norm_num [L]) hS0
    have hprod := mul_nonneg
      (show 0≤Real.cos s+(L-1/2)*Real.sin s-3/4 by linarith)
      (show 0≤Real.cos z-Real.sin z by linarith)
    have hprod2 := mul_nonneg hgap (show 0≤Real.cos z by linarith)
    unfold errorDerivative L at *
    nlinarith

def F (s : ℝ) : ℝ :=
  κ/2*Real.sin (2*s+ℓ)+Real.cos (2*s+ℓ)/4+
    3/4*Real.cos ℓ+(2-κ)/2*Real.sin ℓ-Real.cos s-K*Real.sin s

def dF (s : ℝ) : ℝ :=
  κ*Real.cos (2*s+ℓ)-Real.sin (2*s+ℓ)/2+Real.sin s-K*Real.cos s

def ddF (s : ℝ) : ℝ :=
  -2*κ*Real.sin (2*s+ℓ)-Real.cos (2*s+ℓ)+Real.cos s+K*Real.sin s

def dddF (s : ℝ) : ℝ :=
  -4*κ*Real.cos (2*s+ℓ)+2*Real.sin (2*s+ℓ)-Real.sin s+K*Real.cos s

theorem F_error (s : ℝ) : F s=error (s+ℓ) s := by
  simp only [F,error,coefficient,Real.sin_add,Real.cos_add,
    Real.sin_two_mul,Real.cos_two_mul,L,K,κ]
  linear_combination (-(Real.cos ℓ/2-(47/800)*Real.sin ℓ))*Real.sin_sq_add_cos_sq s

theorem F_derivatives (s : ℝ) :
    HasDerivAt F (dF s) s ∧ HasDerivAt dF (ddF s) s ∧
      HasDerivAt ddF (dddF s) s := by
  have ha : HasDerivAt (fun x : ℝ => 2*x+ℓ) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul 2).add_const ℓ
  have hs := (Real.hasDerivAt_sin (2*s+ℓ)).comp s ha
  have hc := (Real.hasDerivAt_cos (2*s+ℓ)).comp s ha
  refine ⟨?_,?_,?_⟩
  · have h := (((((hs.const_mul (κ/2)).fun_add (hc.div_const 4)).add_const
      (3/4*Real.cos ℓ)).add_const ((2-κ)/2*Real.sin ℓ)).fun_sub
      (Real.hasDerivAt_cos s)).fun_sub ((Real.hasDerivAt_sin s).const_mul K)
    exact h.congr_deriv (by unfold dF; ring)
  · have h := (((hc.const_mul κ).fun_sub (hs.div_const 2)).fun_add
      (Real.hasDerivAt_sin s)).fun_sub ((Real.hasDerivAt_cos s).const_mul K)
    exact h.congr_deriv (by unfold ddF; ring)
  · have h := (((hs.const_mul (-2*κ)).fun_sub hc).fun_add (Real.hasDerivAt_cos s)).fun_add
      ((Real.hasDerivAt_sin s).const_mul K)
    exact h.congr_deriv (by unfold dddF; ring)

theorem dddF_negative {s : ℝ} (hs : s∈Icc 0 (1/3 : ℝ)) : dddF s<0 := by
  have hw : 2*s+ℓ ∈ Icc 0 (463/600 : ℝ) := by
    constructor <;> dsimp [ℓ] <;> linarith [hs.1,hs.2]
  have hb := trig_bracket (l := 0) (u := (463/600 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hw
  have hC : 716/1000 < Real.cos (2*s+ℓ) := by
    have := hb.2.2.1
    norm_num at this
    linarith
  have hS : Real.sin (2*s+ℓ)<698/1000 := by
    have := hb.2.1
    norm_num at this
    linarith
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
    (by linarith [hs.2,Real.pi_gt_three])
  have hcos := Real.cos_le_one s
  dsimp [dddF,κ,K]
  nlinarith

theorem ddF_zero_negative : ddF 0<0 := by
  have hs := Real.sin_ge_sub_cube (x := (21/200 : ℝ)) (by norm_num)
  have hc := Real.one_sub_sq_div_two_le_cos (x := (21/200 : ℝ))
  norm_num [ddF,ℓ,κ,K] at hs hc ⊢
  linarith

theorem F_concave : ConcaveOn ℝ (Icc 0 (1/3 : ℝ)) F := by
  have hm : AntitoneOn ddF (Icc 0 (1/3 : ℝ)) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun x _ => (F_derivatives x).2.2.continuousAt.continuousWithinAt
    · intro x hx
      exact (F_derivatives x).2.2
    · intro x hx
      exact (dddF_negative (Ioo_subset_Icc_self hx)).le
  apply concave_of_deriv2
    (fun x hx => (F_derivatives x).1)
    (fun x hx => (F_derivatives x).2.1)
  intro x hx
  exact (hm (by norm_num) hx hx.1).trans ddF_zero_negative.le

theorem F_zero_reserve : 1/25 < F 0 := by
  rw [F_error]
  have hs := sin_lower_seven (x := (21/200 : ℝ)) (by norm_num)
  have hc := cos_lower_six (x := (21/200 : ℝ)) (by norm_num)
  norm_num [error,ℓ] at hs hc ⊢
  linarith

theorem F_third_reserve : 1/25 < F (1/3) := by
  rw [F_error]
  have hst := sin_lower_seven (x := (263/600 : ℝ)) (by norm_num)
  have hct := cos_lower_six (x := (263/600 : ℝ)) (by norm_num)
  have hsr := sin_upper_five (x := (1/3 : ℝ)) (by norm_num)
  have hcr := cos_lower_six (x := (1/3 : ℝ)) (by norm_num)
  have ht := transport_trig (x := (263/600 : ℝ)) (by norm_num)
  have hr := transport_trig (x := (1/3 : ℝ)) (by norm_num)
  let B₀ : ℝ := (L-1/2)*
    (1-(263/600 : ℝ)^2/2+(263/600 : ℝ)^4/24-(263/600 : ℝ)^6/720)+
    ((263/600 : ℝ)-(263/600 : ℝ)^3/6+(263/600 : ℝ)^5/120-
      (263/600 : ℝ)^7/5040)/2-K
  let A₀ : ℝ :=
    ((263/600 : ℝ)-(263/600 : ℝ)^3/6+(263/600 : ℝ)^5/120-
      (263/600 : ℝ)^7/5040)+
    (1-(263/600 : ℝ)^2/2+(263/600 : ℝ)^4/24-(263/600 : ℝ)^6/720)-1
  have hA : A₀ ≤ Real.sin (263/600)+Real.cos (263/600)-1 := by
    dsimp [A₀]
    linarith
  have hA0 : 0≤A₀ := by norm_num [A₀]
  have hB : B₀ ≤ coefficient (263/600) := by
    unfold coefficient L K
    dsimp [B₀,L,K]
    linarith
  have hB0 : B₀≤0 := by norm_num [B₀,L,K]
  have hprodA := mul_le_mul hA hcr (by norm_num) (hA0.trans hA)
  have hprodB₁ := mul_le_mul_of_nonneg_right hB hr.2.2.1
  have hprodB₂ := mul_le_mul_of_nonpos_left hsr hB0
  have hnum : 1/25 < A₀*
      (1-(1/3 : ℝ)^2/2+(1/3 : ℝ)^4/24-(1/3 : ℝ)^6/720)+
      B₀*((1/3 : ℝ)-(1/3 : ℝ)^3/6+(1/3 : ℝ)^5/120) := by
    norm_num [A₀,B₀,L,K]
  dsimp [error,ℓ]
  norm_num at hprodA hprodB₁ hprodB₂ ⊢
  nlinarith

theorem F_reserve {s : ℝ} (hs : s∈Icc 0 (1/3 : ℝ)) : 1/25<F s :=
  concave_gt_of_endpoints F_concave hs F_zero_reserve F_third_reserve

/-- The unchanged original witnesses imply the strict transverse reserve
at the aligned comparison point. -/
theorem replacement_slack {H G A : SignedPoint} {s v : ℝ}
    (hH : H.y<9/10) (hA : A.a<283/200) (hG : L≤G.a)
    (hGa : G.a<283/200) (hg : 0≤G.y)
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10)
    (hHG : width v ≤ H.y+G.a*Real.sin v-G.y*Real.cos v)
    (hGA : width (v+s) ≤ A.a-G.a*Real.sin (v+s)+G.y*Real.cos (v+s)) :
    1/25 < H.y-(7/12)*Real.sin s+(A.a-1)*Real.cos s-width s := by
  obtain ⟨hlarge,hshort⟩ := original_pair_bounds hH hA hG hg hs hv hvs hHG hGA
  have hvcut := positive_error_cut hH hGa hg ⟨hv,by linarith⟩ hHG
  have hcs := (transport_trig_coarse (x := s) ⟨hs,by linarith⟩).1
  have hss := (transport_trig_coarse (x := s) ⟨hs,by linarith⟩).2.1
  have hcz := (transport_trig_coarse (x := v+s) ⟨by linarith,hvs⟩).1
  have hsz := (transport_trig_coarse (x := v+s) ⟨by linarith,hvs⟩).2.1
  have hw := mul_le_mul_of_nonneg_right hGA (show 0≤Real.cos s by linarith)
  have hsin : Real.sin (v+s)*Real.cos s-Real.sin v=
      Real.cos (v+s)*Real.sin s := by
    rw [Real.sin_add,Real.cos_add]
    linear_combination (Real.sin v)*Real.sin_sq_add_cos_sq s
  have hcos : Real.cos v-Real.cos (v+s)*Real.cos s=
      Real.sin (v+s)*Real.sin s := by
    rw [Real.sin_add,Real.cos_add]
    linear_combination (-Real.cos v)*Real.sin_sq_add_cos_sq s
  have hprodL := mul_nonneg (sub_nonneg.mpr hG) (mul_nonneg (show 0≤Real.cos (v+s) by linarith) hss)
  have hprodG := mul_nonneg hg (mul_nonneg hsz hss)
  have hbound : error (v+s) s ≤
      H.y-(7/12)*Real.sin s+(A.a-1)*Real.cos s-width s := by
    dsimp [error,coefficient,width,L,K] at *
    nlinarith
  have hmono := (error_increasing (s := s) ⟨hs,hshort.le⟩).monotoneOn
    (show s+ℓ∈Icc 0 (7/10 : ℝ) by constructor <;> dsimp [ℓ] <;> linarith)
    (show v+s∈Icc 0 (7/10 : ℝ) by constructor <;> linarith)
    (by linarith : s+ℓ≤v+s)
  have hF := F_reserve ⟨hs,hshort.le⟩
  rw [F_error] at hF
  exact hF.trans_le (hmono.trans hbound)

end WrongSign

/-- The nonpositive-total wrong-sign move of G to the flat point `G'`, stated with signed
coordinates and both original weak physical owners; `G'` takes the frame of A. There is no
opposite-side or E premise. -/
theorem wrong_sign_nonpositive_total_transport
    {q : ℝ} {H G A : SignedPoint} {s v : ℝ}
    (hq : q≤qCap)
    (hHs : H.Sorted) (hGs : G.Sorted) (hAs : A.Sorted)
    (hHc : H.Contained q) (hGc : G.Contained q) (hAc : A.Contained q)
    (hHcore : H.AvoidsCore) (hGcore : G.AvoidsCore) (hAcore : A.AvoidsCore)
    (_hHy : 0≤H.y) (hGy : 0≤G.y) (hAy : 0≤A.y)
    (hs : 0≤ s) (hv : 0≤v) (hvs : v+s≤7/10)
    (hHG : zeroFeasible H G v 0)
    (hGA : quarterFeasible G A (-(v+s)) 1) :
    let G' := SignedPoint.flat (-(A.a-1))
    G'.Sorted ∧ G'.Core ∧ G'.circle<q ∧
      zeroFeasible H G' (-s) 0 ∧
      quarterFeasible G' A 0 0 ∧ quarterFeasible G' A 0 1 ∧
      1/25 < zeroProjection H G' (-s) 0-edgeWidth (-s) := by
  obtain ⟨hHl,hHu,hHb⟩ := H.coordinate_bounds hHs hHcore hHc hq
  obtain ⟨hGl,hGu,hGb⟩ := G.coordinate_bounds hGs hGcore hGc hq
  obtain ⟨hAl,hAu,hAb⟩ := A.coordinate_bounds hAs hAcore hAc hq
  have hHwidth : WrongSign.width v ≤ H.y+G.a*Real.sin v-G.y*Real.cos v := by
    have h := hHG
    unfold zeroFeasible at h
    rw [edgeWidth_positive_formula ⟨hv,by linarith⟩] at h
    simp only [zeroProjection,Matrix.cons_val_zero] at h
    exact h
  have hAwidth : WrongSign.width (v+s) ≤
      A.a-G.a*Real.sin (v+s)+G.y*Real.cos (v+s) := by
    have h := hGA
    unfold quarterFeasible at h
    rw [edgeWidth_negative_formula ⟨by linarith,hvs⟩] at h
    simp only [quarterProjection,Matrix.cons_val_one,Matrix.cons_val_zero,Real.sin_neg,
      Real.cos_neg] at h
    unfold WrongSign.width
    linarith
  have hHy' : H.y<9/10 := (le_abs_self _).trans_lt hHb
  obtain ⟨hlarge,hshort⟩ := WrongSign.original_pair_bounds hHy' hAu hGl.le hGy hs hv
    hvs hHwidth hAwidth
  have hy : |-(A.a-1)|≤1/2 := by
    rw [abs_neg,abs_of_nonneg (by linarith : 0≤A.a-1)]
    linarith
  have hsort := SignedPoint.flat_sorted hy
  have hcore := SignedPoint.flat_on_core hy
  have hloss : (SignedPoint.flat (-(A.a-1))).circle<q := by
    have hA := hAc
    simp only [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] at hA
    simp only [SignedPoint.flat,SignedPoint.circle,abs_neg,
      abs_of_nonneg (by linarith : 0≤A.a-1)]
    nlinarith [sq_nonneg A.y]
  have hreserve := WrongSign.replacement_slack hHy' hAu hGl.le hGu hGy hs hv hvs
    hHwidth hAwidth
  have hactual : 1/25 < zeroProjection H (SignedPoint.flat (-(A.a-1))) (-s) 0-
      edgeWidth (-s) := by
    rw [edgeWidth_negative_formula ⟨hs,by linarith⟩]
    simp only [zeroProjection,SignedPoint.flat,Matrix.cons_val_zero,Real.sin_neg,Real.cos_neg]
    unfold WrongSign.width at hreserve
    linarith
  refine ⟨hsort,hcore,hloss,?_,?_,?_,hactual⟩
  · unfold zeroFeasible
    linarith
  · simp [quarterFeasible,quarterProjection,SignedPoint.flat]
  · simp [quarterFeasible,quarterProjection,SignedPoint.flat]

end SquaresInCircles.Eight