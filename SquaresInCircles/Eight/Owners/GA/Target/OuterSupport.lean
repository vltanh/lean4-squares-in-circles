module

public import SquaresInCircles.Eight.Owners.GA.Target.OuterData

/-!
# Eight squares: the original outer target support is maximized at tangent one half

The support comparison is on the whole permitted arc. Its endpoint
derivative is certified by the decreasing scalar B, with the prescribed
single Taylor evaluation at the frame cap.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target.Outer
open FramePair FrameCircleArc Arithmetic

theorem Cd_upper {u : ℝ} (hu : u∈Icc 0 frameCap) : Cd u<10/17 := by
  have ht := transport_trig hu
  have hc := div_le_div_of_nonneg_right ht.2.1 S_pos.le
  dsimp [Cd]
  linarith [inv_S_bounds.2,ht.2.2.1]

theorem B_bracket_pos {u : ℝ} (hu : u∈Icc 0 frameCap) :
    0<U u*(1+C u^2)-K u*C u*Cd u := by
  have hk := K_bounds hu
  have hc := C_bounds hu
  have hU := U_lower hu
  have hprod : (7/5:ℝ)<U u*(1+C u^2) := by
    have hC2 : (2:ℝ)≤1+C u^2 := by nlinarith [hc.1]
    calc
      _<U u*2 := by linarith
      _≤_ := mul_le_mul_of_nonneg_left hC2 (by linarith)
  by_cases hd : 0≤Cd u
  · have hKC : K u*C u≤2*(7/6:ℝ) :=
      mul_le_mul hk.2 hc.2.le (by linarith [hc.1]) (by norm_num)
    have hb : K u*C u*Cd u<(70/51:ℝ) := by
      calc
        _≤(2*(7/6:ℝ))*Cd u := mul_le_mul_of_nonneg_right hKC hd
        _<(2*(7/6:ℝ))*(10/17) :=
          mul_lt_mul_of_pos_left (Cd_upper hu) (by norm_num)
        _=70/51 := by norm_num
    linarith
  · have hKC : 0<K u*C u := mul_pos (by linarith [hk.1]) (by linarith [hc.1])
    have hh := mul_neg_of_pos_of_neg hKC (lt_of_not_ge hd)
    linarith

theorem B_hasDerivAt (u : ℝ) :
    HasDerivAt B (-2*K u*(U u*(1+C u^2)-K u*C u*Cd u)) u := by
  have hK : HasDerivAt (fun x => K x^2) ((2:ℕ)*K u^(2-1)*(-U u)) u :=
    (K_hasDerivAt u).fun_pow 2
  have hC : HasDerivAt (fun x => 1+C x^2) ((2:ℕ)*C u^(2-1)*Cd u) u :=
    ((C_hasDerivAt u).fun_pow 2).const_add 1
  have h : HasDerivAt (fun x => K x^2*(1+C x^2)-Q0)
      ((2:ℕ)*K u^(2-1)*(-U u)*(1+C u^2)+K u^2*((2:ℕ)*C u^(2-1)*Cd u)) u :=
    (hK.fun_mul hC).sub_const Q0
  exact h.congr_deriv (by push_cast; ring)

theorem B_antitone : AntitoneOn B (Icc 0 frameCap) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (B_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => B_hasDerivAt u)
    (fun u hu => by
      have hh := B_bracket_pos (Ioo_subset_Icc_self hu)
      have hk := (K_bounds (Ioo_subset_Icc_self hu)).1
      nlinarith)

def capCosLower : ℝ := 1-frameCap^2/2+frameCap^4/24-frameCap^6/720
def capKLower : ℝ := 1+capCosLower-(7075129/10000000)*sin9 frameCap
def capCLower : ℝ := capCosLower+sin7 frameCap/(17075129/10000000)

theorem cap_K_lower : capKLower<K frameCap := by
  have hcap : 0≤frameCap := by norm_num [frameCap]
  have hs := sin_le_sin9 hcap
  have hc := cos_lower_six hcap
  have hsp : 0<Real.sin frameCap := by
    linarith [CommonQuarter.cap_trig.1]
  have hp := mul_lt_mul_of_pos_right P_bounds.2 hsp
  have hp' := mul_le_mul_of_nonneg_left hs
    (by norm_num : (0:ℝ)≤7075129/10000000)
  dsimp [capKLower,capCosLower,K]
  linarith

theorem cap_C_lower : capCLower<C frameCap := by
  have hcap : 0≤frameCap := by norm_num [frameCap]
  have hs : sin7 frameCap≤Real.sin frameCap := by
    simpa [sin7] using sin_lower_seven hcap
  have hc := cos_lower_six hcap
  have hs7 : 0<sin7 frameCap := by norm_num [sin7,frameCap]
  have hprod := mul_lt_mul_of_pos_left S_bounds.2 hs7
  have hprod' := mul_le_mul_of_nonneg_right hs
    (by norm_num : (0:ℝ)≤17075129/10000000)
  have hdiv : sin7 frameCap/(17075129/10000000)<Real.sin frameCap/S :=
    (div_lt_div_iff₀ (by norm_num) S_pos).2 (by linarith)
  dsimp [capCLower,capCosLower,C]
  linarith

theorem cap_square_reserve :
    (3/100:ℝ)<capKLower^2*(1+capCLower^2)-Q0 := by
  norm_num [capKLower,capCLower,capCosLower,sin9,sin7,frameCap,Q0]

theorem B_cap : (3/100:ℝ)<B frameCap := by
  have hk0 : 0≤capKLower := by
    norm_num [capKLower,capCosLower,sin9,sin7,frameCap]
  have hc0 : 0≤capCLower := by
    norm_num [capCLower,capCosLower,sin7,frameCap]
  have hk := pow_lt_pow_left₀ cap_K_lower hk0 (by norm_num : (2:ℕ)≠0)
  have hc := pow_lt_pow_left₀ cap_C_lower hc0 (by norm_num : (2:ℕ)≠0)
  have hp := mul_lt_mul'' hk (by linarith : 1+capCLower^2<1+C frameCap^2)
    (by positivity) (by positivity)
  dsimp [B]
  linarith [cap_square_reserve]

theorem B_pos {u : ℝ} (hu : u∈Icc 0 frameCap) : 0<B u := by
  have hh := B_antitone hu (by norm_num [frameCap] : frameCap∈Icc 0 frameCap) hu.2
  linarith [B_cap]

theorem endpoint_slope_negative {u : ℝ} (hu : Domain u) : m-weight u*C u<0 := by
  have hb := B_pos hu.1
  have hy := Y_sq hu
  have hp := Y_pos hu
  have hk := (K_bounds hu.1).1
  have hc := (C_bounds hu.1).1
  have hkc : Y u<K u*C u := by
    have hprod : 0<K u*C u := mul_pos (by linarith) (by linarith)
    dsimp [B] at hb
    nlinarith
  have he : m-weight u*C u=(m/Y u)*(Y u-K u*C u) := by
    dsimp [weight]
    field_simp [hp.ne']
  rw [he]
  exact mul_neg_of_pos_of_neg (div_pos (by norm_num [m]) hp) (by linarith)

theorem A_half : A (1/2)=S-1/2 := by
  norm_num [A,S]

theorem Ad_antitone : AntitoneOn Ad (Icc 0 c0) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (Ad_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun b hb => Ad_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun b hb => (Add_negative (Ioo_subset_Icc_self hb)).le)

theorem target_support (a : State) (ha : a.branch.type≠0) (hb : (1/2:ℝ)≤a.b)
    {u : ℝ} (hu : Domain u) :
    weight u*a.a*Real.sin u+(m-weight u*Real.cos u)*a.b≤
      weight u*(S-1/2)*Real.sin u+(m-weight u*Real.cos u)/2 := by
  have hchart := state_outer_chart a ha
  have hhalf : (1/2:ℝ)∈Icc 0 c0 := ⟨by norm_num,by linarith [c0_bounds.1]⟩
  have hp : 0≤weight u*Real.sin u :=
    mul_nonneg (weight_pos hu).le (transport_trig hu.1).2.2.1
  have hAdhalf : Ad (1/2)=-1/S := by
    rw [Ad,A_half]
    ring
  have hm : AntitoneOn (linear (weight u*Real.sin u) (m-weight u*Real.cos u))
      (Icc (1/2) c0) := by
    apply antiOn_of_hasDeriv_nonpos
      (fun b hb => (linear_hasDerivAt ⟨by linarith [hb.1],hb.2⟩ _ _).continuousAt.continuousWithinAt)
      (fun b hb => linear_hasDerivAt ⟨by linarith [hb.1],hb.2.le⟩ _ _)
    intro b hb
    have hAd := Ad_antitone hhalf ⟨by linarith [hb.1],hb.2.le⟩ hb.1.le
    rw [hAdhalf] at hAd
    have hh := mul_le_mul_of_nonneg_left hAd hp
    have he : (weight u*Real.sin u)*(-1/S)+(m-weight u*Real.cos u)=m-weight u*C u := by
      dsimp [C]
      ring
    have hs := endpoint_slope_negative hu
    linarith
  have hbound := hm ⟨le_rfl,hhalf.2⟩ ⟨hb,hchart.2.2⟩ hb
  rw [linear,linear,A_half] at hbound
  rw [hchart.1]
  nlinarith only [hbound]

theorem optimizing_identity {u : ℝ} (hu : Domain u) :
    weight u*K u-CommonQuarter.radius*Real.sqrt (weight u^2+m^2)=-m*Y u := by
  have hy := Y_pos hu
  have hysq := Y_sq hu
  obtain ⟨n,hndef⟩ : ∃ n : ℝ, n=Real.sqrt (weight u^2+m^2) := ⟨_,rfl⟩
  have hn : 0≤n := by rw [hndef]; exact Real.sqrt_nonneg _
  have hn2 : n^2=weight u^2+m^2 := by rw [hndef]; exact Real.sq_sqrt (by positivity)
  have hr := CommonQuarter.radius_sq
  have hrp : 0<CommonQuarter.radius := by linarith [CommonQuarter.radius_bounds.1]
  have hroot : n=m*CommonQuarter.radius/Y u := by
    have hp : 0 < m*CommonQuarter.radius/Y u :=
      div_pos (mul_pos (by norm_num [m]) hrp) hy
    have he : (m*CommonQuarter.radius/Y u)^2=weight u^2+m^2 := by
      dsimp [weight]
      field_simp [hy.ne']
      rw [hr]
      nlinarith only [congrArg (fun z : ℝ => m^2*z) hysq]
    nlinarith
  rw [← hndef]
  rw [hroot]
  dsimp [weight]
  field_simp [hy.ne']
  nlinarith only [congrArg (fun z : ℝ => m*z) hysq,
    congrArg (fun z : ℝ => m*z) hr]

end SquaresInCircles.Eight.GlobalGA.Target.Outer
