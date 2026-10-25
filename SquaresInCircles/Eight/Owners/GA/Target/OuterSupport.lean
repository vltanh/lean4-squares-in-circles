module

public import SquaresInCircles.Eight.Frames.High.Arc
public import SquaresInCircles.Eight.Owners.CenteredMonomialBounds
public import SquaresInCircles.Eight.Owners.Outer.AnchorDomain
public import SquaresInCircles.Eight.Owners.Stationary.TerminalWeights
public import SquaresInCircles.Eight.Owners.Zero.SignSupport

/-!
# Eight squares: the original outer target support is maximized at tangent one half

The support comparison is on the whole permitted arc. Its endpoint
derivative is certified by the decreasing scalar B, with the prescribed
single Taylor evaluation at the frame cap.
-/

section
/-!
## The stronger original outer marker floor for the high-GA target cut

The three original charts keep their actual markers, including both
choices at either junction. The low arc uses its whole-arc derivative,
the middle arc its two intrinsic endpoints, and the high arc the
displayed positive shifted-circle square reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target
open FramePair ZeroPrimary FrameCircleArc FrameLowArc FrameMidArc
open GlobalZeroSign

def m : ℝ := 8669/10000

lemma low_marker {b : ℝ} (hb : b∈Icc 0 b1) : m*b≤L b := by
  have hmono : MonotoneOn (fun z => L z-m*z) (Icc 0 b1) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun z hz => ((L_hasDerivAt hz).sub ((hasDerivAt_id z).const_mul m)).continuousAt.continuousWithinAt)
      (fun z hz => (L_hasDerivAt (Ioo_subset_Icc_self hz)).sub ((hasDerivAt_id z).const_mul m))
    intro z hz
    have hr := (slope_bounds (Ioo_subset_Icc_self hz)).2
    dsimp [Ld,FrameLowArc.u,FrameLowArc.v,m]
    linarith
  have hh := hmono ⟨le_rfl,b1_mem.1⟩ hb hb.1
  simpa only [L_zero,mul_zero,sub_zero,sub_nonneg] using hh

lemma middle_marker {b : ℝ} (hb : b∈Icc b1 b2) : m*b≤M b := by
  have he := linear_endpoint_lower (p:=p) (q:=q-m) (by norm_num [p]) b1_mem.1 b2_mem.2 hb
  have hleft : -cM<linear p (q-m) b1 := by
    rw [linear,A_b1]
    dsimp [p,q,m,cM,b1]
    linarith [a1_bounds.1]
  have hright : -cM<linear p (q-m) b2 := by
    rw [linear,A_b2]
    dsimp [p,q,m,cM,b2]
    linarith [a2_bounds.1]
  have hh := (lt_min hleft hright).trans_le he
  dsimp [linear,FrameMidArc.M] at hh ⊢
  linarith

lemma high_square_reserve :
    ((314159/100000:ℝ)/4+(89293/500000)*(449607/500000)+
      (FrameHighArc.u+(m-FrameHighArc.v))/2)^2-
        Q0*(FrameHighArc.u^2+(m-FrameHighArc.v)^2)=
      6545897824987888201/62500000000000000000000 := by
  norm_num [FrameHighArc.u,FrameHighArc.v,m,Q0]

lemma high_support_reserve :
    CommonQuarter.radius*Real.sqrt (FrameHighArc.u^2+(m-FrameHighArc.v)^2)-
      (FrameHighArc.u+(m-FrameHighArc.v))/2<FrameHighArc.k := by
  let n : ℝ := Real.sqrt (FrameHighArc.u^2+(m-FrameHighArc.v)^2)
  let l : ℝ := (314159/100000:ℝ)/4+(89293/500000)*(449607/500000)+
    (FrameHighArc.u+(m-FrameHighArc.v))/2
  have hn : n^2=FrameHighArc.u^2+(m-FrameHighArc.v)^2 := Real.sq_sqrt (by positivity)
  have hprod : (CommonQuarter.radius*n)^2=Q0*(FrameHighArc.u^2+(m-FrameHighArc.v)^2) := by
    rw [mul_pow,CommonQuarter.radius_sq,hn]
  have hl : 0<l := by norm_num [l,FrameHighArc.u,FrameHighArc.v,m]
  have hreserve := high_square_reserve
  change l^2-Q0*(FrameHighArc.u^2+(m-FrameHighArc.v)^2)=_ at hreserve
  have hroot : CommonQuarter.radius*n<l := by nlinarith
  have hpi := Arithmetic.pi_hand_enclosure.1
  have hc := FrameHighArc.diagonal_bounds.1
  change CommonQuarter.radius*n-(FrameHighArc.u+(m-FrameHighArc.v))/2<FrameHighArc.k
  dsimp [l,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,m] at *
  linarith

theorem marker_floor (s : State) (hs : s.branch.type≠0) : m*s.b≤unsigned s := by
  cases hj : s.branch with
  | coreSide | coreCorner => simp [hj,Branch.type] at hs
  | low =>
      have hc := state_low_chart s hj
      simpa [unsigned,hj,label,L,FrameLowArc.u,FrameLowArc.v,←hc.1] using low_marker hc.2
  | middle =>
      have hc := state_mid_chart s hj
      have hh := middle_marker hc.2
      dsimp [FrameMidArc.M,p,q,cM] at hh
      rw [← hc.1] at hh
      simp only [unsigned,hj,label]
      linarith
  | high =>
      have hp := state_support s FrameHighArc.u (m-FrameHighArc.v)
      have hr := high_support_reserve
      dsimp [unsigned]
      rw [hj]
      dsimp [label,FrameHighArc.k,FrameHighArc.u,FrameHighArc.v,m] at *
      linarith

end SquaresInCircles.Eight.GlobalGA.Target
end
end
end

section
/-!
## The larger reserve for a core high-GA target

The actual
GA3 inequality first forces the angle above 3/10. The remaining scalar
is concave on the entire interval, and only its two stated endpoints
are evaluated. The fixed force base is proved by positive squaring.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target.Core
open FramePair ZeroPrimary GlobalOuterAnchor Arithmetic

def weight : ℝ := 7/5
def angleSupport (u : ℝ) : ℝ := 1/2+Real.cos u-Real.sin u/12
def error (a : State) (u : ℝ) : ℝ :=
  u-weight*((a.b+1/2)*(1-Real.cos u)+(a.a-1/2)*Real.sin u)
def f (u : ℝ) : ℝ :=
  u-weight*((53/50)*(1-Real.cos u)+(1/12)*Real.sin u)
def fd (u : ℝ) : ℝ :=
  1-weight*((53/50)*Real.sin u+(1/12)*Real.cos u)
def fdd (u : ℝ) : ℝ :=
  -weight*((53/50)*Real.cos u-(1/12)*Real.sin u)
def base : ℝ := 2*m+2*weight-CommonQuarter.radius*Real.sqrt (weight^2+m^2)

theorem coordinate_bounds (a : State) (ha : a.branch.type=0) :
    a.a≤7/12 ∧ a.b<14/25 := by
  have hh := FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart a ha)
  have hd := CoreAngleEndpoint.diagonal_bounds.2
  exact ⟨hh.2.1,by linarith [hh.2.2.2]⟩

theorem angleSupport_hasDerivAt (u : ℝ) :
    HasDerivAt angleSupport (-Real.sin u-Real.cos u/12) u :=
  ((Real.hasDerivAt_cos u).const_add (1/2)).sub ((Real.hasDerivAt_sin u).div_const 12)

theorem angleSupport_antitone : AntitoneOn angleSupport (Icc 0 frameCap) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (angleSupport_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => angleSupport_hasDerivAt u)
    (fun u hu => by
      have ht := transport_trig (Ioo_subset_Icc_self hu)
      linarith [ht.1,ht.2.2.1])

theorem angleSupport_reference : (283/200:ℝ)<angleSupport (3/10) := by
  have hc := cos_lower_six (by norm_num : (0:ℝ)≤3/10)
  have hs := sin_upper_five (by norm_num : (0:ℝ)≤3/10)
  norm_num at hc hs
  dsimp [angleSupport]
  linarith

theorem angle_lower (g a : State) (ha : a.branch.type=0) (hb : (1/2:ℝ)≤a.b)
    {u : ℝ} (hu : u∈Icc 0 frameCap)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u) : (3/10:ℝ)<u := by
  have ht := transport_trig hu
  have hA := mul_le_mul_of_nonneg_right (coordinate_bounds a ha).1 ht.2.2.1
  have hB := mul_le_mul_of_nonneg_right hb (by linarith [ht.1] : 0≤Real.cos u)
  have hwidth : GlobalOuterAnchor.width u=(1+Real.cos u+Real.sin u)/2 := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg ht.2.2.1]
  have hlower : angleSupport u≤g.a := by
    rw [hwidth] at hGA
    dsimp [angleSupport]
    nlinarith
  by_contra! hsmall
  have hh := angleSupport_antitone hu (by norm_num [frameCap] : (3/10:ℝ)∈Icc 0 frameCap) hsmall
  linarith [angleSupport_reference,(coordinates g).2.1]

theorem f_hasDerivAt (u : ℝ) : HasDerivAt f (fd u) u := by
  have h := (hasDerivAt_id' u).fun_sub
    (((((Real.hasDerivAt_cos u).const_sub 1).const_mul (53/50:ℝ)).fun_add
      ((Real.hasDerivAt_sin u).const_mul (1/12:ℝ))).const_mul weight)
  exact h.congr_deriv (by dsimp [fd]; ring)

theorem fd_hasDerivAt (u : ℝ) : HasDerivAt fd (fdd u) u := by
  have h := ((((Real.hasDerivAt_sin u).const_mul (53/50:ℝ)).fun_add
    ((Real.hasDerivAt_cos u).const_mul (1/12:ℝ))).const_mul weight).const_sub 1
  exact h.congr_deriv (by dsimp [fdd]; ring)

theorem f_concave : ConcaveOn ℝ (Icc (3/10:ℝ) frameCap) f :=
  concave_of_deriv2 (fun u _ => f_hasDerivAt u) (fun u _ => fd_hasDerivAt u)
    (fun u hu => by
      have ht := transport_trig ⟨by linarith [hu.1],hu.2⟩
      dsimp [fdd,weight]
      linarith [ht.1,ht.2.2.2.1])

theorem f_left : (19/100:ℝ)<f (3/10) := by
  have hc := cos_lower_six (by norm_num : (0:ℝ)≤3/10)
  have hs := sin_upper_five (by norm_num : (0:ℝ)≤3/10)
  norm_num at hc hs
  dsimp [f,weight]
  linarith

theorem f_right : (19/100:ℝ)<f frameCap := by
  have hc := cos_lower_six (by norm_num [frameCap] : 0≤frameCap)
  have hs := sin_upper_five (by norm_num [frameCap] : 0≤frameCap)
  norm_num [frameCap] at hc hs
  dsimp [f,weight,frameCap]
  linarith

theorem f_lower {u : ℝ} (hu : u∈Icc (3/10:ℝ) frameCap) : (19/100:ℝ)<f u := by
  have hh := f_concave.min_le_of_mem_Icc (by norm_num [frameCap])
    (by norm_num [frameCap]) hu
  exact (lt_min f_left f_right).trans_le hh

theorem error_lower (a : State) (ha : a.branch.type=0) {u : ℝ}
    (hu : u∈Icc (3/10:ℝ) frameCap) : (19/100:ℝ)<error a u := by
  have hc := coordinate_bounds a ha
  have ht := transport_trig ⟨by linarith [hu.1],hu.2⟩
  have hA := mul_le_mul_of_nonneg_right (show a.a-1/2≤(1/12:ℝ) by linarith [hc.1]) ht.2.2.1
  have hB := mul_le_mul_of_nonneg_right (show a.b+1/2≤(53/50:ℝ) by linarith [hc.2])
    (sub_nonneg.mpr (Real.cos_le_one u))
  have hh := f_lower hu
  dsimp [f,error,weight] at *
  linarith

theorem error_separator (g a : State) {u : ℝ} (hu : u∈Icc 0 frameCap)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u) :
    error a u≤u+weight*(g.a-a.b-1) := by
  have ht := transport_trig hu
  dsimp [GlobalOuterAnchor.width] at hGA
  rw [abs_of_nonneg ht.2.2.1] at hGA
  dsimp [error,weight]
  nlinarith

theorem base_lower : (127/100:ℝ)<base := by
  obtain ⟨n,hndef⟩ : ∃ n : ℝ, n=Real.sqrt (weight^2+m^2) := ⟨_,rfl⟩
  obtain ⟨l,hldef⟩ : ∃ l : ℝ, l=2*m+2*weight-127/100 := ⟨_,rfl⟩
  have hn : n^2=weight^2+m^2 := by rw [hndef]; exact Real.sq_sqrt (by positivity)
  have hp : 0≤CommonQuarter.radius*n :=
    mul_nonneg (Real.sqrt_nonneg _) (by rw [hndef]; exact Real.sqrt_nonneg _)
  have hs : (CommonQuarter.radius*n)^2=Q0*(weight^2+m^2) := by
    rw [mul_pow,CommonQuarter.radius_sq,hn]
  have hl : 0<l := by norm_num [hldef,m,weight]
  have hr : Q0*(weight^2+m^2)<l^2 := by norm_num [Q0,hldef,m,weight]
  have hh : CommonQuarter.radius*n<l := by nlinarith
  have hb : base=2*m+2*weight-CommonQuarter.radius*n := by rw [hndef]; rfl
  rw [hb]
  rw [hldef] at hh
  linarith

end SquaresInCircles.Eight.GlobalGA.Target.Core
end
end
end

section
/-!
## The one-variable outer target support

The radical is used only on its actual feasible interval. In particular,
no differentiability assertion is made at the infeasible angle zero.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target.Outer
open FramePair FrameCircleArc Arithmetic

def S : ℝ := Real.sqrt (Q0-1)
def P : ℝ := S-1
def K (u : ℝ) : ℝ := 1+Real.cos u-P*Real.sin u
def Y (u : ℝ) : ℝ := Real.sqrt (Q0-K u^2)
def C (u : ℝ) : ℝ := Real.cos u+Real.sin u/S
def Cd (u : ℝ) : ℝ := -Real.sin u+Real.cos u/S
def U (u : ℝ) : ℝ := Real.sin u+P*Real.cos u
def B (u : ℝ) : ℝ := K u^2*(1+C u^2)-Q0
def N (d : ℝ) : ℝ := Q0*(1+P^2)-Q0*(2*d^2+d)+d*(d+1)^3
def weight (u : ℝ) : ℝ := m*K u/Y u
def J (u : ℝ) : ℝ := u+m*(2-Y u)+(9/100)*(Real.sin u+Real.cos u-1)
def Jd (u : ℝ) : ℝ := 1-m*K u*U u/Y u+(9/100)*(Real.cos u-Real.sin u)
def Jdd (u : ℝ) : ℝ := m*N (K u-1)/Y u^3-(9/100)*(Real.sin u+Real.cos u)

def Domain (u : ℝ) : Prop := u∈Icc 0 frameCap ∧ K u≤a0+1/2

theorem S_bounds : (2134391/1250000:ℝ)<S ∧ S<17075129/10000000 := by
  have hs := Real.sq_sqrt (by norm_num [Q0] : 0≤Q0-1)
  have hp := Real.sqrt_nonneg (Q0-1)
  dsimp [S,Q0] at *
  constructor <;> nlinarith

theorem S_pos : 0<S := by linarith [S_bounds.1]
theorem P_bounds : (7/10:ℝ)<P ∧ P<7075129/10000000 := by
  dsimp [P]
  constructor <;> linarith [S_bounds.1,S_bounds.2]

theorem inv_S_bounds : (0:ℝ)<1/S ∧ 1/S<10/17 := by
  exact ⟨div_pos (by norm_num) S_pos,
    (div_lt_iff₀ S_pos).2 (by linarith [S_bounds.1])⟩

theorem K_hasDerivAt (u : ℝ) : HasDerivAt K (-U u) u := by
  have h1 : HasDerivAt (fun x => 1+Real.cos x) (-Real.sin u) u :=
    (Real.hasDerivAt_cos u).const_add 1
  have h2 : HasDerivAt (fun x => P*Real.sin x) (P*Real.cos u) u :=
    (Real.hasDerivAt_sin u).const_mul P
  have h : HasDerivAt (fun x => 1+Real.cos x-P*Real.sin x) (-Real.sin u-P*Real.cos u) u :=
    h1.fun_sub h2
  exact h.congr_deriv (by dsimp [U]; ring)

theorem U_hasDerivAt (u : ℝ) :
    HasDerivAt U (Real.cos u-P*Real.sin u) u := by
  have h2 : HasDerivAt (fun x => P*Real.cos x) (P*(-Real.sin u)) u :=
    (Real.hasDerivAt_cos u).const_mul P
  have h : HasDerivAt (fun x => Real.sin x+P*Real.cos x) (Real.cos u+P*(-Real.sin u)) u :=
    (Real.hasDerivAt_sin u).fun_add h2
  exact h.congr_deriv (by ring)

theorem C_hasDerivAt (u : ℝ) : HasDerivAt C (Cd u) u :=
  (Real.hasDerivAt_cos u).add ((Real.hasDerivAt_sin u).div_const S)

theorem Cd_hasDerivAt (u : ℝ) : HasDerivAt Cd (-C u) u := by
  have h1 : HasDerivAt (fun x => -Real.sin x) (-Real.cos u) u := (Real.hasDerivAt_sin u).neg
  have h2 : HasDerivAt (fun x => Real.cos x/S) (-Real.sin u/S) u :=
    (Real.hasDerivAt_cos u).div_const S
  have h : HasDerivAt (fun x => -Real.sin x+Real.cos x/S) (-Real.cos u+-Real.sin u/S) u :=
    h1.fun_add h2
  exact h.congr_deriv (by dsimp [C]; ring)

theorem K_bounds {u : ℝ} (hu : u∈Icc 0 frameCap) : (13/10:ℝ)<K u ∧ K u≤2 := by
  have ht := transport_trig hu
  have hprod := mul_le_mul P_bounds.2.le ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤7075129/10000000)
  have hnonneg := mul_nonneg (by linarith [P_bounds.1] : 0≤P) ht.2.2.1
  dsimp [K]
  exact ⟨by linarith [ht.1],by linarith [ht.2.1]⟩

theorem U_increasing_derivative {u : ℝ} (hu : u∈Icc 0 frameCap) :
    0<Real.cos u-P*Real.sin u := by
  have ht := transport_trig hu
  have hprod := mul_le_mul P_bounds.2.le ht.2.2.2.1.le ht.2.2.1
    (by norm_num : (0:ℝ)≤7075129/10000000)
  linarith [ht.1]

theorem U_monotone : MonotoneOn U (Icc 0 frameCap) :=
  monoOn_of_hasDeriv_nonneg
    (fun u _ => (U_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => U_hasDerivAt u)
    (fun _ hu => (U_increasing_derivative (Ioo_subset_Icc_self hu)).le)

theorem U_lower {u : ℝ} (hu : u∈Icc 0 frameCap) : (7/10:ℝ)<U u := by
  have hh := U_monotone (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hu hu.1
  simp only [U,Real.sin_zero,Real.cos_zero,mul_one,zero_add] at hh
  exact P_bounds.1.trans_le hh

theorem K_antitone : AntitoneOn K (Icc 0 frameCap) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (K_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => K_hasDerivAt u)
    (fun u hu => by linarith [U_lower (Ioo_subset_Icc_self hu)])

theorem C_pos {u : ℝ} (hu : u∈Icc 0 frameCap) : 0<C u := by
  have ht := transport_trig hu
  dsimp [C]
  exact add_pos_of_pos_of_nonneg (by linarith [ht.1]) (div_nonneg ht.2.2.1 S_pos.le)

theorem C_cap : 1<C frameCap := by
  have ht := CommonQuarter.cap_trig
  have hquot : (3221/5000:ℝ)/(17075129/10000000)<Real.sin frameCap/S := by
    apply (div_lt_div_iff₀ (by norm_num) S_pos).2
    have hp := mul_lt_mul'' ht.1 S_bounds.2 (by norm_num) S_pos.le
    simpa [frameCap,mul_comm] using hp
  dsimp [C,frameCap]
  norm_num at hquot
  linarith [ht.2.2.1]

theorem C_bounds {u : ℝ} (hu : u∈Icc 0 frameCap) : 1≤C u ∧ C u<7/6 := by
  have hc : ConcaveOn ℝ (Icc 0 frameCap) C :=
    concave_of_deriv2 (fun u _ => C_hasDerivAt u) (fun u _ => Cd_hasDerivAt u)
      (fun u hu => by linarith [C_pos hu])
  have hlo := hc.min_le_of_mem_Icc
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap)
    (by norm_num [frameCap] : frameCap∈Icc 0 frameCap) hu
  have hmin : 1 ≤ min (C 0) (C frameCap) := le_min (by norm_num [C]) C_cap.le
  have hn : (1/S)^2+1<(7/6:ℝ)^2 := by
    have hp := pow_lt_pow_left₀ inv_S_bounds.2 inv_S_bounds.1.le (by norm_num : (2:ℕ)≠0)
    norm_num at hp ⊢
    linarith
  have hproj := FrameCoreArc.projection_lt (a:=1/S) (b:=(1:ℝ)) (by norm_num : (0:ℝ)<7/6)
    (by simpa using hn) u
  refine ⟨hmin.trans hlo,?_⟩
  dsimp [C]
  convert hproj using 1; ring

theorem domain_radicand {u : ℝ} (hu : Domain u) : (1/4:ℝ)≤Q0-K u^2 := by
  have ha : (a0+1/2)^2=Q0-1/4 := by
    simpa [a0] using Real.sq_sqrt (by norm_num [Q0] : 0≤Q0-1/4)
  have hk := pow_le_pow_left₀ (by linarith [(K_bounds hu.1).1] : 0≤K u) hu.2 2
  nlinarith

theorem Y_pos {u : ℝ} (hu : Domain u) : 0<Y u :=
  Real.sqrt_pos.mpr (by linarith [domain_radicand hu])

theorem Y_sq {u : ℝ} (hu : Domain u) : Y u^2=Q0-K u^2 :=
  Real.sq_sqrt (by linarith [domain_radicand hu])

theorem Y_bounds {u : ℝ} (hu : Domain u) : (1/2:ℝ)≤Y u ∧ Y u<3/2 := by
  have hy := Y_sq hu
  have hp := Y_pos hu
  have hk := (K_bounds hu.1).1
  have hr := domain_radicand hu
  dsimp [Q0] at hy hr
  constructor <;> nlinarith

theorem domain_interval {l u z : ℝ} (hl : Domain l) (hu : u∈Icc 0 frameCap)
    (hz : z∈Icc l u) : Domain z := by
  have hz' : z∈Icc 0 frameCap := ⟨hl.1.1.trans hz.1,hz.2.trans hu.2⟩
  exact ⟨hz',(K_antitone hl.1 hz' hz.1).trans hl.2⟩

theorem weight_pos {u : ℝ} (hu : Domain u) : 0<weight u := by
  dsimp [weight]
  exact div_pos (mul_pos (by norm_num [m]) (by linarith [(K_bounds hu.1).1])) (Y_pos hu)

theorem Y_hasDerivAt {u : ℝ} (hu : Domain u) : HasDerivAt Y (K u*U u/Y u) u := by
  have hK := K_hasDerivAt u
  have h1 : HasDerivAt (fun x => K x^2) ((2:ℕ)*K u^(2-1)*(-U u)) u := hK.fun_pow 2
  have h2 : HasDerivAt (fun x => Q0-K x^2) (-((2:ℕ)*K u^(2-1)*(-U u))) u := h1.const_sub Q0
  have h3 : HasDerivAt (fun x => Real.sqrt (Q0-K x^2))
      (-((2:ℕ)*K u^(2-1)*(-U u))/(2*Real.sqrt (Q0-K u^2))) u :=
    h2.sqrt (show Q0-K u^2≠0 by linarith [domain_radicand hu])
  exact h3.congr_deriv (by dsimp only [Y]; push_cast; ring)

theorem J_hasDerivAt {u : ℝ} (hu : Domain u) : HasDerivAt J (Jd u) u := by
  have hY := Y_hasDerivAt hu
  have h1 : HasDerivAt (fun x => m*(2-Y x)) (m*(-(K u*U u/Y u))) u := (hY.const_sub 2).const_mul m
  have h2 : HasDerivAt (fun x => x+m*(2-Y x)) (1+m*(-(K u*U u/Y u))) u :=
    (hasDerivAt_id' u).fun_add h1
  have h3 : HasDerivAt (fun x => Real.sin x+Real.cos x) (Real.cos u+-Real.sin u) u :=
    (Real.hasDerivAt_sin u).fun_add (Real.hasDerivAt_cos u)
  have h4 : HasDerivAt (fun x => (9/100:ℝ)*(Real.sin x+Real.cos x-1))
      ((9/100)*(Real.cos u+-Real.sin u)) u := (h3.sub_const 1).const_mul (9/100:ℝ)
  have h : HasDerivAt (fun x => x+m*(2-Y x)+(9/100)*(Real.sin x+Real.cos x-1))
      (1+m*(-(K u*U u/Y u))+(9/100)*(Real.cos u+-Real.sin u)) u := h2.fun_add h4
  exact h.congr_deriv (by dsimp [Jd]; ring)

theorem circle_identity (u : ℝ) : (K u-1)^2+U u^2=1+P^2 := by
  have ht := Real.sin_sq_add_cos_sq u
  calc
    _=(1+P^2)*(Real.sin u^2+Real.cos u^2) := by dsimp [K,U]; ring
    _=1+P^2 := by rw [ht]; ring

theorem N_identity {u : ℝ} (hu : Domain u) :
    N (K u-1)=Q0*U u^2-K u*(K u-1)*Y u^2 := by
  have hU : U u^2=1+P^2-(K u-1)^2 := by linarith [circle_identity u]
  rw [Y_sq hu,hU]
  dsimp [N]
  ring

theorem Jd_hasDerivAt {u : ℝ} (hu : Domain u) : HasDerivAt Jd (Jdd u) u := by
  have hy := (Y_pos hu).ne'
  have hysq := Y_sq hu
  have hK := K_hasDerivAt u
  have hU := U_hasDerivAt u
  have hY := Y_hasDerivAt hu
  have h1 : HasDerivAt (fun x => m*K x) (m*(-U u)) u := hK.const_mul m
  have h2 : HasDerivAt (fun x => m*K x*U x)
      (m*(-U u)*U u+m*K u*(Real.cos u-P*Real.sin u)) u := h1.fun_mul hU
  have h3 : HasDerivAt (fun x => m*K x*U x/Y x)
      (((m*(-U u)*U u+m*K u*(Real.cos u-P*Real.sin u))*Y u-m*K u*U u*(K u*U u/Y u))/
        Y u^2) u := h2.fun_div hY hy
  have h4 : HasDerivAt (fun x => (9/100:ℝ)*(Real.cos x-Real.sin x))
      ((9/100)*(-Real.sin u-Real.cos u)) u :=
    ((Real.hasDerivAt_cos u).fun_sub (Real.hasDerivAt_sin u)).const_mul (9/100:ℝ)
  have h : HasDerivAt (fun x => 1-m*K x*U x/Y x+(9/100)*(Real.cos x-Real.sin x))
      (-(((m*(-U u)*U u+m*K u*(Real.cos u-P*Real.sin u))*Y u-m*K u*U u*(K u*U u/Y u))/
        Y u^2)+(9/100)*(-Real.sin u-Real.cos u)) u := (h3.const_sub 1).fun_add h4
  refine h.congr_deriv ?_
  dsimp only [Jdd]
  rw [N_identity hu,show Real.cos u-P*Real.sin u=K u-1 by dsimp [K]; ring]
  rw [show Q0=Y u^2+K u^2 by linarith [hysq]]
  field_simp
  ring

end SquaresInCircles.Eight.GlobalGA.Target.Outer
end
end
end

section
/-!
## Whole-feasible-interval curvature of the outer target scalar

The polynomial N is decreasing on the one displayed interval, and its
single right endpoint gives the complete positive curvature reserve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target.Outer
open FramePair FrameCircleArc

theorem D_bounds {u : ℝ} (hu : Domain u) :
    K u-1∈Icc (3/10:ℝ) (183/200) := by
  have hk := (K_bounds hu.1).1
  have ha := FrameLowArc.a0_bounds.2
  exact ⟨by linarith,by linarith [hu.2]⟩

theorem N_hasDerivAt (d : ℝ) :
    HasDerivAt N (-(4*d+1)*(Q0-(d+1)^2)) d := by
  have h1 : HasDerivAt (fun x : ℝ => Q0*(2*x^2+x)) (Q0*(2*(2*d)+1)) d := by
    have := ((((hasDerivAt_id' d).fun_pow 2).const_mul 2).fun_add (hasDerivAt_id' d)).const_mul Q0
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => x*(x+1)^3) ((d+1)^3+d*(3*(d+1)^2)) d := by
    have := (hasDerivAt_id' d).fun_mul (((hasDerivAt_id' d).add_const 1).fun_pow 3)
    exact this.congr_deriv (by ring)
  have h := (h1.const_sub (Q0*(1+P^2))).fun_add h2
  exact h.congr_deriv (by ring)

theorem N_derivative_negative {d : ℝ} (hd : d∈Icc (3/10:ℝ) (183/200)) :
    -(4*d+1)*(Q0-(d+1)^2)<0 := by
  have hrad : 0<Q0-(d+1)^2 := by
    have hh := pow_le_pow_left₀ (by linarith [hd.1] : 0≤d+1)
      (by linarith [hd.2] : d+1≤383/200) 2
    norm_num [Q0] at hh ⊢
    linarith
  exact mul_neg_of_neg_of_pos (by linarith [hd.1]) hrad

theorem N_antitone : AntitoneOn N (Icc (3/10:ℝ) (183/200)) :=
  antiOn_of_hasDeriv_nonpos
    (fun d _ => (N_hasDerivAt d).continuousAt.continuousWithinAt)
    (fun d _ => N_hasDerivAt d)
    (fun _ hd => (N_derivative_negative (Ioo_subset_Icc_self hd)).le)

theorem N_endpoint : (2:ℝ)<N (183/200) := by
  have hp := P_bounds.1
  have hp2 : (49/100:ℝ)<P^2 := by nlinarith
  dsimp [N,Q0]
  nlinarith

theorem N_lower {u : ℝ} (hu : Domain u) : (2:ℝ)<N (K u-1) := by
  have hd := D_bounds hu
  exact N_endpoint.trans_le (N_antitone hd (by norm_num) hd.2)

theorem sine_cosine_upper (u : ℝ) : Real.sin u+Real.cos u<(71/50:ℝ) := by
  have hh := FrameCoreArc.projection_lt (a:=(1:ℝ)) (b:=(1:ℝ))
    (by norm_num : (0:ℝ)<71/50) (by norm_num) u
  simpa using hh

theorem curvature_lower {u : ℝ} (hu : Domain u) : (1/3:ℝ)<Jdd u := by
  have hy := Y_pos hu
  have hy3 := pow_lt_pow_left₀ (Y_bounds hu).2 hy.le (by norm_num : (3:ℕ)≠0)
  have hn := N_lower hu
  have hquot : (2/(3/2)^3:ℝ)<N (K u-1)/Y u^3 := by
    apply (div_lt_div_iff₀ (by norm_num) (pow_pos hy 3)).2
    nlinarith
  have hprod := mul_lt_mul_of_pos_left hquot (by norm_num [m] : 0 < m)
  have htr := sine_cosine_upper u
  dsimp [Jdd,m] at *
  norm_num at hprod
  rw [mul_div_assoc]
  linarith

end SquaresInCircles.Eight.GlobalGA.Target.Outer
end
end
end

section
/-!
## The single rational reference for the outer target scalar

All arithmetic is at the prescribed angle 61/100, with the prescribed
adjacent Taylor polynomials and positive-square radical bounds. The
curvature theorem then controls the complete feasible interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.Target.Outer
open FramePair FrameCircleArc Arithmetic HighOrderTaylor StationaryPrimitives

def reference : ℝ := 61/100
def referenceSin : Interval (Real.sin reference) := Interval.of_bounds
  ⟨S11_le_sin (by norm_num [reference]),sin_le_sin9 (by norm_num [reference])⟩
def referenceCos : Interval (Real.cos reference) := Interval.of_bounds
  ⟨cos10_le_cos (by norm_num [reference]),cos_le_C12 (by norm_num [reference])⟩
def Sbox : Interval S := Interval.of_bounds ⟨S_bounds.1.le,S_bounds.2.le⟩
def Pbox : Interval P := Sbox.sub (Interval.point 1)
def referenceK : Interval (K reference) :=
  ((Interval.point 1).add referenceCos).sub (Pbox.mul referenceSin)
def referenceU : Interval (U reference) := referenceSin.add (Pbox.mul referenceCos)
def referenceRadicand : Interval (Q0-K reference^2) :=
  (Interval.point Q0).sub referenceK.square

macro "ga_target_fixed" : tactic => `(tactic|
  norm_num [Interval.of_bounds,Interval.point,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.square,Interval.cube,Interval.div,Interval.inv,
    referenceSin,referenceCos,Sbox,Pbox,referenceK,referenceU,referenceRadicand,
    reference,S11,C12,sin9,sin7,cos10,cos8,Q0,m])

theorem reference_domain : Domain reference := by
  have hK : K reference<(3/2:ℝ) := by
    have hh : referenceK.hi<(3/2:ℝ) := by ga_target_fixed
    exact referenceK.mem.2.trans_lt hh
  exact ⟨by norm_num [reference,frameCap],by linarith [FrameLowArc.a0_bounds.1]⟩

theorem reference_Y : (6919629/5000000:ℝ)<Y reference ∧
    Y reference<13839261/10000000 := by
  have hh := sqrt_bounds referenceRadicand.mem
    (by norm_num : (0:ℝ)≤6919629/5000000)
    (by norm_num : (0:ℝ)≤13839261/10000000)
    (show (6919629/5000000:ℝ)^2<referenceRadicand.lo by ga_target_fixed)
    (show referenceRadicand.hi<(13839261/10000000:ℝ)^2 by ga_target_fixed)
  exact hh

def referenceY : Interval (Y reference) := Interval.of_bounds
  ⟨reference_Y.1.le,reference_Y.2.le⟩

def referenceSlope : Interval (Jd reference) :=
  ((Interval.point 1).sub ((((Interval.point m).mul referenceK).mul referenceU).div referenceY (by norm_num [referenceY,Interval.of_bounds]))).add
      ((Interval.point (9/100)).mul (referenceCos.sub referenceSin))

theorem reference_value : (117939/100000:ℝ)<J reference := by
  have hsin := referenceSin.mem.1
  have hcos := referenceCos.mem.1
  have hy := reference_Y.2
  have hnum : (117939/100000:ℝ)<reference+m*(2-13839261/10000000)+
      (9/100)*(S11 reference+cos10 reference-1) := by
    norm_num [reference,m,S11,sin9,sin7,cos10,cos8]
  change S11 reference≤Real.sin reference at hsin
  change cos10 reference≤Real.cos reference at hcos
  dsimp [J,m] at *
  linarith

theorem reference_slope : |Jd reference|<(1/1000:ℝ) := by
  have hlo : -(1/1000:ℝ)<referenceSlope.lo := by
    dsimp [referenceSlope,referenceY]
    ga_target_fixed
  have hhi : referenceSlope.hi<(1/1000:ℝ) := by
    dsimp [referenceSlope,referenceY]
    ga_target_fixed
  exact abs_lt.mpr ⟨hlo.trans_le referenceSlope.mem.1,referenceSlope.mem.2.trans_lt hhi⟩

theorem scalar_lower {u : ℝ} (hu : Domain u) : (58969/50000:ℝ)<J u := by
  have hr := reference_domain
  have hl : Domain (min u reference) := by
    rcases le_total u reference with h | h
    · simpa [min_eq_left h] using hu
    · simpa [min_eq_right h] using hr
  have hh : max u reference∈Icc 0 frameCap :=
    ⟨le_max_of_le_left hu.1.1,max_le hu.1.2 hr.1.2⟩
  have hdom (z : ℝ) (hz : z∈Icc (min u reference) (max u reference)) : Domain z :=
    domain_interval hl hh hz
  have ht := CenteredMonomialBounds.second_derivative_tangent_lower
    (κ:=(1/3:ℝ))
    (fun z hz => J_hasDerivAt (hdom z hz))
    (fun z hz => Jd_hasDerivAt (hdom z hz))
    (fun z hz => (curvature_lower (hdom z hz)).le)
    (show reference∈Icc (min u reference) (max u reference) from
      ⟨min_le_right _ _,le_max_right _ _⟩)
    (show u∈Icc (min u reference) (max u reference) from
      ⟨min_le_left _ _,le_max_left _ _⟩)
  have habs := mul_le_mul_of_nonneg_right reference_slope.le (abs_nonneg (u-reference))
  rw [←abs_mul] at habs
  have hlin := (abs_le.mp habs).1
  have hsquare := sq_nonneg (|u-reference|-3/1000)
  have hsqabs := sq_abs (u-reference)
  have hvalue := reference_value
  nlinarith

end SquaresInCircles.Eight.GlobalGA.Target.Outer
end
end
end

section
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
    (fun _ hb => (Ad_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun _ hb => Ad_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun _ hb => (Add_negative (Ioo_subset_Icc_self hb)).le)

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
end
end
end
