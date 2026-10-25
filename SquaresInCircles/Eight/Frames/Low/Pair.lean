module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor
public import SquaresInCircles.Eight.Frames.CircleArc

/-!
# Eight squares: the low/low pairs

Two states of the closed low arc, with any signs, separated along any forward axis at a gap of at
least `19/25`, have the cost of the pair above `91/100` (`low_pair`; `low_cycle_pair` on the edges
of a boundary cycle at `Q0`). The angle is then positive (`angle_pos`), and beyond the quarter
turn the cost exceeds `91/100` directly (`beyond_quadrant`). On the secondary axis, a positive
target is bounded by the support of the whole circle or, where its support decreases along the
arc, by the end of the arc (`full_circle_support`, `endpoint_support`, `secondary_positive`), and
a negative target by the smaller of its values at the two ends (`negative_target_endpoint`,
`secondary_negative`). On the primary axis, a positive target forces `x > 13/10`
(`primary_positive_cut`, `primary_positive`), and the supports of a negative target use the
monotonicity along the arc and the concavity in the angle on `[0, 13/10]`
(`primary_negative_short`, `primary_negative`). The two axes of the target are axes of the source
of the reversed pair.
-/

section
/-!
## The complete low outer arc and its frame marker

The endpoints are exact positive roots of the
outer-circle equation.  Every low state lies on this one closed arc.
The marker bounds and all source-loss bounds follow from monotonicity
or endpoint concavity on the full arc.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowArc
open FramePair FrameCircleArc

def u : ℝ := 3231/8000
def v : ℝ := 217813/200000
def a1 : ℝ := (Real.sqrt (272*Q0-36)-10)/17
def b1 : ℝ := a1/4
def L (b : ℝ) : ℝ := u*(A b-a0)+v*b
def L1 : ℝ := u*(a1-a0)+v*b1
def slope (b : ℝ) : ℝ := (b+1/2)/(A b+1/2)
def Ld (b : ℝ) : ℝ := v-u*slope b

theorem a0_bounds : (141457/100000:ℝ)<a0 ∧ a0<70729/50000 := by
  have hs := Real.sq_sqrt (show 0≤Q0-1/4 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (Q0-1/4)
  dsimp [a0,Q0] at *
  constructor <;> nlinarith

theorem a1_bounds : (64937/50000:ℝ)<a1 ∧ a1<1039/800 := by
  have hs := Real.sq_sqrt (show 0≤272*Q0-36 by norm_num [Q0])
  have hn := Real.sqrt_nonneg (272*Q0-36)
  dsimp [a1,Q0] at *
  constructor <;> nlinarith

theorem b1_bounds : (64937/200000:ℝ)<b1 ∧ b1<1039/3200 := by
  dsimp [b1]
  constructor <;> linarith [a1_bounds.1,a1_bounds.2]

theorem endpoint_circle : (a1+1/2)^2+(b1+1/2)^2=Q0 := by
  have hs := Real.sq_sqrt (show 0≤272*Q0-36 by norm_num [Q0])
  have he : Real.sqrt (272*Q0-36)=17*a1+10 := by dsimp [a1]; ring
  rw [he] at hs
  dsimp [b1]
  nlinarith only [hs]

theorem b1_mem : b1∈Icc 0 c0 :=
  ⟨by linarith [b1_bounds.1],by linarith [b1_bounds.2,c0_bounds.1]⟩

theorem A_b1 : A b1=a1 := by
  dsimp [A]
  rw [show Q0-(b1+1/2)^2=(a1+1/2)^2 by linarith [endpoint_circle],
    Real.sqrt_sq (by linarith [a1_bounds.1])]
  ring

theorem A_low_bounds {b : ℝ} (hb : b∈Icc 0 b1) : a1≤A b ∧ A b≤a0 := by
  have hb' : b∈Icc 0 c0 := ⟨hb.1,hb.2.trans b1_mem.2⟩
  have hh := A_antitone hb' b1_mem hb.2
  rw [A_b1] at hh
  exact ⟨hh,(A_bounds hb').2⟩

theorem L1_bounds : (30681/100000:ℝ)<L1 ∧ L1<30683/100000 := by
  have ha0 := a0_bounds
  have ha1 := a1_bounds
  have hb1 := b1_bounds
  dsimp [L1,u,v]
  constructor <;> linarith

@[simp] theorem L_zero : L 0=0 := by simp [L,A_zero]
@[simp] theorem L_b1 : L b1=L1 := by simp [L,L1,A_b1]

theorem slope_bounds {b : ℝ} (hb : b∈Icc 0 b1) :
    (13/50:ℝ)<slope b ∧ slope b<23/50 := by
  have ha := A_low_bounds hb
  have hden := A_shift_pos (show b∈Icc 0 c0 from ⟨hb.1,hb.2.trans b1_mem.2⟩)
  dsimp [slope]
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith [hb.1,ha.2,a0_bounds.2]
  · apply (div_lt_iff₀ hden).2
    linarith [hb.2,ha.1,a1_bounds.1,b1_bounds.2]

theorem L_hasDerivAt {b : ℝ} (hb : b∈Icc 0 b1) : HasDerivAt L (Ld b) b := by
  have hh := (((A_hasDerivAt ⟨hb.1,hb.2.trans b1_mem.2⟩).sub_const a0).const_mul u).add
    ((hasDerivAt_id b).const_mul v)
  convert hh using 1
  · rfl
  · dsimp [Ld,Ad,slope]
    ring

theorem Ld_bounds {b : ℝ} (hb : b∈Icc 0 b1) : 0<Ld b ∧ Ld b<1 := by
  have hh := slope_bounds hb
  dsimp [Ld,u,v]
  constructor <;> linarith

theorem L_monotone : MonotoneOn L (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun b hb => (L_hasDerivAt hb).continuousAt.continuousWithinAt
  · exact fun b hb => L_hasDerivAt (Ioo_subset_Icc_self hb)
  · exact fun b hb => (Ld_bounds (Ioo_subset_Icc_self hb)).1.le

theorem loss_monotone : MonotoneOn (fun b => b-L b) (Icc 0 b1) := by
  apply monoOn_of_hasDeriv_nonneg
  · intro b hb
    exact ((hasDerivAt_id b).sub (L_hasDerivAt hb)).continuousAt.continuousWithinAt
  · intro b hb
    exact (hasDerivAt_id b).sub (L_hasDerivAt (Ioo_subset_Icc_self hb))
  · intro b hb
    linarith [(Ld_bounds (Ioo_subset_Icc_self hb)).2]

theorem L_bounds {b : ℝ} (hb : b∈Icc 0 b1) : 0≤L b ∧ L b≤b ∧ L b≤L1 := by
  have hb0 : (0:ℝ)∈Icc 0 b1 := ⟨le_rfl,b1_mem.1⟩
  have hb1 : b1∈Icc 0 b1 := ⟨b1_mem.1,le_rfl⟩
  have hlo := L_monotone hb0 hb hb.1
  have hhi := L_monotone hb hb1 hb.2
  have hloss := loss_monotone hb0 hb hb.1
  simp only [L_zero,L_b1,sub_zero] at hlo hhi hloss
  exact ⟨hlo,by linarith,hhi⟩

theorem label_loss_lower {b lambda epsilon : ℝ} (hb : b∈Icc 0 b1)
    (he : 0≤epsilon) (hend : -epsilon≤L1-lambda*b1) :
    -epsilon≤L b-lambda*b := by
  have hh := linear_endpoint_lower (p := u) (q := v-lambda)
    (by norm_num [u]) (by norm_num : (0:ℝ)≤0) b1_mem.2 hb
  have hzero : u*a0-epsilon≤linear u (v-lambda) 0 := by
    simp only [linear,A_zero,mul_zero,add_zero]
    linarith
  have hlast : u*a0-epsilon≤linear u (v-lambda) b1 := by
    dsimp [linear]
    rw [A_b1]
    dsimp [L1] at hend
    nlinarith
  have hlo := (le_min hzero hlast).trans hh
  dsimp [linear,L] at *
  nlinarith

theorem state_low_chart (s : FramePair.State) (hs : s.branch=.low) :
    s.a=A s.b ∧ s.b∈Icc 0 b1 := by
  have hn : s.branch.type≠0 := by simp [hs,Branch.type]
  have hh := state_outer_chart s hn
  have hc := s.outer_eq hn
  have hb := s.b_nonneg
  have hcut : 4*s.b≤ s.a := by simpa [hs,TypeMem] using s.type_mem
  have hsq := pow_le_pow_left₀ (show 0≤4*s.b+1/2 by linarith)
    (show 4*s.b+1/2≤ s.a+1/2 by linarith) 2
  have hlast := endpoint_circle
  have ha1 : a1=4*b1 := by dsimp [b1]; ring
  rw [ha1] at hlast
  have hbU : s.b≤b1 := by
    by_contra! hbad
    have hprod := mul_pos (by linarith : 0<s.b-b1)
      (by linarith [b1_mem.1] : 0<s.b+b1)
    nlinarith
  exact ⟨hh.1,⟨hb,hbU⟩⟩

theorem state_low_label (s : FramePair.State) (hs : s.branch=.low) :
    s.signedLabel=sign s.positive*L s.b := by
  rw [State.signedLabel,hs]
  simp only [label]
  rw [(state_low_chart s hs).1]
  rfl

theorem low_offset_bounds (s : FramePair.State) (hs : s.branch=.low) :
    -(1/4:ℝ)<s.offset ∧ s.offset<1/4 := by
  have hcut : 4*s.b≤ s.a := by simpa [hs,TypeMem] using s.type_mem
  have hr : 0≤ s.b/s.a ∧ s.b/s.a≤1/4 :=
    ⟨div_nonneg s.b_nonneg s.a_pos.le,(div_le_iff₀ s.a_pos).2 (by linarith)⟩
  have hangle0 : 0≤Real.arctan (s.b/s.a) := Real.arctan_nonneg.2 hr.1
  have hangle : Real.arctan (s.b/s.a)<1/4 :=
    (Real.arctan_mono hr.2).trans_lt (Real.arctan_lt_self (by norm_num : (0:ℝ)<1/4))
  rcases sign_cases s.positive with he | he <;>
    simp only [State.offset,he,one_mul,neg_one_mul] <;> constructor <;> linarith

end SquaresInCircles.Eight.FrameLowArc
end
end
end

section
/-!
## The scalar supports of the low/low pairs

With the multiplier `lambda i`, `189/200` for a positive source and `1` for a negative one, the
support of the whole circle exceeds `91/100` on `[0, cut i]` (`full_circle_lower`). It is at least
`T i x + 91/100 - R N i x` and `N² ≤ normUpper` (`G_lower_T`, `N_sq_upper`), so it suffices that
`T > 0` and that `P = T² - Q0 normUpper > 0`: `P` is a polynomial of degree eight, concave on
`[0, cut i]` and positive at both ends (`P_concave`, `P_endpoints`, `P_positive`, `T_positive`).
Beyond the cut, the support `E i x` at the end of the arc has curvature above `1/4` up to `π/2`
and starts above `459/500` with slope above `-3/50` (`E_curvature`, `E_start_bounds`), so it
stays above `91/100` (`endpoint_continuation`). The axial support of the negative target exceeds
`91/100` on the whole quadrant, by one completed cubic (`axial_lower`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowScalars
open FramePair FrameCircleArc FrameLowArc

def lambda (positive : Bool) : ℝ := if positive then 189/200 else 1
def epsilon (positive : Bool) : ℝ := if positive then 1/50000 else 0
def cut (positive : Bool) : ℝ := if positive then 24/25 else 11/10

theorem parameters (i : Bool) :
    (189/200:ℝ)≤lambda i ∧ lambda i≤1 ∧
      0≤epsilon i ∧ epsilon i≤1/50000 ∧ 24/25≤cut i ∧ cut i≤11/10 := by
  cases i <;> norm_num [lambda,epsilon,cut]

def S3 (x : ℝ) : ℝ := x-x^3/6
def C4 (x : ℝ) : ℝ := 1-x^2/2+x^4/24
def S5 (x : ℝ) : ℝ := x-x^3/6+x^5/120
def C6 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720

theorem S3_deriv (x : ℝ) : HasDerivAt S3 (1-x^2/2) x := by
  unfold S3
  convert (hasDerivAt_id' x).fun_sub ((hasDerivAt_pow 3 x).div_const 6) using 1
  ring

theorem C4_deriv (x : ℝ) : HasDerivAt C4 (-S3 x) x := by
  unfold C4
  convert (((hasDerivAt_pow 2 x).div_const 2).const_sub 1).fun_add
    ((hasDerivAt_pow 4 x).div_const 24) using 1
  simp only [S3]
  ring

theorem S5_deriv (x : ℝ) : HasDerivAt S5 (C4 x) x := by
  show HasDerivAt (fun y => S3 y+y^5/120) _ x
  convert (S3_deriv x).fun_add ((hasDerivAt_pow 5 x).div_const 120) using 1
  simp only [C4]
  ring

theorem C6_deriv (x : ℝ) : HasDerivAt C6 (-S5 x) x := by
  show HasDerivAt (fun y => C4 y-y^6/720) _ x
  convert (C4_deriv x).fun_sub ((hasDerivAt_pow 6 x).div_const 720) using 1
  simp only [S3,S5]
  ring

def T (i : Bool) (x : ℝ) : ℝ :=
  x+u*(141457/100000)+(u+v+lambda i)/2-91/100-epsilon i+
    (lambda i-9/100)*S3 x+(9/100)*(1-C4 x)
def T1 (i : Bool) (x : ℝ) : ℝ :=
  1+(lambda i-9/100)*(1-x^2/2)+(9/100)*S3 x
def T2 (i : Bool) (x : ℝ) : ℝ :=
  -(lambda i-9/100)*x+(9/100)*(1-x^2/2)

def normUpper (i : Bool) (x : ℝ) : ℝ :=
  u^2+v^2+(lambda i)^2+2*lambda i*(u*S5 x-v*C6 x)
def normUpper1 (i : Bool) (x : ℝ) : ℝ :=
  2*lambda i*(u*C4 x+v*S5 x)
def normUpper2 (i : Bool) (x : ℝ) : ℝ :=
  2*lambda i*(-u*S3 x+v*C4 x)

def P (i : Bool) (x : ℝ) : ℝ := (T i x)^2-Q0*normUpper i x
def P1 (i : Bool) (x : ℝ) : ℝ := 2*T i x*T1 i x-Q0*normUpper1 i x
def P2 (i : Bool) (x : ℝ) : ℝ :=
  2*(T1 i x)^2+2*T i x*T2 i x-Q0*normUpper2 i x

theorem T_deriv (i : Bool) (x : ℝ) : HasDerivAt (T i) (T1 i x) x := by
  unfold T
  have h1 := ((((hasDerivAt_id' x).add_const (u*(141457/100000))).add_const
    ((u+v+lambda i)/2)).sub_const (91/100)).sub_const (epsilon i)
  convert (h1.fun_add ((S3_deriv x).const_mul (lambda i-9/100))).fun_add
    (((C4_deriv x).const_sub 1).const_mul (9/100)) using 1
  simp only [T1]
  ring

theorem T1_deriv (i : Bool) (x : ℝ) : HasDerivAt (T1 i) (T2 i x) x := by
  unfold T1
  convert (((((hasDerivAt_pow 2 x).div_const 2).const_sub 1).const_mul
    (lambda i-9/100)).const_add 1).fun_add ((S3_deriv x).const_mul (9/100)) using 1
  simp only [T2]
  ring

theorem normUpper_deriv (i : Bool) (x : ℝ) :
    HasDerivAt (normUpper i) (normUpper1 i x) x := by
  unfold normUpper
  convert ((((S5_deriv x).const_mul u).fun_sub ((C6_deriv x).const_mul v)).const_mul
    (2*lambda i)).const_add (u^2+v^2+(lambda i)^2) using 1
  simp only [normUpper1]
  ring

theorem normUpper1_deriv (i : Bool) (x : ℝ) :
    HasDerivAt (normUpper1 i) (normUpper2 i x) x := by
  unfold normUpper1
  convert (((C4_deriv x).const_mul u).fun_add ((S5_deriv x).const_mul v)).const_mul
    (2*lambda i) using 1
  simp only [normUpper2]
  ring

theorem P_deriv (i : Bool) (x : ℝ) : HasDerivAt (P i) (P1 i x) x := by
  unfold P
  convert ((T_deriv i x).fun_pow 2).fun_sub ((normUpper_deriv i x).const_mul Q0) using 1
  simp only [P1]
  ring

theorem P1_deriv (i : Bool) (x : ℝ) : HasDerivAt (P1 i) (P2 i x) x := by
  unfold P1
  convert (((T_deriv i x).const_mul 2).fun_mul (T1_deriv i x)).fun_sub
    ((normUpper1_deriv i x).const_mul Q0) using 1
  simp only [P2]
  ring

def secondUpper (x : ℝ) : ℝ :=
  -1+(51/20)*x-(23/10)*x^2+
    x^3*(-1+(13/40)*x+(6/125)*x^2+(1/1250)*x^3)

theorem P2_upper (i : Bool) {x : ℝ} (hx : 0≤x) : P2 i x<secondUpper x := by
  have h2 := pow_nonneg hx 2
  have h3 := pow_nonneg hx 3
  have h4 := pow_nonneg hx 4
  have h5 := pow_nonneg hx 5
  have h6 := pow_nonneg hx 6
  cases i <;>
    simp only [secondUpper,P2,T1,T2,T,normUpper2,S3,C4,u,v,lambda,epsilon,Q0,
      Bool.false_eq_true,ite_false,ite_true] <;>
    linarith

theorem secondUpper_negative {x : ℝ} (hx : x∈Icc 0 (11/10:ℝ)) :
    secondUpper x<0 := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx3 := pow_le_pow_left₀ hx.1 hx.2 3
  norm_num at hx2 hx3
  have hquad : -1+(51/20)*x-(23/10)*x^2<0 := by
    nlinarith [sq_nonneg ((23/5)*x-51/20)]
  have htail : -1+(13/40)*x+(6/125)*x^2+(1/1250)*x^3<0 := by
    linarith [hx.2]
  have hprod := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx.1 3) htail.le
  dsimp [secondUpper]
  linarith

theorem P_concave (i : Bool) : ConcaveOn ℝ (Icc 0 (cut i)) (P i) := by
  apply concave_of_deriv2 (fun x _ => P_deriv i x) (fun x _ => P1_deriv i x)
  intro x hx
  exact ((P2_upper i hx.1).trans
    (secondUpper_negative ⟨hx.1,hx.2.trans (parameters i).2.2.2.2.2⟩)).le

theorem P_endpoints (i : Bool) : 0<P i 0 ∧ 0<P i (cut i) := by
  cases i <;> norm_num [P,T,normUpper,S3,C4,S5,C6,u,v,lambda,epsilon,cut,Q0]

theorem P_positive (i : Bool) {x : ℝ} (hx : x∈Icc 0 (cut i)) : 0<P i x :=
  concave_gt_of_endpoints (P_concave i) hx (P_endpoints i).1 (P_endpoints i).2

theorem T_positive (i : Bool) {x : ℝ} (hx : x∈Icc 0 (cut i)) : 0<T i x := by
  have hxU : x≤11/10 := hx.2.trans (parameters i).2.2.2.2.2
  have hx2 := pow_le_pow_left₀ hx.1 hxU 2
  norm_num at hx2
  have hS : 0≤S3 x := by
    have hh := mul_nonneg hx.1 (show 0≤1-x^2/6 by nlinarith)
    dsimp [S3]
    nlinarith
  have hC : 0≤1-C4 x := by
    have hh := mul_nonneg (sq_nonneg x) (show 0≤1/2-x^2/24 by nlinarith)
    dsimp [C4]
    nlinarith
  have hscaled := mul_nonneg (show 0≤lambda i-9/100 by linarith [(parameters i).1]) hS
  dsimp [T]
  cases i <;> norm_num [u,v,lambda,epsilon] at * <;> linarith

def N (i : Bool) (x : ℝ) : ℝ :=
  Real.sqrt ((u+lambda i*Real.sin x)^2+(lambda i*Real.cos x-v)^2)

def G (i : Bool) (x : ℝ) : ℝ :=
  x+9/100+u*a0+(u+v+lambda i)/2-epsilon i+
    (lambda i-9/100)*Real.sin x-(9/100)*Real.cos x-R*N i x

theorem N_sq (i : Bool) (x : ℝ) :
    (N i x)^2=u^2+v^2+(lambda i)^2+
      2*lambda i*(u*Real.sin x-v*Real.cos x) := by
  have hh := Real.sq_sqrt
    (show 0≤(u+lambda i*Real.sin x)^2+(lambda i*Real.cos x-v)^2 by positivity)
  change (N i x)^2=_ at hh
  rw [hh]
  linear_combination (lambda i)^2*(Real.sin_sq_add_cos_sq x)

theorem N_sq_upper (i : Bool) {x : ℝ} (hx : 0≤x) : (N i x)^2≤normUpper i x := by
  have hl : 0≤lambda i := by linarith [(parameters i).1]
  have hs : Real.sin x≤S5 x := sin_upper_five hx
  have hc : C6 x≤Real.cos x := cos_lower_six hx
  have hsm := mul_le_mul_of_nonneg_left hs (show 0≤2*lambda i*u by dsimp [u]; positivity)
  have hcm := mul_le_mul_of_nonneg_left hc (show 0≤2*lambda i*v by dsimp [v]; positivity)
  rw [N_sq]
  dsimp [normUpper]
  nlinarith

theorem G_lower_T (i : Bool) {x : ℝ} (hx : 0≤x) :
    T i x≤G i x-91/100+R*N i x := by
  have hs : S3 x≤Real.sin x := Real.sin_ge_sub_cube hx
  have hc : Real.cos x≤C4 x := cos_upper_four hx
  have hsm := mul_le_mul_of_nonneg_left hs
    (show 0≤lambda i-9/100 by linarith [(parameters i).1])
  have ha := mul_le_mul_of_nonneg_left a0_bounds.1.le (show 0≤u by norm_num [u])
  dsimp [T,G]
  linarith

theorem full_circle_lower (i : Bool) {x : ℝ} (hx : x∈Icc 0 (cut i)) :
    (91/100:ℝ)<G i x := by
  have hp := P_positive i hx
  have ht := T_positive i hx
  have hn := N_sq_upper i hx.1
  have hN0 : 0≤N i x := Real.sqrt_nonneg _
  have hprod : 0≤R*N i x := mul_nonneg R_pos.le hN0
  have hsq : (R*N i x)^2=Q0*(N i x)^2 := by rw [mul_pow,R_sq]
  have hscaled := mul_le_mul_of_nonneg_left hn (show 0≤Q0 by norm_num [Q0])
  have hroot : R*N i x<T i x := by dsimp [P] at hp; nlinarith
  linarith [G_lower_T i hx.1]

def pCoeff (i : Bool) : ℝ := (lambda i-9/50)/2+lambda i*b1
def nCoeff (i : Bool) : ℝ := lambda i*a1-(lambda i-9/50)/2
def pLo (i : Bool) : ℝ := (lambda i-9/50)/2+lambda i*(64937/200000)
def pHi (i : Bool) : ℝ := (lambda i-9/50)/2+lambda i*(1039/3200)
def nLo (i : Bool) : ℝ := lambda i*(64937/50000)-(lambda i-9/50)/2
def nHi (i : Bool) : ℝ := lambda i*(1039/800)-(lambda i-9/50)/2

def sinLo (i : Bool) : ℝ := if i then 81919/100000 else 557/625
def sinHi (i : Bool) : ℝ := if i then 512/625 else 89121/100000
def cosLo (i : Bool) : ℝ := if i then 57351/100000 else 45359/100000
def cosHi (i : Bool) : ℝ := if i then 7169/12500 else 567/1250

def E (i : Bool) (x : ℝ) : ℝ :=
  x-epsilon i-L1+(lambda i+9/50)/2+pCoeff i*Real.cos x-nCoeff i*Real.sin x
def Ed (i : Bool) (x : ℝ) : ℝ :=
  1-pCoeff i*Real.sin x-nCoeff i*Real.cos x
def Edd (i : Bool) (x : ℝ) : ℝ :=
  -pCoeff i*Real.cos x+nCoeff i*Real.sin x

theorem E_deriv (i : Bool) (x : ℝ) : HasDerivAt (E i) (Ed i x) x := by
  unfold E
  convert (((((hasDerivAt_id' x).sub_const (epsilon i)).sub_const L1).add_const
    ((lambda i+9/50)/2)).fun_add ((Real.hasDerivAt_cos x).const_mul (pCoeff i))).fun_sub
      ((Real.hasDerivAt_sin x).const_mul (nCoeff i)) using 1
  simp only [Ed]
  ring

theorem Ed_deriv (i : Bool) (x : ℝ) : HasDerivAt (Ed i) (Edd i x) x := by
  unfold Ed
  convert (((Real.hasDerivAt_sin x).const_mul (pCoeff i)).const_sub 1).fun_sub
    ((Real.hasDerivAt_cos x).const_mul (nCoeff i)) using 1
  simp only [Edd]
  ring

theorem coefficient_bounds (i : Bool) :
    0<pLo i ∧ pLo i<pCoeff i ∧ pCoeff i<pHi i ∧ pHi i<147/200 ∧
      21/25<nLo i ∧ nLo i<nCoeff i ∧ nCoeff i<nHi i := by
  have ha := a1_bounds
  have hb := b1_bounds
  cases i <;>
    simp only [pLo,pCoeff,pHi,nLo,nCoeff,nHi,lambda,Bool.false_eq_true,ite_false,ite_true] <;>
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem cut_trig (i : Bool) :
    sinLo i<Real.sin (cut i) ∧ Real.sin (cut i)<sinHi i ∧
      cosLo i<Real.cos (cut i) ∧ Real.cos (cut i)<cosHi i := by
  have hx : 0≤cut i := by linarith [(parameters i).2.2.2.2.1]
  have hsl := HighOrderTaylor.S11_le_sin hx
  have hsu := HighOrderTaylor.sin_le_S13 hx
  have hcl := Arithmetic.cos10_le_cos hx
  have hcu := HighOrderTaylor.cos_le_C12 hx
  cases i <;>
    norm_num [cut,sinLo,sinHi,cosLo,cosHi,HighOrderTaylor.S11,HighOrderTaylor.S13,
      HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos10,
      Arithmetic.cos8] at * <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem E_start_bounds (i : Bool) : (459/500:ℝ)<E i (cut i) ∧
    -(3/50:ℝ)<Ed i (cut i) := by
  have hc := coefficient_bounds i
  have ht := cut_trig i
  have hp0 : 0≤pCoeff i := by linarith [hc.1,hc.2.1]
  have hn0 : 0≤nCoeff i := by linarith [hc.2.2.2.2.1,hc.2.2.2.2.2.1]
  have hpH0 : 0≤pHi i := by linarith [hc.2.2.1]
  have hnH0 : 0≤nHi i := by linarith [hc.2.2.2.2.2.2]
  have hs0 : 0≤Real.sin (cut i) := by
    have hh : 0<sinLo i := by cases i <;> norm_num [sinLo]
    linarith [ht.1]
  have hc0 : 0≤Real.cos (cut i) := by
    have hh : 0<cosLo i := by cases i <;> norm_num [cosLo]
    linarith [ht.2.2.1]
  have hpc := mul_le_mul hc.2.1.le ht.2.2.1.le
    (by cases i <;> norm_num [cosLo] : 0≤cosLo i) hp0
  have hns := mul_le_mul hc.2.2.2.2.2.2.le ht.2.1.le hs0 hnH0
  have hps := mul_le_mul hc.2.2.1.le ht.2.1.le hs0 hpH0
  have hnc := mul_le_mul hc.2.2.2.2.2.2.le ht.2.2.2.le hc0 hnH0
  have hval : (459/500:ℝ)<cut i-epsilon i-30683/100000+(lambda i+9/50)/2+
      pLo i*cosLo i-nHi i*sinHi i := by
    cases i <;> norm_num [cut,epsilon,lambda,pLo,nHi,cosLo,sinHi]
  have hd : -(3/50:ℝ)<1-pHi i*sinHi i-nHi i*cosHi i := by
    cases i <;> norm_num [pHi,nHi,lambda,sinHi,cosHi]
  dsimp [E,Ed]
  exact ⟨by linarith [L1_bounds.2],by linarith⟩

theorem E_curvature (i : Bool) {x : ℝ} (hx : x∈Icc (cut i) (Real.pi/2)) :
    (1/4:ℝ)<Edd i x := by
  have hc := coefficient_bounds i
  have ht := cut_trig i
  have hz : 0≤cut i := by linarith [(parameters i).2.2.2.2.1]
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤cut i) hx.2 hx.1
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hz
    (by linarith [hx.2,Real.pi_pos]) hx.1
  have hsL : (819/1000:ℝ)≤Real.sin x := by
    have hh : (819/1000:ℝ)<sinLo i := by cases i <;> norm_num [sinLo]
    linarith [ht.1]
  have hcU : Real.cos x≤287/500 := by
    have hh : cosHi i<287/500 := by cases i <;> norm_num [cosHi]
    linarith [ht.2.2.2]
  have hc0 : 0≤Real.cos x := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
  have hpU : pCoeff i≤147/200 := by linarith [hc.2.2.1,hc.2.2.2.1]
  have hnL : (21/25:ℝ)≤nCoeff i := by linarith [hc.2.2.2.2.1,hc.2.2.2.2.2.1]
  have hn0 : 0≤nCoeff i := by linarith
  have hprodL := mul_le_mul hnL hsL (by norm_num : (0:ℝ)≤819/1000) hn0
  have hprodU := mul_le_mul hpU hcU hc0 (by norm_num : (0:ℝ)≤147/200)
  dsimp [Edd]
  nlinarith

theorem endpoint_continuation (i : Bool) {x : ℝ}
    (hx : x∈Icc (cut i) (Real.pi/2)) : (91/100:ℝ)<E i x := by
  have hcut : cut i∈Icc (cut i) (Real.pi/2) := ⟨le_rfl,hx.1.trans hx.2⟩
  have hh := curvature_tangent (κ := (1/4:ℝ)) hx hcut
    (fun y _ => E_deriv i y) (fun y _ => Ed_deriv i y)
    (fun y hy => (E_curvature i hy).le)
  have hstart := E_start_bounds i
  have hprod : 0≤(Ed i (cut i)+3/50)*(x-cut i) :=
    mul_nonneg (by linarith [hstart.2]) (by linarith [hx.1])
  nlinarith [sq_nonneg (x-cut i-6/25)]

/-- The axial support of the negative target exceeds `91/100` on the whole quadrant for
`B ≤ 969/1000`, by one completed cubic. -/
theorem axial_lower {B x : ℝ} (hB : B≤969/1000)
    (hx : x∈Icc 0 (Real.pi/2)) :
    (91/100:ℝ)<557/1000+x+(39/100)*Real.cos x-B*Real.sin x := by
  have hxU : x≤11/7 := by linarith [hx.2,pi_lt_22_over_7]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2,Real.pi_pos])
  have hBsin := mul_le_mul_of_nonneg_right hB hs0
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsin := sin_upper_five hx.1
  have hx2 := pow_le_pow_left₀ hx.1 hxU 2
  have htail : 0≤x^3*((1/50:ℝ)-(323/40000)*x^2) := by
    apply mul_nonneg (pow_nonneg hx.1 3)
    norm_num at hx2
    nlinarith
  let p : ℝ := 37/1000+(31/1000)*x-(39/200)*x^2+(283/2000)*x^3
  have hid : p=1181/125000-(233/25000)*(x-4/5)+
      (x-4/5)^2*(157/5000+(283/2000)*x) := by dsimp [p]; ring
  have hrem : 0≤(283/2000)*x*(x-4/5)^2 := by
    have := mul_nonneg hx.1 (sq_nonneg (x-4/5))
    linarith
  have hp : 0<p := by
    have hs := sq_nonneg ((157/2500)*(x-4/5)-233/25000)
    nlinarith only [hid,hrem,hs]
  have hcosScaled := mul_le_mul_of_nonneg_left hcos
    (show (0:ℝ)≤39/100 by norm_num)
  have hsinScaled := mul_le_mul_of_nonneg_left hsin
    (show (0:ℝ)≤969/1000 by norm_num)
  dsimp [p] at hp
  nlinarith

end SquaresInCircles.Eight.FrameLowScalars
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameLowPair
open FramePair FrameCircleArc FrameLowArc FrameLowScalars

def width (x : ℝ) : ℝ := (1+Real.sin x+Real.cos x)/2
def cost (i k : Bool) (b B x : ℝ) : ℝ :=
  x-(9/100)*(Real.cos x+Real.sin x-1)+sign i*L b-sign k*L B
def secondary (i k : Bool) (b B x : ℝ) : ℝ :=
  sign i*b+A B*Real.sin x-sign k*B*Real.cos x-width x
def primary (k : Bool) (b B x : ℝ) : ℝ :=
  A b-A B*Real.cos x-sign k*B*Real.sin x-width x

theorem quadrant {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    0≤Real.sin x ∧ Real.sin x≤1 ∧ 0≤Real.cos x ∧ Real.cos x≤1 := by
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_pos]),Real.sin_le_one x,
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩,
    Real.cos_le_one x⟩

theorem pairWidth_eq {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) : pairWidth x=width x := by
  have hh := quadrant hx
  simp [pairWidth,width,abs_of_nonneg hh.1,abs_of_nonneg hh.2.2.1]

theorem pi_lower : (157/50:ℝ)<Real.pi := by
  linarith [Arithmetic.pi_hand_enclosure.1]

theorem signed_label_bounds (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -L1≤ sign i*L b ∧ sign i*L b≤L1 := by
  have hh := L_bounds hb
  cases i <;> norm_num [sign] <;> constructor <;> linarith [L1_bounds.1]

theorem minus_label_le (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -L b≤ sign i*L b := by
  have hh := (L_bounds hb).1
  cases i <;> norm_num [sign]
  linarith

theorem source_loss (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -epsilon i≤ sign i*(L b-lambda i*b) := by
  cases i with
  | false =>
      have hh := (L_bounds hb).2.1
      norm_num [epsilon,sign,lambda]
      linarith
  | true =>
      have he : -(1/50000:ℝ)≤L1-(189/200)*b1 := by
        linarith [L1_bounds.1,b1_bounds.2]
      simpa [epsilon,sign,lambda] using
        label_loss_lower hb (by norm_num : (0:ℝ)≤1/50000) he

theorem source_loss_negative (i : Bool) {b : ℝ} (hb : b∈Icc 0 b1) :
    -(13/1000:ℝ)≤ sign i*(L b-(24/25)*b) := by
  cases i with
  | false =>
      have hh := (L_bounds hb).2.1
      have hbU := hb.2.trans b1_bounds.2.le
      norm_num [sign]
      linarith
  | true =>
      have he : -(13/1000:ℝ)≤L1-(24/25)*b1 := by
        linarith [L1_bounds.1,b1_bounds.2]
      simpa [sign] using
        label_loss_lower hb (by norm_num : (0:ℝ)≤13/1000) he

/-! ## The positive-target secondary axis -/

theorem full_circle_support (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hm : 0≤ secondary i true b B x) : G i x≤cost i true b B x := by
  have hlam : 0≤lambda i := by linarith [(parameters i).1]
  have hscaled := mul_nonneg hlam hm
  have hsource := source_loss i hb
  have hc := circle_linear_lower
    (A_circle ⟨hB.1,hB.2.trans b1_mem.2⟩)
    (-u-lambda i*Real.sin x) (lambda i*Real.cos x-v)
  have hn : Real.sqrt ((-u-lambda i*Real.sin x)^2+
      (lambda i*Real.cos x-v)^2)=N i x := by
    unfold N
    congr 1
    ring
  rw [hn] at hc
  dsimp [secondary,cost,width,G,L] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

def tailSlope (x : ℝ) : ℝ := (23/50)*Real.sin x+Real.cos x

theorem tailSlope_deriv (x : ℝ) :
    HasDerivAt tailSlope ((23/50)*Real.cos x-Real.sin x) x := by
  unfold tailSlope
  convert ((Real.hasDerivAt_sin x).const_mul (23/50)).fun_add
    (Real.hasDerivAt_cos x) using 1

theorem tailSlope_antitone (i : Bool) :
    AntitoneOn tailSlope (Icc (cut i) (Real.pi/2)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (tailSlope_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => tailSlope_deriv x
  · intro x hx
    have hz : 0≤cut i := by linarith [(parameters i).2.2.2.2.1]
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤cut i) hx.2.le hx.1.le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hz
      (by linarith [hx.2,Real.pi_pos]) hx.1.le
    have ht := cut_trig i
    have hnum : (23/50)*cosHi i-sinLo i<0 := by
      cases i <;> norm_num [cosHi,sinLo]
    linarith [ht.1,ht.2.2.2]

theorem target_positive_antitone (i : Bool) {x : ℝ}
    (hx : x∈Icc (cut i) (Real.pi/2)) :
    AntitoneOn (linear (-u-lambda i*Real.sin x) (lambda i*Real.cos x-v))
      (Icc 0 b1) := by
  have hx0 : 0≤x := by linarith [hx.1,(parameters i).2.2.2.2.1]
  have hq := quadrant ⟨hx0,hx.2⟩
  have hlam : 0≤lambda i := by linarith [(parameters i).1]
  have hcoef : 0≤u+lambda i*Real.sin x := by
    exact add_nonneg (by norm_num [u]) (mul_nonneg hlam hq.1)
  have ht := tailSlope_antitone i ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1
  have htrig := cut_trig i
  have htail : tailSlope x≤(23/50)*sinHi i+cosHi i := by
    dsimp [tailSlope] at ht ⊢
    linarith [htrig.2.1,htrig.2.2.2]
  have hscaled := mul_le_mul_of_nonneg_left htail hlam
  have hnum : (23/50)*u+lambda i*((23/50)*sinHi i+cosHi i)-v<0 := by
    cases i <;> norm_num [u,v,lambda,sinHi,cosHi]
  apply antiOn_of_hasDeriv_nonpos
  · intro B hB
    exact (linear_hasDerivAt ⟨hB.1,hB.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
  · intro B hB
    exact linear_hasDerivAt ⟨hB.1.le,hB.2.le.trans b1_mem.2⟩ _ _
  · intro B hB
    have hb := slope_bounds (Ioo_subset_Icc_self hB)
    have hmul := mul_le_mul_of_nonneg_left hb.2.le hcoef
    have hAd : Ad B= -FrameLowArc.slope B := by
      simp only [Ad,FrameLowArc.slope,neg_div]
    rw [hAd]
    dsimp [tailSlope] at hscaled
    linarith

theorem endpoint_support (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc (cut i) (Real.pi/2))
    (hm : 0≤ secondary i true b B x) : E i x≤cost i true b B x := by
  have hlam : 0≤lambda i := by linarith [(parameters i).1]
  have hscaled := mul_nonneg hlam hm
  have hsource := source_loss i hb
  have htarget := target_positive_antitone i hx hB ⟨b1_mem.1,le_rfl⟩ hB.2
  dsimp [linear] at htarget
  rw [A_b1] at htarget
  dsimp [secondary,cost,width,E,pCoeff,nCoeff,L,L1] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

theorem secondary_positive (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤ secondary i true b B x) :
    (91/100:ℝ)<cost i true b B x := by
  by_cases hcut : x≤cut i
  · exact (full_circle_lower i ⟨hx.1,hcut⟩).trans_le
      (full_circle_support i hb hB hm)
  · exact (endpoint_continuation i ⟨(lt_of_not_ge hcut).le,hx.2⟩).trans_le
      (endpoint_support i hb hB ⟨(lt_of_not_ge hcut).le,hx.2⟩ hm)

/-! ## The negative-target secondary axis -/

theorem negative_target_endpoint {B x : ℝ} (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) :
    min (linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) 0)
      (linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) b1)≤
        linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) B := by
  by_cases hp : 0≤u-(24/25)*Real.sin x
  · exact linear_endpoint_lower hp (by norm_num) b1_mem.2 hB
  · have hq : 0≤v-(24/25)*Real.cos x := by
      have hc := (quadrant hx).2.2.2
      dsimp [v]
      linarith
    exact (min_le_left _ _).trans
      (linear_monotone (le_of_not_ge hp) hq
        ⟨le_rfl,b1_mem.1.trans b1_mem.2⟩
        ⟨hB.1,hB.2.trans b1_mem.2⟩ hB.1)

def negativeEndpoint (x : ℝ) : ℝ :=
  x-13/1000+L1+57/100+(39/100-(24/25)*b1)*Real.cos x+
    (39/100-(24/25)*a1)*Real.sin x

theorem negativeEndpoint_deriv (x : ℝ) :
    HasDerivAt negativeEndpoint
      (1-(39/100-(24/25)*b1)*Real.sin x-
        ((24/25)*a1-39/100)*Real.cos x) x := by
  unfold negativeEndpoint
  convert (((((hasDerivAt_id' x).sub_const (13/1000)).add_const L1).add_const
    (57/100)).fun_add ((Real.hasDerivAt_cos x).const_mul
      (39/100-(24/25)*b1))).fun_add ((Real.hasDerivAt_sin x).const_mul
        (39/100-(24/25)*a1)) using 1
  ring

theorem negativeEndpoint_lower {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    (91/100:ℝ)<negativeEndpoint x := by
  have hp : 0≤39/100-(24/25)*b1 := by linarith [b1_bounds.2]
  have hn : 0≤(24/25)*a1-39/100 := by linarith [a1_bounds.1]
  have hm : MonotoneOn negativeEndpoint (Icc 0 (Real.pi/2)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun y _ => (negativeEndpoint_deriv y).continuousAt.continuousWithinAt
    · exact fun y _ => negativeEndpoint_deriv y
    · intro y hy
      have hq := quadrant (Ioo_subset_Icc_self hy)
      have hps := mul_le_mul_of_nonneg_left hq.2.1 hp
      have hnc := mul_le_mul_of_nonneg_left hq.2.2.2 hn
      have he : a1=4*b1 := by dsimp [b1]; ring
      nlinarith [a1_bounds.2,b1_bounds.1]
  have h0 : (91/100:ℝ)<negativeEndpoint 0 := by
    simp only [negativeEndpoint,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,
      zero_sub,add_zero]
    linarith [L1_bounds.1,b1_bounds.2]
  exact h0.trans_le (hm ⟨le_rfl,by positivity⟩ hx hx.1)

theorem secondary_negative (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤ secondary i false b B x) :
    (91/100:ℝ)<cost i false b B x := by
  have hscaled := mul_nonneg (show (0:ℝ)≤24/25 by norm_num) hm
  have hsource := source_loss_negative i hb
  have htarget := negative_target_endpoint hB hx
  have haxial := axial_lower
    (show (24/25)*a0-39/100≤969/1000 by linarith [a0_bounds.2]) hx
  have hend := negativeEndpoint_lower hx
  have hh : min
      (557/1000+x+(39/100)*Real.cos x-((24/25)*a0-39/100)*Real.sin x)
      (negativeEndpoint x)≤cost i false b B x := by
    have hzero : linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) 0=
        (u-(24/25)*Real.sin x)*a0 := by simp [linear]
    have hlast : linear (u-(24/25)*Real.sin x) (v-(24/25)*Real.cos x) b1=
        (u-(24/25)*Real.sin x)*a1+(v-(24/25)*Real.cos x)*b1 := by
      simp [linear,A_b1]
    rw [hzero,hlast] at htarget
    rcases le_total ((u-(24/25)*Real.sin x)*a0)
      ((u-(24/25)*Real.sin x)*a1+(v-(24/25)*Real.cos x)*b1) with h | h
    · rw [min_eq_left h] at htarget
      apply (min_le_left _ _).trans
      dsimp [secondary,cost,width,L,linear] at *
      simp only [sign,Bool.false_eq_true,ite_false] at *
      linarith
    · rw [min_eq_right h] at htarget
      apply (min_le_right _ _).trans
      dsimp [secondary,cost,width,L,linear,negativeEndpoint,L1] at *
      simp only [sign,Bool.false_eq_true,ite_false] at *
      linarith
  exact (lt_min haxial hend).trans_le hh

/-! ## The two primary-axis signs -/

theorem trig_thirteen_tenths :
    (93/100:ℝ)<Real.sin (13/10:ℝ) ∧ (13/50:ℝ)<Real.cos (13/10:ℝ) := by
  have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤13/10 by norm_num)
  have hc := cos_lower_six (show (0:ℝ)≤13/10 by norm_num)
  norm_num at hs hc
  constructor <;> linarith

theorem primary_positive_cut {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary true b B x) :
    (13/10:ℝ)<x := by
  by_contra! hxU
  have ha := A_low_bounds hb
  have hA := A_low_bounds hB
  have hq := quadrant hx
  have hAc := mul_le_mul_of_nonneg_right hA.1 hq.2.2.1
  have hBs := mul_nonneg hB.1 hq.1
  have hsupport : 0<1/2-a0+(a1+1/2)*Real.cos x+(1/2)*Real.sin x := by
    apply harmonic_pos_of_endpoints
      (show 0≤a1+1/2 by linarith [a1_bounds.1]) (by norm_num) (by norm_num)
      (by linarith [pi_lower] : (13/10:ℝ)≤Real.pi/2) ⟨hx.1,hxU⟩
    · simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero]
      linarith [a0_bounds.2,a1_bounds.1]
    · have hp := mul_lt_mul_of_pos_left trig_thirteen_tenths.2
        (show 0<a1+1/2 by linarith [a1_bounds.1])
      nlinarith [trig_thirteen_tenths.1,a0_bounds.2,a1_bounds.1]
  dsimp [primary,width,sign] at hm
  norm_num at hm
  nlinarith

theorem primary_source_endpoint {lam b : ℝ} (hb : b∈Icc 0 b1)
    (hlam : 0≤lam) (hlamU : lam≤5/4) :
    linear (-(u+lam)) (-v) b1≤linear (-(u+lam)) (-v) b := by
  have hcoef : 0≤u+lam := by dsimp [u]; linarith
  have hm : AntitoneOn (linear (-(u+lam)) (-v)) (Icc 0 b1) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (linear_hasDerivAt ⟨hz.1,hz.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
    · intro z hz
      exact linear_hasDerivAt ⟨hz.1.le,hz.2.le.trans b1_mem.2⟩ _ _
    · intro z hz
      have hs := (slope_bounds (Ioo_subset_Icc_self hz)).2
      have hh := mul_le_mul_of_nonneg_left hs.le hcoef
      have hAd : Ad z= -FrameLowArc.slope z := by
        simp only [Ad,FrameLowArc.slope,neg_div]
      rw [hAd]
      dsimp [u,v] at *
      nlinarith
  exact hm hb ⟨b1_mem.1,le_rfl⟩ hb.2

theorem primary_positive_target_endpoint {B x : ℝ} (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) :
    linear (-u+(9/10)*Real.cos x) ((9/10)*Real.sin x-v) b1≤
      linear (-u+(9/10)*Real.cos x) ((9/10)*Real.sin x-v) B := by
  have hq := quadrant hx
  have hm : AntitoneOn (linear (-u+(9/10)*Real.cos x)
      ((9/10)*Real.sin x-v)) (Icc 0 b1) := by
    apply antiOn_of_hasDeriv_nonpos
    · intro z hz
      exact (linear_hasDerivAt ⟨hz.1,hz.2.trans b1_mem.2⟩ _ _).continuousAt.continuousWithinAt
    · intro z hz
      exact linear_hasDerivAt ⟨hz.1.le,hz.2.le.trans b1_mem.2⟩ _ _
    · intro z hz
      have hs := slope_bounds (Ioo_subset_Icc_self hz)
      have hh := mul_nonneg hq.2.2.1 (show 0≤FrameLowArc.slope z by linarith [hs.1])
      have hu := mul_le_mul_of_nonneg_left hs.2.le (show 0≤u by norm_num [u])
      have hAd : Ad z= -FrameLowArc.slope z := by
        simp only [Ad,FrameLowArc.slope,neg_div]
      rw [hAd]
      dsimp [u,v] at *
      nlinarith
  exact hm hB ⟨b1_mem.1,le_rfl⟩ hB.2

def primaryPositiveEndpoint (x : ℝ) : ℝ :=
  x-2*L1+27/50-(9/10)*a1+
    (9/25+(9/10)*a1)*Real.cos x+(9/25+(9/10)*b1)*Real.sin x

theorem primaryPositiveEndpoint_lower {x : ℝ}
    (hx : x∈Icc (13/10:ℝ) (Real.pi/2)) :
    (91/100:ℝ)<primaryPositiveEndpoint x := by
  have hA : 0≤9/25+(9/10)*b1 := by linarith [b1_bounds.1]
  have hB : 0≤9/25+(9/10)*a1 := by linarith [a1_bounds.1]
  have hs := mul_le_mul_of_nonneg_left trig_thirteen_tenths.1.le hA
  have hc := mul_le_mul_of_nonneg_left trig_thirteen_tenths.2.le hB
  have hh := trig_concave_gt (α := 1)
    (m := 91/100+2*L1-27/50+(9/10)*a1)
    hA hB (by norm_num) le_rfl hx
    (by nlinarith [L1_bounds.2,a1_bounds.1,a1_bounds.2,b1_bounds.1])
    (by simp only [Real.sin_pi_div_two,Real.cos_pi_div_two,mul_one,mul_zero,add_zero];
        linarith [pi_lower,L1_bounds.2,a1_bounds.2,b1_bounds.1])
  dsimp [primaryPositiveEndpoint]
  nlinarith

theorem primary_positive (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary true b B x) :
    (91/100:ℝ)<cost i true b B x := by
  have hcut := primary_positive_cut hb hB hx hm
  have hscalar := primaryPositiveEndpoint_lower ⟨hcut.le,hx.2⟩
  have hsrc := primary_source_endpoint hb
    (by norm_num : (0:ℝ)≤9/10) (by norm_num : (9/10:ℝ)≤5/4)
  have htgt := primary_positive_target_endpoint hB hx
  have hsign := minus_label_le i hb
  have hscaled := mul_nonneg (show (0:ℝ)≤9/10 by norm_num) hm
  dsimp [linear] at hsrc htgt
  rw [A_b1] at hsrc htgt
  dsimp [cost,primary,width,primaryPositiveEndpoint,L,L1] at *
  simp only [sign,ite_true,one_mul] at *
  nlinarith

def primaryNegativeZero (x : ℝ) : ℝ :=
  x-L1+143/200-(5/4)*a1+(107/200+(5/4)*a0)*Real.cos x+
    (107/200)*Real.sin x
def primaryNegativeLast (x : ℝ) : ℝ :=
  x+143/200-(5/4)*a1+(107/200+(5/4)*a1)*Real.cos x+
    (107/200-(5/4)*b1)*Real.sin x

theorem primaryNegativeZero_lower {x : ℝ} (hx : x∈Icc 0 (13/10:ℝ)) :
    (91/100:ℝ)<primaryNegativeZero x := by
  have hB : 0≤107/200+(5/4)*a0 := by linarith [a0_bounds.1]
  have hs := mul_le_mul_of_nonneg_left trig_thirteen_tenths.1.le
    (show (0:ℝ)≤107/200 by norm_num)
  have hc := mul_le_mul_of_nonneg_left trig_thirteen_tenths.2.le hB
  have hh := trig_concave_gt (α := 1)
    (m := 91/100+L1-143/200+(5/4)*a1)
    (by norm_num : (0:ℝ)≤107/200) hB (by norm_num)
    (by linarith [pi_lower] : (13/10:ℝ)≤Real.pi/2) hx
    (by simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add];
        linarith [L1_bounds.2,a1_bounds.2,a0_bounds.1])
    (by nlinarith [L1_bounds.2,a1_bounds.2,a0_bounds.1])
  dsimp [primaryNegativeZero]
  nlinarith

theorem primaryNegativeLast_lower {x : ℝ} (hx : x∈Icc 0 (13/10:ℝ)) :
    (91/100:ℝ)<primaryNegativeLast x := by
  have hA : 0≤107/200-(5/4)*b1 := by linarith [b1_bounds.2]
  have hB : 0≤107/200+(5/4)*a1 := by linarith [a1_bounds.1]
  have hs := mul_le_mul_of_nonneg_left trig_thirteen_tenths.1.le hA
  have hc := mul_le_mul_of_nonneg_left trig_thirteen_tenths.2.le hB
  have hh := trig_concave_gt (α := 1)
    (m := 91/100-143/200+(5/4)*a1)
    hA hB (by norm_num) (by linarith [pi_lower] : (13/10:ℝ)≤Real.pi/2) hx
    (by simp only [Real.sin_zero,Real.cos_zero,mul_zero,mul_one,zero_add]; linarith)
    (by nlinarith [a1_bounds.1,a1_bounds.2,b1_bounds.2])
  dsimp [primaryNegativeLast]
  nlinarith

theorem primary_negative_short (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (13/10:ℝ)) (hm : 0≤primary false b B x) :
    (91/100:ℝ)<cost i false b B x := by
  have hxq : x∈Icc 0 (Real.pi/2) :=
    ⟨hx.1,by linarith [hx.2,pi_lower]⟩
  have hq := quadrant hxq
  have hp : 0≤u+(5/4)*Real.cos x := by dsimp [u]; linarith [hq.2.2.1]
  have hsrc := primary_source_endpoint hb (by norm_num : (0:ℝ)≤5/4) le_rfl
  have htgt := linear_endpoint_lower (q := v-(5/4)*Real.sin x) hp
    (by norm_num : (0:ℝ)≤0) b1_mem.2 hB
  have hsign := minus_label_le i hb
  have hscaled := mul_nonneg (show (0:ℝ)≤5/4 by norm_num) hm
  have hzero := primaryNegativeZero_lower hx
  have hlast := primaryNegativeLast_lower hx
  have hh : min (primaryNegativeZero x) (primaryNegativeLast x)≤cost i false b B x := by
    dsimp [linear] at hsrc htgt
    rw [A_b1] at hsrc
    rw [A_zero,A_b1,mul_zero,add_zero] at htgt
    rcases le_total ((u+(5/4)*Real.cos x)*a0)
      ((u+(5/4)*Real.cos x)*a1+(v-(5/4)*Real.sin x)*b1) with h | h
    · rw [min_eq_left h] at htgt
      apply (min_le_left _ _).trans
      dsimp [cost,primary,width,primaryNegativeZero,L,L1] at *
      simp only [sign,Bool.false_eq_true,ite_false] at *
      linarith
    · rw [min_eq_right h] at htgt
      apply (min_le_right _ _).trans
      dsimp [cost,primary,width,primaryNegativeLast,L,L1] at *
      simp only [sign,Bool.false_eq_true,ite_false] at *
      linarith
  exact (lt_min hzero hlast).trans_le hh

theorem primary_negative (i : Bool) {b B x : ℝ}
    (hb : b∈Icc 0 b1) (hB : B∈Icc 0 b1)
    (hx : x∈Icc 0 (Real.pi/2)) (hm : 0≤primary false b B x) :
    (91/100:ℝ)<cost i false b B x := by
  by_cases hcut : x≤13/10
  · exact primary_negative_short i hb hB ⟨hx.1,hcut⟩ hm
  · have hsrc := (signed_label_bounds i hb).1
    have htgt := (L_bounds hB).1
    have hc := CorePairGeometry.charge_upper x
    rw [periodic_cost_quadrant hx] at hc
    have he : cost i false b B x=
        x-(9/100)*(Real.cos x+Real.sin x-1)+sign i*L b+L B := by
      simp [cost,sign]
    rw [he]
    nlinarith [L1_bounds.2]

/-! ## Signed states and every separating axis -/

theorem state_cost_quadrant (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.low) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    s.cost t x=cost s.positive t.positive s.b t.b x := by
  rw [State.cost,periodic_cost_quadrant hx,state_low_label s hs,state_low_label t ht]
  dsimp [cost]
  ring

theorem state_secondary_quadrant (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.low) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    s.Feasible t 0 x ↔ 0≤ secondary s.positive t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,Matrix.cons_val_zero,
    (state_low_chart s hs).1,(state_low_chart t ht).1,pairWidth_eq hx]
  rfl

theorem state_primary_quadrant (s t : FramePair.State)
    (hs : s.branch=.low) (ht : t.branch=.low) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    s.Feasible t 3 x ↔ 0≤primary t.positive s.b t.b x := by
  simp only [State.Feasible,forwardMargin,
    (state_low_chart s hs).1,(state_low_chart t ht).1,pairWidth_eq hx]
  rfl

theorem angle_pos (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) : 0<x := by
  have hso := low_offset_bounds s hs
  have hto := low_offset_bounds t ht
  dsimp [State.gap] at hgap
  linarith

theorem beyond_quadrant (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hx : Real.pi/2≤x) : (91/100:ℝ)<s.cost t x := by
  have hsrc := (signed_label_bounds s.positive (state_low_chart s hs).2).1
  have htgt := (signed_label_bounds t.positive (state_low_chart t ht).2).2
  have hc := CorePairGeometry.charge_upper x
  rw [State.cost,state_low_label s hs,state_low_label t ht]
  linarith [L1_bounds.2,pi_lower]

theorem source_secondary (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 0 x) :
    (91/100:ℝ)<s.cost t x := by
  by_cases hxU : x≤Real.pi/2
  · have hx : x∈Icc 0 (Real.pi/2) := ⟨(angle_pos s t hs ht hgap).le,hxU⟩
    rw [state_cost_quadrant s t hs ht hx]
    have hh := (state_secondary_quadrant s t hs ht hx).mp hm
    have hb := (state_low_chart s hs).2
    have hB := (state_low_chart t ht).2
    cases hk : t.positive with
    | false => rw [hk] at hh; exact secondary_negative s.positive hb hB hx hh
    | true => rw [hk] at hh; exact secondary_positive s.positive hb hB hx hh
  · exact beyond_quadrant s t hs ht (le_of_not_ge hxU)

theorem source_primary (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t 3 x) :
    (91/100:ℝ)<s.cost t x := by
  by_cases hxU : x≤Real.pi/2
  · have hx : x∈Icc 0 (Real.pi/2) := ⟨(angle_pos s t hs ht hgap).le,hxU⟩
    rw [state_cost_quadrant s t hs ht hx]
    have hh := (state_primary_quadrant s t hs ht hx).mp hm
    have hb := (state_low_chart s hs).2
    have hB := (state_low_chart t ht).2
    cases hk : t.positive with
    | false => rw [hk] at hh; exact primary_negative s.positive hb hB hx hh
    | true => rw [hk] at hh; exact primary_positive s.positive hb hB hx hh
  · exact beyond_quadrant s t hs ht (le_of_not_ge hxU)

/-- The low/low pair inequality, for all signs, all states of the closed arc and every forward
axis that separates, ties included. -/
theorem low_pair (s t : FramePair.State) (hs : s.branch=.low) (ht : t.branch=.low)
    (j : Fin 4) {x : ℝ} (hgap : (19/25:ℝ)≤ s.gap t x) (hm : s.Feasible t j x) :
    handGamma s.branch.type t.branch.type<s.cost t x := by
  have hnum : handGamma s.branch.type t.branch.type=(91/100:ℝ) := by
    norm_num [hs,ht,Branch.type,handGamma,handGammaNumerator]
  rw [hnum]
  fin_cases j
  · exact source_secondary s t hs ht hgap hm
  · have hh := source_primary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_primary_reverse t x).mp hm)
    simpa using hh
  · have hh := source_secondary t.flip s.flip
      (by simpa [State.flip] using ht) (by simpa [State.flip] using hs)
      (by simpa using hgap) ((s.target_secondary_reverse t x).mp hm)
    simpa using hh
  · exact source_primary s t hs ht hgap hm

/-- The low/low pair inequality on an edge of a boundary cycle at `Q0`, for every forward axis
that separates the two squares. -/
theorem low_cycle_pair (C : BoundaryCycle Q0) (i : Vertex)
    (hi : branchOf C i=.low) (hj : branchOf C (next i)=.low)
    (j : Fin 4) (haxis : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    handGamma (branchOf C i).type (branchOf C (next i)).type<
      (stateOf C i).cost (stateOf C (next i)) (pairAngle C i) := by
  exact low_pair (stateOf C i) (stateOf C (next i)) hi hj j
    (stateOf_gap_bounds C i).1.le (stateOf_feasible C i j haxis)

end SquaresInCircles.Eight.FrameLowPair
end
end
end
