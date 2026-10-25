module

public import SquaresInCircles.Eight.TableFree.FrameLowArc
public import SquaresInCircles.Eight.TableFree.HighOrderTaylor

/-!
# The low/low whole-angle scalar supports

Uncompiled source draft.  The two full-circle supports are reduced to
one concave degree-eight polynomial on each intrinsic support interval.
The two endpoint continuations use a uniform positive curvature bound.
The negative-target axial support uses one completed cubic on the entire
quadrant.  No Bernstein row or recursive interval cover is imported.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameLowScalars
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

/-- A single completed-cubic bound replaces the negative-target axial
Bernstein row on the whole quadrant. -/
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

end SquaresInCircles.Eight.TableFree.FrameLowScalars
