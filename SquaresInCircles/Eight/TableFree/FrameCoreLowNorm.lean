module

public import SquaresInCircles.Eight.TableFree.FramePairShape

/-!
# The complete core/low full-circle support

One cubic majorizes the actual norm throughout `[0,6/5]`.  Its exact
error polynomial has a concave second derivative, and the cost polynomial
is decreasing on the whole interval.  All fixed comparisons are rational
substitutions in the displayed formulas, without coefficient tables.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameCoreLowNorm
open FramePair FrameCircleArc FrameLowArc
open FrameMidArc (g)
open FramePairCalculus FramePairShape

def U (x : ℝ) : ℝ := 81/200+(543/500)*x-(37/1000)*x^2-(6/125)*x^3
def U1 (x : ℝ) : ℝ := 543/500-(37/500)*x-(18/125)*x^2
def U2 (x : ℝ) : ℝ := -(37/500)-(36/125)*x
def U3 : ℝ := -(36/125)
def C6 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720
def C4 (x : ℝ) : ℝ := 1-x^2/2+x^4/24
def S5 (x : ℝ) : ℝ := x-x^3/6+x^5/120
def S3 (x : ℝ) : ℝ := x-x^3/6
def P (x : ℝ) : ℝ :=
  (U x)^2-(u^2+v^2+g^2+2*g*(u*Arithmetic.sin9 x-v*C6 x))
def P1 (x : ℝ) : ℝ :=
  2*U x*U1 x-2*g*(u*Arithmetic.cos8 x+v*S5 x)
def P2 (x : ℝ) : ℝ :=
  2*((U1 x)^2+U x*U2 x)+2*g*(u*Arithmetic.sin7 x-v*C4 x)
def P3 (x : ℝ) : ℝ :=
  2*(3*U1 x*U2 x+U x*U3)+2*g*(u*C6 x+v*S3 x)
def P4 (x : ℝ) : ℝ :=
  -(12263172564/100000000000)-(444007233/1000000000)*x+
    x^2*(-(34388813718/100000000000)+(1450412055/10000000000)*x)-
      (7252060275/1000000000000)*x^5

theorem U_deriv (x : ℝ) : HasDerivAt U (U1 x) x := by
  have hd := (show DifferentiableAt ℝ U x by dsimp [U]; fun_prop).hasDerivAt
  convert hd using 1
  simp (disch := fun_prop) [U,U1]
  ring

theorem P_deriv (x : ℝ) : HasDerivAt P (P1 x) x := by
  have hd := (show DifferentiableAt ℝ P x by
    dsimp [P,U,C6,Arithmetic.sin9,Arithmetic.sin7]; fun_prop).hasDerivAt
  convert hd using 1
  simp (disch := fun_prop) [P,P1,U,U1,C6,S5,Arithmetic.sin9,Arithmetic.sin7,Arithmetic.cos8]
  ring

theorem P1_deriv (x : ℝ) : HasDerivAt P1 (P2 x) x := by
  have hd := (show DifferentiableAt ℝ P1 x by
    dsimp [P1,U,U1,S5,Arithmetic.cos8]; fun_prop).hasDerivAt
  convert hd using 1
  simp (disch := fun_prop) [P1,P2,U,U1,U2,C4,S5,Arithmetic.sin7,Arithmetic.cos8]
  ring

theorem P2_deriv (x : ℝ) : HasDerivAt P2 (P3 x) x := by
  have hd := (show DifferentiableAt ℝ P2 x by
    dsimp [P2,U,U1,U2,C4,Arithmetic.sin7]; fun_prop).hasDerivAt
  convert hd using 1
  simp (disch := fun_prop) [P2,P3,U,U1,U2,U3,C4,C6,S3,Arithmetic.sin7]
  ring

theorem P3_deriv (x : ℝ) : HasDerivAt P3 (P4 x) x := by
  have hd := (show DifferentiableAt ℝ P3 x by
    dsimp [P3,U,U1,U2,C6,S3]; fun_prop).hasDerivAt
  convert hd using 1
  simp (disch := fun_prop) [P3,P4,U,U1,U2,U3,C6,S3,u,v,g]
  ring

theorem P4_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : P4 x<0 := by
  have hcoef : -(34388813718/100000000000:ℝ)+(1450412055/10000000000)*x<0 := by
    linarith [hx.2]
  have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hcoef.le
  have hp := pow_nonneg hx.1 5
  dsimp [P4]
  nlinarith [hx.1]

theorem P3_antitone : AntitoneOn P3 (Icc (0:ℝ) (6/5)) := by
  apply antiOn_of_hasDeriv_nonpos
  · exact fun x _ => (P3_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => P3_deriv x
  · exact fun x hx => (P4_negative (Ioo_subset_Icc_self hx)).le

theorem P2_concave : ConcaveOn ℝ (Icc (0:ℝ) (6/5)) P2 :=
  concave_of_deriv2 (fun x _ => P2_deriv x) (fun x _ => P3_deriv x)
    (fun x hx => (P4_negative hx).le)

theorem P3_initial_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (1/2)) :
    (1/40:ℝ)<P3 x := by
  have hh := P3_antitone ⟨hx.1,by linarith [hx.2]⟩
    ⟨by norm_num,by norm_num⟩ hx.2
  have he : (1/40:ℝ)<P3 (1/2:ℝ) := by
    norm_num [P3,U,U1,U2,U3,C6,S3,u,v,g]
  exact he.trans_le hh

theorem P1_initial_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (1/2)) : 0<P1 x := by
  apply positive_of_curvature (κ := (1/40:ℝ)) (by norm_num) hx
    (show (2/5:ℝ)∈Icc (0:ℝ) (1/2) by constructor <;> norm_num)
    (fun x _ => P1_deriv x) (fun x _ => P2_deriv x)
    (fun x hx => (P3_initial_lower hx).le)
  norm_num [P1,P2,U,U1,U2,C4,S5,Arithmetic.cos8,Arithmetic.sin7,u,v,g]

theorem P_initial_monotone : MonotoneOn P (Icc (0:ℝ) (1/2)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (P_deriv x).continuousAt.continuousWithinAt
  · exact fun x _ => P_deriv x
  · exact fun x hx => (P1_initial_positive (Ioo_subset_Icc_self hx)).le

theorem P_endpoint_lower : (1/6000:ℝ)<P 0 ∧ (1/6000:ℝ)<P (6/5:ℝ) := by
  constructor <;> norm_num [P,U,C6,Arithmetic.sin9,Arithmetic.sin7,u,v,g]

theorem P_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : (1/6000:ℝ)<P x := by
  have hhalf : (1/6000:ℝ)<P (1/2:ℝ) :=
    P_endpoint_lower.1.trans_le (P_initial_monotone
      ⟨le_rfl,by norm_num⟩ ⟨by norm_num,le_rfl⟩ (by norm_num))
  by_cases hfirst : x≤1/2
  · exact P_endpoint_lower.1.trans_le
      (P_initial_monotone ⟨le_rfl,by norm_num⟩ ⟨hx.1,hfirst⟩ hx.1)
  · have he : 0≤P2 (1/2:ℝ) := by
      norm_num [P2,U,U1,U2,C4,Arithmetic.sin7,u,v,g]
    have hd := (P1_initial_positive (show (1/2:ℝ)∈Icc (0:ℝ) (1/2) by
      constructor <;> norm_num)).le
    have hh := endpoint_minimum_of_concave_second
      (show x∈Icc (1/2:ℝ) (6/5) from ⟨(lt_of_not_ge hfirst).le,hx.2⟩)
      (fun x _ => P_deriv x) (fun x _ => P1_deriv x)
      (P2_concave.subset (Icc_subset_Icc (by norm_num) le_rfl) (convex_Icc _ _)) he hd
    exact (lt_min hhalf P_endpoint_lower.2).trans_le hh

theorem U_positive {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : 0<U x := by
  have hm : MonotoneOn U (Icc (0:ℝ) (6/5)) := by
    apply monoOn_of_hasDeriv_nonneg
    · exact fun x _ => (U_deriv x).continuousAt.continuousWithinAt
    · exact fun x _ => U_deriv x
    · intro x hx
      have hx2 := pow_le_pow_left₀ hx.1.le hx.2.le 2
      dsimp [U1]
      nlinarith [hx.2]
  have hh := hm ⟨le_rfl,by norm_num⟩ hx hx.1
  norm_num [U] at hh
  linarith

def N (x : ℝ) : ℝ := Real.sqrt (u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x))
def F (x : ℝ) : ℝ :=
  x+(g+9/50+u+v)/2+u*a0+(g-9/100)*Real.sin x-(9/100)*Real.cos x-R*N x

theorem N_sq {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) :
    (N x)^2=u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x) := by
  have he : u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x)=
      (u+g*Real.sin x)^2+(v-g*Real.cos x)^2 := by
    linear_combination -g^2*(Real.sin_sq_add_cos_sq x)
  exact Real.sq_sqrt (by rw [he]; positivity)

theorem norm_upper {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : N x<U x := by
  have hp := P_positive hx
  have hu := U_positive hx
  have hn := N_sq hx
  have hs := Arithmetic.sin_le_sin9 hx.1
  have hc : C6 x≤Real.cos x := by simpa [C6] using cos_lower_six hx.1
  dsimp [P] at hp
  dsimp [u,v,g] at *
  nlinarith [Real.sqrt_nonneg
    (u^2+v^2+g^2+2*g*(u*Real.sin x-v*Real.cos x))]

def costPolynomial (x : ℝ) : ℝ :=
  x+(g+9/50+u+v)/2+u*(2829/2000)-91/100+
    (g-9/100)*Arithmetic.sin7 x-(9/100)*Arithmetic.cos8 x-(1979/1000)*U x
def costDerivative (x : ℝ) : ℝ :=
  -(80911/500000)+(118223/500000)*x-(20871/100000)*x^2-
    (3/200)*x^3+(82281/2000000)*x^4+(3/4000)*x^5-
      (27427/20000000)*x^6-x^7/56000

theorem costPolynomial_deriv (x : ℝ) :
    HasDerivAt costPolynomial (costDerivative x) x := by
  have hd := (show DifferentiableAt ℝ costPolynomial x by
    dsimp [costPolynomial,U,Arithmetic.sin7,Arithmetic.cos8]; fun_prop).hasDerivAt
  convert hd using 1
  simp (disch := fun_prop) [costPolynomial,costDerivative,U,Arithmetic.sin7,
    Arithmetic.cos8,u,v,g]
  ring

theorem costDerivative_negative {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) :
    costDerivative x<-(1/20:ℝ) := by
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hx3 := pow_le_pow_left₀ hx.1 hx.2 3
  have hx4 := mul_le_mul_of_nonneg_right hx2 (sq_nonneg x)
  have hx5 := mul_le_mul_of_nonneg_right hx3 (sq_nonneg x)
  have h3 := pow_nonneg hx.1 3
  have h6 := pow_nonneg hx.1 6
  have h7 := pow_nonneg hx.1 7
  dsimp [costDerivative]
  nlinarith [sq_nonneg ((7/25)*x-237/1000)]

theorem costPolynomial_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) :
    (13/1000:ℝ)<costPolynomial x := by
  have hm : AntitoneOn costPolynomial (Icc (0:ℝ) (6/5)) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun x _ => (costPolynomial_deriv x).continuousAt.continuousWithinAt
    · exact fun x _ => costPolynomial_deriv x
    · intro x hx
      linarith [costDerivative_negative (Ioo_subset_Icc_self hx)]
  have hh := hm hx ⟨by norm_num,le_rfl⟩ hx.2
  have he : (13/1000:ℝ)<costPolynomial (6/5:ℝ) := by
    norm_num [costPolynomial,U,Arithmetic.sin7,Arithmetic.cos8,u,v,g]
  exact he.trans_le hh

theorem full_circle_lower {x : ℝ} (hx : x∈Icc (0:ℝ) (6/5)) : (91/100:ℝ)<F x := by
  have hu := U_positive hx
  have hn := norm_upper hx
  have hR : R<(1979/1000:ℝ) := by
    have hh := R_sq
    norm_num [Q0] at hh
    nlinarith [R_pos]
  have hRN : R*N x<(1979/1000)*U x :=
    (mul_lt_mul_of_pos_left hn R_pos).trans (mul_lt_mul_of_pos_right hR hu)
  have hs := sin_lower_seven hx.1
  have hc := Arithmetic.cos_le_cos8 hx.1
  have hpoly := costPolynomial_lower hx
  have ha : (2829/2000:ℝ)<a0 := by linarith [a0_bounds.1]
  dsimp [F,costPolynomial,u,v,g] at *
  nlinarith

end SquaresInCircles.Eight.TableFree.FrameCoreLowNorm
