module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalLabels
public import SquaresInCircles.Eight.TableFree.CenteredMonomialBounds

/-!
# Fourth derivatives of the two varying middle/high supports

Both supports use the same affine multiplier and the same two-dimensional
norm identity.  A strict fourth-derivative sign proves concavity of the
second derivative on each complete geometric interval.  The original
folded endpoint, radius, and marker remain literal in the scalar.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighVaryingCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def m (i : Bool) : ℝ := if i then 2/5 else 73/200
def origin (i : Bool) : ℝ := if i then 33/50 else 16/25
def left (i : Bool) : ℝ := if i then 1/10 else 2/5
def right (i : Bool) : ℝ := if i then 21/50 else 3/5
def domain (i : Bool) : Set ℝ := Icc (left i) (right i)
def lam (i : Bool) (x : ℝ) : ℝ := origin i-m i*x
def X : ℝ := 1+a2-b2
def Y : ℝ := 1-a2-b2
def N (i : Bool) (x : ℝ) : ℝ :=
  Real.sqrt ((lam i x-sign i*u)^2+(lam i x-v)^2)
def Delta (i : Bool) : ℝ := (m i)^2*(v-sign i*u)^2
def T (i : Bool) (x : ℝ) : ℝ := m i*(sign i*u+v-2*lam i x)
def N1 (i : Bool) (x : ℝ) : ℝ := T i x/N i x
def N2 (i : Bool) (x : ℝ) : ℝ := Delta i/(N i x)^3
def N3 (i : Bool) (x : ℝ) : ℝ := -3*Delta i*T i x/(N i x)^5
def N4 (i : Bool) (x : ℝ) : ℝ :=
  3*Delta i*(4*(T i x)^2-Delta i)/(N i x)^7

def F (i : Bool) (x : ℝ) : ℝ :=
  x+9/100+M2+2*lam i x-sign i*u*R+
    (lam i x*X-9/100)*Real.cos x+(lam i x*Y-9/100)*Real.sin x-R*N i x
def Fd (i : Bool) (x : ℝ) : ℝ :=
  1-2*m i+(lam i x*Y-9/100-m i*X)*Real.cos x+
    (-lam i x*X+9/100-m i*Y)*Real.sin x-R*N1 i x
def Fdd (i : Bool) (x : ℝ) : ℝ :=
  (-lam i x*X+9/100-2*m i*Y)*Real.cos x+
    (-lam i x*Y+9/100+2*m i*X)*Real.sin x-R*N2 i x
def Fddd (i : Bool) (x : ℝ) : ℝ :=
  (-lam i x*Y+9/100+3*m i*X)*Real.cos x+
    (lam i x*X-9/100+3*m i*Y)*Real.sin x-R*N3 i x
def Fdddd (i : Bool) (x : ℝ) : ℝ :=
  (lam i x*X-9/100+4*m i*Y)*Real.cos x+
    (lam i x*Y-9/100-4*m i*X)*Real.sin x-R*N4 i x

theorem endpoint_order (i : Bool) : left i<right i := by cases i <;> norm_num [left,right]
theorem left_mem (i : Bool) : left i∈domain i := ⟨le_rfl,(endpoint_order i).le⟩
theorem right_mem (i : Bool) : right i∈domain i := ⟨(endpoint_order i).le,le_rfl⟩

theorem domain_quadrant {i : Bool} {x : ℝ} (hx : x∈domain i) :
    x∈Icc 0 (Real.pi/2) := by
  cases i <;> dsimp [domain,left,right] at hx <;>
    constructor <;> linarith [hx.1,hx.2,FrameLowPair.pi_lower]

theorem m_bounds (i : Bool) : (73/200:ℝ)≤m i ∧ m i≤2/5 := by
  cases i <;> norm_num [m]
theorem transverse_positive (i : Bool) : 0<v-sign i*u := by
  cases i <;> norm_num [sign,u,v]
theorem Delta_pos (i : Bool) : 0<Delta i := by
  exact mul_pos (sq_pos_of_pos (by linarith [(m_bounds i).1]))
    (sq_pos_of_pos (transverse_positive i))

theorem multiplier_bounds {i : Bool} {x : ℝ} (hx : x∈domain i) :
    (421/1000:ℝ)≤lam i x ∧ lam i x≤31/50 ∧
      0<2*lam i x-sign i*u-v ∧ 0<4*lam i x-sign i*u-3*v := by
  cases i <;> dsimp [domain,left,right,lam,origin,m,sign,u,v] at * <;>
    repeat' constructor <;> linarith

theorem endpoint_coefficients :
    0<X ∧ X<(33/20:ℝ) ∧ Y<-(1597/1000:ℝ) := by
  rw [X,Y,b2_eq]
  repeat' constructor <;> linarith [a2_precise.1,a2_precise.2]

theorem N_energy_pos (i : Bool) (x : ℝ) :
    0<(lam i x-sign i*u)^2+(lam i x-v)^2 := by
  have hgap := sq_pos_of_pos (transverse_positive i)
  nlinarith [sq_nonneg (2*lam i x-sign i*u-v)]

theorem N_pos (i : Bool) (x : ℝ) : 0<N i x := Real.sqrt_pos.mpr (N_energy_pos i x)
theorem N_sq (i : Bool) (x : ℝ) :
    (N i x)^2=(lam i x-sign i*u)^2+(lam i x-v)^2 :=
  Real.sq_sqrt (N_energy_pos i x).le

theorem norm_identity (i : Bool) (x : ℝ) :
    2*(m i)^2*(N i x)^2-(T i x)^2=Delta i := by
  rw [N_sq]
  dsimp [T,Delta]
  ring

theorem lam_deriv (i : Bool) (x : ℝ) : HasDerivAt (lam i) (-m i) x := by
  convert (hasDerivAt_const x (origin i)).sub ((hasDerivAt_id x).const_mul (m i))
    using 1 <;> dsimp [lam] <;> ring

theorem T_deriv (i : Bool) (x : ℝ) : HasDerivAt (T i) (2*(m i)^2) x := by
  convert ((hasDerivAt_const x (sign i*u+v)).sub
    ((lam_deriv i x).const_mul 2)).const_mul (m i) using 1 <;> dsimp [T] <;> ring

theorem N_deriv (i : Bool) (x : ℝ) : HasDerivAt (N i) (N1 i x) x := by
  have hd := (((lam_deriv i x).sub_const (sign i*u)).pow 2).add
    (((lam_deriv i x).sub_const v).pow 2)
  convert hd.sqrt (N_energy_pos i x).ne' using 1
  · rfl
  · dsimp [N1,T,N]
    ring

theorem N1_deriv (i : Bool) (x : ℝ) : HasDerivAt (N1 i) (N2 i x) x := by
  have hd := (T_deriv i x).div (N_deriv i x) (N_pos i x).ne'
  convert hd using 1
  · rfl
  · dsimp [N1,N2]
    field_simp [(N_pos i x).ne']
    nlinarith only [norm_identity i x]

theorem N2_deriv (i : Bool) (x : ℝ) : HasDerivAt (N2 i) (N3 i x) x := by
  have hd := (hasDerivAt_const x (Delta i)).div ((N_deriv i x).pow 3)
    (pow_ne_zero 3 (N_pos i x).ne')
  convert hd using 1
  · rfl
  · dsimp [N1,N2,N3]
    field_simp [(N_pos i x).ne']
    ring

theorem N3_deriv (i : Bool) (x : ℝ) : HasDerivAt (N3 i) (N4 i x) x := by
  have hd := ((T_deriv i x).const_mul (-3*Delta i)).div
    ((N_deriv i x).pow 5) (pow_ne_zero 5 (N_pos i x).ne')
  convert hd using 1
  · rfl
  · dsimp [N1,N3,N4]
    field_simp [(N_pos i x).ne']
    nlinarith only [norm_identity i x]

theorem N4_positive {i : Bool} {x : ℝ} (hx : x∈domain i) : 0<N4 i x := by
  have hh := multiplier_bounds hx
  have hgap := transverse_positive i
  have hsq : (v-sign i*u)^2<4*(2*lam i x-sign i*u-v)^2 := by
    nlinarith
  have hm := mul_lt_mul_of_pos_left hsq
    (sq_pos_of_pos (by linarith [(m_bounds i).1] : 0<m i))
  have hnum : 0<4*(T i x)^2-Delta i := by dsimp [T,Delta]; nlinarith only [hm]
  exact div_pos (mul_pos (mul_pos (by norm_num) (Delta_pos i)) hnum)
    (pow_pos (N_pos i x) 7)

theorem F_deriv (i : Bool) (x : ℝ) : HasDerivAt (F i) (Fd i x) x := by
  have hbase := ((((hasDerivAt_id x).add_const (9/100)).add_const M2).add
    ((lam_deriv i x).const_mul 2)).sub_const (sign i*u*R)
  have hc := (((lam_deriv i x).mul_const X).sub_const (9/100)).mul
    (Real.hasDerivAt_cos x)
  have hs := (((lam_deriv i x).mul_const Y).sub_const (9/100)).mul
    (Real.hasDerivAt_sin x)
  convert ((hbase.add hc).add hs).sub ((N_deriv i x).const_mul R) using 1 <;>
    dsimp [F,Fd] <;> ring

theorem Fd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Fd i) (Fdd i x) x := by
  have hc := ((((lam_deriv i x).mul_const Y).sub_const (9/100)).sub_const (m i*X)).mul
    (Real.hasDerivAt_cos x)
  have hs := (((((lam_deriv i x).mul_const X).neg).add_const (9/100)).
    sub_const (m i*Y)).mul (Real.hasDerivAt_sin x)
  convert (((hasDerivAt_const x (1-2*m i)).add hc).add hs).sub
    ((N1_deriv i x).const_mul R) using 1 <;> dsimp [Fd,Fdd] <;> ring

theorem Fdd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Fdd i) (Fddd i x) x := by
  have hc := (((((lam_deriv i x).mul_const X).neg).add_const (9/100)).
    sub_const (2*m i*Y)).mul (Real.hasDerivAt_cos x)
  have hs := (((((lam_deriv i x).mul_const Y).neg).add_const (9/100)).
    add_const (2*m i*X)).mul (Real.hasDerivAt_sin x)
  convert (hc.add hs).sub ((N2_deriv i x).const_mul R) using 1 <;>
    dsimp [Fdd,Fddd] <;> ring

theorem Fddd_deriv (i : Bool) (x : ℝ) : HasDerivAt (Fddd i) (Fdddd i x) x := by
  have hc := (((((lam_deriv i x).mul_const Y).neg).add_const (9/100)).
    add_const (3*m i*X)).mul (Real.hasDerivAt_cos x)
  have hs := ((((lam_deriv i x).mul_const X).sub_const (9/100)).
    add_const (3*m i*Y)).mul (Real.hasDerivAt_sin x)
  convert (hc.add hs).sub ((N3_deriv i x).const_mul R) using 1 <;>
    dsimp [Fddd,Fdddd] <;> ring

theorem fourth_negative {i : Bool} {x : ℝ} (hx : x∈domain i) : Fdddd i x<0 := by
  have hcoeff := endpoint_coefficients
  have hmult := multiplier_bounds hx
  have hm := m_bounds i
  have htrig := FrameLowPair.quadrant (domain_quadrant hx)
  have hλX := mul_le_mul hmult.2.1 hcoeff.2.1.le hcoeff.1.le (by norm_num : (0:ℝ)≤31/50)
  have hmY := mul_le_mul_of_nonpos_right hm.1 (by linarith [hcoeff.2.2] : Y≤0)
  have hc : lam i x*X-9/100+4*m i*Y<0 := by nlinarith [hcoeff.2.2]
  have hλY : lam i x*Y≤0 := mul_nonpos_of_nonneg_of_nonpos
    (by linarith [hmult.1]) (by linarith [hcoeff.2.2])
  have hmX := mul_pos (by linarith [hm.1] : 0<m i) hcoeff.1
  have hs : lam i x*Y-9/100-4*m i*X<0 := by linarith
  have hcos := mul_nonpos_of_nonpos_of_nonneg hc.le htrig.2.2.1
  have hsin := mul_nonpos_of_nonpos_of_nonneg hs.le htrig.1
  have hnorm := mul_pos R_pos (N4_positive hx)
  dsimp [Fdddd]
  linarith

theorem second_concave (i : Bool) : ConcaveOn ℝ (domain i) (Fdd i) := by
  exact concave_of_deriv2 (fun x _ => Fdd_deriv i x)
    (fun x _ => Fddd_deriv i x) (fun x hx => (fourth_negative hx).le)

end SquaresInCircles.Eight.TableFree.FrameMidHighVaryingCalculus
