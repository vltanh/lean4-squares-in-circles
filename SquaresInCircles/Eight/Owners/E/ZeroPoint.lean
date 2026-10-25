module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.Interval
public import SquaresInCircles.Eight.Owners.E.ZeroHessian
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor

/-!
# Eight squares: one rational comparison point for the continuous E-zero maximum

This is a single comparison point after the uniform
Hessian theorem.  Sine and cosine use alternating Taylor polynomials;
each radical enclosure is proved by squaring rational endpoints.  There
is no angular mesh or collection of contact configurations.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.EZeroPoint
open Arithmetic QInterval HighOrderTaylor EZeroFunctions EZeroNested EZeroHessian

def e0 : ℝ := 37/800
def d0 : ℝ := 13/200
def box (l u : ℚ) : QInterval := ⟨l/1000000000000,u/1000000000000⟩

theorem trig_mem (x : ℝ) (hx : 0≤x) (S C : QInterval)
    (hsL : (S.lo:ℝ)≤S11 x) (hsU : S13 x≤(S.hi:ℝ))
    (hcL : (C.lo:ℝ)≤cos10 x) (hcU : C12 x≤(C.hi:ℝ)) :
    S.Mem (Real.sin x) ∧ C.Mem (Real.cos x) :=
  ⟨⟨hsL.trans (S11_le_sin hx),(sin_le_S13 hx).trans hsU⟩,
    ⟨hcL.trans (cos10_le_cos hx),(cos_le_C12 hx).trans hcU⟩⟩

theorem e0_trig :
    (box 46233513156 46233513157).Mem (Real.sin e0) ∧
      (box 998930659385 998930659386).Mem (Real.cos e0) := by
  apply trig_mem e0 (by norm_num [e0]) <;>
    norm_num [box,e0,S11,S13,C12,sin9,sin7,cos10,cos8]

theorem d0_trig :
    (box 64954238834 64954238835).Mem (Real.sin d0) ∧
      (box 997888243671 997888243672).Mem (Real.cos d0) := by
  apply trig_mem d0 (by norm_num [d0]) <;>
    norm_num [box,d0,S11,S13,C12,sin9,sin7,cos10,cos8]

theorem sum_trig :
    (box 111020659871 111020659872).Mem (Real.sin (e0+d0)) ∧
      (box 993818098588 993818098589).Mem (Real.cos (e0+d0)) := by
  apply trig_mem (e0+d0) (by norm_num [e0,d0]) <;>
    norm_num [box,e0,d0,S11,S13,C12,sin9,sin7,cos10,cos8]

theorem v_mem : (box 914575671003 914575671004).Mem v := by
  have hroot : (box 1914575671003 1914575671004).Mem (Real.sqrt (qCap-1/4)) := by
    apply mem_sqrt (I := point (9789/2500-1/4))
      (by norm_num [Mem,point,qCap]) <;> norm_num [box,point]
  obtain ⟨h1,h2⟩ := hroot
  show _ ∧ _
  simp only [box] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  dsimp only [v]
  constructor <;> linarith

theorem e0_uj :
    (box 1457181283374 1457181283376).Mem (u e0) ∧
      (box 936714434670 936714434673).Mem (j e0) := by
  have hu := mem_sub (mem_add (mem_point 1) (mem_mul (mem_point (1/2)) e0_trig.2))
    (mem_mul v_mem e0_trig.1)
  have hj := mem_add (mem_mul (mem_point (1/2)) e0_trig.1) (mem_mul v_mem e0_trig.2)
  constructor
  · apply mem_mono (by simpa [u,div_eq_mul_inv,mul_comm] using hu) <;>
      norm_num [box,point,QInterval.add,QInterval.sub,QInterval.neg,QInterval.mul]
  · apply mem_mono (by simpa [j,div_eq_mul_inv,mul_comm] using hj) <;>
      norm_num [box,point,QInterval.add,QInterval.sub,QInterval.neg,QInterval.mul]

theorem d0_uj :
    (box 1439538555268 1439538555270).Mem (u d0) ∧
      (box 945121429458 945121429461).Mem (j d0) := by
  have hu := mem_sub (mem_add (mem_point 1) (mem_mul (mem_point (1/2)) d0_trig.2))
    (mem_mul v_mem d0_trig.1)
  have hj := mem_add (mem_mul (mem_point (1/2)) d0_trig.1) (mem_mul v_mem d0_trig.2)
  constructor
  · apply mem_mono (by simpa [u,div_eq_mul_inv,mul_comm] using hu) <;>
      norm_num [box,point,QInterval.add,QInterval.sub,QInterval.neg,QInterval.mul]
  · apply mem_mono (by simpa [j,div_eq_mul_inv,mul_comm] using hj) <;>
      norm_num [box,point,QInterval.add,QInterval.sub,QInterval.neg,QInterval.mul]

theorem e0_rho : (box 1338739223067 1338739223070).Mem (rho e0) := by
  have hu := mem_sub (mem_point (9789/2500)) (mem_pow e0_uj.1 2)
  apply mem_sqrt (by simpa [qCap] using hu) <;>
    norm_num [box,point,QInterval.sub,QInterval.add,QInterval.neg,QInterval.pow,QInterval.mul]

theorem d0_rho : (box 1357692434939 1357692434942).Mem (rho d0) := by
  have hu := mem_sub (mem_point (9789/2500)) (mem_pow d0_uj.1 2)
  apply mem_sqrt (by simpa [qCap] using hu) <;>
    norm_num [box,point,QInterval.sub,QInterval.add,QInterval.neg,QInterval.pow,QInterval.mul]

theorem e0_h : (box 838739223067 838739223070).Mem (h e0) := by
  obtain ⟨h1,h2⟩ := e0_rho
  show _ ∧ _
  simp only [box] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  dsimp only [h]
  constructor <;> linarith

theorem d0_h : (box 857692434939 857692434942).Mem (h d0) := by
  obtain ⟨h1,h2⟩ := d0_rho
  show _ ∧ _
  simp only [box] at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  dsimp only [h]
  constructor <;> linarith

theorem e0_hd : (box 1019588220428 1019588220436).Mem (hd e0) := by
  have hh := mem_mul (mem_mul e0_uj.1 e0_uj.2)
    (mem_inv_pos (by norm_num [box]) e0_rho)
  apply mem_mono (by simpa [hd,div_eq_mul_inv] using hh) <;>
    norm_num [box,QInterval.mul,QInterval.inv]

theorem d0_hd : (box 1002096426333 1002096426340).Mem (hd d0) := by
  have hh := mem_mul (mem_mul d0_uj.1 d0_uj.2)
    (mem_inv_pos (by norm_num [box]) d0_rho)
  apply mem_mono (by simpa [hd,div_eq_mul_inv] using hh) <;>
    norm_num [box,QInterval.mul,QInterval.inv]

theorem e0_A : (box 1661260776930 1661260776933).Mem (A e0) := by
  have hh := mem_sub (mem_point (5/2)) e0_h
  norm_num [Mem,box,QInterval.sub,QInterval.add,QInterval.neg,point] at hh ⊢
  simpa [A] using hh

theorem e0_w : (box 1075087266701 1075087266707).Mem (w e0) := by
  have hh := mem_sub (mem_point (9789/2500)) (mem_pow e0_A 2)
  apply mem_sqrt (by simpa [qCap] using hh) <;>
    norm_num [box,point,QInterval.sub,QInterval.add,QInterval.neg,QInterval.pow,QInterval.mul]

theorem e0_Y : (box 924912733293 924912733299).Mem (Y e0) := by
  have hh := mem_sub (mem_point 2) e0_w
  norm_num [Mem,box,QInterval.sub,QInterval.add,QInterval.neg,point] at hh ⊢
  simpa [Y] using hh

theorem e0_r : (box 1749324565591 1749324565595).Mem (r e0) := by
  have hh := mem_sub (mem_point (9789/2500)) (mem_pow e0_Y 2)
  apply mem_sqrt (by simpa [qCap] using hh) <;>
    norm_num [box,point,QInterval.sub,QInterval.add,QInterval.neg,QInterval.pow,QInterval.mul]

theorem e0_k : (box 1575501795686 1575501795711).Mem (k e0) := by
  have hh := mem_mul (mem_mul e0_A e0_hd) (mem_inv_pos (by norm_num [box]) e0_w)
  apply mem_mono (by simpa [k,div_eq_mul_inv] using hh) <;>
    norm_num [box,QInterval.mul,QInterval.inv]

theorem comparison : F e0 d0<(1499701/1000000 : ℝ) ∧
    |Fe e0 d0|<1/2500 ∧ |Fd e0 d0|<1/2500 := by
  have hX := mem_sub e0_r (mem_point 1)
  have hXd := mem_mul (mem_mul e0_Y e0_k) (mem_inv_pos (by norm_num [box]) e0_r)
  have hF := mem_sub (mem_add d0_h (mem_mul hX sum_trig.2)) (mem_mul e0_Y sum_trig.1)
  have hFe := mem_add (mem_mul (mem_sub hXd e0_Y) sum_trig.2)
    (mem_mul (mem_sub e0_k hX) sum_trig.1)
  have hFd := mem_sub (mem_sub d0_hd (mem_mul hX sum_trig.1)) (mem_mul e0_Y sum_trig.2)
  change _ ∧ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · have hb : F e0 d0≤(1499701/1000000 : ℝ)-(1/100000000) := by
      have hh := hF.2
      norm_num [box,QInterval.Mem,QInterval.point,QInterval.add,QInterval.sub,
        QInterval.neg,QInterval.mul,QInterval.inv] at hh
      dsimp [F,X]
      linarith
    linarith
  · apply abs_lt.mpr
    have hhL := hFe.1
    have hhU := hFe.2
    norm_num [box,QInterval.Mem,QInterval.point,QInterval.add,QInterval.sub,
      QInterval.neg,QInterval.mul,QInterval.inv] at hhL hhU
    dsimp [Fe,Xd,X]
    rw [div_eq_mul_inv (Y e0*k e0) (r e0)]
    constructor <;> linarith
  · apply abs_lt.mpr
    have hhL := hFd.1
    have hhU := hFd.2
    norm_num [box,QInterval.Mem,QInterval.point,QInterval.add,QInterval.sub,
      QInterval.neg,QInterval.mul,QInterval.inv] at hhL hhU
    dsimp [Fd,X]
    constructor <;> linarith

end SquaresInCircles.Eight.EZeroPoint
