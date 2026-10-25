module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor
public import SquaresInCircles.Eight.Arithmetic.Interval
public import SquaresInCircles.Eight.Owners.E.ZeroHessian
public import SquaresInCircles.Eight.Owners.Endpoint.Principles

/-!
# Eight squares: the cap reduction of the E-zero scalar

The only angular cut is the unique crossing of the increasing endpoint bound with the diagonal cap
of the circle (`crossing`). Each variable is moved down to that crossing in a scalar majorant only
(`clipped_representation`, `capped_bounds`), which bounds the E-zero scalar (`maximum`); the
comparison moves no square and asserts no contact.
-/

section
/-!
## One rational comparison point for the continuous E-zero maximum

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
end
end
end

section
/-!
## The E-zero coupled scalar is uniformly below its required value

The Hessian bound is integrated along the actual line
segment from one rational comparison point.  Completing a square gives
the bound on the whole square; the small gradient at the comparison point
is not assumed to vanish.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroScalar
open EZeroFunctions EZeroNested EZeroHessian EZeroPoint

theorem along_F {f g : ℝ → ℝ} {z a b : ℝ}
    (hf : HasDerivAt f a z) (hg : HasDerivAt g b z)
    (he : f z∈Icc 0 (11/100 : ℝ)) (hd : g z∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt (fun t => F (f t) (g t)) (Fe (f z) (g z)*a+Fd (f z) (g z)*b) z := by
  have hh := (h_hasDerivAt ⟨hd.1,by linarith [hd.2]⟩).comp z hg
  have hX := (X_hasDerivAt he).comp z hf
  have hY := (Y_hasDerivAt he).comp z hf
  have hc := (Real.hasDerivAt_cos (f z+g z)).comp z (hf.add hg)
  have hs := (Real.hasDerivAt_sin (f z+g z)).comp z (hf.add hg)
  convert (hh.add (hX.mul hc)).sub (hY.mul hs) using 1
  · rfl
  · dsimp [Fe,Fd]
    ring

theorem along_Fe {f g : ℝ → ℝ} {z a b : ℝ}
    (hf : HasDerivAt f a z) (hg : HasDerivAt g b z)
    (he : f z∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt (fun t => Fe (f t) (g t)) (Fee (f z) (g z)*a+Fed (f z) (g z)*b) z := by
  have hXd := (Xd_hasDerivAt he).comp z hf
  have hY := (Y_hasDerivAt he).comp z hf
  have hk := (k_hasDerivAt he).comp z hf
  have hX := (X_hasDerivAt he).comp z hf
  have hc := (Real.hasDerivAt_cos (f z+g z)).comp z (hf.add hg)
  have hs := (Real.hasDerivAt_sin (f z+g z)).comp z (hf.add hg)
  convert ((hXd.sub hY).mul hc).add ((hk.sub hX).mul hs) using 1
  · rfl
  · dsimp [Fee,Fed]
    ring

theorem along_Fd {f g : ℝ → ℝ} {z a b : ℝ}
    (hf : HasDerivAt f a z) (hg : HasDerivAt g b z)
    (he : f z∈Icc 0 (11/100 : ℝ)) (hd : g z∈Icc 0 (11/100 : ℝ)) :
    HasDerivAt (fun t => Fd (f t) (g t)) (Fed (f z) (g z)*a+Fdd (f z) (g z)*b) z := by
  have hh := (hd_hasDerivAt ⟨hd.1,by linarith [hd.2]⟩).comp z hg
  have hX := (X_hasDerivAt he).comp z hf
  have hY := (Y_hasDerivAt he).comp z hf
  have hc := (Real.hasDerivAt_cos (f z+g z)).comp z (hf.add hg)
  have hs := (Real.hasDerivAt_sin (f z+g z)).comp z (hf.add hg)
  convert (hh.sub (hX.mul hs)).sub (hY.mul hc) using 1
  · rfl
  · dsimp [Fed,Fdd]
    ring

/-- A one-dimensional form of the integrated second-derivative bound. -/
theorem taylor_upper {f df ddf : ℝ → ℝ} {c : ℝ}
    (hf : ∀t∈Icc (0:ℝ) 1,HasDerivAt f (df t) t)
    (hdf : ∀t∈Icc (0:ℝ) 1,HasDerivAt df (ddf t) t)
    (hcurv : ∀t∈Icc (0:ℝ) 1,ddf t≤ -c) :
    f 1≤f 0+df 0-c/2 := by
  have hG (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s => f s+c/2*s^2) (df t+c*t) t := by
    convert (hf t ht).fun_add ((hasDerivAt_pow 2 t).const_mul (c/2)) using 1
    ring
  have hDG (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasDerivAt (fun s => df s+c*s) (ddf t+c) t := by
    convert (hdf t ht).fun_add ((hasDerivAt_id' t).const_mul c) using 1
    ring
  have hm : AntitoneOn (fun s => df s+c*s) (Icc (0:ℝ) 1) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun t ht => (hDG t ht).continuousAt.continuousWithinAt
    · exact fun t ht => hDG t (Ioo_subset_Icc_self ht)
    · exact fun t ht => by linarith [hcurv t (Ioo_subset_Icc_self ht)]
  have hbound := derivative_reserve
    (f := fun t => -(f t+c/2*t^2)) (df := fun t => -(df t+c*t)) (l := (0:ℝ)) (u := 1)
    (k := -df 0)
    (fun t ht => (hG t ht).fun_neg.continuousAt.continuousWithinAt)
    (fun t ht => (hG t (Ioo_subset_Icc_self ht)).fun_neg)
    (fun t ht => by
      have hh := hm (show (0:ℝ)∈Icc 0 1 by norm_num) (Ioo_subset_Icc_self ht) ht.1.le
      simp only at hh ⊢
      linarith)
    (show (0:ℝ)∈Icc 0 1 by norm_num) (show (1:ℝ)∈Icc 0 1 by norm_num) (by norm_num)
  linarith

def line (a b t : ℝ) : ℝ := a+t*(b-a)

theorem line_mem {a b t : ℝ} (ha : a∈Icc 0 (11/100 : ℝ))
    (hb : b∈Icc 0 (11/100 : ℝ)) (ht : t∈Icc (0:ℝ) 1) :
    line a b t∈Icc 0 (11/100 : ℝ) := by
  have hm := convex_Icc (0:ℝ) (11/100) ha hb
    (show 0≤1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t=1)
  have heq : (1-t)*a+t*b=line a b t := by dsimp [line]; ring
  simpa [smul_eq_mul,heq] using hm

theorem line_hasDerivAt (a b t : ℝ) : HasDerivAt (line a b) (b-a) t := by
  have h := ((hasDerivAt_id' t).mul_const (b-a)).const_add a
  rw [one_mul] at h
  exact h

theorem tangent_upper {e d : ℝ}
    (he : e∈Icc 0 (11/100 : ℝ)) (hd : d∈Icc 0 (11/100 : ℝ)) :
    F e d≤F e0 d0+Fe e0 d0*(e-e0)+Fd e0 d0*(d-d0)-
      ((e-e0)^2+(d-d0)^2)/10 := by
  have he0 : e0∈Icc 0 (11/100 : ℝ) := by norm_num [e0]
  have hd0 : d0∈Icc 0 (11/100 : ℝ) := by norm_num [d0]
  let e' := line e0 e
  let d' := line d0 d
  let a := e-e0
  let b := d-d0
  let f := fun t => F (e' t) (d' t)
  let df := fun t => Fe (e' t) (d' t)*a+Fd (e' t) (d' t)*b
  let ddf := fun t => Fee (e' t) (d' t)*a^2+2*Fed (e' t) (d' t)*a*b+Fdd (e' t) (d' t)*b^2
  have hf (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt f (df t) t :=
    along_F (line_hasDerivAt e0 e t) (line_hasDerivAt d0 d t)
      (line_mem he0 he ht) (line_mem hd0 hd ht)
  have hdf (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt df (ddf t) t := by
    have hFe := along_Fe (line_hasDerivAt e0 e t) (line_hasDerivAt d0 d t) (line_mem he0 he ht)
    have hFd := along_Fd (line_hasDerivAt e0 e t) (line_hasDerivAt d0 d t)
      (line_mem he0 he ht) (line_mem hd0 hd ht)
    convert (hFe.mul_const a).add (hFd.mul_const b) using 1
    dsimp [a,b,ddf,e',d']
    ring
  have hcurv (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : ddf t≤ -(1/5)*(a^2+b^2) :=
    quadratic_form (line_mem he0 he ht) (line_mem hd0 hd ht) a b
  have hh := taylor_upper (c := (1/5)*(a^2+b^2)) hf hdf
    (fun t ht => by simpa using hcurv t ht)
  have h1 : ∀ x y : ℝ, line x y 1=y := fun x y => by simp [line]
  have h0 : ∀ x y : ℝ, line x y 0=x := fun x y => by simp [line]
  simp only [f,df,e',d',a,b,h1,h0] at hh
  linarith

theorem maximum {e d : ℝ}
    (he : e∈Icc 0 (11/100 : ℝ)) (hd : d∈Icc 0 (11/100 : ℝ)) :
    F e d<(1499702/1000000 : ℝ) := by
  have ht := tangent_upper he hd
  have hc := comparison
  have hFe := abs_lt.mp hc.2.1
  have hFd := abs_lt.mp hc.2.2
  have hsFe : (Fe e0 d0)^2<(1/2500 : ℝ)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hFe.2) (show 0<1/2500+Fe e0 d0 by linarith)]
  have hsFd : (Fd e0 d0)^2<(1/2500 : ℝ)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hFd.2) (show 0<1/2500+Fd e0 d0 by linarith)]
  have hsqE := sq_nonneg ((e-e0)-5*Fe e0 d0)
  have hsqD := sq_nonneg ((d-d0)-5*Fd e0 d0)
  nlinarith [hc.1]

end SquaresInCircles.Eight.EZeroScalar
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.EZeroCapped
open EZeroFunctions EZeroNested EZeroHessian

def W (e : ℝ) : ℝ := Real.sqrt (qCap-(5/2-capped e)^2)
def Yc (e : ℝ) : ℝ := 2-W e
def Xc (e : ℝ) : ℝ := Real.sqrt (qCap-(Yc e)^2)-1
def Fc (e d : ℝ) : ℝ := capped d+Xc e*Real.cos (e+d)-Yc e*Real.sin (e+d)

theorem diagonal_bounds : (79/100 : ℝ)<diagonalCoordinate qCap ∧
    diagonalCoordinate qCap<9/10 := by
  have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hn := Real.sqrt_nonneg (qCap/2)
  dsimp [diagonalCoordinate,qCap]
  constructor <;> nlinarith

theorem crossing : ∃c∈Ioo (0:ℝ) (11/100),h c=diagonalCoordinate qCap := by
  have h0 : h 0<diagonalCoordinate qCap := by
    have hr := rho_sq (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
    have hp := rho_pos (show (0:ℝ)∈Icc 0 (7/10) by norm_num)
    have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
    have hn := Real.sqrt_nonneg (qCap/2)
    norm_num [u,qCap] at hr
    dsimp [h,diagonalCoordinate,qCap]
    nlinarith
  have h1 : diagonalCoordinate qCap<h (11/100) := by
    have ht : (11/100 : ℝ)∈Icc 0 (7/10) := by norm_num
    have hp := uj_bounds ht
    have hb := trig_bracket (l := (11/100 : ℝ)) (u := (11/100 : ℝ))
      (by norm_num) (by linarith [Real.pi_gt_three]) (by constructor <;> rfl)
    have hv := v_bounds
    have hmul := mul_le_mul (show (1829/2000 : ℝ)≤v by linarith) hb.1
      (by norm_num : (0:ℝ)≤11/100-(11/100)^3/6+(11/100)^5/120-(11/100)^7/5040)
      (by linarith : 0≤v)
    have hu : u (11/100)<1397/1000 := by
      dsimp [u]
      norm_num at hb hmul
      linarith [hb.2.2.2]
    have hu2 := pow_le_pow_left₀ hp.1.le hu.le 2
    have hr := rho_sq ht
    have hrp := rho_pos ht
    have hs := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
    have hn := Real.sqrt_nonneg (qCap/2)
    dsimp [h,diagonalCoordinate,qCap] at *
    nlinarith
  have hc : ContinuousOn h (Icc (0:ℝ) (11/100)) := fun t ht =>
    (h_hasDerivAt ⟨ht.1,by linarith [ht.2]⟩).continuousAt.continuousWithinAt
  obtain ⟨c,hc',heq⟩ := intermediate_value_Icc (show (0:ℝ)≤11/100 by norm_num) hc
    (show diagonalCoordinate qCap∈Icc (h 0) (h (11/100)) from ⟨h0.le,h1.le⟩)
  refine ⟨c,⟨?_,?_⟩,heq⟩
  · apply lt_of_le_of_ne hc'.1
    intro hz
    rw [← hz] at heq
    linarith
  · apply lt_of_le_of_ne hc'.2
    intro hz
    rw [hz] at heq
    linarith

theorem clipped_representation {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    ∃x∈Icc (0:ℝ) (11/100),x≤t ∧ capped t=h x ∧
      W t=w x ∧ Yc t=Y x ∧ Xc t=X x := by
  obtain ⟨c,hc,heq⟩ := crossing
  let x := min t c
  have hc' : c∈Icc (0:ℝ) (7/10) := ⟨hc.1.le,by linarith [hc.2]⟩
  have hx : x∈Icc (0:ℝ) (11/100) :=
    ⟨le_min ht.1 hc.1.le,(min_le_right _ _).trans hc.2.le⟩
  have hcap : capped t=h x := by
    by_cases htc : t≤c
    · have hm := h_monotone ht hc' htc
      rw [heq] at hm
      simp [capped,x,min_eq_left htc,min_eq_right hm]
    · have hm := h_monotone hc' ht (le_of_not_ge htc)
      rw [heq] at hm
      simp [capped,x,min_eq_right (le_of_not_ge htc),min_eq_left hm,heq]
  refine ⟨x,hx,min_le_left _ _,hcap,?_,?_,?_⟩ <;>
    simp [W,Yc,Xc,w,Y,X,A,r,hcap]

theorem nested_bounds {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (199/200 : ℝ)<W t ∧ W t<117/100 ∧
      (83/100 : ℝ)<Yc t ∧ Yc t<101/100 ∧
      (7/10 : ℝ)<Xc t ∧ Xc t<4/5 := by
  obtain ⟨x,hx,hxt,hcap,hw,hy,hX⟩ := clipped_representation ht
  have hb := bounds hx
  rw [hw,hy,hX]
  exact ⟨hb.w_bounds.1,hb.w_bounds.2,hb.Y_bounds.1,hb.Y_bounds.2,
    hb.X_bounds.1,hb.X_bounds.2⟩

theorem W_sq {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (W t)^2=qCap-(5/2-capped t)^2 := by
  obtain ⟨x,hx,hxt,hcap,hw,hy,hX⟩ := clipped_representation ht
  rw [hw,hcap]
  simpa [A] using w_sq hx

theorem corner_square {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (Xc t+1)^2+(Yc t)^2=qCap := by
  obtain ⟨x,hx,hxt,hcap,hw,hy,hX⟩ := clipped_representation ht
  rw [hy,hX]
  dsimp [X]
  nlinarith [r_sq hx]

theorem capped_bounds {t : ℝ} (ht : t∈Icc 0 (7/10 : ℝ)) :
    (79/100 : ℝ)<capped t ∧ capped t<9/10 := by
  obtain ⟨x,hx,hxt,hcap,_,_,_⟩ := clipped_representation ht
  refine ⟨by rw [hcap]; exact (small_h hx).1,?_⟩
  exact (min_le_left _ _).trans_lt diagonal_bounds.2

theorem maximum {e d : ℝ} (he : 0≤e) (hd : 0≤d) (ha : e+d≤7/10) :
    Fc e d<(1499702/1000000 : ℝ) := by
  have he' : e∈Icc 0 (7/10 : ℝ) := ⟨he,by linarith⟩
  have hd' : d∈Icc 0 (7/10 : ℝ) := ⟨hd,by linarith⟩
  obtain ⟨x,hx,hxe,hce,hw,hy,hX⟩ := clipped_representation he'
  obtain ⟨y,hy',hyd,hcd,_,_,_⟩ := clipped_representation hd'
  have hb := bounds hx
  have hsum : x+y≤e+d := add_le_add hxe hyd
  have hxy : 0≤x+y := add_nonneg hx.1 hy'.1
  have hcos : Real.cos (e+d)≤Real.cos (x+y) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hxy (by linarith [Real.pi_gt_three]) hsum
  have hsin : Real.sin (x+y)≤Real.sin (e+d) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three])
      (by linarith [Real.pi_gt_three]) hsum
  have hcx := mul_le_mul_of_nonneg_left hcos (show 0≤X x by linarith [hb.X_bounds.1])
  have hsy := mul_le_mul_of_nonneg_left hsin (show 0≤Y x by linarith [hb.Y_bounds.1])
  have hbound : Fc e d≤F x y := by
    dsimp [Fc,F]
    rw [hcd,hy,hX]
    linarith
  exact hbound.trans_lt (EZeroScalar.maximum hx hy')

end SquaresInCircles.Eight.EZeroCapped
end
end
end
