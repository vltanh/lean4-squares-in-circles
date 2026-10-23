module

public import SquaresInCircles.Eight.TableFree.EZeroPoint

/-!
# The E-zero coupled scalar is uniformly below its required value

Uncompiled draft.  The Hessian bound is integrated along the actual line
segment from one rational comparison point.  Completing a square gives
the bound on the whole square; the small gradient at the comparison point
is not assumed to vanish.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EZeroScalar
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
  let G := fun t => f t+c/2*t^2
  let DG := fun t => df t+c*t
  have hG (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt G (DG t) t := by
    convert (hf t ht).add (((hasDerivAt_id t).pow 2).const_mul (c/2)) using 1 <;>
      dsimp [G,DG] <;> ring
  have hDG (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt DG (ddf t+c) t := by
    exact (hdf t ht).add ((hasDerivAt_id t).const_mul c)
  have hm : AntitoneOn DG (Icc (0:ℝ) 1) := by
    apply antiOn_of_hasDeriv_nonpos
    · exact fun t ht => (hDG t ht).continuousAt.continuousWithinAt
    · exact fun t ht => hDG t (Ioo_subset_Icc_self ht)
    · exact fun t ht => by linarith [hcurv t (Ioo_subset_Icc_self ht)]
  have hbound := derivative_reserve
    (f := fun t => -G t) (df := fun t => -DG t) (l := (0:ℝ)) (u := 1)
    (k := -df 0)
    (fun t ht => (hG t ht).neg.continuousAt.continuousWithinAt)
    (fun t ht => (hG t (Ioo_subset_Icc_self ht)).neg)
    (fun t ht => by
      have hh := hm (show (0:ℝ)∈Icc 0 1 by norm_num) (Ioo_subset_Icc_self ht) ht.1.le
      dsimp [DG] at hh ⊢
      linarith)
    (show (0:ℝ)∈Icc 0 1 by norm_num) (show (1:ℝ)∈Icc 0 1 by norm_num) (by norm_num)
  dsimp [G] at hbound
  linarith

def line (a b t : ℝ) : ℝ := a+t*(b-a)

theorem line_mem {a b t : ℝ} (ha : a∈Icc 0 (11/100 : ℝ))
    (hb : b∈Icc 0 (11/100 : ℝ)) (ht : t∈Icc (0:ℝ) 1) :
    line a b t∈Icc 0 (11/100 : ℝ) := by
  have hm := (convex_Icc (0:ℝ) (11/100)).combo_mem ha hb
    (show 0≤1-t by linarith [ht.2]) ht.1 (by ring : (1-t)+t=1)
  have heq : (1-t)*a+t*b=line a b t := by dsimp [line]; ring
  simpa [smul_eq_mul,heq] using hm

theorem line_hasDerivAt (a b t : ℝ) : HasDerivAt (line a b) (b-a) t := by
  convert ((hasDerivAt_id t).mul_const (b-a)).const_add a using 1 <;>
    simp [line]

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
    · rfl
    · dsimp [a,b,ddf,e',d']
      ring
  have hcurv (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : ddf t≤ -(1/5)*(a^2+b^2) :=
    quadratic_form (line_mem he0 he ht) (line_mem hd0 hd ht) a b
  have hh := taylor_upper (c := (1/5)*(a^2+b^2)) hf hdf
    (fun t ht => by simpa using hcurv t ht)
  dsimp [f,df,e',d',line,a,b] at hh
  ring_nf at hh ⊢
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

end SquaresInCircles.Eight.TableFree.EZeroScalar
