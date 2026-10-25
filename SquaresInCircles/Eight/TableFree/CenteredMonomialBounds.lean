module

public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
public import SquaresInCircles.Eight.TableFree.EndpointPrinciples
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Whole-interval bounds from translated monomial coefficients

Uncompiled draft.  Even powers keep their favorable coefficient sign;
odd powers are bounded by their absolute coefficient.  The one-sided
upper bound similarly retains the sign of every translated coefficient.
These are bounds for one complete interval, with no sampled states.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set
namespace SquaresInCircles.Eight.TableFree.CenteredMonomialBounds
open Polynomial

def translated (m : ℚ) (p : ℚ[X]) : ℚ[X] := p.comp (C m+X)

def series (n : ℕ) (p : ℚ[X]) : ℚ[X] :=
  C (p.coeff 0)+∑ j : Fin n,C (p.coeff (j.val+1))*X^(j.val+1)

def lowerTerm (c r : ℚ) (n : ℕ) : ℚ :=
  if n%2=0 then min c 0*r^n else -|c| *r^n

def lower (n : ℕ) (r : ℚ) (p : ℚ[X]) : ℚ :=
  p.coeff 0+∑ j : Fin n,lowerTerm (p.coeff (j.val+1)) r (j.val+1)

def upper (n : ℕ) (r : ℚ) (p : ℚ[X]) : ℚ :=
  p.coeff 0+∑ j : Fin n,max (p.coeff (j.val+1)) 0*r^(j.val+1)

def lowerOn (n : ℕ) (m r : ℚ) (p : ℚ[X]) : ℚ :=
  lower n r (translated m p)

def upperOn (n : ℕ) (l h : ℚ) (p : ℚ[X]) : ℚ :=
  upper n (h-l) (translated l p)

theorem lowerTerm_le {c r : ℚ} {x : ℝ} (n : ℕ)
    (hr : 0≤r) (hx : |x|≤(r:ℝ)) :
    (lowerTerm c r n : ℝ)≤(c:ℝ)*x^n := by
  have hp : |x^n|≤(r:ℝ)^n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx n
  by_cases hn : n%2=0
  · have hpow : 0≤x^n := by
      have he : n=(n/2)*2 := by omega
      rw [he,pow_mul]
      exact sq_nonneg _
    have hp' : x^n≤(r:ℝ)^n := (le_abs_self _).trans hp
    simp only [lowerTerm,hn,↓reduceIte]
    push_cast
    by_cases hc : (c:ℝ)≤0
    · rw [min_eq_left hc]
      exact mul_le_mul_of_nonpos_left hp' hc
    · rw [min_eq_right (le_of_not_ge hc),zero_mul]
      exact mul_nonneg (le_of_not_ge hc) hpow
  · have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (c:ℝ))
    rw [← abs_mul] at hm
    have hlo := (abs_le.mp hm).1
    simp only [lowerTerm,hn,↓reduceIte]
    push_cast
    linarith

theorem series_lower {n : ℕ} {r : ℚ} {p : ℚ[X]} {x : ℝ}
    (hr : 0≤r) (hx : |x|≤(r:ℝ)) :
    (lower n r p : ℝ)≤aeval x (series n p) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin n) _ => lowerTerm_le (c := p.coeff (j.val+1)) (j.val+1) hr hx)
  simp only [series,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  dsimp [lower]
  push_cast
  linarith

theorem series_upper {n : ℕ} {r : ℚ} {p : ℚ[X]} {x : ℝ}
    (hx : x∈Icc 0 (r:ℝ)) :
    aeval x (series n p)≤(upper n r p : ℝ) := by
  have hterm (j : Fin n) :
      (p.coeff (j.val+1):ℝ)*x^(j.val+1)≤
        max (p.coeff (j.val+1):ℝ) 0*(r:ℝ)^(j.val+1) := by
    calc
      _≤max (p.coeff (j.val+1):ℝ) 0*x^(j.val+1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx.1 _)
      _≤_ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hx.1 hx.2 _) (le_max_right _ _)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  simp only [series,map_add,map_sum,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast]
  dsimp [upper]
  push_cast
  linarith

theorem interval_lower {n : ℕ} {m r : ℚ} {p : ℚ[X]} {x : ℝ}
    (hidentity : translated m p=series n (translated m p))
    (hr : 0≤r) (hx : |x-(m:ℝ)|≤(r:ℝ)) :
    (lowerOn n m r p : ℝ)≤aeval x p := by
  have he := congrArg (fun q : ℚ[X] => aeval (x-(m:ℝ)) q) hidentity
  simp only [translated,aeval_comp,map_add,aeval_C,aeval_X,eq_ratCast] at he
  rw [show (m:ℝ)+(x-(m:ℝ))=x by ring] at he
  rw [he]
  exact series_lower hr hx

theorem interval_upper {n : ℕ} {l h : ℚ} {p : ℚ[X]} {x : ℝ}
    (hidentity : translated l p=series n (translated l p))
    (hx : x∈Icc (l:ℝ) (h:ℝ)) :
    aeval x p≤(upperOn n l h p : ℝ) := by
  have he := congrArg (fun q : ℚ[X] => aeval (x-(l:ℝ)) q) hidentity
  simp only [translated,aeval_comp,map_add,aeval_C,aeval_X,eq_ratCast] at he
  rw [show (l:ℝ)+(x-(l:ℝ))=x by ring] at he
  rw [he]
  apply series_upper
  push_cast
  exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem aeval_hasDerivAt (p : ℚ[X]) (x : ℝ) :
    HasDerivAt (fun y : ℝ => aeval y p) (aeval x p.derivative) x := by
  simpa only [Polynomial.derivative_map,Polynomial.eval_map,Polynomial.aeval_def]
    using (p.map (algebraMap ℚ ℝ)).hasDerivAt x

/-- A second-derivative lower bound, integrated on either side of the
chosen interior point, retains the exact tangent and quadratic reserve. -/
theorem second_derivative_tangent_lower {f df ddf : ℝ → ℝ} {l h x₀ x κ : ℝ}
    (hd : ∀ z∈Icc l h,HasDerivAt f (df z) z)
    (hdd : ∀ z∈Icc l h,HasDerivAt df (ddf z) z)
    (hcurv : ∀ z∈Icc l h,κ≤ddf z)
    (hx₀ : x₀∈Icc l h) (hx : x∈Icc l h) :
    f x₀+df x₀*(x-x₀)+κ/2*(x-x₀)^2≤f x := by
  let F : ℝ → ℝ := fun z => f z-f x₀-df x₀*(z-x₀)-κ/2*(z-x₀)^2
  let D : ℝ → ℝ := fun z => df z-df x₀-κ*(z-x₀)
  have hF (z : ℝ) (hz : z∈Icc l h) : HasDerivAt F (D z) z := by
    have h1 := (hd z hz).sub_const (f x₀)
    have h2 : HasDerivAt (fun y => df x₀*(y-x₀)) (df x₀*1) z :=
      ((hasDerivAt_id' z).sub_const x₀).const_mul (df x₀)
    have h3 : HasDerivAt (fun y => κ/2*(y-x₀)^2) (κ/2*((2:ℕ)*(z-x₀)^(2-1)*1)) z :=
      (((hasDerivAt_id' z).sub_const x₀).pow 2).const_mul (κ/2)
    have h4 := (h1.fun_sub h2).fun_sub h3
    show HasDerivAt (fun z => f z-f x₀-df x₀*(z-x₀)-κ/2*(z-x₀)^2)
      (df z-df x₀-κ*(z-x₀)) z
    convert h4 using 1
    push_cast
    ring
  have hcont : ContinuousOn df (Icc l h) :=
    fun z hz => (hdd z hz).continuousAt.continuousWithinAt
  have hreserve (z w : ℝ) (hz : z∈Icc l h) (hw : w∈Icc l h) (hzw : z≤w) :
      κ*(w-z)≤df w-df z :=
    derivative_reserve hcont (fun r hr => hdd r (Ioo_subset_Icc_self hr))
      (fun r hr => hcurv r (Ioo_subset_Icc_self hr)) hz hw hzw
  have hzero : F x₀=0 := by simp [F]
  by_cases horder : x₀≤x
  · have hsub : Icc x₀ x⊆Icc l h := by
      intro z hz
      exact ⟨hx₀.1.trans hz.1,hz.2.trans hx.2⟩
    have hg := derivative_reserve
      (f := F) (df := D) (k := 0)
      (fun z hz => (hF z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => hF z (hsub (Ioo_subset_Icc_self hz)))
      (fun z hz => by
        have hh := hreserve x₀ z hx₀ (hsub (Ioo_subset_Icc_self hz)) hz.1.le
        dsimp [D]
        linarith)
      (left_mem_Icc.mpr horder) (right_mem_Icc.mpr horder) horder
    rw [hzero] at hg
    dsimp [F] at hg
    linarith
  · have horder' : x≤x₀ := le_of_not_ge horder
    have hsub : Icc x x₀⊆Icc l h := by
      intro z hz
      exact ⟨hx.1.trans hz.1,hz.2.trans hx₀.2⟩
    have hg := derivative_reserve
      (f := fun z => -F z) (df := fun z => -D z) (k := 0)
      (fun z hz => (hF z (hsub hz)).neg.continuousAt.continuousWithinAt)
      (fun z hz => (hF z (hsub (Ioo_subset_Icc_self hz))).neg)
      (fun z hz => by
        have hh := hreserve z x₀ (hsub (Ioo_subset_Icc_self hz)) hx₀ hz.2.le
        dsimp [D]
        linarith)
      (left_mem_Icc.mpr horder') (right_mem_Icc.mpr horder') horder'
    rw [hzero] at hg
    dsimp [F] at hg
    linarith

end SquaresInCircles.Eight.TableFree.CenteredMonomialBounds
