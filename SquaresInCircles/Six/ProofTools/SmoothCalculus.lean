module
public import SquaresInCircles.Six.ProofTools.Smooth
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Real calculus consequences of the smooth-expression checker

The interval hypotheses include the endpoints. This gives continuity on every
closed segment before applying the mean-value theorem. No assertion that a
piecewise support function is globally differentiable occurs here.
-/

noncomputable section
namespace SquaresInCircles.Six.ProofTools
namespace Smooth

@[simp] lemma value_var {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    (Smooth.var i).value x=x i := rfl
@[simp] lemma value_rat {n : ℕ} (q : ℚ) (x : Fin n → ℝ) :
    (Smooth.rat q).value x=(q:ℝ) := rfl
@[simp] lemma value_pi {n : ℕ} (x : Fin n → ℝ) : (Smooth.pi : Smooth n).value x=Real.pi := rfl
@[simp] lemma value_add {n : ℕ} (a b : Smooth n) (x : Fin n → ℝ) :
    (a+b).value x=a.value x+b.value x := rfl
@[simp] lemma value_neg {n : ℕ} (a : Smooth n) (x : Fin n → ℝ) :
    (-a).value x= -a.value x := rfl
@[simp] lemma value_sub {n : ℕ} (a b : Smooth n) (x : Fin n → ℝ) :
    (a-b).value x=a.value x-b.value x := rfl
@[simp] lemma value_mul {n : ℕ} (a b : Smooth n) (x : Fin n → ℝ) :
    (a*b).value x=a.value x*b.value x := rfl
@[simp] lemma value_inv {n : ℕ} (a : Smooth n) (x : Fin n → ℝ) :
    (Smooth.inv a).value x=1/a.value x := rfl
@[simp] lemma value_div {n : ℕ} (a b : Smooth n) (x : Fin n → ℝ) :
    (a/b).value x=a.value x/b.value x := by
  simp only [HDiv.hDiv,Div.div,value_mul,value_inv,div_eq_mul_inv]
@[simp] lemma value_sqrt {n : ℕ} (a : Smooth n) (x : Fin n → ℝ) :
    (Smooth.sqrt a).value x=Real.sqrt (a.value x) := rfl
@[simp] lemma value_sin {n : ℕ} (a : Smooth n) (x : Fin n → ℝ) :
    (Smooth.sin a).value x=Real.sin (a.value x) := rfl
@[simp] lemma value_cos {n : ℕ} (a : Smooth n) (x : Fin n → ℝ) :
    (Smooth.cos a).value x=Real.cos (a.value x) := rfl
@[simp] lemma value_nat {n k : ℕ} (x : Fin n → ℝ) :
    (OfNat.ofNat k : Smooth n).value x=(k:ℝ) := by
  simp [value,expr,Expr.denote]

lemma update_pair_zero (u v t : ℝ) : Function.update ![u,v] (0:Fin 2) t=![t,v] := by
  funext i
  fin_cases i <;> simp

lemma update_pair_one (u v t : ℝ) : Function.update ![u,v] (1:Fin 2) t=![u,t] := by
  funext i
  fin_cases i <;> simp

lemma segment_nondecreasing {f : ℝ → ℝ} {a b : ℝ} (hab : a≤b)
    (hd : ∀ t ∈ Set.Icc a b, ∃ d, HasDerivAt f d t ∧ 0≤d) : f a≤f b := by
  have hcont : ContinuousOn f (Set.Icc a b) := by
    intro t ht
    obtain ⟨d,hd,_⟩ := hd t ht
    exact hd.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc a b)) := by
    intro t ht
    obtain ⟨d,hd,_⟩ := hd t (interior_subset ht)
    exact hd.differentiableAt.differentiableWithinAt
  have hnonneg : ∀ t ∈ interior (Set.Icc a b), 0≤deriv f t := by
    intro t ht
    obtain ⟨d,hd,hpos⟩ := hd t (interior_subset ht)
    rwa [hd.deriv]
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hnonneg
  exact hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

/-- Coordinate monotonicity on a closed nonnegative square. Every derivative
claim includes an actual HasDerivAt proof, including at its boundary. -/
theorem origin_le_on_square (f : Smooth 2) {δ x y : ℝ}
    (hx : 0≤x ∧ x≤δ) (hy : 0≤y ∧ y≤δ)
    (hd : ∀ i : Fin 2, ∀ u v : ℝ, 0≤u → u≤δ → 0≤v → v≤δ →
      HasDerivAt (fun t => f.value (Function.update ![u,v] i t))
          ((derivative i f).value ![u,v]) (![u,v] i) ∧
        0≤(derivative i f).value ![u,v]) : f.value ![0,0]≤f.value ![x,y] := by
  have hδ : 0≤δ := hx.1.trans hx.2
  have hfirst : f.value ![0,0]≤f.value ![x,0] := by
    apply segment_nondecreasing hx.1
    intro u hu
    have hh := hd 0 u 0 hu.1 (hu.2.trans hx.2) le_rfl hδ
    refine ⟨(derivative 0 f).value ![u,0],?_,hh.2⟩
    simpa only [update_pair_zero,Matrix.cons_val_zero] using hh.1
  have hsecond : f.value ![x,0]≤f.value ![x,y] := by
    apply segment_nondecreasing hy.1
    intro v hv
    have hh := hd 1 x v hx.1 hx.2 hv.1 (hv.2.trans hy.2)
    refine ⟨(derivative 1 f).value ![x,v],?_,hh.2⟩
    simpa only [update_pair_one,Matrix.cons_val_one] using hh.1
  exact hfirst.trans hsecond

end Smooth
end SquaresInCircles.Six.ProofTools
