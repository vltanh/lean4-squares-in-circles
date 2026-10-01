import SquaresInCircles.Six.Analytic.RadicalTrigConcavity

/-!
# Stresses with fixed centres

With the centres of the squares fixed, a weighted sum of separating
inequalities is a function of the angles alone. When it is a constant plus
harmonics `A cos x + B sin x`, with `A, B ≥ 0`, in `v`, `d` and `v + d`, and
`v + d ≤ π/2`, it is concave in each of `v` and `d`. So it is positive on a
rectangle of angles as soon as it is positive at the four corners.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma positive_trig_concave {A B : ℝ} (hA : 0≤A) (hB : 0≤B) :
    ConcaveOn ℝ (Set.Icc 0 (Real.pi/2)) (fun x => A*Real.cos x+B*Real.sin x) := by
  let f' : ℝ → ℝ := fun x => -A*Real.sin x+B*Real.cos x
  let f'' : ℝ → ℝ := fun x => -A*Real.cos x-B*Real.sin x
  have hd (x : ℝ) : HasDerivAt (fun x => A*Real.cos x+B*Real.sin x) (f' x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul A).add
      ((Real.hasDerivAt_sin x).const_mul B) using 1
    dsimp [f']
    ring
  have hdd (x : ℝ) : HasDerivAt f' (f'' x) x := by
    convert ((Real.hasDerivAt_sin x).const_mul (-A)).add
      ((Real.hasDerivAt_cos x).const_mul B) using 1
    dsimp [f'']
    ring
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) (f' := f') (f'' := f'')
    (by fun_prop)
  · intro x _
    exact (hd x).hasDerivWithinAt
  · intro x _
    exact (hdd x).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have hc : 0≤Real.cos x :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos,hx'.1],hx'.2⟩
    have hs : 0≤Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi hx'.1 (by linarith [Real.pi_pos,hx'.2])
    have hAc := mul_nonneg hA hc
    have hBs := mul_nonneg hB hs
    dsimp [f'']
    linarith

lemma positive_trig_affine_concave {A B l u a b : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hmap : ∀ x∈Set.Icc l u, 0≤a*x+b ∧ a*x+b≤Real.pi/2) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x => A*Real.cos (a*x+b)+B*Real.sin (a*x+b)) :=
  concave_affine_argument (positive_trig_concave hA hB) hmap

/-- A function on `[l, u] × [L, U]`, concave in the first variable and concave
in the second on the edges `x = l` and `x = u`, is positive if it is positive
at the four corners. -/
lemma positive_on_separately_concave_rectangle {f : ℝ → ℝ → ℝ} {l u L U x y : ℝ}
    (hx : l≤x ∧ x≤u) (hy : L≤y ∧ y≤U)
    (hfirst : ∀ t∈Set.Icc L U, ConcaveOn ℝ (Set.Icc l u) (fun z => f z t))
    (hleft : ConcaveOn ℝ (Set.Icc L U) (f l))
    (hright : ConcaveOn ℝ (Set.Icc L U) (f u))
    (hll : 0<f l L) (hlu : 0<f l U) (hul : 0<f u L) (huu : 0<f u U) : 0<f x y := by
  exact positive_on_concave_interval (f := fun z => f z y) (hfirst y hy) hx
    (positive_on_concave_interval (f := f l) hleft hy hll hlu)
    (positive_on_concave_interval (f := f u) hright hy hul huu)

/-- A constant plus harmonics in `v`, `d` and `v + d`: the form of a stress
with fixed centres. -/
def frozenTrig (C Av Bv Ad Bd Aq Bq v d : ℝ) : ℝ :=
  C+(Av*Real.cos v+Bv*Real.sin v)+(Ad*Real.cos d+Bd*Real.sin d)+
    (Aq*Real.cos (v+d)+Bq*Real.sin (v+d))

lemma frozenTrig_concave_v {C Av Bv Ad Bd Aq Bq V D d : ℝ}
    (hAv : 0≤Av) (hBv : 0≤Bv) (hAq : 0≤Aq) (hBq : 0≤Bq)
    (hD : 0≤D) (hsum : V+D≤Real.pi/2) (hd : 0≤d ∧ d≤D) :
    ConcaveOn ℝ (Set.Icc 0 V) (fun v => frozenTrig C Av Bv Ad Bd Aq Bq v d) := by
  have hv := positive_trig_affine_concave (l := 0) (u := V) (a := 1) (b := 0)
    hAv hBv (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  have hq := positive_trig_affine_concave (l := 0) (u := V) (a := 1) (b := d)
    hAq hBq (by intro x hx; constructor <;> linarith [hx.1,hx.2,hd.1,hd.2])
  have hc := concave_constant C 0 V
  have hdc := concave_constant (Ad*Real.cos d+Bd*Real.sin d) 0 V
  refine (((hc.add hv).add hdc).add hq).congr ?_
  intro x _
  simp only [frozenTrig,Pi.add_apply,one_mul,add_zero]

lemma frozenTrig_concave_d {C Av Bv Ad Bd Aq Bq V D v : ℝ}
    (hAd : 0≤Ad) (hBd : 0≤Bd) (hAq : 0≤Aq) (hBq : 0≤Bq)
    (hV : 0≤V) (hsum : V+D≤Real.pi/2) (hv : 0≤v ∧ v≤V) :
    ConcaveOn ℝ (Set.Icc 0 D) (fun d => frozenTrig C Av Bv Ad Bd Aq Bq v d) := by
  have hd := positive_trig_affine_concave (l := 0) (u := D) (a := 1) (b := 0)
    hAd hBd (by intro x hx; constructor <;> linarith [hx.1,hx.2])
  have hq := positive_trig_affine_concave (l := 0) (u := D) (a := 1) (b := v)
    hAq hBq (by intro x hx; constructor <;> linarith [hx.1,hx.2,hv.1,hv.2])
  have hc := concave_constant C 0 D
  have hvc := concave_constant (Av*Real.cos v+Bv*Real.sin v) 0 D
  refine (((hc.add hvc).add hd).add hq).congr ?_
  intro x _
  simp only [frozenTrig,Pi.add_apply,one_mul,add_zero,add_comm x v]

/-- With nonnegative coefficients and `V + D ≤ π/2`, positivity at the four
corners of `[0, V] × [0, D]` gives positivity on the whole rectangle. -/
theorem frozenTrig_positive {C Av Bv Ad Bd Aq Bq V D v d : ℝ}
    (hAv : 0≤Av) (hBv : 0≤Bv) (hAd : 0≤Ad) (hBd : 0≤Bd) (hAq : 0≤Aq) (hBq : 0≤Bq)
    (hV : 0≤V) (hD : 0≤D) (hsum : V+D≤Real.pi/2)
    (hv : 0≤v ∧ v≤V) (hd : 0≤d ∧ d≤D)
    (h00 : 0<frozenTrig C Av Bv Ad Bd Aq Bq 0 0)
    (h0D : 0<frozenTrig C Av Bv Ad Bd Aq Bq 0 D)
    (hV0 : 0<frozenTrig C Av Bv Ad Bd Aq Bq V 0)
    (hVD : 0<frozenTrig C Av Bv Ad Bd Aq Bq V D) :
    0<frozenTrig C Av Bv Ad Bd Aq Bq v d := by
  apply positive_on_separately_concave_rectangle hv hd
    (fun y hy => frozenTrig_concave_v hAv hBv hAq hBq hD hsum hy)
    (frozenTrig_concave_d hAd hBd hAq hBq hV hsum ⟨le_rfl,hV⟩)
    (frozenTrig_concave_d hAd hBd hAq hBq hV hsum ⟨hV,le_rfl⟩)
    h00 h0D hV0 hVD

end SquaresInCircles.Six.Analytic
