module
public import SquaresInCircles.Six.Analytic.RadicalTrigConcavity

@[expose] public section

/-!
# Freeze centers before reducing stress angles

A separating stress is evaluated at fixed local center coordinates and fixed
central coordinates. When its angle-dependent terms are positive combinations
of sine and cosine on the first quadrant, they are concave before taking any
support supremum. Thus rectangle corners suffice without differentiating a
piecewise cap/vertex support or splitting at its walls.

The endpoint hypotheses in this general theorem are explicit obligations.
Applications below provide ordinary analytic endpoint proofs; no computation
or external certificate is hidden in this reduction.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic

lemma positive_trig_concave {A B : ℝ} (hA : 0≤A) (hB : 0≤B) :
    ConcaveOn ℝ (Set.Icc 0 (Real.pi/2)) (fun x => A*Real.cos x+B*Real.sin x) := by
  have hsin : ConcaveOn ℝ (Set.Icc 0 (Real.pi/2)) Real.sin :=
    strictConcaveOn_sin_Icc.concaveOn.subset
      (Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])) (convex_Icc _ _)
  have hcos : ConcaveOn ℝ (Set.Icc 0 (Real.pi/2)) Real.cos :=
    strictConcaveOn_cos_Icc.concaveOn.subset
      (Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl) (convex_Icc _ _)
  simpa only [smul_eq_mul] using (hcos.smul hA).add (hsin.smul hB)

lemma positive_trig_affine_concave {A B l u a b : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hmap : ∀ x∈Set.Icc l u, 0≤a*x+b ∧ a*x+b≤Real.pi/2) :
    ConcaveOn ℝ (Set.Icc l u)
      (fun x => A*Real.cos (a*x+b)+B*Real.sin (a*x+b)) :=
  concave_affine_argument (positive_trig_concave hA hB) hmap

/-- Separate concavity sends a rectangle to exactly its four original corners. -/
lemma positive_on_separately_concave_rectangle {f : ℝ → ℝ → ℝ} {l u L U x y : ℝ}
    (hx : l≤x ∧ x≤u) (hy : L≤y ∧ y≤U)
    (hfirst : ∀ t∈Set.Icc L U, ConcaveOn ℝ (Set.Icc l u) (fun z => f z t))
    (hleft : ConcaveOn ℝ (Set.Icc L U) (f l))
    (hright : ConcaveOn ℝ (Set.Icc L U) (f u))
    (hll : 0<f l L) (hlu : 0<f l U) (hul : 0<f u L) (huu : 0<f u U) : 0<f x y := by
  exact positive_on_concave_interval (hfirst y hy) hx
    (positive_on_concave_interval hleft hy hll hlu)
    (positive_on_concave_interval hright hy hul huu)

/-- The common three-angle form: v, d and v+d. All coefficients are fixed
when the square centers are frozen. Its only domain condition is geometric. -/
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
  simpa only [frozenTrig,one_mul,add_zero] using ((hc.add hv).add hdc).add hq

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
  simpa only [frozenTrig,one_mul,add_zero,add_comm] using ((hc.add hvc).add hd).add hq

/-- No support-wall case is required: the proof precedes support maximization. -/
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
