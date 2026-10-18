module

public import SquaresInCircles.Eight.ExactFamily.PerturbationModel

/-!
# The five trigonometric remainder estimates

Uncompiled draft of the exact center-square argument.  The estimates are
uniform in the actual positions.  The projected slider coordinates enter only
the first derivative and the radius-three-halves coordinate bound.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily.Perturbation
open Coordinates

theorem sin_remainder (x : ℝ) : |Real.sin x-x|≤|x|^3/6 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact abs_le.mpr ⟨by linarith [Real.sin_ge_sub_cube hx],by linarith [Real.sin_le hx]⟩
  · have hh := Real.sin_ge_sub_cube (neg_nonneg.mpr hx)
    have hu := Real.sin_le (neg_nonneg.mpr hx)
    rw [abs_of_nonpos hx]
    simp only [Real.sin_neg] at hh hu
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

theorem cosine_remainder (x : ℝ) : 0≤1-Real.cos x ∧ 1-Real.cos x≤x^2/2 :=
  ⟨sub_nonneg.mpr (Real.cos_le_one x),by linarith [Real.one_sub_sq_div_two_le_cos (x:=x)]⟩

theorem shifted_cosine_remainder (t x : ℝ) :
    -(x^2/2)≤Real.cos (t+x)-Real.cos t+Real.sin t*x := by
  have h := curvature_tangent (l:=-|x|) (u:=|x|) (x:=x) (t:=0) (κ:=-1)
    (f:=fun r => Real.cos (t+r)) (d:=fun r => -Real.sin (t+r))
    (dd:=fun r => -Real.cos (t+r))
    ⟨neg_abs_le x,le_abs_self x⟩ ⟨by linarith [abs_nonneg x],abs_nonneg x⟩
    (fun r _ => by simpa using (Real.hasDerivAt_cos (t+r)).comp r
      ((hasDerivAt_id r).const_add t))
    (fun r _ => by simpa using ((Real.hasDerivAt_sin (t+r)).comp r
      ((hasDerivAt_id r).const_add t)).neg)
    (fun r _ => by linarith [Real.cos_le_one (t+r)])
  simpa using h

theorem shifted_sine_remainder {t x M : ℝ}
    (hc : 0≤Real.cos t) (hs : 0≤Real.sin t) (hx : |x|≤M) :
    -(Real.sin t)*M^2/2-M^3/6 ≤
      Real.sin (t+x)-Real.sin t-Real.cos t*x := by
  have hM : 0≤M := (abs_nonneg x).trans hx
  have hx2 : x^2≤M^2 := by simpa using pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hx3 := pow_le_pow_left₀ (abs_nonneg x) hx 3
  have hcos := (cosine_remainder x).2
  have hsin := (abs_le.mp (sin_remainder x)).1
  have hc1 := Real.cos_le_one t
  have hsMul := mul_le_mul_of_nonneg_left hcos hs
  have hqMul := mul_le_mul_of_nonneg_left hx2 hs
  have hsinMul := mul_le_mul_of_nonneg_left hsin hc
  have hcMul := mul_le_mul_of_nonneg_right hc1 (pow_nonneg hM 3)
  rw [Real.sin_add]
  nlinarith

theorem sin_remainder_bounded {x M : ℝ} (hx : |x|≤M) :
    -M^3/6≤Real.sin x-x ∧ Real.sin x-x≤M^3/6 := by
  have hh := abs_le.mp (sin_remainder x)
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 3
  constructor <;> linarith

theorem two_cosines_difference {x y M : ℝ} (hx : |x|≤M) (hy : |y|≤M) :
    |Real.cos x-Real.cos y|≤M^2/2 := by
  have hxc := (small_angle hx).1
  have hyc := (small_angle hy).1
  exact abs_le.mpr ⟨by linarith [Real.cos_le_one y],by linarith [Real.cos_le_one x]⟩

theorem sum_tree_power (a : Errors) (k : ℕ) (hk : 1≤k) :
    (∑ i : Fin 5, |tree a i|^k)≤(errorSum a)^k := by
  exact Finset.sum_pow_le_pow_sum_of_nonneg (fun i _ => abs_nonneg (tree a i)) hk

theorem coefficient_identities {d : Coordinates} (hw : d.WeightDomain) :
    KA d=d.edgeAlpha*d.x₁/d.c ∧ KB d=d.edgeBeta*(d.y+2) ∧
    KD d= -d.edgeDelta*d.x₃ ∧ KE d= -d.edgeDelta*d.x₄/d.s ∧
    KH d= -d.edgeEpsilon*d.h₁ := by
  have hM := ne_of_gt hw.weightMass_pos
  have hA := ne_of_gt hw.rawAlpha_pos
  have hB := ne_of_gt hw.rawBeta_pos
  have hc := ne_of_gt hw.c_pos
  have hs := ne_of_gt hw.s_pos
  have hx₁ := ne_of_gt hw.x₁_pos
  have hx₃ := ne_of_lt hw.x₃_neg
  have hx₄ := ne_of_lt hw.x₄_neg
  have hh₁ := ne_of_lt hw.h₁_neg
  have hh₂ := ne_of_lt hw.h₂_neg
  have hy := ne_of_gt hw.y_add_two_pos
  dsimp [KA,KB,KD,KE,KH,edgeAlpha,edgeBeta,edgeDelta,edgeEpsilon,edgeOmega,
    lam,mu,rawLambda,rawMu,rawMuA,rawMuB,rawMuD,rawMuE,rawMuH,rawDelta,rawEpsilon]
  repeat' constructor
  all_goals field_simp [hM,hA,hB,hc,hs,hx₁,hx₃,hx₄,hh₁,hh₂,hy] <;> ring

theorem force_coefficients_pos {d : Coordinates} (hw : d.WeightDomain) :
    0<KA d ∧ 0<KB d ∧ 0<KD d ∧ 0<KE d ∧ 0<KH d := by
  have h0 := hw.lam_pos 0
  have h1 := hw.lam_pos 1
  have h3 := hw.lam_pos 3
  have h4 := hw.lam_pos 4
  have h6 := hw.lam_pos 6
  have hm0 := hw.mu_pos 0
  have hm1 := hw.mu_pos 1
  have hm2 := hw.mu_pos 2
  have hm3 := hw.mu_pos 3
  have hm4 := hw.mu_pos 4
  dsimp [KA,KB,KD,KE,KH,edgeAlpha,edgeBeta,edgeDelta,edgeEpsilon,edgeOmega]
  exact ⟨by positivity,by positivity,by positivity,by positivity,by positivity⟩

theorem norm_linear_combination (a b : ℝ) (u v : Point) :
    normSq (add (scale a u) (scale b v))=
      a^2*normSq u+b^2*normSq v+2*a*b*dot u v := by
  dsimp [normSq,add,scale,dot]; ring

@[simp] theorem norm_ex (t : ℝ) : normSq (ex t)=1 := by
  simpa [normSq,ex] using Real.cos_sq_add_sin_sq t
@[simp] theorem norm_ey (t : ℝ) : normSq (ey t)=1 := by
  simpa [normSq,ey,add_comm] using Real.cos_sq_add_sin_sq t
theorem dot_ey_ex (b t : ℝ) : dot (ey b) (ex t)=Real.sin (t-b) := by
  simp [dot,ey,ex,Real.sin_sub]; ring
theorem dot_ex_ey (t b : ℝ) : dot (ex t) (ey b)=Real.sin (t-b) := by
  simp [dot,ey,ex,Real.sin_sub]; ring
theorem dot_ey_ey (b t : ℝ) : dot (ey b) (ey t)=Real.cos (t-b) := by
  simp [dot,ey,Real.cos_sub]; ring

theorem force_term_difference {d : Coordinates} (hw : d.WeightDomain)
    (t : ℝ) (a : Errors) (o : Owners) :
    forceTerm d t a o-forceTerm d t (fun _=>0) o =
      KA d*(Real.sin (t-ownerB a o)-Real.sin t)-
      KB d*Real.sin (ownerU a o-ownerB a o)+
      KD d*Real.sin (ownerV a o-ownerD a o)+
      KE d*(Real.cos (t+a 4-ownerD a o)-Real.cos t)+
      (if o 4 then 0 else KH d*Real.sin (a 4)) := by
  have hm (i : Fin 5) : d.mu i≠0 := ne_of_gt (hw.mu_pos i)
  have hsub (u v : Point) : sub u v=add u (scale (-1) v) := by
    ext <;> simp [sub,add,scale] <;> ring
  have hneg (u : Point) : normSq (scale (-1) u)=normSq u := by
    dsimp [normSq,scale]; ring
  cases hH : o 4 <;>
    simp [forceTerm,force,Fin.sum_univ_succ,hsub,hneg,norm_linear_combination,
      norm_ex,norm_ey,dot_ey_ex,dot_ex_ey,dot_ey_ey,
      ownerB,ownerU,ownerV,ownerD,ownerH,hH,KA,KB,KD,KE,KH,
      Real.sin_neg,Real.cos_neg] <;>
    field_simp [hm 0,hm 1,hm 2,hm 3,hm 4] <;> ring

theorem force_term_lower {d : Coordinates} (hw : d.WeightDomain)
    {t : ℝ} (htc : Real.cos t=d.c) (hts : Real.sin t=d.s)
    (a : Errors) (o : Owners) :
    forceTerm d t (fun _=>0) o+forceLinear d a o-
      ((KA d*d.s+KE d)/2)*(errorSum a)^2-
      ((KA d+KB d+KD d+KH d)/6)*(errorSum a)^3 ≤ forceTerm d t a o := by
  obtain ⟨hb,hu,hv,hd,hub,hvd,hhd,hhe⟩ := owner_error_bounds a o
  have hS := errorSum_nonneg a
  have hC := chainSum_nonneg a
  have hCS : chainSum a≤errorSum a := by rw [errorSum_decompose]; positivity
  obtain ⟨hKA,hKB,hKD,hKE,hKH⟩ := force_coefficients_pos hw
  have hA := shifted_sine_remainder (t:=t) (x:=-ownerB a o)
    (by simpa [htc] using hw.c_pos.le) (by simpa [hts] using hw.s_pos.le)
    (by simpa using hb.trans hCS)
  have hB := sin_remainder_bounded (hub.trans hCS)
  have hD := sin_remainder_bounded (hvd.trans hCS)
  have hE := shifted_cosine_remainder t (a 4-ownerD a o)
  have hEpow : (a 4-ownerD a o)^2≤(errorSum a)^2 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) hhd 2
  have hH := sin_remainder_bounded (M:=errorSum a)
    (by rw [errorSum_decompose]; linarith : |a 4|≤errorSum a)
  have hAm := mul_le_mul_of_nonneg_left hA hKA.le
  have hBm := mul_le_mul_of_nonneg_left hB.2 hKB.le
  have hDm := mul_le_mul_of_nonneg_left hD.1 hKD.le
  have hEm := mul_le_mul_of_nonneg_left hE hKE.le
  have hEpm := mul_le_mul_of_nonneg_left hEpow hKE.le
  have hHm := mul_le_mul_of_nonneg_left hH.1 hKH.le
  have hKcube : 0≤KH d*(errorSum a)^3 := mul_nonneg hKH.le (pow_nonneg hS 3)
  have heq := force_term_difference hw t a o
  rw [htc,hts] at hAm
  cases hHowner : o 4 <;>
    simp [forceLinear,hHowner,sub_eq_add_neg,add_assoc] at heq ⊢ <;> linarith

def supportRows (a : Errors) (o : Owners) : Fin 5 → ℝ :=
  ![1+Real.cos (tree a 0)-Real.sin (tree a 0)/2+|Real.sin (tree a 0)|/2,
    if o 1 then 1+Real.cos (tree a 1)/2+|Real.sin (tree a 1)|/2
      else 1/2+Real.cos (tree a 1)+Real.sin (tree a 1)/2+|Real.sin (tree a 1)|/2,
    if o 2 then 1/2+Real.cos (tree a 2)+Real.sin (tree a 2)/2+|Real.sin (tree a 2)|/2
      else 1+Real.cos (tree a 2)/2+|Real.sin (tree a 2)|/2,
    1+Real.cos (tree a 3)+Real.sin (tree a 3)/2+|Real.sin (tree a 3)|/2,
    if o 4 then 1+Real.cos (tree a 4)/2+|Real.sin (tree a 4)|/2
      else 1/2+Real.cos (tree a 4)-Real.sin (tree a 4)/2+|Real.sin (tree a 4)|/2]

theorem terminal_angles {t : ℝ} (ht : 1/10≤t ∧ t≤4/25) {a : Errors}
    (hS : errorSum a≤1/1000) :
    0≤Real.cos t ∧ 0≤Real.sin t ∧
    (∀ i : Fin 5, 0≤Real.cos (tree a i)) ∧
    0≤Real.cos (t+a 4-a 3) ∧ 0≤Real.sin (t+a 4-a 3) := by
  have hS0 := errorSum_nonneg a
  have hh := (owner_error_bounds a (fun _=>false)).2.2.2.2.2.2.2
  have he := abs_le.mp hh
  have hr : 0≤t+a 4-a 3 ∧ t+a 4-a 3≤Real.pi/2 := by
    constructor <;> linarith [Real.pi_gt_three]
  have htr : 0≤t ∧ t≤Real.pi/2 := by constructor <;> linarith [Real.pi_gt_three]
  refine ⟨(cos_sin_nonneg htr).1,(cos_sin_nonneg htr).2,?_,
    (cos_sin_nonneg hr).1,(cos_sin_nonneg hr).2⟩
  intro i
  have hb := (small_angle ((tree_bound a i).trans hS)).1
  norm_num at hb
  linarith

theorem support_term_rows {d : Coordinates} {t : ℝ}
    (ht : 1/10≤t ∧ t≤4/25) {a : Errors} (hS : errorSum a≤1/1000) (o : Owners) :
    supportTerm d t a o=(∑ i : Fin 5, edgeWeights d i*supportRows a o i)+
      d.edgeEpsilon*(1+Real.sin (t+a 4-a 3))+d.edgeOmega*(1/2+Real.cos t) := by
  obtain ⟨hc,hs,hca,hce,hse⟩ := terminal_angles ht hS
  have hunit (x : ℝ) := Real.cos_sq_add_sin_sq x
  have habs (i : Fin 5) : |Real.cos (tree a i)|=Real.cos (tree a i) := abs_of_nonneg (hca i)
  cases h0 : o 0 <;> cases h1 : o 1 <;> cases h2 : o 2 <;>
    cases h3 : o 3 <;> cases h4 : o 4
  all_goals
    simp [supportTerm,supportRows,force,support,phases,tails,heads,offset,
      edgeWeights,normal,ownerB,ownerU,ownerV,ownerD,ownerH,h0,h1,h2,h3,h4,
      Fin.sum_univ_succ,edgeAlpha,edgeBeta,edgeDelta,edgeEpsilon,edgeOmega,
      lam,rawLambda,dot,add,sub,scale,R,ex,ey,
      Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,Real.cos_neg,Real.sin_neg,
      abs_neg,abs_of_nonneg hc,abs_of_nonneg hs,abs_of_nonneg hce,abs_of_nonneg hse,
      tree] at habs ⊢
  all_goals
    rw [abs_of_nonneg (hca 0),abs_of_nonneg (hca 1),abs_of_nonneg (hca 2),
      abs_of_nonneg (hca 3),abs_of_nonneg (hca 4)]
    ring_nf
    nlinarith [hunit (a 0),hunit (a 1),hunit (a 2),hunit (a 3),hunit (a 4),hunit t]

theorem aligned_row_remainder {A B x : ℝ} (hA : 0≤A) (hA1 : A≤1)
    (hB : |B|≤1/2) :
    -x^2/2-|x|^3/6 ≤ A*(Real.cos x-1)+B*(Real.sin x-x)+
      (|Real.sin x|-|x|)/2 := by
  have hcos := cosine_remainder x
  have hsin := sin_remainder x
  have habs := abs_abs_sub_abs_le_abs_sub (Real.sin x) x
  have hsin' := abs_le.mp hsin
  have habs' : -|x|^3/6≤|Real.sin x|-|x| := by
    have h := (abs_le.mp (habs.trans hsin)).1
    exact h
  have hbprod : B*(Real.sin x-x)≥ -|x|^3/12 := by
    have h := abs_mul B (Real.sin x-x)
    have hm := mul_le_mul hB hsin (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
    rw [← h] at hm
    linarith [(abs_le.mp hm).1]
  have hAc := mul_le_mul_of_nonneg_left hcos.2 hA
  have hAp := mul_le_mul_of_nonneg_right hA1 (sq_nonneg x)
  nlinarith

theorem support_term_lower {d : Coordinates} (hw : d.WeightDomain)
    {t : ℝ} (ht : 1/10≤t ∧ t≤4/25) (htc : Real.cos t=d.c) (hts : Real.sin t=d.s)
    {a : Errors} (hS : errorSum a≤1/1000) (o : Owners) {w : ℝ}
    (hw0 : 0≤w) (hweights : ∀ i : Fin 7, d.lam i≤w) :
    supportTerm d t (fun _=>0) o+supportLinear d a o+cusp d a-
      (w/2+d.edgeEpsilon*d.s/2)*(errorSum a)^2-
      (w/6+d.edgeEpsilon/6)*(errorSum a)^3 ≤ supportTerm d t a o := by
  have hrows := support_term_rows (d:=d) ht hS o
  have hzero := support_term_rows (d:=d) ht (a:=fun _=>0) (by norm_num [errorSum,tree]) o
  have hedge (i : Fin 5) : edgeWeights d i≤w := by
    fin_cases i <;> simp [edgeWeights,edgeAlpha,edgeBeta,edgeDelta,edgeOmega] <;>
      first | exact hweights 0 | exact hweights 1 | exact hweights 3 | exact hweights 4
  have hedge0 (i : Fin 5) : 0≤edgeWeights d i := by
    fin_cases i <;> simp [edgeWeights,edgeAlpha,edgeBeta,edgeDelta,edgeOmega] <;>
      first | exact (hw.lam_pos 0).le | exact (hw.lam_pos 1).le |
        exact (hw.lam_pos 3).le | exact (hw.lam_pos 4).le
  have hr (i : Fin 5) :
      -w*(tree a i)^2/2-w*|tree a i|^3/6 ≤
      edgeWeights d i*(supportRows a o i-supportRows (fun _=>0) o i)-
      (edgeWeights d i/2)*|tree a i|-
      (![(-d.edgeAlpha/2),if o 1 then 0 else d.edgeBeta/2,
        if o 2 then d.edgeBeta/2 else 0,d.edgeDelta/2,
        if o 4 then 0 else -d.edgeOmega/2] i)*tree a i := by
    have h₁ := aligned_row_remainder (A:=1) (B:=-(1/2)) (x:=tree a i)
      (by norm_num) (by norm_num) (by norm_num)
    have h₂ := aligned_row_remainder (A:=1/2) (B:=0) (x:=tree a i)
      (by norm_num) (by norm_num) (by norm_num)
    have h₃ := aligned_row_remainder (A:=1) (B:=1/2) (x:=tree a i)
      (by norm_num) (by norm_num) (by norm_num)
    have hm₁ := mul_le_mul_of_nonneg_left h₁ (hedge0 i)
    have hm₂ := mul_le_mul_of_nonneg_left h₂ (hedge0 i)
    have hm₃ := mul_le_mul_of_nonneg_left h₃ (hedge0 i)
    have hp₂ := mul_le_mul_of_nonneg_right (hedge i) (sq_nonneg (tree a i))
    have hp₃ := mul_le_mul_of_nonneg_right (hedge i) (pow_nonneg (abs_nonneg _) 3)
    fin_cases i <;> cases h1 : o 1 <;> cases h2 : o 2 <;> cases h4 : o 4 <;>
      simp [edgeWeights,supportRows,h1,h2,h4,tree] at * <;> linarith
  have hsum := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 5))) (fun i _=>hr i)
  have hp₂ := sum_tree_power a 2 (by omega)
  have hp₃ := sum_tree_power a 3 (by omega)
  have hp₂w := mul_le_mul_of_nonneg_left hp₂ hw0
  have hp₃w := mul_le_mul_of_nonneg_left hp₃ hw0
  have hdiff := (owner_error_bounds a o).2.2.2.2.2.2.2
  have hmixed := shifted_sine_remainder
    (by simpa [htc] using hw.c_pos.le) (by simpa [hts] using hw.s_pos.le) hdiff
  have hmixed' := mul_le_mul_of_nonneg_left hmixed (hw.lam_pos 6).le
  rw [htc,hts] at hmixed'
  simp [Fin.sum_univ_succ,supportLinear,cusp,edgeWeights,tree] at hsum hp₂w hp₃w hzero ⊢
  rw [hrows]
  linarith

theorem slider_exact (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) (p : Positions) :
    sliderTerm d t a o p=
      d.edgeBeta*(p 5).1*(Real.cos (ownerU a o)-Real.cos (ownerV a o))+
      d.edgeBeta*(p 5).2*(Real.sin (ownerU a o)-Real.sin (ownerV a o))+
      if o 4 then d.edgeOmega*dot (ex t) (p 6)*(1-Real.cos (a 4))-
        d.edgeOmega*dot (ey t) (p 6)*Real.sin (a 4) else 0 := by
  cases h : o 4 <;>
    simp [sliderTerm,force,ownerH,h,dot,scale,sub,ex,ey,Real.cos_add,Real.sin_add] <;> ring

theorem product_lower_of_abs {u v A B : ℝ} (hu : |u|≤A) (hv : |v|≤B) :
    -(A*B)≤u*v := by
  have h := mul_le_mul hu hv (abs_nonneg _) ((abs_nonneg _).trans hu)
  rw [← abs_mul] at h
  exact (abs_le.mp h).1

theorem slider_term_lower {d : Coordinates} (hw : d.WeightDomain)
    (t : ℝ) (a : Errors) (o : Owners) (p : Positions) {w : ℝ}
    (hw0 : 0≤w) (hβ : d.edgeBeta≤w) (hω : d.edgeOmega≤w)
    (hX : |(p 5).1|≤3/2) (hZ : |(p 5).2|≤3/2)
    (hU : |dot (ex t) (p 6)|≤3/2) (hV : |dot (ey t) (p 6)|≤3/2) :
    sliderLinear d a o (p 5).2 (dot (ey t) (p 6))-
      (3*w/4)*(errorSum a)^2-(w/2)*(errorSum a)^3 ≤ sliderTerm d t a o p := by
  obtain ⟨hb,hu,hv,hd,hub,hvd,hhd,hhe⟩ := owner_error_bounds a o
  have hC := chainSum_nonneg a
  have hS := errorSum_nonneg a
  have hc := two_cosines_difference hu hv
  have hsu := sin_remainder_bounded hu
  have hsv := sin_remainder_bounded hv
  have hsinuv : |(Real.sin (ownerU a o)-Real.sin (ownerV a o))-
      (ownerU a o-ownerV a o)|≤(chainSum a)^3/3 := by
    rw [abs_le]
    constructor <;> linarith
  have hXc := product_lower_of_abs hX hc
  have hZs := product_lower_of_abs hZ hsinuv
  have hXcβ := mul_le_mul_of_nonneg_left hXc (hw.lam_pos 1).le
  have hZsβ := mul_le_mul_of_nonneg_left hZs (hw.lam_pos 1).le
  have hhcos : |1-Real.cos (a 4)|≤(a 4)^2/2 := by
    rw [abs_of_nonneg (cosine_remainder (a 4)).1]
    exact (cosine_remainder (a 4)).2
  have hhU := product_lower_of_abs hU hhcos
  have hhV := product_lower_of_abs hV (sin_remainder (a 4))
  have hhVm := product_lower_of_abs (by simpa using hV : |-dot (ey t) (p 6)|≤3/2)
    (sin_remainder (a 4))
  have hhUω := mul_le_mul_of_nonneg_left hhU (hw.lam_pos 4).le
  have hhVω := mul_le_mul_of_nonneg_left hhVm (hw.lam_pos 4).le
  have hβ₂ := mul_le_mul_of_nonneg_right hβ (sq_nonneg (chainSum a))
  have hβ₃ := mul_le_mul_of_nonneg_right hβ (pow_nonneg hC 3)
  have hω₂ := mul_le_mul_of_nonneg_right hω (sq_nonneg (a 4))
  have hω₃ := mul_le_mul_of_nonneg_right hω (pow_nonneg (abs_nonneg (a 4)) 3)
  have hp₂ : (chainSum a)^2+(a 4)^2≤(errorSum a)^2 := by
    rw [errorSum_decompose]
    nlinarith [mul_nonneg hC (abs_nonneg (a 4)),sq_abs (a 4)]
  have hp₃ : (chainSum a)^3+|a 4|^3≤(errorSum a)^3 := by
    rw [errorSum_decompose]
    nlinarith [mul_nonneg (sq_nonneg (chainSum a)) (abs_nonneg (a 4)),
      mul_nonneg hC (sq_nonneg |a 4|)]
  have hp₂w := mul_le_mul_of_nonneg_left hp₂ hw0
  have hp₃w := mul_le_mul_of_nonneg_left hp₃ hw0
  have hex := slider_exact d t a o p
  cases hh : o 4 <;> simp [sliderLinear,hh] at hex ⊢ <;> linarith

theorem coefficient_reserve {d : Coordinates} (hw : d.WeightDomain)
    (hstation : d.positionDerivative=0) (hY : 0<d.cutY ∧ d.cutY<1)
    (hαβ : d.edgeAlpha<d.edgeBeta) (hx : d.x₄-d.x₃<0)
    {ρ Z η : ℝ} (hres : ∀ j : Fin 9, ρ≤d.ownerReserve j)
    (hZ : 557/1000≤Z ∧ Z≤1417/1000)
    (hη : -515/1000≤η ∧ η≤392/1000) (o : Owners) (i : Fin 5) :
    ρ≤edgeWeights d i/2-|coefficient d o Z η i| := by
  have h0 := hres 0; have h1 := hres 1; have h2 := hres 2
  have h3 := hres 3; have h4 := hres 4; have h5 := hres 5
  have h6 := hres 6; have h7 := hres 7; have h8 := hres 8
  simp only [ownerReserve,Matrix.cons_val_zero,Matrix.cons_val_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨hK,hL,hδx⟩ := cut_identities hw hstation
  have hα := hw.lam_pos 0
  have hβ := hw.lam_pos 1
  have hδ := hw.lam_pos 3
  have hω := hw.lam_pos 4
  change 0<d.edgeAlpha at hα
  change 0<d.edgeBeta at hβ
  change 0<d.edgeDelta at hδ
  change 0<d.edgeOmega at hω
  have hαY := mul_pos hα hY.1
  have hα1Y := mul_pos hα (by linarith : 0<1-d.cutY)
  have hδdiff := mul_neg_of_pos_of_neg hδ hx
  have hZl := mul_le_mul_of_nonneg_left hZ.1 hβ.le
  have hZu := mul_le_mul_of_nonneg_left hZ.2 hβ.le
  have hηl := mul_le_mul_of_nonneg_left hη.1 hω.le
  have hηu := mul_le_mul_of_nonneg_left hη.2 hω.le
  have hXdef : d.cutX=d.edgeBeta*(d.y+2+d.cutJ) := rfl
  have reserve_iff (r w c : ℝ) : r≤w/2-|c| ↔ -w/2+r≤c ∧ c≤w/2-r := by
    constructor
    · intro h
      have hc : |c|≤w/2-r := by linarith
      have hh := abs_le.mp hc
      exact ⟨by linarith,hh.2⟩
    · intro h
      have hc : |c|≤w/2-r := abs_le.mpr ⟨by linarith,h.2⟩
      linarith
  fin_cases i <;> simp only [edgeWeights,coefficient,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals
    split_ifs <;> rw [reserve_iff] <;> constructor <;> nlinarith

theorem linear_cusp_lower {d : Coordinates} (hw : d.WeightDomain)
    (hstation : d.positionDerivative=0) (hY : 0<d.cutY ∧ d.cutY<1)
    (hαβ : d.edgeAlpha<d.edgeBeta) (hx : d.x₄-d.x₃<0)
    {ρ Z η : ℝ} (hres : ∀ j : Fin 9, ρ≤d.ownerReserve j)
    (hZ : 557/1000≤Z ∧ Z≤1417/1000)
    (hη : -515/1000≤η ∧ η≤392/1000) (a : Errors) (o : Owners) :
    ρ*errorSum a ≤ (∑ i : Fin 5, coefficient d o Z η i*tree a i)+cusp d a := by
  have hterm (i : Fin 5) : ρ*|tree a i|≤
      coefficient d o Z η i*tree a i+(edgeWeights d i/2)*|tree a i| := by
    have hr := coefficient_reserve hw hstation hY hαβ hx hres hZ hη o i
    have hm := mul_le_mul_of_nonneg_right hr (abs_nonneg (tree a i))
    have hab : -|coefficient d o Z η i|*|tree a i|≤coefficient d o Z η i*tree a i := by
      rw [← neg_mul,← abs_mul]
      exact neg_abs_le _
    linarith
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 5))) (fun i _=>hterm i)
  simpa [errorSum,cusp,Finset.mul_sum,Finset.sum_add_distrib] using hs

def quadraticCoefficient (d : Coordinates) (w : ℝ) : ℝ :=
  (KA d*d.s+KE d)/2+w/2+d.edgeEpsilon*d.s/2+3*w/4
def cubicCoefficient (d : Coordinates) (w : ℝ) : ℝ :=
  (KA d+KB d+KD d+KH d)/6+w/6+d.edgeEpsilon/6+w/2

end SquaresInCircles.Eight.ExactFamily.Perturbation
