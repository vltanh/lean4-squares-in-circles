module

public import SquaresInCircles.Eight.ExactFamily.PerturbationModel

/-!
# Eight squares: the remainder estimates of the terminal dual

After the squares are completed at the centres (`PerturbationModel.lean`), each of the three parts
of the reduced dual, the force, support and slider terms, is at least its value at zero frame
errors plus a first-order term, less quadratic and cubic remainders in the total error
`errorSum` (`force_term_lower`, `support_term_lower`, `slider_term_lower`); the remainders add up
to `quadraticCoefficient` and `cubicCoefficient`. The estimates are uniform in the centres: the
coordinates of the two slider centres enter only the first-order term and the bound `3/2` on their
size. When the nine owner reserves are at least `ρ`, the first-order terms together with the cusps
of the supports are at least `ρ` times the total error (`coefficient_reserve`,
`linear_cusp_lower`).
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
    have h3 := pow_nonneg hx 3
    exact abs_le.mpr ⟨by linarith [Real.sin_ge_sub_cube hx],by linarith [Real.sin_le hx]⟩
  · have hh := Real.sin_ge_sub_cube (neg_nonneg.mpr hx)
    have hu := Real.sin_le (neg_nonneg.mpr hx)
    rw [abs_of_nonpos hx]
    simp only [Real.sin_neg] at hh hu
    have h3 := pow_nonneg (neg_nonneg.mpr hx) 3
    exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem cosine_remainder (x : ℝ) : 0≤1-Real.cos x ∧ 1-Real.cos x≤x^2/2 :=
  ⟨sub_nonneg.mpr (Real.cos_le_one x),by linarith [Real.one_sub_sq_div_two_le_cos (x:=x)]⟩

theorem shifted_cosine_remainder (t x : ℝ) :
    -(x^2/2)≤Real.cos (t+x)-Real.cos t+Real.sin t*x := by
  have hd : ∀ r ∈ Icc (-|x|) |x|,
      HasDerivAt (fun r => Real.cos (t+r)) (-Real.sin (t+r)) r := by
    intro r _
    have h := ((hasDerivAt_id' r).const_add t).cos
    simpa using h
  have hdd : ∀ r ∈ Icc (-|x|) |x|,
      HasDerivAt (fun r => -Real.sin (t+r)) (-Real.cos (t+r)) r := by
    intro r _
    have h := ((hasDerivAt_id' r).const_add t).sin.fun_neg
    simpa using h
  have h := curvature_tangent (l:=-|x|) (u:=|x|) (x:=x) (t:=0) (κ:=-1)
    ⟨neg_abs_le x,le_abs_self x⟩ ⟨by linarith [abs_nonneg x],abs_nonneg x⟩
    hd hdd (fun r _ => by linarith [Real.cos_le_one (t+r)])
  simp at h
  linarith

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
  nlinarith only [hsMul, hqMul, hsinMul, hcMul, hc, hx3]

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
  have hk0 : k ≠ 0 := by omega
  have key : ∀ s : Finset (Fin 5),
      (∑ i ∈ s, |tree a i|^k) ≤ (∑ i ∈ s, |tree a i|)^k := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [zero_pow hk0]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      calc |tree a j|^k + ∑ i ∈ s, |tree a i|^k
          ≤ |tree a j|^k + (∑ i ∈ s, |tree a i|)^k := by gcongr
        _ ≤ (|tree a j| + ∑ i ∈ s, |tree a i|)^k :=
          pow_add_pow_le (abs_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hk0
  exact key Finset.univ

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
  have hsubn (x y : ℝ) (u v : Point) :
      normSq (sub (scale x u) (scale y v))=x^2*normSq u+y^2*normSq v-2*x*y*dot u v := by
    dsimp [normSq,sub,scale,dot]; ring
  have hneg (u : Point) : normSq (scale (-1) u)=normSq u := by
    dsimp [normSq,scale]; ring
  have hF (b : Errors) : forceTerm d t b o = -(
      (d.edgeAlpha^2+d.edgeOmega^2-2*d.edgeAlpha*d.edgeOmega*Real.sin (t-ownerB b o))/(4*d.mu 0)+
      (d.edgeAlpha^2+d.edgeBeta^2+2*d.edgeAlpha*d.edgeBeta*Real.sin (ownerU b o-ownerB b o))/
        (4*d.mu 1)+
      (d.edgeBeta^2+d.edgeDelta^2-2*d.edgeBeta*d.edgeDelta*Real.sin (ownerV b o-ownerD b o))/
        (4*d.mu 2)+
      (d.edgeDelta^2+d.edgeEpsilon^2-2*d.edgeDelta*d.edgeEpsilon*Real.cos (t+b 4-ownerD b o))/
        (4*d.mu 3)+
      (d.edgeOmega^2+d.edgeEpsilon^2+2*d.edgeOmega*d.edgeEpsilon*Real.sin (ownerH b o-b 4))/
        (4*d.mu 4)) := by
    have n0 : normSq (force d t b o 0)=
        d.edgeAlpha^2+d.edgeOmega^2-2*d.edgeAlpha*d.edgeOmega*Real.sin (t-ownerB b o) := by
      change normSq (sub (scale d.edgeAlpha (ey (ownerB b o))) (scale d.edgeOmega (ex t)))=_
      rw [hsubn,norm_ey,norm_ex,dot_ey_ex]; ring
    have n1 : normSq (force d t b o 1)=
        d.edgeAlpha^2+d.edgeBeta^2+2*d.edgeAlpha*d.edgeBeta*Real.sin (ownerU b o-ownerB b o) := by
      change normSq (scale (-1) (add (scale d.edgeAlpha (ey (ownerB b o)))
        (scale d.edgeBeta (ex (ownerU b o)))))=_
      rw [hneg,norm_linear_combination,norm_ey,norm_ex,dot_ey_ex]; ring
    have n2 : normSq (force d t b o 2)=
        d.edgeBeta^2+d.edgeDelta^2-2*d.edgeBeta*d.edgeDelta*Real.sin (ownerV b o-ownerD b o) := by
      change normSq (sub (scale d.edgeBeta (ex (ownerV b o))) (scale d.edgeDelta (ey (ownerD b o))))=_
      rw [hsubn,norm_ey,norm_ex,dot_ex_ey]; ring
    have n3 : normSq (force d t b o 3)=
        d.edgeDelta^2+d.edgeEpsilon^2-2*d.edgeDelta*d.edgeEpsilon*Real.cos (t+b 4-ownerD b o) := by
      change normSq (sub (scale d.edgeDelta (ey (ownerD b o))) (scale d.edgeEpsilon (ey (t+b 4))))=_
      rw [hsubn,norm_ey,norm_ey,dot_ey_ey]; ring
    have n4 : normSq (force d t b o 4)=
        d.edgeOmega^2+d.edgeEpsilon^2+2*d.edgeOmega*d.edgeEpsilon*Real.sin (ownerH b o-b 4) := by
      change normSq (add (scale d.edgeOmega (ex (t+ownerH b o))) (scale d.edgeEpsilon (ey (t+b 4))))=_
      rw [norm_linear_combination,norm_ey,norm_ex,dot_ex_ey]
      ring_nf
    simp only [forceTerm,Fin.sum_univ_five]
    change -(normSq (force d t b o 0)/(4*d.mu 0)+normSq (force d t b o 1)/(4*d.mu 1)+
      normSq (force d t b o 2)/(4*d.mu 2)+normSq (force d t b o 3)/(4*d.mu 3)+
      normSq (force d t b o 4)/(4*d.mu 4))=_
    rw [n0,n1,n2,n3,n4]
  rw [hF a,hF (fun _=>0)]
  cases hH : o 4 <;>
    simp [ownerB,ownerU,ownerV,ownerD,ownerH,hH,KA,KB,KD,KE,KH] <;>
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
  have hCS : chainSum a≤errorSum a := by
    rw [errorSum_decompose]; linarith only [abs_nonneg (a 4)]
  obtain ⟨hKA,hKB,hKD,hKE,hKH⟩ := force_coefficients_pos hw
  have hA := shifted_sine_remainder (t:=t) (x:=-ownerB a o)
    (by simpa [htc] using hw.c_pos.le) (by simpa [hts] using hw.s_pos.le)
    (by simpa using hb.trans hCS)
  rw [← sub_eq_add_neg] at hA
  have hB := sin_remainder_bounded (hub.trans hCS)
  have hD := sin_remainder_bounded (hvd.trans hCS)
  have hE := shifted_cosine_remainder t (a 4-ownerD a o)
  rw [← add_sub_assoc] at hE
  have hEpow : (a 4-ownerD a o)^2≤(errorSum a)^2 := by
    simpa using pow_le_pow_left₀ (abs_nonneg _) hhd 2
  have hH := sin_remainder_bounded (M:=errorSum a)
    (by rw [errorSum_decompose]; linarith only [hC] : |a 4|≤errorSum a)
  rw [htc,hts] at hA hE
  have hAm := mul_le_mul_of_nonneg_left hA hKA.le
  have hBm := mul_le_mul_of_nonneg_left hB.2 hKB.le
  have hDm := mul_le_mul_of_nonneg_left hD.1 hKD.le
  have hEm := mul_le_mul_of_nonneg_left hE hKE.le
  have hEpm := mul_le_mul_of_nonneg_left hEpow hKE.le
  have hHm := mul_le_mul_of_nonneg_left hH.1 hKH.le
  have hKcube : 0≤KH d*(errorSum a)^3 := mul_nonneg hKH.le (pow_nonneg hS 3)
  have heq := force_term_difference hw t a o
  rw [htc,hts] at heq
  cases hHowner : o 4 <;>
    simp only [forceLinear,hHowner,Bool.false_eq_true,↓reduceIte] at heq ⊢ <;> linarith only [hAm,
      hBm, hDm, hEm, hEpm, hHm, heq, hKcube]

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

private theorem dot_ex_pt (φ x y : ℝ) : dot (ex φ) (x,y)=x*Real.cos φ+y*Real.sin φ := by
  simp only [dot,ex]; ring
private theorem dot_ey_pt (φ x y : ℝ) : dot (ey φ) (x,y)=-x*Real.sin φ+y*Real.cos φ := by
  simp only [dot,ey]; ring
private theorem dot_ex_R (φ θ x y : ℝ) :
    dot (ex φ) (R θ (x,y))=x*Real.cos (φ-θ)+y*Real.sin (φ-θ) := by
  simp only [dot,ex,R,Real.cos_sub,Real.sin_sub]; ring
private theorem dot_ey_R (φ θ x y : ℝ) :
    dot (ey φ) (R θ (x,y))=-x*Real.sin (φ-θ)+y*Real.cos (φ-θ) := by
  simp only [dot,ey,R,Real.cos_sub,Real.sin_sub]; ring

private theorem support_term_edges (d : Coordinates) (t : ℝ) (a : Errors) (o : Owners) :
    supportTerm d t a o=
      d.edgeAlpha*(support t a 0-dot (ey (ownerB a o)) (sub (offset t a 0) (offset t a 1)))+
      d.edgeBeta*(support t a 1+dot (ex (ownerU a o)) (offset t a 1))+
      d.edgeBeta*(support t a 2-dot (ex (ownerV a o)) (offset t a 2))+
      d.edgeDelta*(support t a 3-dot (ey (ownerD a o)) (sub (offset t a 3) (offset t a 2)))+
      d.edgeOmega*(support t a 4+dot (ex t) (offset t a 0))+
      d.edgeOmega*(support t a 5-dot (ex (t+ownerH a o)) (offset t a 4))+
      d.edgeEpsilon*(support t a 6-dot (ey (t+a 4)) (sub (offset t a 4) (offset t a 3))) := by
  simp only [supportTerm,Fin.sum_univ_seven,Fin.sum_univ_five]
  change d.edgeAlpha*support t a 0+d.edgeBeta*support t a 1+d.edgeBeta*support t a 2+
    d.edgeDelta*support t a 3+d.edgeOmega*support t a 4+d.edgeOmega*support t a 5+
    d.edgeEpsilon*support t a 6-
    (dot (sub (scale d.edgeAlpha (ey (ownerB a o))) (scale d.edgeOmega (ex t))) (offset t a 0)+
      dot (scale (-1) (add (scale d.edgeAlpha (ey (ownerB a o)))
        (scale d.edgeBeta (ex (ownerU a o))))) (offset t a 1)+
      dot (sub (scale d.edgeBeta (ex (ownerV a o))) (scale d.edgeDelta (ey (ownerD a o))))
        (offset t a 2)+
      dot (sub (scale d.edgeDelta (ey (ownerD a o))) (scale d.edgeEpsilon (ey (t+a 4))))
        (offset t a 3)+
      dot (add (scale d.edgeOmega (ex (t+ownerH a o))) (scale d.edgeEpsilon (ey (t+a 4))))
        (offset t a 4))=_
  simp only [dot,sub,add,scale]
  ring

private theorem edge_row0 (t : ℝ) (a : Errors) (o : Owners) (hc : 0≤Real.cos (tree a 0)) :
    support t a 0-dot (ey (ownerB a o)) (sub (offset t a 0) (offset t a 1))=
      supportRows a o 0 := by
  have hs : support t a 0=(1+|Real.cos (a 0-0)|+|Real.sin (a 0-0)|)/2 := rfl
  have ht : tree a 0=-a 0 := rfl
  have hoff0 : offset t a 0=(1/2,-1/2) := rfl
  have hoff1 : offset t a 1=R (a 0) (1/2,1/2) := rfl
  have hrow : supportRows a o 0=
      1+Real.cos (tree a 0)-Real.sin (tree a 0)/2+|Real.sin (tree a 0)|/2 := rfl
  rw [ht,Real.cos_neg] at hc
  rw [hs,hrow,ht,hoff0,hoff1,dot_sub_right,dot_ey_pt,dot_ey_R,Real.cos_neg,Real.sin_neg,
    abs_neg,sub_zero,abs_of_nonneg hc]
  cases h : o 0 <;>
    simp only [ownerB,h,Bool.false_eq_true,↓reduceIte,Real.sin_zero,Real.cos_zero,zero_sub,
      sub_self,Real.sin_neg,Real.cos_neg] <;> ring

private theorem edge_row1 (t : ℝ) (a : Errors) (o : Owners) (hc : 0≤Real.cos (tree a 1)) :
    support t a 1+dot (ex (ownerU a o)) (offset t a 1)=supportRows a o 1 := by
  have hs : support t a 1=(1+|Real.cos (a 0-a 1)|+|Real.sin (a 0-a 1)|)/2 := rfl
  have ht : a 0-a 1=-tree a 1 := by simp [tree]
  have ht' : a 1-a 0=tree a 1 := rfl
  have hoff1 : offset t a 1=R (a 0) (1/2,1/2) := rfl
  have hrow : supportRows a o 1=
      if o 1 then 1+Real.cos (tree a 1)/2+|Real.sin (tree a 1)|/2
      else 1/2+Real.cos (tree a 1)+Real.sin (tree a 1)/2+|Real.sin (tree a 1)|/2 := rfl
  rw [hs,ht,hoff1,dot_ex_R,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc,hrow]
  cases h : o 1 <;>
    simp only [ownerU,h,Bool.false_eq_true,↓reduceIte,Real.sin_zero,Real.cos_zero,
      sub_self,ht'] <;> ring

private theorem edge_row2 (t : ℝ) (a : Errors) (o : Owners) (hc : 0≤Real.cos (tree a 2)) :
    support t a 2-dot (ex (ownerV a o)) (offset t a 2)=supportRows a o 2 := by
  have hs : support t a 2=(1+|Real.cos (a 1-a 2)|+|Real.sin (a 1-a 2)|)/2 := rfl
  have ht : a 1-a 2=-tree a 2 := by simp [tree]
  have hoff2 : offset t a 2=R (a 2) (-1/2,1/2) := rfl
  have hrow : supportRows a o 2=
      if o 2 then 1/2+Real.cos (tree a 2)+Real.sin (tree a 2)/2+|Real.sin (tree a 2)|/2
      else 1+Real.cos (tree a 2)/2+|Real.sin (tree a 2)|/2 := rfl
  rw [hs,hoff2,dot_ex_R,hrow]
  cases h : o 2 <;>
    simp only [ownerV,h,Bool.false_eq_true,↓reduceIte,Real.sin_zero,Real.cos_zero,
      sub_self,ht,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc] <;> ring

private theorem edge_row3 (t : ℝ) (a : Errors) (o : Owners) (hc : 0≤Real.cos (tree a 3)) :
    support t a 3-dot (ey (ownerD a o)) (sub (offset t a 3) (offset t a 2))=
      supportRows a o 3 := by
  have hs : support t a 3=(1+|Real.cos (a 2-a 3)|+|Real.sin (a 2-a 3)|)/2 := rfl
  have ht : a 2-a 3=-tree a 3 := by simp [tree]
  have ht' : a 3-a 2=tree a 3 := rfl
  have hoff2 : offset t a 2=R (a 2) (-1/2,1/2) := rfl
  have hoff3 : offset t a 3=R (a 3) (-1/2,-1/2) := rfl
  have hrow : supportRows a o 3=
      1+Real.cos (tree a 3)+Real.sin (tree a 3)/2+|Real.sin (tree a 3)|/2 := rfl
  rw [hs,hoff2,hoff3,dot_sub_right,dot_ey_R,dot_ey_R,hrow]
  cases h : o 3 <;>
    simp only [ownerD,h,Bool.false_eq_true,↓reduceIte,Real.sin_zero,Real.cos_zero,
      sub_self,ht,ht',Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc] <;> ring

private theorem edge_row4 (t : ℝ) (a : Errors) (hc : 0≤Real.cos t) (hs : 0≤Real.sin t) :
    support t a 4+dot (ex t) (offset t a 0)=1/2+Real.cos t := by
  have hsup : support t a 4=(1+|Real.cos (0-t)|+|Real.sin (0-t)|)/2 := rfl
  have hoff0 : offset t a 0=(1/2,-1/2) := rfl
  rw [hsup,hoff0,dot_ex_pt,zero_sub,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc,
    abs_of_nonneg hs]
  ring

private theorem edge_row5 (t : ℝ) (a : Errors) (o : Owners) (hc : 0≤Real.cos (tree a 4)) :
    support t a 5-dot (ex (t+ownerH a o)) (offset t a 4)=supportRows a o 4 := by
  have hs : support t a 5=(1+|Real.cos (t-(t+a 4))|+|Real.sin (t-(t+a 4))|)/2 := rfl
  have ht : t-(t+a 4)=-tree a 4 := by simp [tree]
  have ht4 : tree a 4=a 4 := rfl
  have hoff4 : offset t a 4=R (t+a 4) (-1/2,-1/2) := rfl
  have hrow : supportRows a o 4=
      if o 4 then 1+Real.cos (tree a 4)/2+|Real.sin (tree a 4)|/2
      else 1/2+Real.cos (tree a 4)-Real.sin (tree a 4)/2+|Real.sin (tree a 4)|/2 := rfl
  have h0 : t+a 4-(t+a 4)=0 := by ring
  have h1 : t+0-(t+a 4)=-tree a 4 := by simp [tree]
  rw [hs,ht,hoff4,dot_ex_R,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc,hrow]
  cases h : o 4 <;>
    simp only [ownerH,h,Bool.false_eq_true,↓reduceIte,Real.sin_zero,Real.cos_zero,
      h0,h1,ht4,Real.cos_neg,Real.sin_neg] <;> ring

private theorem edge_row6 (t : ℝ) (a : Errors) (hc : 0≤Real.cos (t+a 4-a 3))
    (hs : 0≤Real.sin (t+a 4-a 3)) :
    support t a 6-dot (ey (t+a 4)) (sub (offset t a 4) (offset t a 3))=
      1+Real.sin (t+a 4-a 3) := by
  have hsup : support t a 6=(1+|Real.cos (a 3-(t+a 4))|+|Real.sin (a 3-(t+a 4))|)/2 := rfl
  have ht : a 3-(t+a 4)=-(t+a 4-a 3) := by ring
  have hoff3 : offset t a 3=R (a 3) (-1/2,-1/2) := rfl
  have hoff4 : offset t a 4=R (t+a 4) (-1/2,-1/2) := rfl
  rw [hsup,ht,hoff3,hoff4,dot_sub_right,dot_ey_R,dot_ey_R,sub_self,Real.sin_zero,Real.cos_zero,
    Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hc,abs_of_nonneg hs]
  ring

theorem support_term_rows {d : Coordinates} {t : ℝ}
    (ht : 1/10≤t ∧ t≤4/25) {a : Errors} (hS : errorSum a≤1/1000) (o : Owners) :
    supportTerm d t a o=(∑ i : Fin 5, edgeWeights d i*supportRows a o i)+
      d.edgeEpsilon*(1+Real.sin (t+a 4-a 3))+d.edgeOmega*(1/2+Real.cos t) := by
  obtain ⟨hc,hs,hca,hce,hse⟩ := terminal_angles ht hS
  rw [support_term_edges,edge_row0 t a o (hca 0),edge_row1 t a o (hca 1),
    edge_row2 t a o (hca 2),edge_row3 t a o (hca 3),edge_row4 t a hc hs,
    edge_row5 t a o (hca 4),edge_row6 t a hce hse,Fin.sum_univ_five]
  change _=d.edgeAlpha*supportRows a o 0+d.edgeBeta*supportRows a o 1+
    d.edgeBeta*supportRows a o 2+d.edgeDelta*supportRows a o 3+
    d.edgeOmega*supportRows a o 4+_+_
  ring

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
    linarith
  have hbprod : B*(Real.sin x-x)≥ -|x|^3/12 := by
    have h := abs_mul B (Real.sin x-x)
    have hm := mul_le_mul hB hsin (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
    rw [← h] at hm
    linarith [(abs_le.mp hm).1]
  have hAc := mul_le_mul_of_nonneg_left hcos.2 hA
  have hAp := mul_le_mul_of_nonneg_right hA1 (sq_nonneg x)
  linarith

private theorem row_lower {W w x A B : ℝ} (hW : 0≤W) (hWw : W≤w) (hA : 0≤A) (hA1 : A≤1)
    (hB : |B|≤1/2) :
    -w*x^2/2-w*|x|^3/6 ≤ W*(A*(Real.cos x-1)+B*(Real.sin x-x)+(|Real.sin x|-|x|)/2) := by
  have h := aligned_row_remainder hA hA1 hB (x:=x)
  have hm := mul_le_mul_of_nonneg_left h hW
  have h2 := mul_le_mul_of_nonneg_right hWw (sq_nonneg x)
  have h3 := mul_le_mul_of_nonneg_right hWw (pow_nonneg (abs_nonneg x) 3)
  linarith

theorem support_term_lower {d : Coordinates} (hw : d.WeightDomain)
    {t : ℝ} (ht : 1/10≤t ∧ t≤4/25) (htc : Real.cos t=d.c) (hts : Real.sin t=d.s)
    {a : Errors} (hS : errorSum a≤1/1000) (o : Owners) {w : ℝ}
    (hw0 : 0≤w) (hweights : ∀ i : Fin 7, d.lam i≤w) :
    supportTerm d t (fun _=>0) o+supportLinear d a o+cusp d a-
      (w/2+d.edgeEpsilon*d.s/2)*(errorSum a)^2-
      (w/6+d.edgeEpsilon/6)*(errorSum a)^3 ≤ supportTerm d t a o := by
  have hrows := support_term_rows (d:=d) ht hS o
  have hzero := support_term_rows (d:=d) ht (a:=fun _=>0)
    (by norm_num [errorSum,tree,Fin.sum_univ_five]) o
  have hα : 0≤d.edgeAlpha := (hw.lam_pos 0).le
  have hβ : 0≤d.edgeBeta := (hw.lam_pos 1).le
  have hδ : 0≤d.edgeDelta := (hw.lam_pos 3).le
  have hω : 0≤d.edgeOmega := (hw.lam_pos 4).le
  have hε : 0≤d.edgeEpsilon := (hw.lam_pos 6).le
  have e0 : edgeWeights d 0=d.edgeAlpha := rfl
  have e1 : edgeWeights d 1=d.edgeBeta := rfl
  have e2 : edgeWeights d 2=d.edgeBeta := rfl
  have e3 : edgeWeights d 3=d.edgeDelta := rfl
  have e4 : edgeWeights d 4=d.edgeOmega := rfl
  have hr0 : -w*(tree a 0)^2/2-w*|tree a 0|^3/6 ≤
      edgeWeights d 0*(supportRows a o 0-supportRows (fun _=>0) o 0)-
      (edgeWeights d 0/2)*|tree a 0|-(-(d.edgeAlpha/2))*tree a 0 := by
    have s0 : supportRows a o 0=
        1+Real.cos (tree a 0)-Real.sin (tree a 0)/2+|Real.sin (tree a 0)|/2 := rfl
    have z0 : supportRows (fun _=>0) o 0=2 := by norm_num [supportRows,tree]
    have h := row_lower (w:=w) (x:=tree a 0) (A:=1) (B:=-1/2) hα (hweights 0)
      (by norm_num) (by norm_num) (by norm_num [abs_of_neg])
    rw [e0,s0,z0]
    linarith only [h]
  have hr1 : -w*(tree a 1)^2/2-w*|tree a 1|^3/6 ≤
      edgeWeights d 1*(supportRows a o 1-supportRows (fun _=>0) o 1)-
      (edgeWeights d 1/2)*|tree a 1|-(if o 1 then 0 else d.edgeBeta/2)*tree a 1 := by
    rw [e1]
    cases h1 : o 1
    · have s1 : supportRows a o 1=1/2+Real.cos (tree a 1)+Real.sin (tree a 1)/2+
          |Real.sin (tree a 1)|/2 := by simp [supportRows,h1]
      have z1 : supportRows (fun _=>0) o 1=3/2 := by norm_num [supportRows,tree,h1]
      have h := row_lower (w:=w) (x:=tree a 1) (A:=1) (B:=1/2) hβ (hweights 1)
        (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
      rw [s1,z1]
      simp only [Bool.false_eq_true,↓reduceIte]
      linarith only [h]
    · have s1 : supportRows a o 1=1+Real.cos (tree a 1)/2+|Real.sin (tree a 1)|/2 := by
        simp [supportRows,h1]
      have z1 : supportRows (fun _=>0) o 1=3/2 := by norm_num [supportRows,tree,h1]
      have h := row_lower (w:=w) (x:=tree a 1) (A:=1/2) (B:=0) hβ (hweights 1)
        (by norm_num) (by norm_num) (by norm_num)
      rw [s1,z1]
      simp only [↓reduceIte]
      linarith only [h]
  have hr2 : -w*(tree a 2)^2/2-w*|tree a 2|^3/6 ≤
      edgeWeights d 2*(supportRows a o 2-supportRows (fun _=>0) o 2)-
      (edgeWeights d 2/2)*|tree a 2|-(if o 2 then d.edgeBeta/2 else 0)*tree a 2 := by
    rw [e2]
    cases h2 : o 2
    · have s2 : supportRows a o 2=1+Real.cos (tree a 2)/2+|Real.sin (tree a 2)|/2 := by
        simp [supportRows,h2]
      have z2 : supportRows (fun _=>0) o 2=3/2 := by norm_num [supportRows,tree,h2]
      have h := row_lower (w:=w) (x:=tree a 2) (A:=1/2) (B:=0) hβ (hweights 1)
        (by norm_num) (by norm_num) (by norm_num)
      rw [s2,z2]
      simp only [Bool.false_eq_true,↓reduceIte]
      linarith only [h]
    · have s2 : supportRows a o 2=1/2+Real.cos (tree a 2)+Real.sin (tree a 2)/2+
          |Real.sin (tree a 2)|/2 := by simp [supportRows,h2]
      have z2 : supportRows (fun _=>0) o 2=3/2 := by norm_num [supportRows,tree,h2]
      have h := row_lower (w:=w) (x:=tree a 2) (A:=1) (B:=1/2) hβ (hweights 1)
        (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
      rw [s2,z2]
      simp only [↓reduceIte]
      linarith only [h]
  have hr3 : -w*(tree a 3)^2/2-w*|tree a 3|^3/6 ≤
      edgeWeights d 3*(supportRows a o 3-supportRows (fun _=>0) o 3)-
      (edgeWeights d 3/2)*|tree a 3|-(d.edgeDelta/2)*tree a 3 := by
    have s3 : supportRows a o 3=
        1+Real.cos (tree a 3)+Real.sin (tree a 3)/2+|Real.sin (tree a 3)|/2 := rfl
    have z3 : supportRows (fun _=>0) o 3=2 := by norm_num [supportRows,tree]
    have h := row_lower (w:=w) (x:=tree a 3) (A:=1) (B:=1/2) hδ (hweights 3)
      (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
    rw [e3,s3,z3]
    linarith only [h]
  have hr4 : -w*(tree a 4)^2/2-w*|tree a 4|^3/6 ≤
      edgeWeights d 4*(supportRows a o 4-supportRows (fun _=>0) o 4)-
      (edgeWeights d 4/2)*|tree a 4|-(if o 4 then 0 else -d.edgeOmega/2)*tree a 4 := by
    rw [e4]
    cases h4 : o 4
    · have s4 : supportRows a o 4=1/2+Real.cos (tree a 4)-Real.sin (tree a 4)/2+
          |Real.sin (tree a 4)|/2 := by simp [supportRows,h4]
      have z4 : supportRows (fun _=>0) o 4=3/2 := by norm_num [supportRows,tree,h4]
      have h := row_lower (w:=w) (x:=tree a 4) (A:=1) (B:=-1/2) hω (hweights 4)
        (by norm_num) (by norm_num) (by norm_num [abs_of_neg])
      rw [s4,z4]
      simp only [Bool.false_eq_true,↓reduceIte]
      linarith only [h]
    · have s4 : supportRows a o 4=1+Real.cos (tree a 4)/2+|Real.sin (tree a 4)|/2 := by
        simp [supportRows,h4]
      have z4 : supportRows (fun _=>0) o 4=3/2 := by norm_num [supportRows,tree,h4]
      have h := row_lower (w:=w) (x:=tree a 4) (A:=1/2) (B:=0) hω (hweights 4)
        (by norm_num) (by norm_num) (by norm_num)
      rw [s4,z4]
      simp only [↓reduceIte]
      linarith only [h]
  have hp₂ := sum_tree_power a 2 (by norm_num)
  have hp₃ := sum_tree_power a 3 (by norm_num)
  simp only [Fin.sum_univ_five,sq_abs] at hp₂ hp₃
  have hp₂w := mul_le_mul_of_nonneg_left hp₂ hw0
  have hp₃w := mul_le_mul_of_nonneg_left hp₃ hw0
  have hdiff := (owner_error_bounds a o).2.2.2.2.2.2.2
  have hmixed := shifted_sine_remainder (t:=t)
    (by simpa [htc] using hw.c_pos.le) (by simpa [hts] using hw.s_pos.le) hdiff
  rw [← add_sub_assoc,htc,hts] at hmixed
  have hmixed' := mul_le_mul_of_nonneg_left hmixed hε
  have hz : t+(fun _ : Fin 5 => (0:ℝ)) 4-(fun _ : Fin 5 => (0:ℝ)) 3=t := by simp
  rw [hz,hts] at hzero
  rw [hrows,hzero]
  simp only [Fin.sum_univ_five,supportLinear,cusp]
  linarith only [hr0, hr1, hr2, hr3, hr4, hp₂w, hp₃w, hmixed']

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
  have hβ0 : 0≤d.edgeBeta := (hw.lam_pos 1).le
  have hω0 : 0≤d.edgeOmega := (hw.lam_pos 4).le
  have hc := two_cosines_difference hu hv
  have hsu := sin_remainder_bounded hu
  have hsv := sin_remainder_bounded hv
  have hsinuv : |(Real.sin (ownerU a o)-Real.sin (ownerV a o))-
      (ownerU a o-ownerV a o)|≤(chainSum a)^3/3 := by
    rw [abs_le]
    constructor <;> linarith only [hsu, hsv]
  have hXc := product_lower_of_abs hX hc
  have hZs := product_lower_of_abs hZ hsinuv
  have hXcβ := mul_le_mul_of_nonneg_left hXc hβ0
  have hZsβ := mul_le_mul_of_nonneg_left hZs hβ0
  have hhcos : |1-Real.cos (a 4)|≤(a 4)^2/2 := by
    rw [abs_of_nonneg (cosine_remainder (a 4)).1]
    exact (cosine_remainder (a 4)).2
  have hhU := product_lower_of_abs hU hhcos
  have hhVm := product_lower_of_abs (by simpa using hV : |-dot (ey t) (p 6)|≤3/2)
    (sin_remainder (a 4))
  have hhUω := mul_le_mul_of_nonneg_left hhU hω0
  have hhVω := mul_le_mul_of_nonneg_left hhVm hω0
  have hβ₂ := mul_le_mul_of_nonneg_right hβ (sq_nonneg (chainSum a))
  have hβ₃ := mul_le_mul_of_nonneg_right hβ (pow_nonneg hC 3)
  have hω₂ := mul_le_mul_of_nonneg_right hω (sq_nonneg (a 4))
  have hω₃ := mul_le_mul_of_nonneg_right hω (pow_nonneg (abs_nonneg (a 4)) 3)
  have hw₂ := mul_nonneg hw0 (sq_nonneg (a 4))
  have hw₃ := mul_nonneg hw0 (pow_nonneg (abs_nonneg (a 4)) 3)
  have hp₂ : (chainSum a)^2+(a 4)^2≤(errorSum a)^2 := by
    rw [errorSum_decompose]
    have h₁ := mul_nonneg hC (abs_nonneg (a 4))
    have h₂ := sq_abs (a 4)
    have h₃ : (chainSum a+|a 4|)^2=(chainSum a)^2+2*(chainSum a*|a 4|)+|a 4|^2 := by ring
    linarith only [h₁, h₂]
  have hp₃ : (chainSum a)^3+|a 4|^3≤(errorSum a)^3 := by
    rw [errorSum_decompose]
    have h₁ := mul_nonneg (sq_nonneg (chainSum a)) (abs_nonneg (a 4))
    have h₂ := mul_nonneg hC (sq_nonneg |a 4|)
    have h₃ : (chainSum a+|a 4|)^3=(chainSum a)^3+3*((chainSum a)^2*|a 4|)+
        3*(chainSum a*|a 4|^2)+|a 4|^3 := by ring
    linarith only [h₁, h₂]
  have hp₂w := mul_le_mul_of_nonneg_left hp₂ hw0
  have hp₃w := mul_le_mul_of_nonneg_left hp₃ hw0
  have hex := slider_exact d t a o p
  cases hh : o 4 <;>
    simp only [sliderLinear,hh,Bool.false_eq_true,↓reduceIte] at hex ⊢
  · linarith only [hex,hXcβ,hZsβ,hβ₂,hβ₃,hp₂w,hp₃w,hw₂,hw₃]
  · linarith only [hex,hXcβ,hZsβ,hβ₂,hβ₃,hp₂w,hp₃w,hhUω,hhVω,hω₂,hω₃,hw₂,hw₃]

theorem coefficient_reserve {d : Coordinates} (hw : d.WeightDomain)
    (hstation : d.positionDerivative=0) (hY : 0<d.cutY ∧ d.cutY<1)
    (hαβ : d.edgeAlpha<d.edgeBeta) (hx : d.x₄-d.x₃<0)
    {ρ Z η : ℝ} (hres : ∀ j : Fin 9, ρ≤d.ownerReserve j)
    (hZ : 557/1000≤Z ∧ Z≤1417/1000)
    (hη : -515/1000≤η ∧ η≤392/1000) (o : Owners) (i : Fin 5) :
    ρ≤edgeWeights d i/2-|coefficient d o Z η i| := by
  have h0 : ρ≤d.cutX := hres 0
  have h1 : ρ≤d.edgeAlpha*(1-d.cutY)-d.cutX := hres 1
  have h2 : ρ≤d.cutK := hres 2
  have h3 : ρ≤d.edgeBeta-d.cutK := hres 3
  have h4 : ρ≤d.edgeBeta*(-917/1000-d.cutJ) := hres 4
  have h5 : ρ≤d.edgeBeta*(1057/1000+d.cutJ) := hres 5
  have h6 : ρ≤d.cutL := hres 6
  have h7 : ρ≤d.cutN-(392/1000)*d.edgeOmega := hres 7
  have h8 : ρ≤(485/1000)*d.edgeOmega-d.cutN := hres 8
  obtain ⟨hK,hL,hδx⟩ := cut_identities hw hstation
  have hα : 0<d.edgeAlpha := hw.lam_pos 0
  have hβ : 0<d.edgeBeta := hw.lam_pos 1
  have hδ : 0<d.edgeDelta := hw.lam_pos 3
  have hω : 0<d.edgeOmega := hw.lam_pos 4
  have hαY := mul_pos hα hY.1
  have hδdiff := mul_neg_of_pos_of_neg hδ hx
  have hZl := mul_le_mul_of_nonneg_left hZ.1 hβ.le
  have hZu := mul_le_mul_of_nonneg_left hZ.2 hβ.le
  have hηl := mul_le_mul_of_nonneg_left hη.1 hω.le
  have hηu := mul_le_mul_of_nonneg_left hη.2 hω.le
  have hXdef : d.cutX=d.edgeBeta*(d.y+2+d.cutJ) := rfl
  have reserve_iff (r w c : ℝ) : r≤w/2-|c| ↔ -w/2+r≤c ∧ c≤w/2-r := by
    constructor
    · intro h
      have hc : |c|≤w/2-r := by linarith only [h]
      have hh := abs_le.mp hc
      exact ⟨by linarith only [hh],hh.2⟩
    · intro h
      have hc : |c|≤w/2-r := abs_le.mpr ⟨by linarith only [h],h.2⟩
      linarith only [hc]
  fin_cases i
  · change ρ≤d.edgeAlpha/2-
      |-d.edgeAlpha/2+d.cutX+(if o 0 then d.edgeAlpha*d.cutY else 0)|
    split_ifs <;> rw [reserve_iff] <;> constructor <;> linarith only [h0, hαY, h1]
  · change ρ≤d.edgeBeta/2-
      |if o 1 then -d.edgeBeta*(Z+d.cutJ) else -d.edgeBeta*(d.y+3/2+d.cutJ)|
    split_ifs <;> rw [reserve_iff] <;> constructor <;> linarith only [h4, hZu, h5, hZl, hαβ, h1,
      hαY, hXdef, h0]
  · change ρ≤d.edgeBeta/2-|if o 2 then d.edgeBeta/2-d.cutK else -d.edgeBeta*(Z+d.cutJ)|
    split_ifs <;> rw [reserve_iff] <;> constructor <;> linarith only [h3, h2, h4, hZu, h5, hZl]
  · change ρ≤d.edgeDelta/2-
      |d.edgeDelta/2-d.edgeEpsilon*d.c-(if o 3 then d.edgeDelta*(d.x₄-d.x₃) else 0)|
    split_ifs <;> rw [reserve_iff] <;> constructor <;> linarith only [h6, hL, hδdiff, h2, hK]
  · change ρ≤d.edgeOmega/2-|-d.edgeOmega/2+d.cutN-(if o 4 then d.edgeOmega*η else 0)|
    split_ifs <;> rw [reserve_iff] <;> constructor <;> linarith only [h7, hηu, h8, hηl, hω]

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
    have hab : -|coefficient d o Z η i| * |tree a i|≤coefficient d o Z η i*tree a i := by
      rw [neg_mul,← abs_mul]
      exact neg_abs_le _
    linarith
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin 5))) (fun i _=>hterm i)
  simpa [errorSum,cusp,Finset.mul_sum,Finset.sum_add_distrib] using hs

def quadraticCoefficient (d : Coordinates) (w : ℝ) : ℝ :=
  (KA d*d.s+KE d)/2+w/2+d.edgeEpsilon*d.s/2+3*w/4
def cubicCoefficient (d : Coordinates) (w : ℝ) : ℝ :=
  (KA d+KB d+KD d+KH d)/6+w/6+d.edgeEpsilon/6+w/2

end SquaresInCircles.Eight.ExactFamily.Perturbation
