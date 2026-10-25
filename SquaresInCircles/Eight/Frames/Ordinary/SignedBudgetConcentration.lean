module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import SquaresInCircles.Eight.Frames.Ordinary.NegativeSlope
public import SquaresInCircles.Eight.Owners.GA.Negative.ATD2Concentration
public import SquaresInCircles.Eight.Owners.Negative.TerminalSharp

/-!
# Eight squares: the ordinary blocks under two signed budgets

The ordinary blocks have positive parts `P k` with `∑ P ≤ frameCap - θ` and negative parts `N k`
with `∑ N ≤ frameCap - s`, and `∑ N - ∑ P = θ - s`. The sum of the block functions
`mixedBlock R (p k) (q k) (P k) (N k)` is then at least, for some blocks `i` and `j`, the smaller of
two values (`concentrate`): `pure`, where the only mass is the surplus `|θ - s|` on one block, and
`saturated`, where both budgets are used up. The two simplex steps of `both_signs_concentrate`
keep the totals, and the concentrated sum is concave between these two ends
(`reverse_separated_concave` and the concavity of the other lines), so it is least at an end. The
sign of the surplus is not assumed.
-/

section
/-!
## Negative-angle growth for the full removed-primary interval

The fixed ratio 2/3 has the two exact reserves
.6744 and .25823. They compensate the largest possible E secant on
the entire interval 0≤s≤h, using a single concave affine-cosine product.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.OrdinaryLongSecantGrowth
open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope VaryingBFunctions
open PositiveStressCoefficients NegativeEOneAngle

theorem cap_trig :
    (644217687/1000000000 : ℝ)≤Real.sin frameCap ∧
      Real.sin frameCap≤644217688/1000000000 ∧
      (764842187/1000000000 : ℝ)≤Real.cos frameCap := by
  have hsL := HighOrderTaylor.S11_le_sin (show 0≤frameCap by norm_num [frameCap])
  have hsU := Arithmetic.sin_le_sin9 (show 0≤frameCap by norm_num [frameCap])
  have hcL := Arithmetic.cos10_le_cos (show 0≤frameCap by norm_num [frameCap])
  norm_num [frameCap,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8] at hsL hsU hcL ⊢
  exact ⟨by linarith,by linarith,by linarith⟩

theorem endpoint_slope :
    (843/1250 : ℝ)<Vd (Real.sqrt qCap) (2/3) 1 frameCap := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos (2/3) (sin_mem hh)
  have hN2 := root_sq (2/3) (sin_mem hh)
  have hNupper : root (2/3) (Real.sin frameCap)≤76517157/100000000 := by
    nlinarith [cap_trig.1]
  have hRlower : (19787875/10000000 : ℝ)≤Real.sqrt qCap :=
    (Real.le_sqrt' (by norm_num)).2 (by norm_num [qCap])
  have hleft : ((843/1250 : ℝ)+Real.sin frameCap)*root (2/3) (Real.sin frameCap)≤
      (843/1250+644217688/1000000000)*(76517157/100000000) :=
    mul_le_mul (by linarith [cap_trig.2.1]) hNupper hN.le (by norm_num)
  have hright : (19787875/10000000 : ℝ)*(2/3)*(764842187/1000000000)≤
      Real.sqrt qCap*(2/3)*Real.cos frameCap :=
    mul_le_mul (mul_le_mul_of_nonneg_right hRlower (by norm_num)) cap_trig.2.2
      (by norm_num) (by positivity)
  have hreserve : ((843/1250 : ℝ)+644217688/1000000000)*(76517157/100000000)<
      (19787875/10000000)*(2/3)*(764842187/1000000000) := by norm_num
  have hcross := hleft.trans_lt (hreserve.trans_le hright)
  have hdiv := (lt_div_iff₀ hN).2 hcross
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)]
  simp only [div_one,one_mul]
  linarith

theorem fixed_second_upper {t : ℝ} (ht : t∈Icc 0 frameCap) :
    curvature (Real.sqrt qCap) (2/3) 1 (-t)-Real.cos t≤ -(25823/100000) := by
  obtain ⟨N,hNdef⟩ : ∃ N : ℝ, N=pairNorm (2/3) 1 0 := ⟨_,rfl⟩
  have hN : 0<N := by
    rw [hNdef]
    exact pairNorm_pos (by norm_num) (by norm_num) (by norm_num [frameCap])
  have hN2 : N^2=13/9 := by
    have hh := pairNorm_sq (p := (2/3:ℝ)) (q := 1) (t := 0)
      (by norm_num) (by norm_num) (by norm_num [frameCap])
    rw [hNdef,hh]
    simp only [pairEnergy,pairProduct,Real.sin_zero]
    norm_num
  have hN6 : (N^3)^2=(13/9 : ℝ)^3 := by
    calc (N^3)^2=(N^2)^3 := by ring
         _=_ := by rw [hN2]
  have hR := Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hcross : Real.sqrt qCap*(4/9)<(50661/100000)*N^3 := by
    have hreserve : qCap*(4/9 : ℝ)^2<(50661/100000)^2*(13/9)^3 := by norm_num [qCap]
    have hright0 : 0<(50661/100000 : ℝ)*N^3 := by positivity
    have hright2 : ((50661/100000 : ℝ)*N^3)^2=(50661/100000)^2*(13/9)^3 := by
      rw [mul_pow,hN6]
    have hleft2 : (Real.sqrt qCap*(4/9))^2=qCap*(4/9 : ℝ)^2 := by rw [mul_pow,hR]
    apply lt_of_pow_lt_pow_left₀ 2 hright0.le
    rw [hleft2,hright2]
    exact hreserve
  have hzero : curvatureZero (Real.sqrt qCap) (2/3) 1<50661/100000 := by
    have he : curvatureZero (Real.sqrt qCap) (2/3) 1=Real.sqrt qCap*(4/9)/N^3 := by
      rw [curvatureZero,pairProduct,← hNdef]
      norm_num
    rw [he]
    exact (div_lt_iff₀ (pow_pos hN 3)).2 hcross
  have hcurv := curvature_negative_upper (Real.sqrt_nonneg qCap)
    (by norm_num : (0:ℝ)<2/3) (by norm_num : (0:ℝ)<1)
    (show -t∈Icc (-frameCap) 0 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  have hcosmono := Real.cos_le_cos_of_nonneg_of_le_pi ht.1
    (by norm_num [frameCap]; linarith [Real.pi_gt_three]) ht.2
  have hcos : (19121/25000 : ℝ)<Real.cos t := by linarith [cap_trig.2.2]
  linarith

theorem fixed_slope_lower {t : ℝ} (ht : t∈Icc 0 frameCap) :
    843/1250+(25823/100000)*(frameCap-t)<Vd (Real.sqrt qCap) (2/3) 1 t := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      HasDerivAt (fun x => -Vd (Real.sqrt qCap) (2/3) 1 x)
        (-(curvature (Real.sqrt qCap) (2/3) 1 (-x)-Real.cos x)) x := by
    have h := (Vd_hasDerivAt (R := Real.sqrt qCap) (by norm_num : (0:ℝ)<2/3)
      (by norm_num : (0:ℝ)<1) hx).neg
    rw [one_mul] at h
    exact h
  have h := derivative_reserve
    (f := fun x => -Vd (Real.sqrt qCap) (2/3) 1 x)
    (df := fun x => -(curvature (Real.sqrt qCap) (2/3) 1 (-x)-Real.cos x))
    (k := (25823/100000 : ℝ))
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Ioo_subset_Icc_self hx))
    (fun x hx => by linarith [fixed_second_upper (Ioo_subset_Icc_self hx)]) ht hh ht.2
  linarith [endpoint_slope]

theorem shortened_slope {p q s t : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hs : 0≤ s) (ht : t∈Icc 0 (frameCap-s)) :
    (843/1250+(25823/100000)*s)*q≤Vd (Real.sqrt qCap) p q t := by
  have hq := hp.trans_le hpq
  have ht2 : t≤7/10-s := ht.2
  have ht' : t∈Icc 0 frameCap := ⟨ht.1,by show t≤7/10; linarith⟩
  have hfrac := normalized_fraction_mono (by norm_num : (0:ℝ)≤2/3)
    ((le_div_iff₀ hq).2 hratio) ((div_le_one hq).2 hpq) (sin_mem ht')
  have hcoef : 0≤Real.sqrt qCap*Real.cos t := mul_nonneg (Real.sqrt_nonneg _)
    (by linarith [(transport_trig ht').1])
  have hmul := mul_le_mul_of_nonneg_left hfrac hcoef
  have hbase := fixed_slope_lower ht'
  rw [Vd_normalized (by norm_num : (0:ℝ)<1)] at hbase
  simp only [div_one,one_mul] at hbase
  have hbase' : 843/1250+(25823/100000)*(7/10-t) < -Real.sin t+
      Real.sqrt qCap*(2/3)*Real.cos t/root (2/3) (Real.sin t) := hbase
  have hnormal : 843/1250+(25823/100000)*s≤ -Real.sin t+
      Real.sqrt qCap*(p/q)*Real.cos t/root (p/q) (Real.sin t) := by
    have e1 : Real.sqrt qCap*(2/3)*Real.cos t/root (2/3) (Real.sin t)=
        Real.sqrt qCap*Real.cos t*(2/3/root (2/3) (Real.sin t)) := by ring
    have e2 : Real.sqrt qCap*(p/q)*Real.cos t/root (p/q) (Real.sin t)=
        Real.sqrt qCap*Real.cos t*(p/q/root (p/q) (Real.sin t)) := by ring
    rw [e1] at hbase'
    rw [e2]
    linarith
  rw [Vd_normalized hq]
  nlinarith only [mul_le_mul_of_nonneg_left hnormal hq.le]

theorem affine_cos_concave {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun t => (a+b*t)*Real.cos t) := by
  apply concave_of_deriv2
    (f' := fun t => b*Real.cos t-(a+b*t)*Real.sin t)
    (f'' := fun t => -2*b*Real.sin t-(a+b*t)*Real.cos t)
  · intro t _
    have h : HasDerivAt (fun x => (a+b*x)*Real.cos x)
        ((b*1)*Real.cos t+(a+b*t)*(-Real.sin t)) t :=
      (((hasDerivAt_id' t).const_mul b).const_add a).fun_mul (Real.hasDerivAt_cos t)
    convert h using 1
    ring
  · intro t _
    have h : HasDerivAt (fun x => b*Real.cos x-(a+b*x)*Real.sin x)
        (b*(-Real.sin t)-((b*1)*Real.sin t+(a+b*t)*Real.cos t)) t :=
      ((Real.hasDerivAt_cos t).const_mul b).fun_sub
        ((((hasDerivAt_id' t).const_mul b).const_add a).fun_mul (Real.hasDerivAt_sin t))
    convert h using 1
    ring
  · intro t ht
    have hs := (transport_trig ht).2.2.1
    have hc : 0≤Real.cos t := by linarith [(transport_trig ht).1]
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hb) hs
    have h2 := mul_nonneg (add_nonneg ha (mul_nonneg hb ht.1)) hc
    linarith

theorem secant_chord {s : ℝ} (hs : s∈Icc 0 frameCap) :
    1/Real.cos s≤1+(11/25)*s := by
  have hc := affine_cos_concave (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤11/25)
  have hmin := hc.min_le_of_mem_Icc (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hs
  have hend : 1≤(1+(11/25)*frameCap)*Real.cos frameCap := by
    have hcos := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
    norm_num [frameCap] at hcos ⊢
    linarith
  have hval : 1≤(1+(11/25)*s)*Real.cos s := by
    simpa [min_eq_left hend] using hmin
  exact (div_le_iff₀ (by linarith [(transport_trig hs).1] : 0<Real.cos s)).2 hval

theorem secant_compensation {s : ℝ} (hs : s∈Icc 0 frameCap) :
    gamma s≤k*(843/1250+(25823/100000)*s) := by
  have hc := affine_cos_concave
    (a := k*(843/1250)) (b := k*(25823/100000)) (by norm_num [k]) (by norm_num [k])
  have hmin := hc.min_le_of_mem_Icc (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hs
  have hzero : (109/200 : ℝ)*(2069/2000)≤k*(843/1250) := by norm_num [k]
  have hend : (109/200 : ℝ)*(2069/2000)≤
      (k*(843/1250)+k*(25823/100000)*frameCap)*Real.cos frameCap := by
    have hh := cap_trig.2.2
    norm_num [frameCap,k] at hh ⊢
    linarith
  have hval : (109/200 : ℝ)*(2069/2000)≤
      (k*(843/1250)+k*(25823/100000)*s)*Real.cos s := by
    have hz : (109/200 : ℝ)*(2069/2000)≤
        (k*(843/1250)+k*(25823/100000)*0)*Real.cos 0 := by simpa using hzero
    exact (le_min hz hend).trans hmin
  dsimp [gamma]
  apply (div_le_iff₀ (by linarith [(transport_trig hs).1] : 0<Real.cos s)).2
  nlinarith

theorem growth {p q s t u : ℝ} (hp : 0<p) (hpq : p≤q)
    (hratio : (2/3)*q≤p) (hq : k≤q) (hs : s∈Icc 0 frameCap)
    (ht : t∈Icc 0 (frameCap-s)) (hu : u∈Icc 0 (frameCap-s)) (htu : t≤u) :
    gamma s*(u-t)≤V (Real.sqrt qCap) p q u-V (Real.sqrt qCap) p q t := by
  have hq0 := hp.trans_le hpq
  have hmem {x : ℝ} (hx : x∈Icc 0 (frameCap-s)) : x∈Icc 0 frameCap :=
    ⟨hx.1,by linarith [hx.2,hs.1]⟩
  apply derivative_reserve
    (fun x hx => (V_hasDerivAt hp hq0 (hmem hx)).continuousAt.continuousWithinAt)
    (fun x hx => V_hasDerivAt hp hq0 (hmem (Ioo_subset_Icc_self hx)))
    (fun x hx => ?_) ht hu htu
  have hbase := shortened_slope hp hpq hratio hs.1 (Ioo_subset_Icc_self hx)
  have hmul := mul_le_mul_of_nonneg_left hq
    (show 0≤843/1250+(25823/100000)*s by linarith [hs.1])
  have hcomp := secant_compensation hs
  nlinarith

end SquaresInCircles.Eight.OrdinaryLongSecantGrowth
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.OrdinarySignedBudgetConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration

variable {ι : Type*} [DecidableEq ι]

def pure (R : ℝ) (p q : ι→ℝ) (i j : ι) (s θ : ℝ) : ℝ :=
  if s≤θ then V R (p j) (q j) (θ-s) else U R (p i) (q i) (s-θ)
def saturated (R : ℝ) (p q : ι→ℝ) (i j : ι) (s θ : ℝ) : ℝ :=
  if i=j then mixedBlock R (p i) (q i) (frameCap-θ) (frameCap-s)
  else U R (p i) (q i) (frameCap-θ)+V R (p j) (q j) (frameCap-s)

theorem reverse_separated_concave {R p q p' q' t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p')
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t)) (fun N => U R p q (t+N)+V R p' q' N) := by
  have hU := concave_affine_argument (U_concave hR hQ hp hpq hqp)
    (a:=1) (b:=t) (l:=0) (u:=frameCap-t)
    (fun N hN => ⟨by linarith [hN.1,ht.1],by linarith [hN.2]⟩)
  have hV := (V_concave hR hQ hp' hpq' hqp').subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  refine (hU.add hV).congr fun N _ => ?_
  simp only [Pi.add_apply,one_mul,add_comm t]


theorem concentrate [Fintype ι] [Nonempty ι]
    (R : ℝ) (p q P N : ι→ℝ) {s θ : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀i,0<p i) (hpq : ∀i,p i≤q i) (hqp : ∀i,q i≤2*p i)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hs : s∈Icc 0 frameCap) (hθ : θ∈Icc 0 frameCap)
    (hPb : (∑i,P i)≤frameCap-θ) (hNb : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)-(∑i,P i)=θ-s) :
    ∃i j,min (pure R p q i j s θ) (saturated R p q i j s θ)≤
      ∑k,mixedBlock R (p k) (q k) (P k) (N k) := by
  have hPt : (∑i,P i)≤frameCap := by linarith [hθ.1]
  have hNt : (∑i,N i)≤frameCap := by linarith [hs.1]
  obtain ⟨i,j,hij⟩ := both_signs_concentrate R p q P N hR hQ hp hpq hqp hP hN hPt hNt
  refine ⟨i,j,?_⟩
  by_cases horder : s≤θ
  · have ht : θ-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hθ.2,hs.1]⟩
    have htotal : (∑i,P i)∈Icc 0 (frameCap-θ) :=
      ⟨Finset.sum_nonneg (fun i _ => hP i),hPb⟩
    have hspan : 0≤frameCap-θ := by linarith [hθ.2]
    have heq : (∑i,N i)=(θ-s)+(∑i,P i) := by linarith
    have hlast : (θ-s)+(frameCap-θ)=frameCap-s := by ring
    by_cases hsame : i=j
    · subst j
      simp only [pure,horder,↓reduceIte,saturated] at ⊢
      simp only [↓reduceIte,heq] at hij
      have hc := (sameBlockLine_concave (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,mixedBlock_zero_left,hlast] at hh
      exact hh.trans hij
    · simp only [pure,horder,↓reduceIte,saturated,hsame] at ⊢
      simp only [hsame,↓reduceIte,heq] at hij
      have hc := (separatedLine_concave hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hs.1])) (convex_Icc 0 (frameCap-θ))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [U_zero,zero_add,add_zero,hlast] at hh
      exact hh.trans hij
  · have ht : s-θ∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hθ.1]⟩
    have htotal : (∑i,N i)∈Icc 0 (frameCap-s) :=
      ⟨Finset.sum_nonneg (fun i _ => hN i),hNb⟩
    have hspan : 0≤frameCap-s := by linarith [hs.2]
    have heq : (∑i,P i)=(s-θ)+(∑i,N i) := by linarith
    have hlast : (s-θ)+(frameCap-s)=frameCap-θ := by ring
    by_cases hsame : i=j
    · subst j
      simp only [pure,horder,↓reduceIte,saturated] at ⊢
      simp only [↓reduceIte,heq] at hij
      have hc := (GlobalGA.NegativeAPositiveTD.Concentration.reverse_ordinary_line_concave
        (R:=R) (hp i).le ((hp i).trans_le (hpq i)).le ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,mixedBlock_zero_right,hlast] at hh
      exact hh.trans hij
    · simp only [pure,horder,↓reduceIte,saturated,hsame] at ⊢
      simp only [hsame,↓reduceIte,heq] at hij
      have hc := (reverse_separated_concave hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) ht).subset
        (Icc_subset_Icc le_rfl (by linarith [hθ.1])) (convex_Icc 0 (frameCap-s))
      have hh := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [V_zero,add_zero,hlast] at hh
      exact hh.trans hij

end SquaresInCircles.Eight.OrdinarySignedBudgetConcentration
end
end
end
