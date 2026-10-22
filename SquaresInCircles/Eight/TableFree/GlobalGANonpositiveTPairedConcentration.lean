module

public import SquaresInCircles.Eight.TableFree.GlobalGANonpositiveTPositiveSlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANonnegativeTotalsNegativeTDConcentration

/-!
# Both ordinary sign totals in the paired nonpositive-T stress

Uncompiled equations (24)--(26). The positive-excess comparison retains
the full same-block charge, and the separated charge gains at least .01
per unit of common variation. Concavity in the original paired magnitude
then leaves precisely 0, delta, and M; all eight new endpoint families and
the three old endpoints are supplied internally.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Concentration
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open OrdinaryNegativeSlope

abbrev positive := NonnegativeTotals.NegativeTD.Concentration.positive
abbrev block := NonnegativeTotals.NegativeTD.Concentration.block
abbrev line := NonnegativeTotals.NegativeTD.Concentration.line

theorem same_block_identity (p q P N : ℝ) :
    mixedBlock R p q P N-U R p q (P-N)=
      2*Real.sin (N/2)*(p*(Real.cos (P-N/2)-Real.sin (P-N/2))-q*Real.sin (N/2)) := by
  have hP : P=(P-N/2)+N/2 := by ring
  have hT : P-N=(P-N/2)-N/2 := by ring
  have hN : N=2*(N/2) := by ring
  have hC : (Real.cos (N/2))^2=1-(Real.sin (N/2))^2 := by
    nlinarith [Real.sin_sq_add_cos_sq (N/2)]
  have hid : p*(phi P-phi (P-N))+q*(Real.cos N-1)=
      2*Real.sin (N/2)*(p*(Real.cos (P-N/2)-Real.sin (P-N/2))-q*Real.sin (N/2)) := by
    have hcP : Real.cos P=Real.cos (P-N/2)*Real.cos (N/2)-Real.sin (P-N/2)*Real.sin (N/2) := by
      conv_lhs => rw [hP,Real.cos_add]
    have hsP : Real.sin P=Real.sin (P-N/2)*Real.cos (N/2)+Real.cos (P-N/2)*Real.sin (N/2) := by
      conv_lhs => rw [hP,Real.sin_add]
    have hcT : Real.cos (P-N)=Real.cos (P-N/2)*Real.cos (N/2)+Real.sin (P-N/2)*Real.sin (N/2) := by
      conv_lhs => rw [hT,Real.cos_sub]
    have hsT : Real.sin (P-N)=Real.sin (P-N/2)*Real.cos (N/2)-Real.cos (P-N/2)*Real.sin (N/2) := by
      conv_lhs => rw [hT,Real.sin_sub]
    have hcN : Real.cos N=2*(Real.cos (N/2))^2-1 := by
      conv_lhs => rw [hN,Real.cos_two_mul]
    simp only [phi,hcP,hsP,hcT,hsT,hcN]
    rw [hC]
    ring
  calc
    _=p*(phi P-phi (P-N))+q*(Real.cos N-1) := by dsimp [mixedBlock,U]; ring
    _=_ := hid

theorem same_block_positive {E t s P N : ℝ} (hE : E∈Icc 0 M) (i : Fin 4)
    (ht : L≤t) (hs : s∈Icc t M) (hP : 0≤P) (hN : 0≤N)
    (hPt : P≤frameCap-t) (hNt : N≤frameCap-s) (hbal : P-N=s-t) :
    U R (p E i) (q E i) (s-t)≤mixedBlock R (p E i) (q E i) P N := by
  have hEf : E∈Icc 0 frameCap := ⟨hE.1,by norm_num [M,frameCap] at *; linarith [hE.2]⟩
  have hc := coefficients hEf i
  have hq : 0<q E i := hc.1.trans_le hc.2.1
  have hx : P-N/2∈Icc 0 (233/600:ℝ) := by
    dsimp [L,M,frameCap] at *
    exact ⟨by linarith,by linarith⟩
  have hn : N/2∈Icc 0 (4/15:ℝ) := by
    dsimp [L,M,frameCap] at *
    exact ⟨by linarith,by linarith⟩
  have hsinX := Real.sin_le hx.1
  have hcosX := Real.one_sub_sq_div_two_le_cos (x:=P-N/2)
  have hx2 := pow_le_pow_left₀ hx.1 hx.2 2
  have hlow : 1-(233/600:ℝ)-(233/600)^2/2≤Real.cos (P-N/2)-Real.sin (P-N/2) := by
    nlinarith only [hsinX,hcosX,hx.2,hx2]
  have hlow0 : 0≤Real.cos (P-N/2)-Real.sin (P-N/2) := by linarith
  have hpq : (2/3)*q E i≤p E i := by linarith [hc.2.2.1]
  have ha := mul_le_mul_of_nonneg_right hpq hlow0
  have hb := mul_le_mul_of_nonneg_left hlow (show 0≤(2/3)*q E i by positivity)
  have hsinN : Real.sin (N/2)≤4/15 := (Real.sin_le hn.1).trans hn.2
  have hsN := mul_le_mul_of_nonneg_left hsinN hq.le
  have hbrace : 0≤p E i*(Real.cos (P-N/2)-Real.sin (P-N/2))-q E i*Real.sin (N/2) := by
    have hreserve : 0≤(98111/1080000)*q E i := by positivity
    nlinarith only [ha,hb,hsN,hreserve]
  have hs0 : 0≤Real.sin (N/2) := (transport_trig
    (show N/2∈Icc 0 frameCap from ⟨hn.1,by norm_num [frameCap]; linarith [hn.2]⟩)).2.2.1
  have hh := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hs0) hbrace
  rw [←same_block_identity,hbal] at hh
  linarith

theorem positive_growth {E x y : ℝ} (hE : E∈Icc 0 M) (i : Fin 4)
    (hx : x∈Icc 0 (8/15:ℝ)) (hy : y∈Icc 0 (8/15:ℝ)) (hxy : x≤y) :
    -(81/100)*(y-x)≤positive E i y-positive E i x := by
  by_cases hi : i=3
  · subst i
    simp only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      PositiveTD.Hybrid.positive,if_pos rfl]
    have ha : aD<81/100 := by
      dsimp [aD,NonnegativeTotals.NegativeTD.aD]
      linarith [diagonal_bounds.2]
    have hh := mul_nonneg (sub_nonneg.mpr ha.le) (sub_nonneg.mpr hxy)
    linarith
  · simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      PositiveTD.Hybrid.positive,if_neg hi] using Paired.positive_growth hE i hx hy hxy

theorem line_positive_excess {E t s P : ℝ} (hE : E∈Icc 0 M) (i j : Fin 4)
    (ht : L≤t) (hs : s∈Icc t M) (hP : P∈Icc (s-t) (frameCap-t)) :
    positive E i (s-t)≤line E i j P (t-s+P) := by
  have hE' : E∈Icc 0 frameCap := ⟨hE.1,by norm_num [M,frameCap] at *; linarith [hE.2]⟩
  have hx : s-t∈Icc 0 (8/15:ℝ) := by
    dsimp [L,M] at *
    exact ⟨by linarith,by linarith⟩
  have hPf : P∈Icc 0 (8/15:ℝ) := by
    dsimp [L,frameCap] at *
    exact ⟨by linarith [hP.1],by linarith [hP.2]⟩
  have hN : t-s+P∈Icc 0 frameCap :=
    ⟨by linarith [hP.1],by dsimp [L,M,frameCap] at *; linarith [hP.2]⟩
  have hseparated : positive E i (s-t)≤positive E i P+V R (p E j) (q E j) (t-s+P) := by
    have hu := positive_growth hE i hx hPf hP.1
    have hv := Paired.negative_growth hE' j
      (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hN hN.1
    simp only [V_zero,sub_zero] at hv
    linarith [hN.1]
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · subst i
      simpa only [line,NonnegativeTotals.NegativeTD.Concentration.line,if_pos rfl,
        block,NonnegativeTotals.NegativeTD.Concentration.block,PositiveTD.Hybrid.block,
        positive,NonnegativeTotals.NegativeTD.Concentration.positive,PositiveTD.Hybrid.positive] using hseparated
    · have hh := same_block_positive hE i ht hs hPf.1 hN.1 hP.2
        (show t-s+P≤frameCap-s by linarith [hP.2]) (show P-(t-s+P)=s-t by ring)
      simpa only [line,NonnegativeTotals.NegativeTD.Concentration.line,if_pos rfl,
        block,NonnegativeTotals.NegativeTD.Concentration.block,PositiveTD.Hybrid.block,
        positive,NonnegativeTotals.NegativeTD.Concentration.positive,PositiveTD.Hybrid.positive,if_neg hi] using hh
  · simpa only [line,NonnegativeTotals.NegativeTD.Concentration.line,if_neg hij] using hseparated

theorem gain_concave : ConcaveOn ℝ (Icc 0 M) gain := by
  apply concave_of_deriv2
    (f':=fun s => c*kappa*(Real.cos s-Real.sin s))
    (f'':=fun s => -c*kappa*phi s)
  · intro s _
    convert (((Real.hasDerivAt_cos s).add (Real.hasDerivAt_sin s)).sub_const 1).const_mul (c*kappa)
      using 1 <;> dsimp [gain,phi] <;> ring
  · intro s _
    convert ((Real.hasDerivAt_cos s).sub (Real.hasDerivAt_sin s)).const_mul (c*kappa)
      using 1 <;> dsimp [phi] <;> ring
  · intro s hs
    have ht := transport_trig (show s∈Icc 0 frameCap from
      ⟨hs.1,by norm_num [M,frameCap] at *; linarith [hs.2]⟩)
    have hp : 0≤phi s := by dsimp [phi]; linarith [ht.1,ht.2.2.1]
    have hh := mul_nonneg (show 0≤c*kappa by norm_num [c,NonnegativeTotals.NegativeTD.c,kappa]) hp
    linarith

theorem negative_endpoint (i : Fin 4) {t E : ℝ}
    (ht : t∈Icc M frameCap) (hE : E∈Icc 0 t) :
    0<base E+primaryCost t E+gain M+V R (p E i) (q E i) (t-M) := by
  fin_cases i
  · exact Paired.negative_positive 0 ht hE
  · exact Paired.negative_positive 1 ht hE
  · exact Paired.negative_positive 2 ht hE
  · exact Paired.negative_positive 0 ht hE

theorem positive_endpoint (i : Fin 4) {t E : ℝ}
    (ht : t∈Icc L M) (hE : E∈Icc 0 t) :
    0<base E+primaryCost t E+gain M+positive E i (M-t) := by
  fin_cases i
  · simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      PositiveTD.Hybrid.positive,Fin.reduceFinMk,ite_false] using Paired.positive_positive 0 ht hE
  · simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      PositiveTD.Hybrid.positive,Fin.reduceFinMk,ite_false] using Paired.positive_positive 1 ht hE
  · simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      PositiveTD.Hybrid.positive,Fin.reduceFinMk,ite_false] using Paired.positive_positive 2 ht hE
  · simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      PositiveTD.Hybrid.positive,if_pos rfl,DScalar,sub_eq_add_neg,neg_mul] using Paired.D_positive ht hE

theorem lower_negative_positive (j : Fin 4) {t E s : ℝ}
    (ht : t∈Icc L frameCap) (hE : E∈Icc 0 t) (hs : s∈Icc 0 (min t M)) :
    0<base E+primaryCost t E+gain s+V R (p E j) (q E j) (t-s) := by
  have hEf : E∈Icc 0 frameCap := ⟨hE.1,hE.2.trans ht.2⟩
  have hc := coefficients hEf j
  have hb0 : 0≤min t M := le_min (by dsimp [L] at ht; linarith [ht.1]) (by norm_num [M])
  have hg := gain_concave.subset
    (show Icc 0 (min t M)⊆Icc 0 M from fun s hs => ⟨hs.1,hs.2.trans (min_le_right _ _)⟩)
    (convex_Icc _ _)
  have hv := concave_affine_argument
    (V_concave (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:=-1) (b:=t) (l:=0) (u:=min t M)
    (fun x hx => ⟨by linarith [hx.2,min_le_left t M],by linarith [hx.1,ht.2]⟩)
  have hconc := (NonnegativeTotals.NegativeTD.Concentration.affine_add_concave hg
    (base E+primaryCost t E) 0).add hv
  have h0 : 0<base E+primaryCost t E+gain 0+V R (p E j) (q E j) t := by
    have hh := NonnegativeTotals.NegativeTD.Concentration.negative_endpoint j
      (show NonnegativeTotals.NegativeTD.Domain t E from ⟨ht,hE⟩)
    simpa [gain,phi] using hh
  have h1 : 0<base E+primaryCost t E+gain (min t M)+V R (p E j) (q E j) (t-min t M) := by
    rcases le_total t M with htm|hmt
    · rw [min_eq_left htm,sub_self,V_zero,add_zero]
      exact Paired.equal_positive ⟨ht.1,htm⟩ hE
    · rw [min_eq_right hmt]
      exact negative_endpoint j ⟨hmt,ht.2⟩ hE
  have hh := concave_gt_of_endpoints hconc hs
    (by simpa only [zero_mul,add_zero,mul_zero,neg_mul,one_mul,neg_add_eq_sub,sub_zero] using h0)
    (by simpa only [zero_mul,add_zero,neg_mul,one_mul,neg_add_eq_sub] using h1)
  simpa only [zero_mul,add_zero,neg_mul,one_mul,neg_add_eq_sub] using hh

theorem lower_positive_positive (i : Fin 4) {t E s : ℝ}
    (ht : t∈Icc L M) (hE : E∈Icc 0 t) (hs : s∈Icc t M) :
    0<base E+primaryCost t E+gain s+positive E i (s-t) := by
  have hEf : E∈Icc 0 frameCap := ⟨hE.1,by norm_num [M,frameCap] at *; linarith [hE.2,ht.2]⟩
  have hc := coefficients hEf i
  have hg := gain_concave.subset
    (show Icc t M⊆Icc 0 M from fun s hs => ⟨by dsimp [L] at ht; linarith [ht.1,hs.1],hs.2⟩)
    (convex_Icc _ _)
  have hu := concave_affine_argument
    (PositiveTD.Hybrid.positive_concave (a:=aD) (p:=p E) (q:=q E) (d:=3) (i:=i)
      (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]))
    (a:=1) (b:=-t) (l:=t) (u:=M)
    (fun s hs => ⟨by linarith [hs.1],by dsimp [L,M,frameCap] at *; linarith [hs.2,ht.1]⟩)
  have hconc := (NonnegativeTotals.NegativeTD.Concentration.affine_add_concave hg
    (base E+primaryCost t E) 0).add hu
  have h0 : 0<base E+primaryCost t E+gain t+positive E i (t-t) := by
    simpa [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      PositiveTD.Hybrid.positive,equalScalar] using Paired.equal_positive ht hE
  have h1 := positive_endpoint i ht hE
  have hh := concave_gt_of_endpoints hconc hs
    (by simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      zero_mul,add_zero,one_mul,←sub_eq_add_neg] using h0)
    (by simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
      zero_mul,add_zero,one_mul,←sub_eq_add_neg] using h1)
  simpa only [positive,NonnegativeTotals.NegativeTD.Concentration.positive,
    zero_mul,add_zero,one_mul,←sub_eq_add_neg] using hh

theorem line_scalar_positive (i j : Fin 4) {t E s P : ℝ}
    (ht : t∈Icc L frameCap) (hE : E∈Icc 0 t) (hs : s∈Icc 0 M)
    (hP : P∈Icc (max 0 (s-t)) (frameCap-t)) :
    0<base E+primaryCost t E+gain s+line E i j P (t-s+P) := by
  have hEf : E∈Icc 0 frameCap := ⟨hE.1,hE.2.trans ht.2⟩
  rcases le_total s t with hst|hts
  · have hd : t-s∈Icc 0 frameCap := ⟨by linarith,by linarith [ht.2,hs.1]⟩
    have hPf : P∈Icc 0 (frameCap-(t-s)) :=
      ⟨(le_max_left 0 (s-t)).trans hP.1,by linarith [hP.2,hs.1]⟩
    have hl := NonnegativeTotals.NegativeTD.Concentration.line_excess_lower hEf i j hd hPf
    have hp := lower_negative_positive j ht hE ⟨hs.1,le_min hst hs.2⟩
    linarith
  · have hEm : E∈Icc 0 M := ⟨hE.1,(hE.2.trans hts).trans hs.2⟩
    have hl := line_positive_excess hEm i j ht.1 ⟨hts,hs.2⟩
      ⟨(le_max_right 0 (s-t)).trans hP.1,hP.2⟩
    have hp := lower_positive_positive i ⟨ht.1,hts.trans hs.2⟩ hE ⟨hts,hs.2⟩
    linarith

/-- The original ordinary budgets, with both actual T arguments deleted. -/
theorem sum_scalar_positive {t E s : ℝ} (P N : Fin 4→ℝ)
    (ht : t∈Icc L frameCap) (hE : E∈Icc 0 t) (hs : s∈Icc 0 M)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-t) (hNt : (∑i,N i)≤frameCap-s)
    (hbalance : (∑i,N i)=t-s+∑i,P i) :
    0<base E+primaryCost t E+gain s+∑i,block E i (P i) (N i) := by
  have hEf : E∈Icc 0 frameCap := ⟨hE.1,hE.2.trans ht.2⟩
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hP i)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hN i)
  obtain ⟨i,j,hij⟩ := PositiveTD.Hybrid.both_signs_concentrate R aD (p E) (q E) P N 3
    (Real.sqrt_nonneg qCap) radius_sq.le
    (fun i => (coefficients hEf i).1) (fun i => (coefficients hEf i).2.1)
    (fun i => by linarith [(coefficients hEf i).2.2.1]) hP hN
    (by dsimp [L] at ht; linarith [ht.1]) (by linarith [hs.1])
  change line E i j (∑i,P i) (∑i,N i)≤∑i,block E i (P i) (N i) at hij
  have hpdom : (∑i,P i)∈Icc (max 0 (s-t)) (frameCap-t) :=
    ⟨max_le hP0 (by linarith),hPt⟩
  have hp := line_scalar_positive i j ht hE hs hpdom
  rw [hbalance] at hij
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NonpositiveT.Paired.Concentration
