module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeELargeAEndpoints
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2PositiveSlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2SameBlock

/-!
# Removing ordinary-angle saturation in the large-A negative-E family

Uncompiled transcription of Sections 3--4 of the single negative-EH
nonpositive-TD2 proof. The negative slope .767 and positive slope -.64q
are proved for the fixed H/G/B pairs. Separate and coincident blocks
then dominate their pure signed excess, with the original P and N
budgets retained. The distinguished D block keeps its actual linear
positive minorant and its H negative minorant.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryNegativeSlope OrdinaryPositiveEnvelope OrdinaryAngleConcentration
open NegativeAPositiveTD.PositiveSlope NegativeAPositiveTD.SameBlock

abbrev aD : ℝ := GlobalGA.Secondary.diagonal-1/2
def positive (i : Fin 4) (P : ℝ) : ℝ := PositiveTD.Hybrid.positive R aD p q 3 i P
abbrev block (i : Fin 4) (P N : ℝ) : ℝ := PositiveTD.Hybrid.block R aD p q 3 i P N
def line (i j : Fin 4) (P N : ℝ) : ℝ :=
  if i=j then block i P N else positive i P+V R (p j) (q j) N

theorem negative_endpoint_derivative (i : Fin 4) :
    (767/1000:ℝ)<Vd R (p i) (q i) frameCap := by
  have hc := coefficients i
  have hq := hc.1.trans_le hc.2.1
  have hN := pairNorm_pos hc.1 hq (t:= -frameCap) (by norm_num [frameCap])
  have ht := transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])
  have hRcos := mul_le_mul radius_tight.1.le ht.1.le
    (by norm_num : (0:ℝ)≤7648/10000) (Real.sqrt_nonneg qCap)
  have hsin := mul_le_mul_of_nonneg_left ht.2.2.2.1.le hq.le
  have hupper := mul_le_mul
    (show 767/1000+q i*Real.sin frameCap≤767/1000+q i*(6443/10000) by linarith)
    (norm_negative_endpoints i).2.1.le hN.le
    (by positivity : 0≤767/1000+q i*(6443/10000))
  have hnum := mul_le_mul_of_nonneg_left hRcos (mul_nonneg hc.1.le hq.le)
  have hcross : (767/1000+q i*Real.sin frameCap)*pairNorm (p i) (q i) (-frameCap)<
      R*p i*q i*Real.cos frameCap := by
    fin_cases i <;> norm_num [p,q,normCapUpper,k,l,c,radiusLo] at hupper hnum ⊢ <;> nlinarith
  have hd := (lt_div_iff₀ hN).2 hcross
  dsimp [Vd,mixedNDerivative,normD1,pairProduct]
  simp only [zero_sub,Real.cos_neg]
  rw [show R*p i*q i*Real.cos frameCap/pairNorm (p i) (q i) (-frameCap)=
    R*(p i*q i*Real.cos frameCap/pairNorm (p i) (q i) (-frameCap)) by ring] at hd
  linarith only [hd]

theorem negative_derivative (i : Fin 4) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    (767/1000:ℝ)<Vd R (p i) (q i) x := by
  have hc := coefficients i
  exact (negative_endpoint_derivative i).trans_le
    (Vd_antitone (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1
      (by linarith [hc.2.2.1]) hx (by norm_num [frameCap]) hx.2)

theorem negative_growth (i : Fin 4) {x y : ℝ}
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    (767/1000)*(y-x)≤V R (p i) (q i) y-V R (p i) (q i) x := by
  have hc := coefficients i
  exact derivative_reserve
    (fun z hz => (V_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) hz).continuousAt.continuousWithinAt)
    (fun z hz => V_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) (Ioo_subset_Icc_self hz))
    (fun z hz => (negative_derivative i (Ioo_subset_Icc_self hz)).le) hx hy hxy

def normSpanLower : Fin 4→ℝ := ![14977/10000,7099/5000,367/200,14977/10000]

theorem norm_span_lower (i : Fin 4) : normSpanLower i<pairNorm (p i) (q i) span := by
  have hc := coefficients i
  have hs := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:=span) (by norm_num [span,frameCap])
  have hp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:=span) (by norm_num [span,frameCap])
  have ht := HighOrderTaylor.S11_le_sin (show (0:ℝ)≤ span by norm_num [span])
  fin_cases i <;>
    norm_num [p,q,normSpanLower,k,l,c,span,pairEnergy,pairProduct,
      HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7] at hs hp ht ⊢ <;> nlinarith

theorem positive_endpoint_derivative (i : Fin 4) :
    -(16/25)*q i<Ud (p i) (q i) span := by
  have hc := coefficients i
  have hq := hc.1.trans_le hc.2.1
  have hN := pairNorm_pos hc.1 hq (t:=span) (by norm_num [span,frameCap])
  have hC := Arithmetic.cos10_le_cos (show (0:ℝ) ≤ span by norm_num [span])
  have hS := Arithmetic.sin_le_sin9 (show (0:ℝ) ≤ span by norm_num [span])
  have hCU := HighOrderTaylor.cos_le_C12 (show (0:ℝ) ≤ span by norm_num [span])
  have hphi : (7/20:ℝ)<Real.cos span-Real.sin span := by
    norm_num [span,Arithmetic.cos10,Arithmetic.cos8,Arithmetic.sin9,Arithmetic.sin7] at hC hS
    linarith
  have hcosU : Real.cos span<(431/500:ℝ) := by
    norm_num [span,HighOrderTaylor.C12,Arithmetic.cos10,Arithmetic.cos8] at hCU
    linarith
  have hcos0 : 0≤Real.cos span := by
    linarith [(transport_trig (show span∈Icc 0 frameCap by norm_num [span,frameCap])).1]
  have hRcos := mul_le_mul radius_tight.2.le hcosU.le hcos0
    (by norm_num [radiusHi] : (0:ℝ)≤radiusHi)
  have hnum := mul_le_mul_of_nonneg_left hRcos (mul_nonneg hc.1.le hq.le)
  have hfactor : 0<(16/25)*q i+(7/20)*p i := by linarith [hc.1]
  have hden := mul_lt_mul_of_pos_left (norm_span_lower i) hfactor
  have hcross : R*p i*q i*Real.cos span<
      ((16/25)*q i+(7/20)*p i)*pairNorm (p i) (q i) span := by
    fin_cases i <;> norm_num [p,q,normSpanLower,k,l,c,radiusHi] at hnum hden ⊢ <;> nlinarith
  have hdiv := (div_lt_iff₀ hN).2 hcross
  have hphip := mul_lt_mul_of_pos_left hphi hc.1
  dsimp [Ud,mixedPDerivative,normD1,pairProduct]
  simp only [sub_zero]
  rw [show R*p i*q i*Real.cos span/pairNorm (p i) (q i) span=
    R*(p i*q i*Real.cos span/pairNorm (p i) (q i) span) by ring] at hdiv
  linarith only [hdiv,hphip]

theorem positive_derivative (i : Fin 4) {x : ℝ} (hx : x∈Icc 0 span) :
    -(16/25)*q i<Ud (p i) (q i) x := by
  have hc := coefficients i
  exact (positive_endpoint_derivative i).trans_le
    (Ud_antitone hc.1 hc.2.1 (by linarith [hc.2.2.1])
      ⟨hx.1,hx.2.trans (by norm_num [span,frameCap])⟩
      (by norm_num [span,frameCap]) hx.2)

theorem positive_lower (i : Fin 4) {x : ℝ} (hx : x∈Icc 0 frameCap) :
    -(109/200)*c*x≤positive i x := by
  by_cases hi : i=3
  · subst i
    simp [positive,PositiveTD.Hybrid.positive]
    have hm := mul_le_mul_of_nonneg_right
      (show aD≤(109/200)*c by dsimp [aD,c]; linarith [diagonal_bounds.2]) hx.1
    simp only [aD,c] at hm ⊢
    linarith
  · have hc := coefficients i
    have hh : -(109/200)*q i*x≤U R (p i) (q i) x :=
      U_lower (Real.sqrt_nonneg qCap) radius_sq.le hc.1 hc.2.1 (by linarith [hc.2.2.1]) hx
    have hm := mul_le_mul_of_nonneg_right hc.2.2.2.2.2 hx.1
    simp only [positive,PositiveTD.Hybrid.positive,if_neg hi]
    simp only [c] at hm ⊢
    linarith

theorem positive_growth (i : Fin 4) {x y : ℝ}
    (hx : x∈Icc 0 span) (hy : y∈Icc 0 span) (hxy : x≤y) :
    -(16/25)*c*(y-x)≤positive i y-positive i x := by
  by_cases hi : i=3
  · subst i
    simp [positive,PositiveTD.Hybrid.positive]
    have hm := mul_le_mul_of_nonneg_right
      (show aD≤(16/25)*c by dsimp [aD,c]; linarith [diagonal_bounds.2]) (sub_nonneg.mpr hxy)
    simp only [aD,c] at hm ⊢
    linarith
  · have hc := coefficients i
    have harg {z : ℝ} (hz : z∈Icc 0 span) : z∈Icc 0 frameCap :=
      ⟨hz.1,hz.2.trans (by norm_num [span,frameCap])⟩
    have hh := derivative_reserve (f:=U R (p i) (q i)) (df:=Ud (p i) (q i))
      (k:= -(16/25)*q i)
      (fun z hz => (U_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) (harg hz)).continuousAt.continuousWithinAt)
      (fun z hz => U_hasDerivAt hc.1 (hc.1.trans_le hc.2.1) (harg (Ioo_subset_Icc_self hz)))
      (fun z hz => (positive_derivative i (Ioo_subset_Icc_self hz)).le) hx hy hxy
    have hm := mul_le_mul_of_nonneg_right hc.2.2.2.2.2 (sub_nonneg.mpr hxy)
    simp only [positive,PositiveTD.Hybrid.positive,if_neg hi]
    simp only [c] at hm ⊢
    linarith

theorem line_negative_excess (i j : Fin 4) {P N : ℝ}
    (hP : P∈Icc 0 N) (hN : N∈Icc 0 frameCap) :
    V R (p j) (q j) (N-P)≤line i j P N := by
  have hPf : P∈Icc 0 frameCap := ⟨hP.1,hP.2.trans hN.2⟩
  have hdiff : N-P∈Icc 0 frameCap := ⟨sub_nonneg.mpr hP.2,by linarith [hN.2,hP.1]⟩
  have hseparated : V R (p j) (q j) (N-P)≤positive i P+V R (p j) (q j) N := by
    have hu := positive_lower i hPf
    have hv := negative_growth j hdiff hN (by linarith [hP.1])
    have hreserve : 0≤(23363/200000:ℝ)*P := mul_nonneg (by norm_num) hP.1
    dsimp [c] at hu
    nlinarith
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · simpa [line,block,positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,hi] using hseparated
    · have hc := coefficients i
      have hs := mul_le_mul_of_nonneg_left (transport_trig hN).2.2.2.1.le
        (hc.1.trans_le hc.2.1).le
      have hsine : q i*Real.sin N≤p i := by linarith [hc.2.2.1]
      simpa [line,block,PositiveTD.Hybrid.block,hi] using negative_surplus hc.1.le hP hN hsine
  · simpa [line,hij] using hseparated

theorem line_positive_excess (i j : Fin 4) {P N : ℝ}
    (hP : P∈Icc 0 span) (hN : N∈Icc 0 P) :
    positive i (P-N)≤line i j P N := by
  have hPf : P∈Icc 0 frameCap := ⟨hP.1,hP.2.trans (by norm_num [span,frameCap])⟩
  have hNf : N∈Icc 0 frameCap := ⟨hN.1,hN.2.trans hPf.2⟩
  have hdiff : P-N∈Icc 0 span := ⟨sub_nonneg.mpr hN.2,by linarith [hP.2,hN.1]⟩
  have hseparated : positive i (P-N)≤positive i P+V R (p j) (q j) N := by
    have hu := positive_growth i hdiff hP (by linarith [hN.1])
    have hv := negative_growth j (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hNf hN.1
    simp only [sub_zero,V_zero] at hv
    have hreserve : 0≤(87/25000:ℝ)*N := mul_nonneg (by norm_num) hN.1
    dsimp [c] at hu
    nlinarith
  by_cases hij : i=j
  · subst j
    by_cases hi : i=3
    · simpa [line,block,positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,hi] using hseparated
    · have hc := coefficients i
      simpa [line,block,positive,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,hi] using
        positive_surplus hc.1.le (show q i≤(17/10)*p i by linarith [hc.2.2.1]) hPf hN
  · simpa [line,hij] using hseparated

/-- The pure signed excess is obtained from the original independent
sign totals, before any scalar gain is chosen. -/
theorem sum_pure_lower {a w : ℝ} (P N : Fin 4→ℝ)
    (ha : a∈Icc L frameCap) (hw : w∈Icc 0 frameCap)
    (hP : ∀i,0≤P i) (hN : ∀i,0≤N i)
    (hPt : (∑i,P i)≤frameCap-a) (hNt : (∑i,N i)≤frameCap-w)
    (hbalance : (∑i,N i)-(∑i,P i)=a-w) :
    ∃i, (if w≤a then V R (p i) (q i) (a-w) else positive i (w-a))≤
      ∑i,block i (P i) (N i) := by
  have ha0 : 0≤a := by dsimp [L] at ha; linarith [ha.1]
  have hP0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hP i)
  have hN0 := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => hN i)
  obtain ⟨i,j,hij⟩ := PositiveTD.Hybrid.both_signs_concentrate R aD p q P N 3
    (Real.sqrt_nonneg qCap) radius_sq.le (fun i => (coefficients i).1)
    (fun i => (coefficients i).2.1) (fun i => by linarith [(coefficients i).1,(coefficients i).2.2.1])
    hP hN (by linarith) (by linarith [hw.1])
  change line i j (∑k,P k) (∑k,N k)≤∑k,block k (P k) (N k) at hij
  by_cases hwa : w≤a
  · refine ⟨j,?_⟩
    rw [if_pos hwa]
    have hh := line_negative_excess i j ⟨hP0,by linarith⟩ ⟨hN0,by linarith [hw.1]⟩
    rw [hbalance] at hh
    exact hh.trans hij
  · refine ⟨i,?_⟩
    rw [if_neg hwa]
    have hh := line_positive_excess i j
      ⟨hP0,by dsimp [L,span,frameCap] at ha hPt ⊢; linarith [ha.1]⟩
      ⟨hN0,by linarith⟩
    have he : (∑k,P k)-(∑k,N k)=w-a := by linarith
    rw [he] at hh
    exact hh.trans hij

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeELargeA
