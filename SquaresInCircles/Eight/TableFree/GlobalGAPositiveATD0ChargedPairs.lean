module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveATD0Parameters
public import SquaresInCircles.Eight.TableFree.GlobalGAActualPairs

/-!
# The three charged low-angle circle blocks

Uncompiled transcription of (11)--(16) in the positive-A/TD0 hand proof.
Separate concavity reduces the actual two signed errors to the four
intrinsic corners. The exact rational radical bounds are the displayed
enclosures of the hand proof.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity ActualOrdinaryBlocks

def chargedMixed (p q P N : ℝ) : ℝ :=
  mixedBlock R p q P N+charge*(P-N)

def chargedPair (p q a b : ℝ) : ℝ :=
  p*psi a+q*psi b-R*(pairNorm p q (a+b)-pairNorm p q 0)+charge*(a+b)

@[simp] theorem chargedMixed_zero (p q : ℝ) : chargedMixed p q 0 0=0 := by
  simp [chargedMixed,mixedBlock]

theorem chargedMixed_concave_P {p q N : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hN : N∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => chargedMixed p q P N) := by
  apply concave_of_deriv2
    (f' := fun P => mixedPDerivative R p q P N+charge)
    (f'' := fun P => curvature R p q (P-N)-p*phi P)
  · intro P hP
    convert (mixedP_hasDerivAt hp (hp.trans_le hpq) hP hN).add
      (((hasDerivAt_id P).sub_const N).const_mul charge) using 1 <;>
      simp [chargedMixed]
  · intro P hP
    exact (mixedPDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN).add_const charge
  · intro P hP
    exact (mixedP_second_lt (Real.sqrt_nonneg _) (by rw [radius_sq])
      hp hpq hqp hP hN).le.trans (by nlinarith)

theorem chargedMixed_concave_N {p q P : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hP : P∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 frameCap) (chargedMixed p q P) := by
  apply concave_of_deriv2
    (f' := fun N => mixedNDerivative R p q P N-charge)
    (f'' := fun N => curvature R p q (P-N)-q*Real.cos N)
  · intro N hN
    convert (mixedN_hasDerivAt hp (hp.trans_le hpq) hP hN).add
      (((hasDerivAt_const N P).sub (hasDerivAt_id N)).const_mul charge) using 1 <;>
      simp [chargedMixed] <;> ring
  · intro N hN
    exact (mixedNDerivative_hasDerivAt hp (hp.trans_le hpq) hP hN).sub_const charge
  · intro N hN
    exact (mixedN_second_lt (Real.sqrt_nonneg _) (by rw [radius_sq])
      hp hpq hqp hP hN).le.trans (by nlinarith [hp.trans_le hpq])

/-- Four intrinsic corners control every allocation of both signed totals. -/
theorem charged_rectangle_strict_lower {p q P N b : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap)
    (h00 : b<chargedMixed p q 0 0)
    (h10 : b<chargedMixed p q frameCap 0)
    (h01 : b<chargedMixed p q 0 frameCap)
    (h11 : b<chargedMixed p q frameCap frameCap) :
    b<chargedMixed p q P N := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have h0 := concave_gt_of_endpoints (chargedMixed_concave_N hp hpq hqp hz) hN h00 h01
  have h1 := concave_gt_of_endpoints (chargedMixed_concave_N hp hpq hqp hh) hN h10 h11
  exact concave_gt_of_endpoints (chargedMixed_concave_P hp hpq hqp hN) hP h0 h1

theorem charged_pair_minorant {p q a b : ℝ} (hp : 0≤p) (hpq : p≤q)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    chargedMixed p q (positivePart a+positivePart b) (negativePart a+negativePart b)≤
      chargedPair p q a b := by
  let B : Block := ⟨p,q,a,b⟩
  have hm := B.minorant R
    (by simpa [B,Block.p,min_eq_left hpq] using hp) hP hN
  have he : positivePart a+positivePart b-(negativePart a+negativePart b)=a+b := by
    linarith [positive_sub_negative a,positive_sub_negative b]
  simp only [B,Block.p,Block.q,Block.P,Block.N,Block.increment,
    min_eq_left hpq,max_eq_right hpq] at hm
  dsimp [chargedMixed,chargedPair]
  rw [he]
  linarith

/-- The zero corner is retained exactly; the other three corners have a
strict reserve. -/
theorem charged_rectangle_nonneg {p q P N : ℝ}
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 frameCap)
    (h10 : 0≤chargedMixed p q frameCap 0)
    (h01 : 0≤chargedMixed p q 0 frameCap)
    (h11 : 0≤chargedMixed p q frameCap frameCap) :
    0≤chargedMixed p q P N := by
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have h0 := (chargedMixed_concave_N hp hpq hqp hz).min_le_of_mem_Icc hz hh hN
  have h1 := (chargedMixed_concave_N hp hpq hqp hh).min_le_of_mem_Icc hz hh hN
  have h2 := (chargedMixed_concave_P hp hpq hqp hN).min_le_of_mem_Icc hz hh hP
  have h00 : 0≤chargedMixed p q 0 0 := by simp
  exact (le_min ((le_min h00 h01).trans h0) ((le_min h10 h11).trans h1)).trans h2

def coefficientP : Fin 3→ℝ := ![lowK,lowK,lowL]
def coefficientQ : Fin 3→ℝ := ![lowL,1,lowC]
def normZeroLower : Fin 3→ℝ := ![1481890/1000000,1268227/1000000,2197180/1000000]
def normZeroUpper : Fin 3→ℝ := ![1481891/1000000,1268228/1000000,2197181/1000000]
def normPositiveUpper : Fin 3→ℝ := ![1860719/1000000,1616596/1000000,2783842/1000000]
def normNegativeUpper : Fin 3→ℝ := ![964223/1000000,776802/1000000,1380373/1000000]

theorem coefficient_ranges (i : Fin 3) :
    0<coefficientP i ∧ coefficientP i≤coefficientQ i ∧ coefficientQ i≤2*coefficientP i := by
  fin_cases i <;> norm_num [coefficientP,coefficientQ,lowK,lowL,lowC]

theorem fixed_norm_zero (i : Fin 3) :
    normZeroLower i<pairNorm (coefficientP i) (coefficientQ i) 0 ∧
      pairNorm (coefficientP i) (coefficientQ i) 0<normZeroUpper i := by
  have hh := coefficient_ranges i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1) (t:=0) (by norm_num [frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1) (t:=0) (by norm_num [frameCap])
  fin_cases i <;>
    norm_num [coefficientP,coefficientQ,normZeroLower,normZeroUpper,lowK,lowL,lowC,
      pairEnergy,pairProduct] at hs hp ⊢ <;> constructor <;> nlinarith

theorem fixed_norm_positive (i : Fin 3) :
    pairNorm (coefficientP i) (coefficientQ i) frameCap<normPositiveUpper i := by
  have hh := coefficient_ranges i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1)
    (t:=frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1)
    (t:=frameCap) (by norm_num [frameCap])
  have ht := cap_trig.2.1
  fin_cases i <;>
    norm_num [coefficientP,coefficientQ,normPositiveUpper,lowK,lowL,lowC,
      pairEnergy,pairProduct,Arithmetic.sin9,frameCap] at hs hp ht ⊢ <;> nlinarith

theorem fixed_norm_negative (i : Fin 3) :
    pairNorm (coefficientP i) (coefficientQ i) (-frameCap)<normNegativeUpper i := by
  have hh := coefficient_ranges i
  have hs := pairNorm_sq hh.1 (hh.1.trans_le hh.2.1)
    (t:= -frameCap) (by norm_num [frameCap])
  have hp := pairNorm_pos hh.1 (hh.1.trans_le hh.2.1)
    (t:= -frameCap) (by norm_num [frameCap])
  have ht := cap_trig.1
  fin_cases i <;>
    norm_num [coefficientP,coefficientQ,normNegativeUpper,lowK,lowL,lowC,
      pairEnergy,pairProduct,Real.sin_neg,Arithmetic.sin7,frameCap] at hs hp ht ⊢ <;> nlinarith

theorem fixed_corners (i : Fin 3) :
    (3/40:ℝ)<chargedMixed (coefficientP i) (coefficientQ i) frameCap 0 ∧
    (7/1000:ℝ)<chargedMixed (coefficientP i) (coefficientQ i) 0 frameCap ∧
    (11/500:ℝ)<chargedMixed (coefficientP i) (coefficientQ i) frameCap frameCap := by
  have hn0 := radius_norm_lower
    (show 0<normZeroLower i by fin_cases i <;> norm_num [normZeroLower]) (fixed_norm_zero i).1
  have hnp := radius_norm_upper
    (show 0<normPositiveUpper i by fin_cases i <;> norm_num [normPositiveUpper]) (fixed_norm_positive i)
  have hnn := radius_norm_upper
    (show 0<normNegativeUpper i by fin_cases i <;> norm_num [normNegativeUpper]) (fixed_norm_negative i)
  have hs := cap_trig.1
  have hc := cap_trig.2.2.1
  fin_cases i <;>
    norm_num [coefficientP,coefficientQ,normZeroLower,normPositiveUpper,normNegativeUpper,
      Arithmetic.sin7,frameCap,lowK,lowL,lowC] at hn0 hnp hnn hs hc ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;>
    norm_num [chargedMixed,mixedBlock,phi,charge,coefficientP,coefficientQ,
      lowK,lowL,lowC,frameCap] <;> nlinarith

theorem fixed_pair_nonneg (i : Fin 3) {a b : ℝ}
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    0≤chargedPair (coefficientP i) (coefficientQ i) a b := by
  have hr := coefficient_ranges i
  have hc := fixed_corners i
  have hh := charged_rectangle_nonneg hr.1 hr.2.1 hr.2.2
    ⟨add_nonneg (positivePart_nonneg _) (positivePart_nonneg _),hP⟩
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hN⟩
    (by linarith [hc.1]) (by linarith [hc.2.1]) (by linarith [hc.2.2])
  exact hh.trans (charged_pair_minorant hr.1.le hr.2.1 hP hN)

def pairIncrement (p q a b : ℝ) (P : SignedPoint) : ℝ :=
  p*(edgeWidth a-1)+q*(edgeWidth b-1)-
    (pairF p q a b*P.a+pairG p q a b*P.y)+
    fullSupport q p+charge*(a+b)

theorem actual_pair_lower {r p q a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (ha : |a|≤frameCap) (hb : |b|≤frameCap) :
    chargedPair p q a b≤pairIncrement p q a b P := by
  have hh := Secondary.actual_pair_lower hy hc hr ha hb (p:=p) (q:=q)
  dsimp [Secondary.chargedPair,Secondary.pairIncrement,chargedPair,pairIncrement] at *
  linarith

theorem actual_fixed_pair_nonneg (i : Fin 3) {r a b : ℝ} {P : SignedPoint}
    (hy : 0≤P.y) (hc : P.Contained r) (hr : r≤qCap)
    (hP : positivePart a+positivePart b≤frameCap)
    (hN : negativePart a+negativePart b≤frameCap) :
    0≤pairIncrement (coefficientP i) (coefficientQ i) a b P := by
  have he := pair_error_bounds hP hN
  exact (fixed_pair_nonneg i hP hN).trans (actual_pair_lower hy hc hr he.1 he.2.1)

def lowBaseline : ℝ := lowK+2*lowL+2*lowC+2-
  fullSupport 1 lowK-fullSupport lowL lowK-fullSupport lowC lowL-(1+lowC)*diagonal

theorem low_baseline_reserve : (13/400:ℝ)<lowBaseline := by
  have hG := radius_norm_upper (by norm_num : (0:ℝ)<1481891/1000000) (fixed_norm_zero 0).2
  have hH := radius_norm_upper (by norm_num : (0:ℝ)<1268228/1000000) (fixed_norm_zero 1).2
  have hB := radius_norm_upper (by norm_num : (0:ℝ)<2197181/1000000) (fixed_norm_zero 2).2
  have hd := diagonal_bounds.2
  rw [lowBaseline,fullSupport_pair lowK 1,fullSupport_pair lowK lowL,fullSupport_pair lowL lowC]
  norm_num [coefficientP,coefficientQ,normZeroUpper,lowK,lowL,lowC] at hG hH hB ⊢
  linarith

theorem low_A_charge_lower {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    -a^2/4-(183/200)*a≤TwoPositive.ASupport.charge a := by
  rw [TwoPositive.ASupport.charge_low ha.2]
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=a)
  have hsin := Real.sin_le ha.1
  have hm := mul_le_mul_of_nonneg_left hsin
    (show 0≤axial-1/2 by linarith [axial_bounds.1])
  have hax := mul_le_mul_of_nonneg_right
    (show axial-1/2≤183/200 by linarith [axial_bounds.2]) ha.1
  dsimp [TwoPositive.ASupport.axialCharge]
  nlinarith

/-- The final one-variable reserve is the exact right-endpoint value
49/15000 in (34). -/
theorem low_scalar_positive {a : ℝ} (ha : a∈Icc 0 (1/6:ℝ)) :
    (49/15000:ℝ)<lowBaseline+charge*a+lowL*TwoPositive.ASupport.charge a := by
  have hj := mul_le_mul_of_nonneg_left (low_A_charge_lower ha)
    (show 0≤lowL by norm_num [lowL])
  have ha2 := pow_le_pow_left₀ ha.1 ha.2 2
  have hbase := low_baseline_reserve
  dsimp [lowL,charge] at *
  nlinarith [ha.2]

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveATD0
