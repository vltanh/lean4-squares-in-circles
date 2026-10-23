module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowSeparatedInterior

/-!
# Both original D branches and the low separated alternatives

Uncompiled completion of Section 7 of the negative-DE TD2 angle
companion. The short polynomial is transferred to the actual cosine
square before division. The interior comparison uses only coefficient
bounds derived from the original support branch. The resulting scalar
monotonicity retains the original A/TD split and every ordinary angle.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryNegativeSlope

theorem diagonal_slope_comparison {p q s : ℝ}
    (hp : 0<p) (hp0 : p≤p0) (hq : q∈Icc 1 qMax)
    (hs : s∈Icc 0 frameCap) :
    Vd R p q (frameCap-s)<LowD.diagonalFirst s := by
  let d : ℝ := frameCap-s
  have hd : d∈Icc 0 frameCap := ⟨by dsimp [d]; linarith [hs.2],by dsimp [d]; linarith [hs.1]⟩
  by_cases hshort : d≤9/25
  · have hpoly := Certificate.short_model_reserve ⟨hd.1,hshort⟩
    have hid : frameCap-d=s := by dsimp [d]; ring
    rw [hid] at hpoly
    have hV := completed_model hp hp0 hq hd
    have hM := model_nonnegative hd
    have hsin := sin_upper_five hs.1
    have hcos := cos_upper_four hs.1
    have hsinP : Real.sin s≤aeval s PositiveTD.Certificate.S5 := by
      simpa [PositiveTD.Certificate.S5] using hsin
    have hcosP : Real.cos s≤aeval s PositiveTD.Certificate.C4 := by
      simpa [PositiveTD.Certificate.C4] using hcos
    have hcos0 := NegativeESecant.cos_pos hs
    have hcos2 := pow_le_pow_left₀ hcos0.le hcosP 2
    have hscale := mul_le_mul_of_nonneg_right hcos2 hM
    have hVscale := mul_le_mul_of_nonneg_right hV.le (sq_nonneg (Real.cos s))
    have hd0 : diagonal-1/2≤2/5 := by linarith [diagonal_bounds.2]
    have h₁ := mul_le_mul_of_nonneg_right hd0 (transport_trig hs).2.2.1
    have h₂ := mul_le_mul_of_nonneg_left hsinP (show (0:ℝ)≤2/5 by norm_num)
    change Vd R p q d<(13/12-(diagonal-1/2)*Real.sin s)/Real.cos s^2
    apply (lt_div_iff₀ (sq_pos_of_pos hcos0)).2
    nlinarith only [hpoly,hscale,hVscale,h₁,h₂]
  · have hV := late_slope_upper hp hp0 hq ⟨(lt_of_not_ge hshort).le,hd.2⟩
    have hD := LowD.diagonal_derivative_lower hs
    norm_num [LowD.M] at hD
    change Vd R p q d<LowD.diagonalFirst s
    linarith

def larger (atH : Bool) (θ : ℝ) : ℝ := if atH then 1 else Explicit.l .low θ

theorem actual_pair_domain (atH : Bool) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    0<Explicit.k .low θ ∧ Explicit.k .low θ≤p0 ∧
      larger atH θ∈Icc 1 qMax := by
  have hr := Explicit.low_ranges hθ
  refine ⟨by linarith [hr.1],hr.2.1.le,?_⟩
  cases atH
  · exact ⟨hr.2.2.1.le,hr.2.2.2.1.le⟩
  · norm_num [larger,qMax]

theorem actual_diagonal_comparison (atH : Bool) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap) :
    Vd R (Explicit.k .low θ) (larger atH θ) (frameCap-s)<LowD.diagonalFirst s := by
  have hp := actual_pair_domain atH hθ
  exact diagonal_slope_comparison hp.1 hp.2.1 hp.2.2 hs

theorem actual_interior_comparison (atH : Bool) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap)
    (hint : Explicit.c .low θ≤LowD.sec s) :
    Vd R (Explicit.k .low θ) (larger atH θ) (frameCap-s)<
      secantGainDeriv qCap (Explicit.c .low θ) s := by
  have hr := Explicit.low_ranges hθ
  have hi := LowRanges.interior_ranges hθ hs hint
  have hq : larger atH θ∈Icc (1:ℝ) (283/250) := by
    cases atH
    · exact ⟨hr.2.2.1.le,hi.2.1.le⟩
    · norm_num [larger]
  exact interior_slope_comparison (by linarith [hr.1]) hi.1.le hq
    (by linarith [hr.2.2.2.2.1]) hs hi.2.2.le

theorem correction_negative_monotone (atH : Bool) {θ : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) :
    MonotoneOn (fun s => LowD.correction (Explicit.c .low θ) s+
      V R (Explicit.k .low θ) (larger atH θ) (frameCap-s)) (Icc 0 frameCap) := by
  have hp := actual_pair_domain atH hθ
  have hq : 0<larger atH θ := by linarith [hp.2.2.1]
  apply LowD.add_monotone
    (by linarith [(Explicit.low_ranges hθ).2.2.2.2.1] : 1≤Explicit.c .low θ) le_rfl le_rfl
    (df:=fun s => -Vd R (Explicit.k .low θ) (larger atH θ) (frameCap-s))
  · intro s hs
    have hh := (V_hasDerivAt hp.1 hq
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1]⟩)).comp s
        ((hasDerivAt_id s).const_sub frameCap)
    simpa only [mul_neg_one] using hh
  · intro s hs _
    linarith [actual_diagonal_comparison atH hθ hs]
  · intro s hs hint
    linarith [actual_interior_comparison atH hθ hs hint]

theorem original_negative_zero_le (atH : Bool) {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 frameCap) :
    Explicit.baseline .low a z 0+V R (Explicit.k .low (a+z)) (larger atH (a+z)) frameCap≤
      Explicit.baseline .low a z s+
        V R (Explicit.k .low (a+z)) (larger atH (a+z)) (frameCap-s) := by
  have hh := correction_negative_monotone atH hθ
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hs hs.1
  simp only [LowD.correction_zero,sub_zero,zero_add] at hh
  rw [LowD.baseline_correction .low a z hs]
  linarith

theorem q_le_m {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    Explicit.q .low θ z i≤Explicit.m .low θ z := by
  have hr := Explicit.low_ranges hθ
  have hm := Explicit.low_tilted hθ hz
  have hlm := hr.2.2.2.2.2.2.1.trans hm.1
  fin_cases i
  · change 1≤Explicit.m .low θ z
    linarith [hr.2.2.1]
  · exact hlm
  · change max (Explicit.l .low θ) (Explicit.m .low θ z)≤Explicit.m .low θ z
    exact max_le hlm le_rfl

theorem positive_allowance {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    -(109/200)*Explicit.m .low θ z*(frameCap-θ)≤Explicit.U .low θ z i (frameCap-θ) := by
  have hp := LowRanges.pairs hθ hz i
  have hP : frameCap-θ∈Icc 0 frameCap :=
    ⟨by norm_num [frameCap]; linarith [hθ.2],by linarith [hθ.1]⟩
  have hh := OrdinaryPositiveEnvelope.U_lower (Real.sqrt_nonneg qCap) radius_sq.le hp.1 hp.2.1 hp.2.2.1 hP
  have hscale := mul_le_mul_of_nonneg_right (q_le_m hθ hz i) hP.1
  change _≤Explicit.U .low θ z i (frameCap-θ) at hh
  nlinarith only [hh,hscale]

/-- Every separated original pair reduces to one of the two s=0
negative envelopes. The positive charge remains the actual tilted m. -/
theorem separated_lower {a z s : ℝ}
    (hθ : a+z∈Icc (0:ℝ) (1/6)) (hz : z∈Icc 0 (a+z))
    (hs : s∈Icc 0 frameCap) (i j : Fin 3) :
    ∃atH : Bool,
      Explicit.baseline .low a z 0-(109/200)*Explicit.m .low (a+z) z*(frameCap-(a+z))+
        V R (Explicit.k .low (a+z)) (larger atH (a+z)) frameCap≤
      Explicit.baseline .low a z s+Explicit.U .low (a+z) z i (frameCap-(a+z))+
        Explicit.V .low (a+z) z j (frameCap-s) := by
  have hu := positive_allowance hθ hz i
  have hH := original_negative_zero_le true hθ hs
  have hG := original_negative_zero_le false hθ hs
  fin_cases j
  · refine ⟨true,?_⟩
    simp only [Explicit.V,Explicit.p,Explicit.q,larger,if_true,Matrix.cons_val_zero] at hH ⊢
    linarith
  · refine ⟨false,?_⟩
    simp only [Explicit.V,Explicit.p,Explicit.q,larger,Bool.false_eq_true,if_false,
      Matrix.cons_val_succ,Matrix.cons_val_zero] at hG ⊢
    linarith
  · refine ⟨true,?_⟩
    have hB := LowNegative.B_dominates_H hθ hz
      (show frameCap-s∈Icc 0 frameCap from ⟨by linarith [hs.2],by linarith [hs.1]⟩)
    simp only [larger,if_true] at hH ⊢
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeDEPositiveTD.LowSeparated
