module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeEHTD2Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2LowRanges
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeDETD2Source

/-!
# Original coefficient ranges for genuine negative EH1 with TD2

Uncompiled whole-interval ranges from the two EH companions. The small
regime retains the original negative-DE families. The far regime uses
the two prescribed linear families, with its low m bound proved before
any interval is enlarged. Every ratio is proved for every original split.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Explicit
open Candidate Secondary PositiveAngularEnvelope

theorem small_low_ratio {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    k .small .low θ<(17/25)*l .small .low θ := by
  let x : ℝ := 1/6-θ
  have hx : x∈Icc (0:ℝ) (1/6) := ⟨by dsimp [x]; linarith [hθ.2],by dsimp [x]; linarith [hθ.1]⟩
  have hx2 : x^2≤x/6 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have he : (17/25)*l .small .low θ-k .small .low θ=
      3541/250000+(653/500)*x-(313/125)*x^2 := by
    dsimp [k,l,NegativeDEPositiveTD.Explicit.k,NegativeDEPositiveTD.Explicit.l,
      NegativeDEPositiveTD.Explicit.L,x]
    ring
  have hh : 0<(17/25)*l .small .low θ-k .small .low θ := by nlinarith
  exact sub_pos.mp hh

theorem short_factor {z : ℝ} (hz : z∈Icc (0:ℝ) (1/4)) :
    1≤Real.cos z+eta*Real.sin z ∧ Real.cos z+eta*Real.sin z≤1+eta*z := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=z)
  have hsin := Real.sin_ge_sub_cube hz.1
  have hprod : 0≤z*((293/1000:ℝ)-z/2-(293/6000)*z^2) := by
    apply mul_nonneg hz.1
    nlinarith [hz.2,hz.1]
  have hupper := mul_le_mul_of_nonneg_left (Real.sin_le hz.1)
    (show (0:ℝ)≤eta by norm_num [eta,NegativeDEPositiveTD.Explicit.eta])
  dsimp [eta,NegativeDEPositiveTD.Explicit.eta] at hupper ⊢
  exact ⟨by nlinarith,by linarith [Real.cos_le_one z]⟩

theorem far_low_ranges {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) :
    k .far .low θ=121/200 ∧ l .far .low θ∈Icc (91/100:ℝ) 1 ∧
    c .far .low θ∈Icc (367/400:ℝ) (111/100) ∧
    l .far .low θ<c .far .low θ := by
  refine ⟨rfl,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩ <;> simp only [l,c] <;> linarith [hθ.1,hθ.2]

theorem far_low_tilted {θ z : ℝ} (hθ : θ∈Icc (0:ℝ) (1/4)) (hz : z∈Icc 0 θ) :
    c .far .low θ≤ m .far .low θ z ∧ m .far .low θ z≤111/100 ∧
    l .far .low θ< m .far .low θ z ∧ m .far .low θ z<(117/100)*l .far .low θ := by
  have hr := far_low_ranges hθ
  have hc : 0<c .far .low θ := by linarith [hr.2.2.1.1]
  have hf := short_factor (show z∈Icc (0:ℝ) (1/4) from ⟨hz.1,hz.2.trans hθ.2⟩)
  have hlo := mul_le_mul_of_nonneg_left hf.1 hc.le
  have hhi := mul_le_mul_of_nonneg_left hf.2 hc.le
  have hθfactor := mul_le_mul_of_nonneg_left hz.2
    (show 0≤c .far .low θ*eta by dsimp [eta,NegativeDEPositiveTD.Explicit.eta]; positivity)
  have hlow : c .far .low θ≤ m .far .low θ z := by simpa [m] using hlo
  have hupper : m .far .low θ z≤c .far .low θ*(1+eta*θ) := by
    dsimp [m]
    nlinarith only [hhi,hθfactor]
  refine ⟨hlow,?_,hr.2.2.2.trans_le hlow,?_⟩
  · dsimp [c,eta,NegativeDEPositiveTD.Explicit.eta] at hupper
    nlinarith [hθ.1,sq_nonneg θ]
  · dsimp [c,l,eta,NegativeDEPositiveTD.Explicit.eta] at hupper ⊢
    nlinarith [hθ.1,sq_nonneg θ]

theorem far_high_ranges {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    k .far .high θ∈Icc (121/200:ℝ) (157/200) ∧
    l .far .high θ∈Icc (1667/2000:ℝ) (91/100) ∧
    c .far .high θ∈Icc (8329/10000:ℝ) (367/400) ∧
    (99/100)*l .far .high θ<c .far .high θ ∧
    c .far .high θ<(101/100)*l .far .high θ := by
  simp only [k,l,c]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,?_,?_⟩ <;> linarith [hθ.1,hθ.2]

theorem far_high_tilted {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) (hz : z∈Icc 0 θ) :
    (19/20)*c .far .high θ< m .far .high θ z ∧
    m .far .high θ z<(1043/1000)*c .far .high θ ∧
    k .far .high θ< min (l .far .high θ) (m .far .high θ z) ∧
    max (l .far .high θ) (m .far .high θ z)<1 ∧
    m .far .high θ z<(23/20)*l .far .high θ := by
  have hr := far_high_ranges hθ
  have hc : 0<c .far .high θ := by linarith [hr.2.2.1.1]
  have hz' : z∈Icc 0 frameCap := ⟨hz.1,by norm_num [frameCap]; linarith [hz.2,hθ.2]⟩
  have hlo := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_lower hz') hc
  have hhi := mul_lt_mul_of_pos_left (PositiveTD.Explicit.factor_upper z) hc
  have hlow : (19/20)*c .far .high θ< m .far .high θ z := by
    simpa [m,eta,NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta,mul_comm] using hlo
  have hupper : m .far .high θ z<(1043/1000)*c .far .high θ := by
    simpa [m,eta,NegativeDEPositiveTD.Explicit.eta,PositiveTD.eta,mul_comm] using hhi
  refine ⟨hlow,hupper,lt_min ?_ ?_,max_lt ?_ ?_,?_⟩ <;>
    nlinarith [hr.1.1,hr.1.2,hr.2.1.1,hr.2.1.2,hr.2.2.1.1,
      hr.2.2.1.2,hr.2.2.2.1,hr.2.2.2.2]

private theorem r78_small_domain (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (left .small f) (right .small f)) :
    θ∈Icc (NegativeDEPositiveTD.Explicit.left f) (NegativeDEPositiveTD.Explicit.right f) := by
  cases f <;> simpa [left,right,L,NegativeDEPositiveTD.Explicit.left,
    NegativeDEPositiveTD.Explicit.right,NegativeDEPositiveTD.Explicit.L] using hθ

theorem family_positive (r : Regime) (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left r f) (right r f)) (hz : z∈Icc 0 θ) :
    0<k r f θ ∧ 0<l r f θ ∧ 0<c r f θ ∧ 0< m r f θ z := by
  cases r
  · exact NegativeDEPositiveTD.Explicit.family_positive f (r78_small_domain f hθ) hz
  · cases f
    · have hr := far_low_ranges hθ
      have hm := far_low_tilted hθ hz
      refine ⟨?_,?_,?_,?_⟩
      · norm_num [k]
      · linarith [hr.2.1.1]
      · linarith [hr.2.2.1.1]
      · linarith [hr.2.2.1.1,hm.1]
    · have hr := far_high_ranges hθ
      have hm := far_high_tilted hθ hz
      refine ⟨?_,?_,?_,?_⟩
      · linarith [hr.1.1]
      · linarith [hr.2.1.1]
      · linarith [hr.2.2.1.1]
      · linarith [hr.1.1,(lt_min_iff.mp hm.2.2.1).2]

theorem far_pairs (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left .far f) (right .far f)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    (3/5:ℝ)≤p .far f θ z i ∧ p .far f θ z i≤q .far f θ z i ∧
      q .far f θ z i≤(5/3)*p .far f θ z i := by
  cases f
  · have hr := far_low_ranges hθ
    have hm := far_low_tilted hθ hz
    have hk : k .far .low θ=121/200 := hr.1
    fin_cases i
    · change (3/5:ℝ)≤k .far .low θ ∧ k .far .low θ≤1 ∧ 1≤(5/3)*k .far .low θ
      rw [hk]; norm_num
    · change (3/5:ℝ)≤k .far .low θ ∧ k .far .low θ≤l .far .low θ ∧
        l .far .low θ≤(5/3)*k .far .low θ
      rw [hk]
      exact ⟨by norm_num,by linarith [hr.2.1.1],by linarith [hr.2.1.2]⟩
    · change (3/5:ℝ)≤ min (l .far .low θ) (m .far .low θ z) ∧
        min (l .far .low θ) (m .far .low θ z)≤ max (l .far .low θ) (m .far .low θ z) ∧
        max (l .far .low θ) (m .far .low θ z)≤(5/3)*min (l .far .low θ) (m .far .low θ z)
      rw [min_eq_left hm.2.2.1.le,max_eq_right hm.2.2.1.le]
      exact ⟨by linarith [hr.2.1.1],hm.2.2.1.le,by linarith [hm.2.2.2,hr.2.1.1]⟩
  · have hr := far_high_ranges hθ
    have hm := far_high_tilted hθ hz
    have hsmall : k .far .high θ≤ min (l .far .high θ) (m .far .high θ z) := hm.2.2.1.le
    fin_cases i
    · change (3/5:ℝ)≤k .far .high θ ∧ k .far .high θ≤1 ∧ 1≤(5/3)*k .far .high θ
      exact ⟨by linarith [hr.1.1],by linarith [hr.1.2],by linarith [hr.1.1]⟩
    · change (3/5:ℝ)≤k .far .high θ ∧ k .far .high θ≤l .far .high θ ∧
        l .far .high θ≤(5/3)*k .far .high θ
      exact ⟨by linarith [hr.1.1],hsmall.trans (min_le_left _ _),by linarith [hr.1.1,hr.2.1.2]⟩
    · change (3/5:ℝ)≤ min (l .far .high θ) (m .far .high θ z) ∧
        min (l .far .high θ) (m .far .high θ z)≤ max (l .far .high θ) (m .far .high θ z) ∧
        max (l .far .high θ) (m .far .high θ z)≤(5/3)*min (l .far .high θ) (m .far .high θ z)
      have hmax : max (l .far .high θ) (m .far .high θ z)<1 := hm.2.2.2.1
      exact ⟨by linarith [hr.1.1],min_le_max,by linarith [hr.1.1]⟩

theorem family_pairs (r : Regime) (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left r f) (right r f)) (hz : z∈Icc 0 θ) (i : Fin 3) :
    0<p r f θ z i ∧ p r f θ z i≤q r f θ z i ∧ q r f θ z i≤2*p r f θ z i := by
  cases r
  · exact (NegativeDEPositiveTD.Source.family_coefficients f (r78_small_domain f hθ) hz).2.2 i
  · have hh := far_pairs f hθ hz i
    exact ⟨by linarith [hh.1],hh.2.1,by linarith [hh.1,hh.2.2]⟩

theorem source_coefficients (r : Regime) (f : Family) {θ z : ℝ}
    (hθ : θ∈Icc (left r f) (right r f)) (hz : z∈Icc 0 θ) :
    k r f θ∈Icc (1/2:ℝ) (17/20) ∧ k r f θ≤l r f θ ∧
      k r f θ≤c r f θ ∧ c r f θ≤2 := by
  cases r
  · cases f
    · have hr := NegativeDEPositiveTD.Explicit.low_ranges hθ
      simp only [k,l,c]
      exact ⟨⟨by linarith [hr.1],by linarith [hr.2.1]⟩,
        by linarith [hr.2.1,hr.2.2.1],by linarith [hr.2.1,hr.2.2.2.2.1],
        by linarith [hr.2.2.2.2.2.1]⟩
    · have hr := NegativeDEPositiveTD.Explicit.high_ranges hθ
      simp only [k,l,c]
      exact ⟨⟨by linarith [hr.1],by linarith [hr.2.1]⟩,
        by linarith [hr.2.1,hr.2.2.1],by linarith [hr.2.1,hr.2.2.2.2.1],
        by linarith [hr.2.2.2.2.2.1]⟩
  · cases f
    · have hr := far_low_ranges hθ
      refine ⟨?_,?_,?_,?_⟩
      · norm_num [k]
      · change (121/200:ℝ)≤l .far .low θ; linarith [hr.2.1.1]
      · change (121/200:ℝ)≤c .far .low θ; linarith [hr.2.2.1.1]
      · linarith [hr.2.2.1.2]
    · have hr := far_high_ranges hθ
      exact ⟨⟨by linarith [hr.1.1],by linarith [hr.1.2]⟩,
        by linarith [hr.1.2,hr.2.1.1],by linarith [hr.1.2,hr.2.2.1.1],by linarith [hr.2.2.1.2]⟩

theorem far_k_domain (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (left .far f) (right .far f)) : k .far f θ∈Icc (3/5:ℝ) (4/5) := by
  cases f
  · norm_num [k]
  · have hr := (far_high_ranges hθ).1
    exact ⟨by linarith [hr.1],by linarith [hr.2]⟩

theorem far_high_q_le_one {θ z : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10))
    (hz : z∈Icc 0 θ) (i : Fin 3) : q .far .high θ z i≤1 := by
  have hr := far_high_ranges hθ
  have hm := far_high_tilted hθ hz
  fin_cases i
  · exact le_rfl
  · exact hr.2.1.2.trans (by norm_num)
  · exact hm.2.2.2.1.le

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeEHPositiveTD.Explicit
