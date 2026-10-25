module

public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2HighSecant
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2OriginalStress
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Data
public import SquaresInCircles.Eight.Owners.GA.Negative.EHTD2Polynomial
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveHighTransfer
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveSplit

/-!
# Eight squares: the gain and circle-norm inputs of the negative-EH endpoints

The shifted ordinary angle is kept independent of the coefficient angle. The lower and upper
tilted coefficients are applied with the sign that each squared norm requires
(`far_tilted_bounds`). The EH multiplier and its constant support loss stay in the gain throughout.
-/

section
/-!
## The actual intrinsic E endpoints of the negative-DE stress

The low endpoint
keeps the sorted diagonal D support.  The high endpoint has its full D
norm, including the secant at s=theta.  All A/TD coefficients still depend
on their common total angle.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def lowBase (e : Split) (θ s : ℝ) : ℝ :=
  Explicit.baseline .low (Explicit.splitA e θ) (Explicit.splitT e θ) s
def highBase (e : Split) (θ s : ℝ) : ℝ :=
  Explicit.fullBaseline .high (Explicit.splitA e θ) (Explicit.splitT e θ) s

theorem split_sum (e : Split) (θ : ℝ) :
    Explicit.splitA e θ+Explicit.splitT e θ=θ := by cases e <;> simp [Explicit.splitA,Explicit.splitT]

theorem low_D_diagonal {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 θ) :
    Explicit.secant s≤Explicit.c .low θ := by
  have hc := (TwoPositive.Split.low_trig ⟨hs.1,hs.2.trans hθ.2⟩).1
  have hr := Explicit.low_ranges hθ
  have hcpos : 0<Real.cos s := by linarith
  apply (div_le_iff₀ hcpos).2
  have hh := mul_le_mul_of_nonneg_left hc
    (show 0≤Explicit.c .low θ by linarith [hr.2.2.2.2.1])
  nlinarith [hr.2.2.2.2.1]

theorem low_baseline_identity (e : Split) {θ s : ℝ}
    (hθ : θ∈Icc (0:ℝ) (1/6)) (hs : s∈Icc 0 θ) :
    lowBase e θ s=lowNonradical e θ-(GlobalGA.Secondary.diagonal-1/2)*(Explicit.secant s-1)+
      Explicit.K*Real.tan s-R*(pairNorm (Explicit.k .low θ) 1 0+
        pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0+
        pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  have hD := low_D_diagonal hθ hs
  simp only [lowBase,Explicit.baseline,split_sum,fullSupport_pair]
  rw [clippedSupport,ite_eq_left hD]
  dsimp [lowNonradical,diagonalSupport,Explicit.splitM]
  ring

theorem high_baseline_identity (e : Split) (θ s : ℝ) :
    highBase e θ s=highNonradical e θ+Explicit.secant s-1+Explicit.K*Real.tan s-
      R*(pairNorm (Explicit.k .high θ) 1 0+
        pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
        pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
        pairNorm (Explicit.secant s) (Explicit.c .high θ) 0) := by
  simp only [highBase,Explicit.fullBaseline,Explicit.baseline,split_sum,fullSupport_pair]
  rw [pairNorm_symm (Explicit.c .high θ) (Explicit.secant s) 0]
  dsimp [highNonradical,Explicit.splitM]
  ring

theorem low_H_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (x : ℝ) :
    lowBase e θ 0+V R (Explicit.k .low θ) 1 x=
      lowNonradical e θ+Real.cos x-1-
        R*(pairNorm (Explicit.k .low θ) 1 (-x)+
          pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0+
          pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  rw [low_baseline_identity e hθ ⟨le_rfl,hθ.1⟩]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,sub_zero,add_zero]
  dsimp [V]
  ring

theorem low_G_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) (x : ℝ) :
    lowBase e θ 0+V R (Explicit.k .low θ) (Explicit.l .low θ) x=
      lowNonradical e θ+Explicit.l .low θ*(Real.cos x-1)-
        R*(pairNorm (Explicit.k .low θ) 1 0+
          pairNorm (Explicit.k .low θ) (Explicit.l .low θ) (-x)+
          pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  rw [low_baseline_identity e hθ ⟨le_rfl,hθ.1⟩]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,sub_self,mul_zero,sub_zero,add_zero]
  dsimp [V]
  ring

theorem high_H_identity (e : Split) (θ : ℝ) :
    highBase e θ 0+V R (Explicit.k .high θ) 1 θ=
      highNonradical e θ+Real.cos θ-1-
        R*(pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
          pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
          pairNorm (Explicit.k .high θ) 1 (-θ)+pairNorm 1 (Explicit.c .high θ) 0) := by
  rw [high_baseline_identity]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,add_zero]
  dsimp [V]
  ring

theorem high_G_identity (e : Split) (θ : ℝ) :
    highBase e θ 0+V R (Explicit.k .high θ) (Explicit.l .high θ) θ=
      highNonradical e θ+Explicit.l .high θ*(Real.cos θ-1)-
        R*(pairNorm (Explicit.k .high θ) 1 0+
          pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
          pairNorm (Explicit.k .high θ) (Explicit.l .high θ) (-θ)+
          pairNorm 1 (Explicit.c .high θ) 0) := by
  rw [high_baseline_identity]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,add_zero]
  dsimp [V]
  ring

theorem high_B_identity (e : Split) (θ : ℝ) :
    highBase e θ 0+V R (min (Explicit.l .high θ) (Explicit.splitM .high e θ))
      (max (Explicit.l .high θ) (Explicit.splitM .high e θ)) θ=
      highNonradical e θ+max (Explicit.l .high θ) (Explicit.splitM .high e θ)*(Real.cos θ-1)-
        R*(pairNorm (Explicit.k .high θ) 1 0+
          pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
          pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) (-θ)+
          pairNorm 1 (Explicit.c .high θ) 0) := by
  rw [high_baseline_identity]
  simp only [Explicit.secant,Real.cos_zero,Real.tan_zero,div_one,mul_zero,add_zero,V,
    TwoPositive.Certificate.sorted_pair_norm]
  ring

theorem low_equal_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6)) :
    Real.cos θ*lowBase e θ θ=
      Real.cos θ*(lowNonradical e θ+(GlobalGA.Secondary.diagonal-1/2))+Explicit.K*Real.sin θ-(GlobalGA.Secondary.diagonal-1/2)-
        R*(Real.cos θ*pairNorm (Explicit.k .low θ) 1 0+
          Real.cos θ*pairNorm (Explicit.k .low θ) (Explicit.l .low θ) 0+
          Real.cos θ*pairNorm (Explicit.l .low θ) (Explicit.splitM .low e θ) 0) := by
  have hc : Real.cos θ≠0 := by
    have hf : θ∈Icc 0 frameCap := ⟨hθ.1,by simp only [frameCap]; linarith [hθ.2]⟩
    linarith [(transport_trig hf).1]
  rw [low_baseline_identity e hθ ⟨hθ.1,le_rfl⟩]
  dsimp [Explicit.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

theorem high_equal_identity (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10)) :
    Real.cos θ*highBase e θ θ=
      Real.cos θ*(highNonradical e θ-1)+1+Explicit.K*Real.sin θ-
        R*(Real.cos θ*pairNorm (Explicit.k .high θ) 1 0+
          Real.cos θ*pairNorm (Explicit.k .high θ) (Explicit.l .high θ) 0+
          Real.cos θ*pairNorm (Explicit.l .high θ) (Explicit.splitM .high e θ) 0+
          Real.cos θ*pairNorm (Explicit.secant θ) (Explicit.c .high θ) 0) := by
  have hc : Real.cos θ≠0 := by
    have hf : θ∈Icc 0 frameCap := ⟨by linarith [hθ.1],by simp only [frameCap]; linarith [hθ.2]⟩
    linarith [(transport_trig hf).1]
  rw [high_baseline_identity]
  dsimp [Explicit.secant]
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hc]
  ring

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveTD.Certificate
end
end
end

section
/-!
## The coefficient ranges for a negative EH1 with TD2

The small regime keeps the negative-DE families. The far regime uses its two linear families, with
the low `m` bound proved before any interval is enlarged (`far_low_ranges`). Every ratio holds for
every split.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Explicit
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
    (hθ : θ∈Icc (left r f) (right r f)) (_hz : z∈Icc 0 θ) :
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

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Explicit
end
end
end

section
@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PairNormCalculus
open PositiveTD.Certificate (S5 S9 S11 C4 C10 C12 taylor_bounds)

abbrev split_sum := NegativeDEPositiveTD.Certificate.split_sum
abbrev split_angles := @NegativeDEPositiveTD.Certificate.split_angles

theorem split_positive (r : Regime) (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left r f) (Explicit.right r f)) :
    0<Explicit.k r f θ ∧ 0<Explicit.l r f θ ∧
      0<Explicit.c r f θ ∧ 0<Explicit.splitM r f e θ := by
  apply Explicit.family_positive r f hθ
  exact (split_angles e (Explicit.family_frame_domain r f hθ)).2.1

theorem g_polynomial_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    aeval s gPoly≤NegativeEH.g s := by
  have ht := taylor_bounds hs
  have hsin := mul_le_mul_of_nonneg_left ht.2.1 (show (0:ℝ)≤13/12 by norm_num)
  have hcos := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 (show (0:ℝ)≤82/125 by norm_num)
  simp only [gPoly,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast]
  dsimp only [NegativeEH.g,NegativeEH.K,NegativeEH.beta,K,beta]
  push_cast
  linarith only [hsin,hcos]

theorem G_polynomial_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    aeval s GPoly≤NegativeEH.G s := by
  have hh := mul_le_mul_of_nonneg_left (g_polynomial_lower hs)
    (show (0:ℝ)≤201/200 by norm_num)
  simp only [GPoly,map_sub,map_mul,aeval_C,eq_ratCast]
  dsimp only [NegativeEH.G,NegativeEH.p,p]
  push_cast
  linarith

theorem g_constant_lower (s : ℚ) (hs : (s:ℝ)∈Icc 0 frameCap) :
    (gStar s:ℝ)≤NegativeEH.g (s:ℝ) := by
  have hh := g_polynomial_lower hs
  rw [NegativeDEPositiveTD.Certificate.eval_rat] at hh
  simpa [gStar,gPoly] using hh

theorem G_constant_lower (s : ℚ) (hs : (s:ℝ)∈Icc 0 frameCap) :
    (GStar s:ℝ)≤NegativeEH.G (s:ℝ) := by
  have hh := G_polynomial_lower hs
  rw [NegativeDEPositiveTD.Certificate.eval_rat] at hh
  simpa [GStar,GPoly,gStar,gPoly] using hh

theorem zero_norm_upper {p q qHi : ℝ} (_hp : 0<p) (hq : 0<q) (hhi : q≤qHi) :
    (pairNorm p q 0)^2≤p^2+qHi^2 := by
  have hh := PositiveTD.Certificate.zero_norm_sq p q
  rw [hh]
  have hsq := pow_le_pow_left₀ hq.le hhi 2
  linarith

theorem negative_norm_upper {p q qLo qHi t : ℝ}
    (hp : 0<p) (hq : 0<q) (_hlo0 : 0≤qLo) (hlo : qLo≤q) (hhi : q≤qHi)
    (ht : t∈Icc 0 frameCap) :
    (pairNorm p q (-t))^2≤p^2+qHi^2-2*p*qLo*aeval t S11 := by
  have hnorm := pairNorm_sq hp hq (show |-t|≤frameCap by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2)
  have htay := taylor_bounds ht
  have hprod := mul_le_mul hlo htay.2.1 htay.1 hq.le
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0≤2*p by positivity)
  have hsq := pow_le_pow_left₀ hq.le hhi 2
  simp only [pairEnergy,pairProduct,Real.sin_neg] at hnorm
  nlinarith only [hnorm,hscaled,hsq]

theorem positive_norm_upper {p q qHi t : ℝ}
    (hp : 0<p) (hq : 0<q) (hhi : q≤qHi) (ht : t∈Icc 0 frameCap) :
    (pairNorm p q t)^2≤p^2+qHi^2+2*p*qHi*aeval t S9 := by
  have hnorm := pairNorm_sq hp hq (by rw [abs_of_nonneg ht.1]; exact ht.2)
  have htay := taylor_bounds ht
  have hprod := mul_le_mul hhi htay.2.2.1 (transport_trig ht).2.2.1 (hq.le.trans hhi)
  have hscaled := mul_le_mul_of_nonneg_left hprod (show 0≤2*p by positivity)
  have hsq := pow_le_pow_left₀ hq.le hhi 2
  simp only [pairEnergy,pairProduct] at hnorm
  nlinarith only [hnorm,hscaled,hsq]

theorem far_tilted_bounds (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left .far f) (Explicit.right .far f)) :
    0<aeval θ (farMLo f e) ∧ aeval θ (farMLo f e)≤Explicit.splitM .far f e θ ∧
      Explicit.splitM .far f e θ≤aeval θ (farMHi f e) := by
  have hc := (split_positive .far f e hθ).2.2.1
  cases e
  · have hh := PositiveTD.Certificate.tilted_polynomial_bounds
      (c:=farC f) (Explicit.family_frame_domain .far f hθ) (by simpa using hc)
    simpa [farMLo,farMHi,Explicit.splitM,Explicit.splitT,Explicit.m,
      NegativeDEPositiveTD.Explicit.splitT,
      Explicit.eta,NegativeDEPositiveTD.Explicit.eta,PositiveTD.tilted,PositiveTD.eta,
      PositiveTD.Certificate.mMinus,PositiveTD.Certificate.mPlus] using hh
  · simpa [farMLo,farMHi,Explicit.splitM,Explicit.splitT,Explicit.m,
      NegativeDEPositiveTD.Explicit.splitT] using
      (show 0<Explicit.c .far f θ ∧ Explicit.c .far f θ≤Explicit.c .far f θ ∧
        Explicit.c .far f θ≤Explicit.c .far f θ from ⟨hc,le_rfl,le_rfl⟩)

theorem far_tilted_upper_simple (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left .far f) (Explicit.right .far f)) :
    Explicit.splitM .far f e θ≤aeval θ (farMu f e) := by
  have hc := (split_positive .far f e hθ).2.2.1
  have hf := Explicit.family_frame_domain .far f hθ
  cases e
  · have hs := sin_upper_five hf.1
    have hcos := cos_upper_four hf.1
    have hh := mul_le_mul_of_nonneg_left
      (show Real.cos θ+(293/1000)*Real.sin θ≤
        1-θ^2/2+θ^4/24+(293/1000)*(θ-θ^3/6+θ^5/120) by
          linarith) hc.le
    have hM : Explicit.splitM .far f .atT θ=
        Explicit.c .far f θ*(Real.cos θ+(293/1000)*Real.sin θ) := by
      simp [Explicit.splitM,Explicit.m,NegativeDEPositiveTD.Explicit.splitT,
        Explicit.eta,NegativeDEPositiveTD.Explicit.eta]
    have hU : aeval θ (farMu f .atT)=
        Explicit.c .far f θ*(1-θ^2/2+θ^4/24+(293/1000)*(θ-θ^3/6+θ^5/120)) := by
      simp only [farMu,C4,S5,map_mul,map_add,map_sub,map_one,map_pow,aeval_C,aeval_X,
        eq_ratCast,farC_eval,PositiveTD.Certificate.etaQ]
      push_cast
      ring
    rw [hM,hU]
    exact hh
  · simp [farMu,Explicit.splitM,Explicit.splitT,Explicit.m,NegativeDEPositiveTD.Explicit.splitT]

theorem far_qStar_lower (e : Split) {θ : ℝ} (hθ : θ∈Icc (1/4:ℝ) (7/10)) :
    max (Explicit.l .far .high θ) (Explicit.splitM .far .high e θ)≤aeval θ farQStar := by
  have hl : Explicit.l .far .high θ≤aeval θ farQStar := by
    simp only [farQStar,map_add,map_mul,map_sub,aeval_C,aeval_X,farL_eval]
    norm_num [PositiveTD.Certificate.h]
    linarith [hθ.2]
  apply max_le hl
  cases e
  · have hm := far_tilted_upper_simple .high .atT hθ
    have hq := far_qstar_T_positive hθ
    simp only [map_sub] at hq
    exact hm.trans (by linarith)
  · have hq := far_qstar_A_positive hθ
    simp only [map_sub,farC_eval] at hq
    simpa [Explicit.splitM,Explicit.splitT,Explicit.m,NegativeDEPositiveTD.Explicit.splitT]
      using (sub_pos.mp hq).le

theorem low_A_charge_quarter {a : ℝ} (ha : a∈Icc (0:ℝ) (1/4)) :
    aeval a J0≤TwoPositive.ASupport.charge a := by
  have hf : a∈Icc 0 frameCap := ⟨ha.1,by norm_num [frameCap]; linarith [ha.2]⟩
  have ht := taylor_bounds hf
  have hcut : a≤TwoPositive.ASupport.alpha := by linarith [ha.2,TwoPositive.ASupport.alpha_bounds.1]
  have hab := TwoPositive.ASupport.axial_le_abar
  have he : ((TwoPositive.Certificate.abar:ℚ):ℝ)=1414575672/1000000000 := by
    norm_num [TwoPositive.Certificate.abar]
  rw [he] at hab
  have h₂ := mul_le_mul_of_nonneg_right hab (transport_trig hf).2.2.1
  simp only [TwoPositive.ASupport.charge,hcut,↓reduceIte,TwoPositive.ASupport.axialCharge,
    J0,NegativeDEPositiveTD.Certificate.J0,map_add,map_mul,map_sub,map_one,aeval_C,eq_ratCast]
  push_cast
  linarith only [ht.2.2.2.2.1,ht.2.2.1,h₂]

def farBaseActual (f : Family) (e : Split) (θ : ℝ) : ℝ :=
  2*Explicit.k .far f θ+3*Explicit.l .far f θ+(3/2)*Explicit.splitM .far f e θ+
    Explicit.c .far f θ/2+3+Explicit.c .far f θ*edgeWidth (Explicit.splitT e θ)-
    Explicit.c .far f θ*Explicit.sigma*Real.sin (Explicit.splitT e θ)+
    Explicit.l .far f θ*TwoPositive.ASupport.charge (Explicit.splitA e θ)

theorem far_nonradical_lower (f : Family) (e : Split) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left .far f) (Explicit.right .far f)) :
    aeval θ (farB f e)≤farBaseActual f e θ := by
  obtain ⟨hk,hl,hc,hm⟩ := split_positive .far f e hθ
  have hf := Explicit.family_frame_domain .far f hθ
  have ht := taylor_bounds hf
  cases e
  · have htilt := (far_tilted_bounds f .atT hθ).2.1
    have hs := PositiveTD.Certificate.sigma_sine_upper hf hc.le
    have hW0 := mul_le_mul_of_nonneg_left (add_le_add ht.2.2.2.2.1 ht.2.1) hc.le
    have hW : Explicit.c .far f θ/2*(1+aeval θ C10+aeval θ S11)≤
        Explicit.c .far f θ*edgeWidth θ := by
      rw [edgeWidth_positive_formula hf]
      nlinarith only [hW0]
    have hj : TwoPositive.ASupport.charge 0=0 := by
      rw [TwoPositive.ASupport.charge_low (by norm_num)]
      norm_num [TwoPositive.ASupport.axialCharge]
    have hsig : Explicit.sigma=PositiveTD.sigma := by
      simp [NegativeDEPositiveTD.Explicit.sigma,PositiveTD.sigma,NegativeDEPositiveTD.Explicit.eta]
    have hsb : ((PositiveTD.Certificate.sigmabar:ℚ):ℝ)=1415477291/1000000000 := by
      norm_num [PositiveTD.Certificate.sigmabar]
    rw [hsb] at hs
    simp only [farB,map_add,map_sub,map_mul,map_one,aeval_C,eq_ratCast,farK_eval,farL_eval,
      farC_eval]
    simp only [farBaseActual,Explicit.splitA,Explicit.splitT,NegativeDEPositiveTD.Explicit.splitA,
      NegativeDEPositiveTD.Explicit.splitT,hj,mul_zero,add_zero,hsig]
    push_cast
    linarith only [htilt,hs,hW]
  · have hJ : aeval θ (if f=.low then J0 else J1)≤TwoPositive.ASupport.charge θ := by
      cases f
      · exact low_A_charge_quarter hθ
      · have h1 := hθ.1
        simp only [Explicit.left,Explicit.u] at h1
        exact NegativeDEPositiveTD.AEnvelope.high_polynomial_charge
          ⟨by linarith,hf.2⟩
    have hJscaled := mul_le_mul_of_nonneg_left hJ hl.le
    have hW : edgeWidth 0=1 := by norm_num [edgeWidth,pairWidth]
    simp only [farB,map_add,map_mul,aeval_C,eq_ratCast,farK_eval,farL_eval,
      farC_eval]
    simp only [farBaseActual,Explicit.splitA,Explicit.splitT,Explicit.splitM,Explicit.m,
      NegativeDEPositiveTD.Explicit.splitA,NegativeDEPositiveTD.Explicit.splitT,
      Real.cos_zero,Real.sin_zero,mul_zero,mul_one,add_zero,sub_zero,hW]
    push_cast
    linarith only [hJscaled]

theorem far_baseline_identity (f : Family) (e : Split) (θ : ℝ) :
    Explicit.baseline .far f (Explicit.splitA e θ) (Explicit.splitT e θ)=farBaseActual f e θ-
      R*(pairNorm (Explicit.k .far f θ) 1 0+
        pairNorm (Explicit.k .far f θ) (Explicit.l .far f θ) 0+
        pairNorm (Explicit.l .far f θ) (Explicit.splitM .far f e θ) 0+
        pairNorm 1 (Explicit.c .far f θ) 0) := by
  simp only [Explicit.baseline,split_sum,Explicit.sortedD,Bool.false_eq_true,ite_false,fullSupport_pair]
  rw [pairNorm_symm (Explicit.c .far f θ) 1 0]
  dsimp [farBaseActual,Explicit.splitM]
  ring

end SquaresInCircles.Eight.GlobalGA.NegativeEHPositiveTD.Certificate
end
end
end
