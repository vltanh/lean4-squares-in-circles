import SquaresInCircles.Six.Analytic.FixedVertexMinorant
import SquaresInCircles.Six.Analytic.PairSharpConstants
import SquaresInCircles.Six.Analytic.FixedPair
import SquaresInCircles.Six.Stress.DiagonalRemainder

/-!
# The diagonal vertex branch for the new fixed-pair line

The pair line contributes 23 Z/100 - 98 beta/100. The new minorant proves
this expression positive on the genuine vertex branch, using the exact
candidate algebra to sharpen only the radius and cap-radius constants.
The rectangle/angle domain remains explicit: this is not its classification.
-/

noncomputable section
namespace SquaresInCircles.Six.Analytic.FixedPair
open Stress Normalization

lemma line_sum (w s : ℝ) :
    line w+line (-s)=(23/100)*(|w|+|s|)-(98/100)*diagonalBeta w s := by
  have hw : line w=(23/100)*|w|-(49/100)*w := by
    by_cases h : 0≤w
    · rw [line,max_eq_right (by linarith),max_eq_left h,abs_of_nonneg h]
      ring
    · have h' : w≤0 := (lt_of_not_ge h).le
      rw [line,max_eq_left (by linarith),max_eq_right h',abs_of_nonpos h']
      ring
  have hs : line (-s)=(23/100)*|s|+(49/100)*s := by
    by_cases h : 0≤s
    · rw [line,neg_neg,max_eq_left h,max_eq_right (by linarith),abs_of_nonneg h]
      ring
    · have h' : s≤0 := (lt_of_not_ge h).le
      rw [line,neg_neg,max_eq_right h',max_eq_left (by linarith),abs_of_nonpos h']
      ring
  rw [hw,hs]
  dsimp [diagonalBeta]
  ring

private lemma fixed_vertex_expression_positive {K R rho x b t : ℝ}
    (hKlo : 5/4≤K) (hKhi : K≤253/200)
    (hRlo : 8/5≤R) (hRhi : R≤8443/5000) (hrho : 1391/1250≤rho)
    (hx : 0≤x) (hdiamond : x+|b|≤11/25)
    (ht : 29/100≤t ∧ t≤2/7+x) :
    0<(46/100)*max x |b|-(98/100)*b+
      K*((3*Real.cos b-Real.sin b)*Real.cos t/2+
        (Real.cos b-Real.sin b)*Real.sin t/2-
        R*(Real.cos b-Real.sin b)+rho-1) := by
  let A := (3/2)*Real.cos t+(1/2)*Real.sin t-R
  let B := R-(Real.cos t+Real.sin t)/2
  let y := |b|
  let M := max x y
  have hK0 : 0<K := by linarith
  have hy0 : 0≤y := abs_nonneg b
  have hy1 : y≤1/2 := by dsimp [y]; linarith
  have hM0 : 0≤M := hx.trans (le_max_left x y)
  have hwidth : Real.cos t+Real.sin t≤3/2 := by
    nlinarith [Real.sin_sq_add_cos_sq t,sq_nonneg (Real.cos t-Real.sin t)]
  have hweighted : (3/2)*Real.cos t+(1/2)*Real.sin t≤8/5 := by
    have hc := sq_nonneg (Real.cos t-3*Real.sin t)
    by_contra! hh
    have hp := mul_pos
      (show 0<3*Real.cos t+Real.sin t-16/5 by linarith)
      (show 0<3*Real.cos t+Real.sin t+16/5 by linarith)
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hA : A≤0 := by dsimp [A]; linarith
  have hB : 17/20≤B := by dsimp [B]; linarith
  have hKB : 17/16≤K*B := by
    have hp := mul_le_mul hKlo hB (by norm_num : (0:ℝ)≤17/20) hK0.le
    nlinarith only [hp]
  have hKB0 : 0≤K*B := by linarith
  have hcos : A≤A*Real.cos b := by
    simpa only [mul_one] using mul_le_mul_of_nonpos_left (Real.cos_le_one b) hA
  have hKcos := mul_le_mul_of_nonneg_left hcos hK0.le
  have hsin : (98/100)*y-K*B*y≤-(98/100)*b+K*B*Real.sin b := by
    by_cases hb : b≤0
    · have hs := Real.sin_le (show 0≤-b by linarith)
      rw [Real.sin_neg] at hs
      have hp := mul_le_mul_of_nonneg_left (show b≤Real.sin b by linarith) hKB0
      dsimp [y]
      rw [abs_of_nonpos hb]
      nlinarith only [hp]
    · have hb0 : 0≤b := (lt_of_not_ge hb).le
      have hb1 : b≤1/2 := by simpa [y,abs_of_nonneg hb0] using hy1
      have hsq := mul_nonneg (sub_nonneg.mpr hb1) (show 0≤1/2+b by linarith)
      have hcube := mul_nonneg hb0 (show 0≤1/4-b^2 by nlinarith)
      have hs := Real.sin_ge_sub_cube hb0
      have hsum : (47/24)*b≤Real.sin b+b := by nlinarith only [hcube,hs]
      have hp := mul_le_mul hKB hsum (show 0≤(47/24)*b by positivity) hKB0
      dsimp [y]
      rw [abs_of_nonneg hb0]
      nlinarith only [hp,hb0]
  have htrig : (46/100)*M+(98/100)*y+K*(A-B*y+rho-1)≤
      (46/100)*M-(98/100)*b+K*(A*Real.cos b+B*Real.sin b+rho-1) := by
    nlinarith only [hKcos,hsin]
  have hM := mul_nonneg (show 0≤46/100-(9/25)*K by linarith) hM0
  have hY := mul_nonneg (show 0≤98/100-(77/100)*K by linarith) hy0
  have hRad := mul_nonneg hK0.le
    (mul_nonneg (sub_nonneg.mpr hRhi) (show 0≤1+y by linarith))
  have hRho := mul_nonneg hK0.le (sub_nonneg.mpr hrho)
  have hid : (46/100)*M+(98/100)*y+K*(A-B*y+rho-1)-
      K*fixedVertexMinorant x y t =
      (46/100-(9/25)*K)*M+(98/100-(77/100)*K)*y+
      K*(8443/5000-R)*(1+y)+K*(rho-1391/1250) := by
    dsimp [A,B,M,fixedVertexMinorant]
    ring
  have hminorant : K*fixedVertexMinorant x y t≤
      (46/100)*M+(98/100)*y+K*(A-B*y+rho-1) := by
    nlinarith only [hid,hM,hY,hRad,hRho]
  have hpos := mul_pos hK0 (fixedVertexMinorant_positive hx hy0 hdiamond ht)
  have hresult := hpos.trans_le (hminorant.trans htrig)
  have he : (3*Real.cos b-Real.sin b)*Real.cos t/2+
      (Real.cos b-Real.sin b)*Real.sin t/2-R*(Real.cos b-Real.sin b)+rho-1=
      A*Real.cos b+B*Real.sin b+rho-1 := by dsimp [A,B]; ring
  rw [he]
  exact hresult

private lemma fixed_diamond {w s d : ℝ} (hd : DiagonalDomain w s d) :
    |(w+s)/2|+|diagonalBeta w s|≤11/25 := by
  let a := (w+s)/2
  let b := diagonalBeta w s
  have hw : a+b=w := by dsimp [a,b,diagonalBeta]; ring
  have hs : a-b=s := by dsimp [a,b,diagonalBeta]; ring
  change |a|+|b|≤11/25
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha,abs_of_nonneg hb]
    linarith [hd.1.2]
  · rw [abs_of_nonneg ha,abs_of_neg hb]
    linarith [hd.2.1.2]
  · rw [abs_of_neg ha,abs_of_nonneg hb]
    linarith [hd.2.1.1]
  · rw [abs_of_neg ha,abs_of_neg hb]
    linarith [hd.1.1]

private lemma fixed_max_bound (w s : ℝ) :
    2*max |(w+s)/2| |diagonalBeta w s|≤|w|+|s| := by
  have ha := abs_add_le w s
  have hb := abs_sub_le w s
  have he : w+s=2*((w+s)/2) := by ring
  have hf : w-s=2*diagonalBeta w s := by dsimp [diagonalBeta]; ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  rw [hf,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
  by_cases h : |(w+s)/2|≤|diagonalBeta w s|
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left (le_of_not_ge h)]; exact ha

/-- The actual vertex contribution absorbs the changed pair-line coefficients. -/
theorem fixed_diagonal_vertex_positive {w s d : ℝ} (hd : DiagonalDomain w s d)
    (hv : 1≤2*Six.radius*|Real.sin (diagonalDelta w s d)|) :
    0<line w+line (-s)+diagonalVertex w s d+2*pairBase := by
  let a := (w+s)/2
  let b := diagonalBeta w s
  let z := diagonalDelta w s d
  let x := |a|
  let t := |z|
  have hdiamond : x+|b|≤11/25 := fixed_diamond hd
  have hR := pair_radius_sharp_bounds
  have hK := diagonal_scale_bounds
  have hsin := abs_sin_le_abs_value z
  have hprod := mul_le_mul hR.2.le hsin (abs_nonneg (Real.sin z))
    (by norm_num : (0:ℝ)≤16885431/10000000)
  have htlo : 29/100≤t := by
    change 1≤2*Six.radius*|Real.sin z| at hv
    dsimp [t]
    nlinarith only [hv,hprod]
  have htriangle := abs_sub_le (d-Real.pi/4) a
  have hsign : d-Real.pi/4≤0 := by linarith [hd.2.2.2]
  rw [abs_of_nonpos hsign] at htriangle
  have hpi : Real.pi<(22:ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hthi : t≤2/7+x := by
    change |d-Real.pi/4-a|≤2/7+|a|
    linarith [hd.2.2.1]
  have hp := fixed_vertex_expression_positive
    (K := diagonalK) (R := Six.radius) (rho := rhoStar) (x := x) (b := b) (t := t)
    (by dsimp [diagonalK]; linarith [hK.1])
    (by simpa only [diagonalK] using hK.2.le)
    (by linarith [hR.1]) (by linarith [hR.2])
    (by linarith [pair_rho_sharp_bounds.1]) (abs_nonneg a) hdiamond ⟨htlo,hthi⟩
  have hzpi : |z|≤Real.pi := by
    have hh := (diagonal_parameters hd).2.1
    change |z|≤71/100 at hh
    linarith [Real.pi_gt_d2]
  dsimp [t] at hp
  rw [Real.cos_abs,sin_abs_angle hzpi] at hp
  have hsum : 2*max x |b|≤|w|+|s| := fixed_max_bound w s
  have hid : line w+line (-s)+diagonalVertex w s d+2*pairBase=
      (23/100)*(|w|+|s|)-(98/100)*b+
      diagonalK*((3*Real.cos b-Real.sin b)*Real.cos z/2+
        (Real.cos b-Real.sin b)*|Real.sin z|/2-
        Six.radius*(Real.cos b-Real.sin b)+rhoStar-1) := by
    rw [line_sum,pairBase_eq_diagonal_scale]
    dsimp [diagonalVertex,b,z,diagonalBeta]
    ring
  rw [hid]
  nlinarith only [hp,hsum]

end SquaresInCircles.Six.Analytic.FixedPair
