module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2GainComparison
public import SquaresInCircles.Eight.Owners.GA.Secant.DSingleData

/-!
# Eight squares: monotonicity in the actual negative-DE secant coefficient

The selected primary
coordinate decreases with the force ratio. The two explicit support
branches are joined at their exact equality values, including ties.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.SecantD
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity PositiveBT3
open NegativeAPositiveTD.SecantCoordinate

def fullSlope (f g : ℝ) : ℝ := R*f/Real.sqrt (f^2+g^2)-1/2

theorem fullSupport_hasDerivAt_first {x g : ℝ} (hg : 0<g) :
    HasDerivAt (fun v => fullSupport v g) (fullSlope x g) x := by
  have hn : HasDerivAt (fun v : ℝ => Real.sqrt (v^2+g^2))
      (x/Real.sqrt (x^2+g^2)) x := by
    have h := radical_hasDerivAt (A:=g^2) (x:=x) (sq_pos_of_pos hg)
    convert h using 1
    · funext v; simp only [radical,add_comm]
    · simp only [radical,add_comm]
  have h2 := (hn.const_mul R).sub (((hasDerivAt_id' x).add_const g).div_const 2)
  convert h2 using 1
  · funext v; simp only [fullSupport,Pi.sub_apply]
  · simp only [fullSlope]; ring

theorem fullSupport_hasDerivAt_shift {x c n : ℝ} (hc : 0<c)
    (hn : n∈Icc 0 frameCap) :
    HasDerivAt (fun v => fullSupport (v-c*Real.sin n) (c*Real.cos n))
      (fullSlope (x-c*Real.sin n) (c*Real.cos n)) x := by
  have hg : 0<c*Real.cos n := mul_pos hc (by linarith [(transport_trig hn).1])
  have h := (fullSupport_hasDerivAt_first (x:=x-c*Real.sin n) hg).comp x
    ((hasDerivAt_id' x).sub_const (c*Real.sin n))
  rw [mul_one] at h
  exact h

/-- On the whole angle interval the half-angle ratio is below one half. -/
theorem half_ratio {n : ℝ} (hn : n∈Icc 0 frameCap) :
    2*(1-Real.cos n)≤Real.sin n := by
  have ht := transport_trig hn
  have hfactor : 0≤Real.cos n-(3/4)*Real.sin n := by
    linarith [ht.1,ht.2.2.2.1]
  have hm := mul_nonneg ht.2.2.1 hfactor
  have hp : 0≤Real.cos n+Real.sin n/2 := by linarith [ht.1,ht.2.2.1]
  have hsq : 1≤(Real.cos n+Real.sin n/2)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq n]
  nlinarith

theorem negative_ratio_order {x c n : ℝ} (_hx : 0≤x) (hc : 0≤c)
    (hxc : x≤2*c) (hn : n∈Icc 0 frameCap) :
    (x-c*Real.sin n)*c≤x*(c*Real.cos n) := by
  have hs := (transport_trig hn).2.2.1
  have hh := half_ratio hn
  have hcos : 0≤1-Real.cos n := sub_nonneg.mpr (Real.cos_le_one n)
  have h₁ := mul_le_mul_of_nonneg_right hxc hcos
  have h₂ := mul_le_mul_of_nonneg_left hh hc
  have h₃ := mul_nonneg hc (show 0≤c*Real.sin n-x*(1-Real.cos n) by linarith)
  nlinarith

/-- Comparison of the selected primary coordinates on two full-circle
branches. Positive squaring preserves the weak force-ratio ordering. -/
theorem fullSlope_ratio {f g x c : ℝ} (hf : 0<f) (hg : 0<g)
    (hx : 0<x) (hc : 0<c) (hratio : f*c≤x*g) :
    fullSlope f g≤fullSlope x c := by
  let N := Real.sqrt (f^2+g^2)
  let M := Real.sqrt (x^2+c^2)
  have hN : 0<N := Real.sqrt_pos.mpr (by positivity)
  have hM : 0<M := Real.sqrt_pos.mpr (by positivity)
  have hN2 : N^2=f^2+g^2 := Real.sq_sqrt (by positivity)
  have hM2 : M^2=x^2+c^2 := Real.sq_sqrt (by positivity)
  have hprod := mul_nonneg (sub_nonneg.mpr hratio)
    (show 0≤x*g+f*c by positivity)
  have hid : (x*N)^2-(f*M)^2=(x*g-f*c)*(x*g+f*c) := by
    rw [mul_pow,mul_pow,hN2,hM2]
    ring
  have hcross : f*M≤x*N := by
    rw [←hid] at hprod
    nlinarith [mul_pos hf hM,mul_pos hx hN]
  have hfrac : f/N≤x/M := (div_le_div_iff₀ hN hM).2 hcross
  have hh := mul_le_mul_of_nonneg_left hfrac (Real.sqrt_nonneg qCap)
  dsimp [fullSlope,N,M] at *
  simpa only [mul_div_assoc] using sub_le_sub_right hh (1/2)

theorem fullSlope_below_diagonal {f g : ℝ} (hf : 0<f) (hg : 0<g)
    (hfg : f≤g) : fullSlope f g≤GlobalGA.Secondary.diagonal := by
  have hN : 0<Real.sqrt (f^2+g^2) := Real.sqrt_pos.mpr (by positivity)
  have hN2 := Real.sq_sqrt (show 0≤f^2+g^2 by positivity)
  have h2 : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h22 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hcross : f*Real.sqrt 2≤Real.sqrt (f^2+g^2) := by
    nlinarith [mul_nonneg hf.le h2.le,sq_nonneg (g-f)]
  have hfrac : f/Real.sqrt (f^2+g^2)≤1/Real.sqrt 2 :=
    (div_le_div_iff₀ hN h2).2 (by simpa using hcross)
  have hh := mul_le_mul_of_nonneg_left hfrac (Real.sqrt_nonneg qCap)
  rw [mul_one_div] at hh
  rw [←JointNegativeAETD2.diagonal_radius] at hh
  have hh' : R*f/Real.sqrt (f^2+g^2)≤GlobalGA.Secondary.diagonal+1/2 := by
    rw [mul_div_assoc]; exact hh
  simp only [fullSlope]
  linarith

theorem monotone_at_cut {f g : ℝ → ℝ} {a b cut : ℝ}
    (hf : MonotoneOn f (Icc a cut)) (hg : MonotoneOn g (Icc cut b))
    (he : f cut=g cut) :
    MonotoneOn (fun x => if x≤cut then f x else g x) (Icc a b) := by
  intro x hx y hy hxy
  by_cases hxc : x≤cut <;> by_cases hyc : y≤cut
  · simpa [hxc,hyc] using hf ⟨hx.1,hxc⟩ ⟨hy.1,hyc⟩ hxy
  · have h₁ := hf ⟨hx.1,hxc⟩ ⟨hx.1.trans hxc,le_rfl⟩ hxc
    have hcy : cut≤y := (lt_of_not_ge hyc).le
    have h₂ := hg ⟨le_rfl,hcy.trans hy.2⟩ ⟨hcy,hy.2⟩ hcy
    rw [he] at h₁
    simpa [hxc,hyc] using h₁.trans h₂
  · exact (hxc (hxy.trans hyc)).elim
  · have h := hg ⟨(lt_of_not_ge hxc).le,hx.2⟩ ⟨(lt_of_not_ge hyc).le,hy.2⟩ hxy
    simpa [hxc,hyc] using h

theorem diagonal_full_monotone {c n : ℝ} (hc : c∈Icc cLower cUpper)
    (hn : n∈Icc 0 frameCap) :
    MonotoneOn (fun x => diagonalSupport x c-
      fullSupport (x-c*Real.sin n) (c*Real.cos n)) (Icc 1 c) := by
  have hc0 : 0<c := by dsimp [cLower] at hc; linarith [hc.1]
  have htrig := transport_trig hn
  have hd (x : ℝ) : HasDerivAt
      (fun v => diagonalSupport v c-fullSupport (v-c*Real.sin n) (c*Real.cos n))
      (GlobalGA.Secondary.diagonal-fullSlope (x-c*Real.sin n) (c*Real.cos n)) x := by
    have h1 : HasDerivAt (fun v => diagonalSupport v c) GlobalGA.Secondary.diagonal x := by
      have h := ((hasDerivAt_id' x).add_const c).mul_const GlobalGA.Secondary.diagonal
      rw [one_mul] at h
      exact h
    exact h1.fun_sub (fullSupport_hasDerivAt_shift hc0 hn)
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (hd x).continuousAt.continuousWithinAt
  · intro x hx
    exact hd x
  · intro x hx
    have hs := mul_lt_mul_of_pos_left htrig.2.2.2.1 hc0
    have hu := mul_le_mul_of_nonneg_right hc.2 (by norm_num : (0:ℝ)≤6443/10000)
    have hf : 0<x-c*Real.sin n := by
      dsimp [cUpper] at hu
      linarith [hx.1]
    have hg : 0<c*Real.cos n := mul_pos hc0 (by linarith [htrig.1])
    have hphi := mul_le_mul_of_nonneg_left (CorrelatedSameBlock.one_le_phi hn) hc0.le
    have hfg : x-c*Real.sin n≤c*Real.cos n := by
      simp only [PositiveAngularEnvelope.phi] at hphi
      nlinarith [hx.2]
    exact sub_nonneg.mpr (fullSlope_below_diagonal hf hg hfg)

theorem full_full_monotone {c n : ℝ} (hc : c∈Icc cLower cUpper)
    (hn : n∈Icc 0 frameCap) :
    MonotoneOn (fun x => fullSupport x c-
      fullSupport (x-c*Real.sin n) (c*Real.cos n)) (Icc c qUpper) := by
  have hc0 : 0<c := by dsimp [cLower] at hc; linarith [hc.1]
  have htrig := transport_trig hn
  have hd (x : ℝ) := (fullSupport_hasDerivAt_first (x:=x) hc0).sub
    (fullSupport_hasDerivAt_shift (x:=x) hc0 hn)
  apply monoOn_of_hasDeriv_nonneg
  · intro x hx
    exact (hd x).continuousAt.continuousWithinAt
  · intro x hx
    exact hd x
  · intro x hx
    have hx0 : 0<x := hc0.trans hx.1
    have hs := mul_lt_mul_of_pos_left htrig.2.2.2.1 hc0
    have hf : 0<x-c*Real.sin n := by nlinarith [hx.1]
    have hg : 0<c*Real.cos n := mul_pos hc0 (by linarith [htrig.1])
    have hxc : x≤2*c := by dsimp [qUpper,cLower] at *; linarith [hx.2,hc.1]
    exact sub_nonneg.mpr (fullSlope_ratio hf hg hx0 hc0
      (negative_ratio_order hx0.le hc0.le hxc hn))

theorem clipped_full_monotone {c n : ℝ} (hc : c∈Icc cLower cUpper)
    (hn : n∈Icc 0 frameCap) :
    MonotoneOn (fun x => clippedSupport x c-
      fullSupport (x-c*Real.sin n) (c*Real.cos n)) (Icc 1 qUpper) := by
  have hc0 : 0<c := by dsimp [cLower] at hc; linarith [hc.1]
  have hh := monotone_at_cut (diagonal_full_monotone hc hn) (full_full_monotone hc hn)
    (by rw [full_at_diagonal (f:=c) (g:=c) rfl (by linarith)])
  simpa only [clippedSupport,ite_sub] using hh

theorem clipped_diagonal_monotone {c n : ℝ} (hc : c∈Icc cLower cUpper) :
    MonotoneOn (fun x => clippedSupport x c-
      diagonalSupport (x-c*Real.sin n) (c*Real.cos n)) (Icc 1 qUpper) := by
  intro x hx y hy hxy
  have hc0 : 0<c := by dsimp [cLower] at hc; linarith [hc.1]
  let P := clippedPoint (f:=x) (g:=c) (by linarith [hx.1]) hc0
  have hsup := raw_clipped_support (f:=y) (g:=c) P.circle.le P.sorted
    (by linarith [P.corners_nonneg.1,P.corners_nonneg.2]) (by linarith [hy.1])
  have hprod := mul_le_mul_of_nonneg_left P.primary_lower (sub_nonneg.mpr hxy)
  dsimp only
  rw [P.supports]
  dsimp [diagonalSupport]
  nlinarith

theorem negative_clipped_monotone {c n : ℝ} (hc : c∈Icc cLower cUpper)
    (hn : n∈Icc 0 frameCap) :
    MonotoneOn (fun x => clippedSupport x c-
      clippedSupport (x-c*Real.sin n) (c*Real.cos n)) (Icc 1 qUpper) := by
  have hc0 : 0<c := by dsimp [cLower] at hc; linarith [hc.1]
  have hh := monotone_continuous_switch
    (e:=fun x => (x-c*Real.sin n)-c*Real.cos n) (by fun_prop)
    (clipped_diagonal_monotone (n:=n) hc) (clipped_full_monotone hc hn)
    (fun x hx he => by
      have hfg : x-c*Real.sin n=c*Real.cos n := by linarith
      have hsum : 0≤(x-c*Real.sin n)+c*Real.cos n := by
        rw [hfg]
        have hg := mul_pos hc0 (show 0<Real.cos n by linarith [(transport_trig hn).1])
        linarith
      rw [full_at_diagonal hfg hsum])
  simpa only [sub_nonpos,clippedSupport,sub_ite] using hh

theorem negative_no_axis {q c n : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (hn : n∈Icc 0 frameCap) :
    (q-c*Real.sin n)/2<(axial+1/2)*(c*Real.cos n) := by
  have hp := coefficient_pos hq hc
  have ht := transport_trig hn
  have hm := mul_le_mul_of_nonneg_left hc.1 (by linarith [ht.1] : 0≤Real.cos n)
  have hmc : (cLower:ℝ)*(7648/10000)<c*Real.cos n := by
    dsimp [cLower] at *
    nlinarith
  have hA : (19/10:ℝ)<axial+1/2 := by linarith [axial_bounds.1]
  have hfinal : 0<c*Real.cos n := mul_pos hp.2.1 (by linarith [ht.1])
  have hmul := mul_lt_mul_of_pos_right hA hfinal
  have hs := mul_nonneg hp.2.1.le ht.2.2.1
  dsimp [qUpper,cLower] at *
  nlinarith [hq.2]

theorem negative_final_clipped {q c n : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (hn : n∈Icc 0 frameCap) :
    sortedSupport (q-c*Real.sin n) (c*Real.cos n)=
      clippedSupport (q-c*Real.sin n) (c*Real.cos n) := by
  have hh := not_le.mpr (negative_no_axis hq hc hn)
  simp only [sortedSupport,clippedSupport,hh,↓reduceIte]

/-- Raising the secant coefficient can only improve the negative-angle
increment. The support transitions retain their exact weak tie values. -/
theorem negative_coefficient_lower {q c n : ℝ} (hq : q∈Icc 1 qUpper)
    (hc : c∈Icc cLower cUpper) (hn : n∈Icc 0 frameCap) :
    increment 1 c (-n)≤ increment q c (-n) := by
  have h1 : (1:ℝ)∈Icc 1 qUpper := by norm_num [qUpper]
  have hh := negative_clipped_monotone hc hn h1 hq hq.1
  dsimp [increment]
  simp only [Real.sin_neg,Real.cos_neg,mul_neg,← sub_eq_add_neg]
  rw [baseline_clipped h1 hc,baseline_clipped hq hc,
    negative_final_clipped h1 hc hn,negative_final_clipped hq hc hn]
  linarith

end SquaresInCircles.Eight.GlobalGA.SecantD
