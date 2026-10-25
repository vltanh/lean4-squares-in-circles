module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Owners.GA.Negative.ESecantGain
public import SquaresInCircles.Eight.Owners.GA.Sorted.Support

/-!
# Eight squares: the large-A negative-DE secant correction

For `c = 1.193` the sorted D support changes from the diagonal to the full circle when
`sec n = c`. Both smooth correction branches have derivative at least `M = 1.045` on their domains
(`diagonal_derivative_lower`, `interior_derivative_lower`). The transition is found by the
intermediate value theorem, and the two branches agree there by the equality of the full and the
diagonal supports (`correction_lower`). No endpoint correction or derivative reserve is a
hypothesis.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
open Secondary

abbrev k : ℝ := 717/1000
abbrev l : ℝ := 457/500
abbrev c : ℝ := 1193/1000
abbrev M : ℝ := 209/200
abbrev K : ℝ := 13/12
abbrev beta : ℝ := 82/125

def secant (s : ℝ) : ℝ := 1/Real.cos s

def dCorrection (s : ℝ) : ℝ :=
  (secant s-1)/2+K*Real.tan s-
    (clippedSupport (secant s) c-clippedSupport 1 c)

def fullCorrection (s : ℝ) : ℝ :=
  secantGain qCap c s+diagonalSupport 1 c-fullSupport 1 c

theorem secant_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt secant (Real.sin s/Real.cos s^2) s := by
  have h := (hasDerivAt_const s (1:ℝ)).div (Real.hasDerivAt_cos s)
    (NegativeESecant.cos_pos hs).ne'
  exact h.congr_deriv (by ring)

theorem secant_monotone : MonotoneOn secant (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun s hs => (secant_hasDerivAt hs).continuousAt.continuousWithinAt)
    (fun s hs => secant_hasDerivAt (Ioo_subset_Icc_self hs))
  intro s hs
  exact div_nonneg (transport_trig (Ioo_subset_Icc_self hs)).2.2.1 (sq_nonneg _)

theorem secant_range {s : ℝ} (hs : s∈Icc 0 frameCap) : secant s∈Icc 1 (327/250:ℝ) :=
  NegativeESecant.de_secant_range hs

theorem correction_diagonal {s : ℝ} (hs : s∈Icc 0 frameCap) (hc : secant s≤c) :
    dCorrection s=NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s := by
  rw [dCorrection,clippedSupport,ite_eq_left hc]
  have h1 : (1:ℝ)≤c := by norm_num [c]
  rw [clippedSupport,ite_eq_left h1,NegativeESecant.gain_secant _ hs]
  dsimp [diagonalSupport,NegativeESecant.K,K,secant]
  ring

theorem correction_full {s : ℝ} (hs : s∈Icc 0 frameCap) (hc : c≤ secant s) :
    dCorrection s=fullCorrection s := by
  have hsupport : clippedSupport (secant s) c=fullSupport (secant s) c := by
    by_cases he : secant s≤c
    · have heq : secant s=c := le_antisymm he hc
      have hsum : 0≤ secant s+c := by
        dsimp [c] at hc ⊢
        linarith
      rw [clippedSupport,ite_eq_left he,full_at_diagonal heq hsum]
    · simp [clippedSupport,he]
  have h1 : (1:ℝ)≤c := by norm_num [c]
  rw [dCorrection,hsupport,clippedSupport,ite_eq_left h1,fullCorrection,
    secantGain_eq_secant_expression qCap c (NegativeESecant.cos_pos hs)]
  dsimp [fullSupport,diagonalSupport,secant,K]
  norm_num
  ring

theorem diagonal_derivative_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    M≤NegativeESecant.gainD (GlobalGA.Secondary.diagonal-1/2) s := by
  have ht := transport_trig hs
  have hd := mul_le_mul_of_nonneg_right
    (show GlobalGA.Secondary.diagonal-1/2≤2/5 by linarith [diagonal_bounds.2]) ht.2.2.1
  dsimp [NegativeESecant.gainD,NegativeESecant.K,M]
  apply (le_div_iff₀ (sq_pos_of_pos (NegativeESecant.cos_pos hs))).2
  nlinarith [Real.sin_sq_add_cos_sq s,sq_nonneg (Real.sin s-(40/209:ℝ))]

theorem diagonal_gain_lower {s : ℝ} (hs : s∈Icc 0 frameCap) :
    M*s≤NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) s := by
  have h := derivative_reserve
    (f := NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2))
    (df := NegativeESecant.gainD (GlobalGA.Secondary.diagonal-1/2)) (k := M)
    (fun z hz => (NegativeESecant.gain_hasDerivAt _ hz).continuousAt.continuousWithinAt)
    (fun z hz => NegativeESecant.gain_hasDerivAt _ (Ioo_subset_Icc_self hz))
    (fun z hz => diagonal_derivative_lower (Ioo_subset_Icc_self hz))
    (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hs hs.1
  simpa using h

theorem interior_sine_lower {s : ℝ} (hs : s∈Icc 0 frameCap) (hc : c≤ secant s) :
    (1/2:ℝ)<Real.sin s := by
  have ht := transport_trig hs
  have hcos := NegativeESecant.cos_pos hs
  have hprod : c*Real.cos s≤1 := (le_div_iff₀ hcos).1 hc
  have hprod0 : 0≤c*Real.cos s := mul_nonneg (by norm_num [c]) hcos.le
  have hprod2 := pow_le_pow_left₀ hprod0 hprod 2
  by_contra! hsin
  have hsin2 := pow_le_pow_left₀ ht.2.2.1 hsin 2
  dsimp [c] at hprod2
  nlinarith [Real.sin_sq_add_cos_sq s]

theorem interior_root_ratio {s : ℝ} (hs : s∈Icc 0 frameCap) :
    Real.sqrt qCap/Real.sqrt (gainRadicand c s)<147/100 := by
  have ht := transport_trig hs
  have hcos2 : (7648/10000:ℝ)^2≤Real.cos s^2 :=
    pow_le_pow_left₀ (by norm_num) ht.1.le 2
  have hr := gainRadicand_pos c s
  have hroot := Real.sqrt_pos.mpr hr
  have hroot2 := Real.sq_sqrt hr.le
  have hcompare : qCap<(147/100:ℝ)^2*gainRadicand c s := by
    dsimp [gainRadicand,c,qCap]
    nlinarith only [hcos2]
  apply (div_lt_iff₀ hroot).2
  have hq0 : (0:ℝ)≤qCap := by norm_num [qCap]
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [mul_pow,Real.sq_sqrt hq0,hroot2]
  linarith

theorem interior_derivative_lower {s : ℝ} (hs : s∈Icc 0 frameCap)
    (hc : c≤ secant s) : M≤ secantGainDeriv qCap c s := by
  have ht := transport_trig hs
  have hsin := interior_sine_lower hs hc
  have hr := interior_root_ratio hs
  have hm := mul_le_mul_of_nonneg_right hr.le ht.2.2.1
  have hunit := Real.sin_sq_add_cos_sq s
  have he : Real.sqrt qCap*Real.sin s/Real.sqrt (gainRadicand c s)=
      (Real.sqrt qCap/Real.sqrt (gainRadicand c s))*Real.sin s := by ring
  dsimp [secantGainDeriv]
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos (NegativeESecant.cos_pos hs))).2
  dsimp [M]
  nlinarith [sq_nonneg (Real.sin s-(1/2:ℝ))]

theorem fullCorrection_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt fullCorrection (secantGainDeriv qCap c s) s :=
  ((secantGain_hasDerivAt qCap c (NegativeESecant.cos_pos hs).ne').add_const (diagonalSupport 1 c)).sub_const (fullSupport 1 c)

/-- Each derivative is used only on its side of the switch of the sorted support. -/
theorem correction_lower {s : ℝ} (hs : s∈Icc 0 frameCap) : M*s≤dCorrection s := by
  by_cases hc : secant s≤c
  · rw [correction_diagonal hs hc]
    exact diagonal_gain_lower hs
  · have hs0 : (0:ℝ) ≤ s := hs.1
    have hcont : ContinuousOn secant (Icc 0 s) := by
      intro z hz
      exact (secant_hasDerivAt ⟨hz.1,hz.2.trans hs.2⟩).continuousAt.continuousWithinAt
    obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hs0 hcont
      (show c∈Icc (secant 0) (secant s) by
        constructor
        · norm_num [secant,c]
        · exact (lt_of_not_ge hc).le)
    have hti : t∈Icc 0 frameCap := ⟨ht.1,ht.2.trans hs.2⟩
    have htransition : NegativeESecant.gain (GlobalGA.Secondary.diagonal-1/2) t=
        fullCorrection t := by
      rw [← correction_diagonal hti hte.le,correction_full hti hte.ge]
    have hlower : M*t≤fullCorrection t := by
      rw [← htransition]
      exact diagonal_gain_lower hti
    have hmono (z : ℝ) (hz : z∈Ioo t s) : c≤ secant z := by
      rw [← hte]
      exact secant_monotone hti ⟨ht.1.trans hz.1.le,hz.2.le.trans hs.2⟩ hz.1.le
    have hderiv := derivative_reserve (f := fullCorrection)
      (df := secantGainDeriv qCap c) (k := M)
      (fun z hz => (fullCorrection_hasDerivAt
        ⟨ht.1.trans hz.1,hz.2.trans hs.2⟩).continuousAt.continuousWithinAt)
      (fun z hz => fullCorrection_hasDerivAt ⟨ht.1.trans hz.1.le,hz.2.le.trans hs.2⟩)
      (fun z hz => interior_derivative_lower
        ⟨ht.1.trans hz.1.le,hz.2.le.trans hs.2⟩ (hmono z hz))
      (show t∈Icc t s from ⟨le_rfl,ht.2⟩)
      (show s∈Icc t s from ⟨ht.2,le_rfl⟩) ht.2
    rw [correction_full hs (lt_of_not_ge hc).le]
    linarith

/-- The geometry of D gives the correction bound directly; the diagonal baseline is kept as it
is. -/
theorem actual_correction_lower {q s : ℝ} {D : SignedPoint}
    (hsort : D.Sorted) (hy : 0≤D.y) (hc : D.Contained q) (hq : q≤qCap)
    (hs : s∈Icc 0 frameCap) :
    M*s≤(secant s-1)/2+K*Real.tan s-
      (secant s*D.a+c*D.y-clippedSupport 1 c) := by
  have hsec := secant_range hs
  have hsupport := actual_clipped_support (f := secant s) (g := c)
    hsort hy hc hq (by dsimp [c]; linarith [hsec.1])
  have hgain := correction_lower hs
  dsimp [dCorrection] at hgain
  simp only [c,K,M] at hgain hsupport ⊢
  linarith only [hgain,hsupport]

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
