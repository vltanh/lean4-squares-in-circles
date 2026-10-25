module

public import SquaresInCircles.Eight.TableFree.SolePositiveTCoefficients
public import SquaresInCircles.Eight.TableFree.SoleAngleGrowth
public import SquaresInCircles.Eight.TableFree.CorrelatedSameBlock
public import SquaresInCircles.Eight.TableFree.WholeIntervalPolynomial
public import SquaresInCircles.Eight.TableFree.PolynomialCertificates

/-!
# Growth comparisons for the positive-T ordinary envelope

Uncompiled source. A single quartic covers every ratio at least .72.
The smaller-ratio families use fixed long secants, transferred by the
monotonicity of the normalized derivative. All estimates hold at the
original radius throughout the working band.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SolePositiveTGrowth
open Polynomial WholeIntervalPolynomial

def lowerRadius : ℚ := 19787/10000

def ratioPolynomial : ℚ[X] :=
  C (lowerRadius^2)*X^2*C ((478/625)^2)-
    (X+C (6443/10000))^2*(1+X^2-C (3221/2500)*X)

open WholeIntervalPolynomial.Certificate in
/-- Build a `Scaled` representation of a polynomial written with `+`, `-`, `*`,
powers, `C`, `X` and numerals, following its syntax; local hypotheses
`Scaled.Rep _ q` are used for the pieces `q` they name. -/
local syntax "r64_repT" : tactic
open WholeIntervalPolynomial.Certificate in
local macro_rules | `(tactic| r64_repT) => `(tactic| first
  | with_reducible assumption
  | (with_reducible apply Scaled.Rep.mul; r64_repT; r64_repT)
  | (with_reducible apply Scaled.Rep.add; r64_repT; r64_repT)
  | (with_reducible apply Scaled.Rep.sub; r64_repT; r64_repT)
  | (with_reducible apply Scaled.Rep.pow; r64_repT)
  | (with_reducible apply Scaled.Rep.neg; r64_repT)
  | with_reducible exact Scaled.rep_const _
  | with_reducible exact Scaled.rep_var
  | with_reducible exact Scaled.rep_zero
  | with_reducible exact Scaled.rep_one
  | with_reducible exact Scaled.rep_ofNat _
  | with_reducible exact Scaled.rep_natCast _)

open WholeIntervalPolynomial.Certificate in
/-- One kernel check gives the expansion identity and the reserve. -/
private theorem r64_cert {c : Scaled} {a b ρ : ℚ} {p : ℚ[X]} {D : ℕ}
    (hc : c.Rep (centered a b p))
    (h : c.s≠0 ∧ c.l.length≤D+1 ∧
      ρ<(lowerZ D (fun j => (chebList c.l).getD j 0):ℚ)/(c.s*2^c.l.length/2)) :
    centered a b p=expansion D (centered a b p) ∧ ρ<lowerOn D a b p := by
  refine ⟨hc.eq_expansion h.1 h.2.1,?_⟩
  rw [lowerOn_eq_of_rep hc h.1 h.2.1]
  exact h.2.2

open WholeIntervalPolynomial.Certificate in
private theorem r64_ratio_cert :
    centered (18/25) 1 ratioPolynomial=expansion 4 (centered (18/25) 1 ratioPolynomial) ∧
      (2/25:ℚ)<lowerOn 4 (18/25) 1 ratioPolynomial := by
  have hp := (by simp only [ratioPolynomial,lowerRadius]; r64_repT :
    Scaled.Rep _ ratioPolynomial)
  exact r64_cert (hp.centered 1 50 43 7 (by norm_num) (by norm_num) (by norm_num))
    (by decide +kernel)

theorem ratio_identity :
    centered (18/25) 1 ratioPolynomial=
      expansion 4 (centered (18/25) 1 ratioPolynomial) := r64_ratio_cert.1

theorem ratio_reserve : (2/25:ℚ)<lowerOn 4 (18/25) 1 ratioPolynomial := r64_ratio_cert.2

open PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open OrdinaryAngleConcentration OrdinaryNegativeSlope OrdinaryNegativeEnvelope
open VaryingBFunctions VaryingBComparison SingleAngleConcavity

theorem radius_le {R : ℝ} (hR : 0≤R) (hQ : qLow≤R^2) :
    (lowerRadius:ℝ)≤R := by
  have h := SoleAngleGrowth.radius_lower hR hQ
  have he : (lowerRadius:ℝ)=19787/10000 := by norm_num [lowerRadius]
  linarith

theorem ratio_square {r : ℝ} (hr : r∈Icc (18/25:ℝ) 1) :
    (2/25:ℝ)<(lowerRadius:ℝ)^2*r^2*(478/625)^2-
      (r+6443/10000)^2*(1+r^2-2*r*(3221/5000)) := by
  have hr' : r∈Icc ((18/25:ℚ):ℝ) ((1:ℚ):ℝ) := by
    push_cast
    exact hr
  have h := positive_on_interval (by norm_num : (18/25:ℚ)<1) ratio_identity ratio_reserve hr'
  have he : aeval r ratioPolynomial=(lowerRadius:ℝ)^2*r^2*(478/625)^2-
      (r+6443/10000)^2*(1+r^2-2*r*(3221/5000)) := by
    simp only [ratioPolynomial,map_sub,map_mul,map_add,map_pow,map_one,aeval_C,aeval_X,
      eq_ratCast]
    push_cast
    ring
  rw [he] at h
  have h2 : ((2/25:ℚ):ℝ)=2/25 := by norm_num
  linarith

theorem normalized_high_slope {R r : ℝ}
    (hR : 0≤R) (hQ : qLow≤R^2) (hr : r∈Icc (18/25:ℝ) 1) :
    r< -Real.sin frameCap+R*r*Real.cos frameCap/root r (Real.sin frameCap) := by
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hs := transport_trig hh
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0<r := by linarith [hr.1]
  have hS : Real.sin frameCap≤6443/10000 := hs.2.2.2.1.le
  have hC : (478/625:ℝ)≤Real.cos frameCap := by linarith [hs.1]
  have hD : (root r (Real.sin frameCap))^2≤
      1+r^2-2*r*(3221/5000) := by
    nlinarith [mul_le_mul_of_nonneg_left cap_sin_lower.le hr0.le]
  have hDmul := mul_le_mul_of_nonneg_left hD (sq_nonneg (r+6443/10000))
  have hpoly := ratio_square hr
  have hcross0 : (r+6443/10000)*root r (Real.sin frameCap)<
      (lowerRadius:ℝ)*r*(478/625) := by
    have hp : 0≤(lowerRadius:ℝ)*r*(478/625) := by
      exact mul_nonneg (mul_nonneg (by norm_num [lowerRadius]) hr0.le) (by norm_num)
    have hsq : ((r+6443/10000)*root r (Real.sin frameCap))^2<
        ((lowerRadius:ℝ)*r*(478/625))^2 := by
      have he1 : ((r+6443/10000)*root r (Real.sin frameCap))^2=
          (r+6443/10000)^2*(root r (Real.sin frameCap))^2 := by ring
      have he2 : ((lowerRadius:ℝ)*r*(478/625))^2=(lowerRadius:ℝ)^2*r^2*(478/625)^2 := by ring
      rw [he1,he2]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hp hsq
  have hleft : (r+Real.sin frameCap)*root r (Real.sin frameCap)≤
      (r+6443/10000)*root r (Real.sin frameCap) :=
    mul_le_mul_of_nonneg_right (by linarith) hN.le
  have hright := mul_le_mul
    (mul_le_mul_of_nonneg_right (radius_le hR hQ) hr0.le) hC
    (by norm_num : (0:ℝ)≤478/625) (mul_nonneg hR hr0.le)
  have hcross : (r+Real.sin frameCap)*root r (Real.sin frameCap)<
      R*r*Real.cos frameCap := hleft.trans_lt (hcross0.trans_le hright)
  have hdiv := (lt_div_iff₀ hN).2 hcross
  linarith

theorem Vd_gt_smaller {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (18/25)*q≤p)
    (ht : t∈Icc 0 frameCap) : p<Vd R p q t := by
  have hq := hp.trans_le hpq
  have hr : p/q∈Icc (18/25:ℝ) 1 :=
    ⟨(le_div_iff₀ hq).2 hratio,(div_le_one hq).2 hpq⟩
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hbase := mul_lt_mul_of_pos_left (normalized_high_slope hR hQL hr) hq
  have hcancel : q*(p/q)=p := by field_simp
  rw [hcancel,← Vd_normalized hq] at hbase
  exact hbase.trans_le ((Vd_antitone hR hQU hp hpq (by linarith)) ht hh ht.2)

theorem VnuDeriv_antitone {R p q nu : ℝ}
    (hR : 0≤R) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) (hnu : p≤nu) :
    AntitoneOn (VnuDeriv R p q nu) (Icc 0 frameCap) := by
  apply antiOn_of_hasDeriv_nonpos
  · intro x hx
    exact (VnuDeriv_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt
  · intro x hx
    exact VnuDeriv_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx)
  · intro x hx
    linarith [Vnu_second_lt hR hQU hp hpq hqp hnu (Ioo_subset_Icc_self hx)]

theorem VnuDeriv_ge_Vd {R p q nu t : ℝ} (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) : Vd R p q t≤VnuDeriv R p q nu t := by
  have h := mul_le_mul_of_nonneg_right hnu (transport_trig ht).2.2.1
  dsimp [Vd,mixedNDerivative,VnuDeriv]
  simp only [zero_sub]
  linarith

theorem high_growth {R p q nu t u : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hratio : (18/25)*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    p*(u-t)≤Vnu R p q nu u-Vnu R p q nu t := by
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp (hp.trans_le hpq) hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp (hp.trans_le hpq) (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hu htu
  exact (Vd_gt_smaller hR hQL hQU hp hpq hratio (Ioo_subset_Icc_self hx)).le.trans
    (VnuDeriv_ge_Vd hnu (Ioo_subset_Icc_self hx))

/-- Comparing derivatives transfers a normalized chord without replacing
the actual one-angle negative coefficient. -/
theorem normalized_growth {R p q nu r t u : ℝ}
    (hR : (lowerRadius:ℝ)≤R) (hp : 0<p) (hpq : p≤q)
    (hr : 0<r) (hratio : r*q≤p) (hnu : nu≤q)
    (ht : t∈Icc 0 frameCap) (hu : u∈Icc 0 frameCap) (htu : t≤u) :
    q*(V (lowerRadius:ℝ) r 1 u-V (lowerRadius:ℝ) r 1 t)≤
      Vnu R p q nu u-Vnu R p q nu t := by
  have hq := hp.trans_le hpq
  have hratio' : r≤p/q := (le_div_iff₀ hq).2 hratio
  have hpq' : p/q≤1 := (div_le_one hq).2 hpq
  have hd (x : ℝ) (hx : x∈Icc 0 frameCap) :
      q*Vd (lowerRadius:ℝ) r 1 x≤VnuDeriv R p q nu x := by
    have hfrac := normalized_fraction_mono hr.le hratio' hpq' (sin_mem hx)
    have hc : 0≤Real.cos x := by linarith [(transport_trig hx).1]
    have hfrac0 : 0≤r/root r (Real.sin x) := div_nonneg hr.le (root_pos r (sin_mem hx)).le
    have hR0 : 0≤R := (by norm_num [lowerRadius] : (0:ℝ)≤lowerRadius).trans hR
    have hfirst := mul_le_mul_of_nonneg_right hR (mul_nonneg hc hfrac0)
    have hsecond := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hR0 hc)
    have he1 : (lowerRadius:ℝ)*r*Real.cos x/root r (Real.sin x)=
        (lowerRadius:ℝ)*(Real.cos x*(r/root r (Real.sin x))) := by ring
    have he2 : R*(p/q)*Real.cos x/root (p/q) (Real.sin x)=
        R*Real.cos x*((p/q)/root (p/q) (Real.sin x)) := by ring
    have he3 : R*(Real.cos x*(r/root r (Real.sin x)))=
        R*Real.cos x*(r/root r (Real.sin x)) := by ring
    have hnormalized :
        -Real.sin x+(lowerRadius:ℝ)*r*Real.cos x/root r (Real.sin x)≤
        -Real.sin x+R*(p/q)*Real.cos x/root (p/q) (Real.sin x) := by
      rw [he1,he2]
      linarith only [hfirst,hsecond,he3]
    have hscaled := mul_le_mul_of_nonneg_left hnormalized hq.le
    have hscaled' : q*Vd (lowerRadius:ℝ) r 1 x≤Vd R p q x := by
      rw [Vd_normalized hq,Vd_normalized (by norm_num : (0:ℝ)<1)]
      simpa only [div_one,one_mul] using hscaled
    exact hscaled'.trans (VnuDeriv_ge_Vd hnu hx)
  have hg := derivative_reserve
    (f := fun x => Vnu R p q nu x-q*V (lowerRadius:ℝ) r 1 x)
    (df := fun x => VnuDeriv R p q nu x-q*Vd (lowerRadius:ℝ) r 1 x)
    (k := 0)
    (fun x hx => ((Vnu_hasDerivAt hp hq hx).sub
      ((V_hasDerivAt hr (by norm_num) hx).const_mul q)).continuousAt.continuousWithinAt)
    (fun x hx => (Vnu_hasDerivAt hp hq (Ioo_subset_Icc_self hx)).sub
      ((V_hasDerivAt hr (by norm_num) (Ioo_subset_Icc_self hx)).const_mul q))
    (fun x hx => sub_nonneg.mpr (hd x (Ioo_subset_Icc_self hx))) ht hu htu
  simp only [zero_mul] at hg
  linarith

/-- For a concave function, a terminal secant remains a lower bound
when its left endpoint is moved further left. -/
theorem extend_terminal_chord {f : ℝ → ℝ} {a t k : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 frameCap) f)
    (ha : a∈Ico 0 frameCap) (ht : t∈Icc 0 a)
    (hchord : k*(frameCap-a)≤f frameCap-f a) :
    k*(frameCap-t)≤f frameCap-f t := by
  have hgap : 0<frameCap-t := by linarith [ha.2,ht.2]
  obtain ⟨α,hαd⟩ : ∃ α : ℝ,α=(frameCap-a)/(frameCap-t) := ⟨_,rfl⟩
  obtain ⟨β,hβd⟩ : ∃ β : ℝ,β=(a-t)/(frameCap-t) := ⟨_,rfl⟩
  have hα : 0≤α := hαd ▸ div_nonneg (by linarith [ha.2]) hgap.le
  have hβ : 0≤β := hβd ▸ div_nonneg (by linarith [ht.2]) hgap.le
  have hαgap : α*(frameCap-t)=frameCap-a := by rw [hαd,div_mul_cancel₀ _ hgap.ne']
  have hβgap : β*(frameCap-t)=a-t := by rw [hβd,div_mul_cancel₀ _ hgap.ne']
  have hsum : α+β=1 := by
    have h1 : (α+β)*(frameCap-t)=1*(frameCap-t) := by linear_combination hαgap+hβgap
    exact mul_right_cancel₀ hgap.ne' h1
  have hpoint : α*t+β*frameCap=a := by
    have h1 : (α*t+β*frameCap)*(frameCap-t)=a*(frameCap-t) := by
      linear_combination t*hαgap+frameCap*hβgap
    exact mul_right_cancel₀ hgap.ne' h1
  have hh := hc.2
    (show t∈Icc 0 frameCap from ⟨ht.1,ht.2.trans ha.2.le⟩)
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hα hβ hsum
  simp only [smul_eq_mul,hpoint] at hh
  have hh' := mul_le_mul_of_nonneg_right hh hgap.le
  have hclear : (frameCap-a)*f t+(a-t)*f frameCap≤(frameCap-t)*f a := by
    have he : (α*f t+β*f frameCap)*(frameCap-t)=
        (frameCap-a)*f t+(a-t)*f frameCap := by
      calc
        _=(α*(frameCap-t))*f t+(β*(frameCap-t))*f frameCap := by ring
        _=_ := by rw [hαgap,hβgap]
    rw [he] at hh'
    linarith
  have hlast := mul_le_mul_of_nonneg_right hchord hgap.le
  have hfactor : 0≤(frameCap-a)*(f frameCap-f t-k*(frameCap-t)) := by
    nlinarith only [hclear,hlast]
  have hpos : 0<frameCap-a := by linarith [ha.2]
  have hnonneg := (mul_nonneg_iff_of_pos_left hpos).1 hfactor
  linarith

theorem scaled_concave {f : ℝ → ℝ} {b : ℝ}
    (hc : ConcaveOn ℝ (Icc 0 frameCap) f) (hb : 0≤b) :
    ConcaveOn ℝ (Icc 0 frameCap) (fun x => b*f x) := by
  refine ⟨hc.1,?_⟩
  intro x hx y hy a c ha hc' hac
  have h := mul_le_mul_of_nonneg_left (hc.2 hx hy ha hc' hac) hb
  simpa only [smul_eq_mul,mul_add,mul_left_comm] using h

theorem cap_trig :
    (6442176872/10000000000:ℝ)≤Real.sin frameCap ∧
    Real.sin frameCap≤6442176873/10000000000 ∧
    (7648421872/10000000000:ℝ)≤Real.cos frameCap := by
  have hsL := HighOrderTaylor.S15_le_sin (show 0≤frameCap by norm_num [frameCap])
  have hsU := HighOrderTaylor.sin_le_S13 (show 0≤frameCap by norm_num [frameCap])
  have hcL := HighOrderTaylor.C14_le_cos (show 0≤frameCap by norm_num [frameCap])
  norm_num [frameCap,HighOrderTaylor.S15,HighOrderTaylor.S13,HighOrderTaylor.S11,
    HighOrderTaylor.C14,HighOrderTaylor.C12,Arithmetic.sin9,Arithmetic.sin7,
    Arithmetic.cos10,Arithmetic.cos8]
    at hsL hsU hcL ⊢
  exact ⟨by linarith,by linarith,by linarith⟩

theorem fixed_chords :
    (121/200)*(frameCap-1/5)<(431/500)*
      (V (lowerRadius:ℝ) (117/200) 1 frameCap-V (lowerRadius:ℝ) (117/200) 1 (1/5)) ∧
    (7/10)*(frameCap-7/20)<(923/1000)*
      (V (lowerRadius:ℝ) (13/20) 1 frameCap-V (lowerRadius:ℝ) (13/20) 1 (7/20)) := by
  have hsA := HighOrderTaylor.sin_le_S13 (by norm_num : (0:ℝ)≤1/5)
  have hcA := HighOrderTaylor.cos_le_C16 (by norm_num : (0:ℝ)≤1/5)
  have hsB := HighOrderTaylor.sin_le_S13 (by norm_num : (0:ℝ)≤7/20)
  have hcB := HighOrderTaylor.cos_le_C16 (by norm_num : (0:ℝ)≤7/20)
  have hsA' : Real.sin (1/5:ℝ)≤1986693308/10000000000 := by
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7] at hsA
    linarith
  have hcA' : Real.cos (1/5:ℝ)≤9800665779/10000000000 := by
    norm_num [HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.cos10,Arithmetic.cos8] at hcA
    linarith
  have hsB' : Real.sin (7/20:ℝ)≤3428978075/10000000000 := by
    norm_num [HighOrderTaylor.S13,HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7] at hsB
    linarith
  have hcB' : Real.cos (7/20:ℝ)≤9393727129/10000000000 := by
    norm_num [HighOrderTaylor.C16,HighOrderTaylor.C14,HighOrderTaylor.C12,
      Arithmetic.cos10,Arithmetic.cos8] at hcB
    linarith
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have ha : (1/5:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hb : (7/20:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hnA := root_pos (117/200) (sin_mem ha)
  have hnH := root_pos (117/200) (sin_mem hh)
  have hnA2 := root_sq (117/200) (sin_mem ha)
  have hnH2 := root_sq (117/200) (sin_mem hh)
  have hmB := root_pos (13/20) (sin_mem hb)
  have hmH := root_pos (13/20) (sin_mem hh)
  have hmB2 := root_sq (13/20) (sin_mem hb)
  have hmH2 := root_sq (13/20) (sin_mem hh)
  have hnAL : (1053461856/1000000000:ℝ)≤root (117/200) (Real.sin (1/5)) := by nlinarith
  have hnHU : root (117/200) (Real.sin frameCap)≤767131219/1000000000 := by
    nlinarith [cap_trig.1]
  have hmBL : (988297956/1000000000:ℝ)≤root (13/20) (Real.sin (7/20)) := by nlinarith
  have hmHU : root (13/20) (Real.sin frameCap)≤764864045/1000000000 := by
    nlinarith [cap_trig.1]
  dsimp [V]
  simp only [negativeNorm_normalized (by norm_num : (0:ℝ)<1),div_one,one_mul]
  dsimp [lowerRadius,frameCap] at *
  constructor <;> nlinarith [cap_trig.2.2]

theorem low_growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 0<p) (hpq : p≤q) (hratio : (117/200)*q≤p)
    (hq : 431/500≤q) (hnu : nu≤q) (ht : t∈Icc 0 (1/5:ℝ)) :
    (121/200)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have hconc := scaled_concave (V_concave (R := (lowerRadius:ℝ)) (q := 1)
    (by norm_num [lowerRadius]) (by norm_num [lowerRadius,qCap]) (by norm_num : (0:ℝ)<117/200)
    (by norm_num) (by norm_num)) (by norm_num : (0:ℝ)≤431/500)
  have ht2 : t≤1/5 := ht.2
  have ha : (1/5:ℝ)∈Ico 0 frameCap := ⟨by norm_num,by norm_num [frameCap]⟩
  have hch := extend_terminal_chord hconc ha ht (k := 121/200) (by
    have h := fixed_chords.1.le
    simp only [mul_sub] at h ⊢
    exact h)
  have hlen : 0≤frameCap-t := by simp only [frameCap]; linarith
  have hv0 : 0≤V (lowerRadius:ℝ) (117/200) 1 frameCap-V (lowerRadius:ℝ) (117/200) 1 t := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ)≤121/200) hlen]
  have hscale := mul_le_mul_of_nonneg_right hq hv0
  have htransfer := normalized_growth (u := frameCap) (radius_le hR hQL) hp hpq (by norm_num)
    hratio hnu ⟨ht.1,by simp only [frameCap]; linarith⟩
    (by norm_num [frameCap]) (by simp only [frameCap]; linarith)
  linarith

theorem middle_growth {R p q nu t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 0<p) (hpq : p≤q) (hratio : (13/20)*q≤p)
    (hq : 923/1000≤q) (hnu : nu≤q) (ht : t∈Icc 0 (7/20:ℝ)) :
    (7/10)*(frameCap-t)≤Vnu R p q nu frameCap-Vnu R p q nu t := by
  have hconc := scaled_concave (V_concave (R := (lowerRadius:ℝ)) (q := 1)
    (by norm_num [lowerRadius]) (by norm_num [lowerRadius,qCap]) (by norm_num : (0:ℝ)<13/20)
    (by norm_num) (by norm_num)) (by norm_num : (0:ℝ)≤923/1000)
  have ht2 : t≤7/20 := ht.2
  have ha : (7/20:ℝ)∈Ico 0 frameCap := ⟨by norm_num,by norm_num [frameCap]⟩
  have hch := extend_terminal_chord hconc ha ht (k := 7/10) (by
    have h := fixed_chords.2.le
    simp only [mul_sub] at h ⊢
    exact h)
  have hlen : 0≤frameCap-t := by simp only [frameCap]; linarith
  have hv0 : 0≤V (lowerRadius:ℝ) (13/20) 1 frameCap-V (lowerRadius:ℝ) (13/20) 1 t := by
    nlinarith [mul_nonneg (by norm_num : (0:ℝ)≤7/10) hlen]
  have hscale := mul_le_mul_of_nonneg_right hq hv0
  have htransfer := normalized_growth (u := frameCap) (radius_le hR hQL) hp hpq (by norm_num)
    hratio hnu ⟨ht.1,by simp only [frameCap]; linarith⟩
    (by norm_num [frameCap]) (by simp only [frameCap]; linarith)
  linarith

theorem DE_A_endpoint {R p q : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2)
    (hp : 113/200≤p) (hq : 0<q)
    (hr : p/q∈Icc (533/1000:ℝ) (81/100)) :
    (18/25:ℝ)<VnuDeriv R p q p frameCap := by
  obtain ⟨r,hrd⟩ : ∃ r : ℝ,r=p/q := ⟨_,rfl⟩
  rw [← hrd] at hr
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  have hN := root_pos r (sin_mem hh)
  have hN2 := root_sq r (sin_mem hh)
  have hr0 : 0≤r := by linarith [hr.1]
  have hproduct := mul_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hr.2)
  have hsin := mul_le_mul_of_nonneg_left cap_sin_lower.le hr0
  have hNupper : root r (Real.sin frameCap)≤157/200 := by
    have hsq : (root r (Real.sin frameCap))^2≤(157/200)^2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hN.le (by norm_num) (by norm_num)).1 hsq
  have hc := (transport_trig hh).1.le
  have hs := (transport_trig hh).2.2.2.1.le
  have hLR : (lowerRadius:ℝ)=19787/10000 := by norm_num [lowerRadius]
  have hnum : (19787/10000:ℝ)*(478/625)≤R*Real.cos frameCap := by
    have h1 := radius_le hR hQL
    rw [hLR] at h1
    exact mul_le_mul h1 (by linarith) (by norm_num) hR
  obtain ⟨k,hkd⟩ : ∃ k : ℝ,k=(19787/10000)*(478/625)/(157/200) := ⟨_,rfl⟩
  have hk0 : 0≤k := by rw [hkd]; norm_num
  have hprod := mul_le_mul_of_nonneg_left hNupper hk0
  have hfraction : k≤R*Real.cos frameCap/root r (Real.sin frameCap) := by
    apply (le_div_iff₀ hN).2
    have hk' : k*(157/200)=(19787/10000)*(478/625) := by rw [hkd]; norm_num
    linarith
  have hbracket : k-6443/10000≤
      -Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap) := by linarith
  have hpositive : 0≤k-6443/10000 := by rw [hkd]; norm_num
  have hmul := mul_le_mul hp hbracket hpositive (by linarith : 0≤p)
  have hreserve : (18/25:ℝ)<(113/200)*(k-6443/10000) := by rw [hkd]; norm_num
  have he : VnuDeriv R p q p frameCap=
      p*(-Real.sin frameCap+R*Real.cos frameCap/root r (Real.sin frameCap)) := by
    simp only [VnuDeriv,normD1,pairProduct]
    rw [Real.cos_neg,negativeNorm_normalized hq,hrd]
    field_simp
  rw [he]
  exact hreserve.trans_le hmul

theorem DE_A_growth {R p q t : ℝ}
    (hR : 0≤R) (hQL : qLow≤R^2) (hQU : R^2≤qCap)
    (hp : 113/200≤p) (hpq : p≤q)
    (hr : p/q∈Icc (533/1000:ℝ) (81/100))
    (ht : t∈Icc 0 frameCap) :
    (18/25)*(frameCap-t)≤Vnu R p q p frameCap-Vnu R p q p t := by
  have hp0 : 0<p := by linarith
  have hq := hp0.trans_le hpq
  have hqp : q≤2*p := by
    have hh := (le_div_iff₀ hq).1 hr.1
    nlinarith
  have hanti := VnuDeriv_antitone hR hQU hp0 hpq hqp (le_refl p)
  have hh : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  apply derivative_reserve
    (fun x hx => (Vnu_hasDerivAt hp0 hq hx).continuousAt.continuousWithinAt)
    (fun x hx => Vnu_hasDerivAt hp0 hq (Ioo_subset_Icc_self hx))
    (fun x hx => ?_) ht hh ht.2
  exact (DE_A_endpoint hR hQL hp hq hr).le.trans
    (hanti (Ioo_subset_Icc_self hx) hh hx.2.le)

end SquaresInCircles.Eight.TableFree.SolePositiveTGrowth
