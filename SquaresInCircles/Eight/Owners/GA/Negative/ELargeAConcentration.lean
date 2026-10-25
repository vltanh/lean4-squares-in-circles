module

public import Mathlib.Algebra.Order.Star.Real
public import SquaresInCircles.Eight.Arithmetic.HighOrderTaylor
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.WholeIntervalBernstein
public import SquaresInCircles.Eight.Owners.GA.HybridConcentration
public import SquaresInCircles.Eight.Owners.GA.Negative.DETD2LowPositiveCoefficients
public import SquaresInCircles.Eight.Owners.GA.Negative.DEBT3PositivePure
public import SquaresInCircles.Eight.Owners.GA.Negative.ELargeADCorrection
public import SquaresInCircles.Eight.Owners.GA.Positive.ANegativeTDGain
public import SquaresInCircles.Eight.Owners.GA.Positive.BT3LowSameBlock
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveASupport

/-!
# Eight squares: removing ordinary-angle saturation in the large-A negative-E family

The negative slope `.767` and the positive slope `-.64 q` hold for the fixed H, G, B pairs
(`negative_growth`, `positive_growth`). Separate and coincident blocks then dominate their pure
signed excess, with the P and N budgets kept (`sum_pure_lower`). The distinguished D block keeps
its linear positive minorant and its H negative minorant.
-/

section
/-!
## The two ordinary same-block comparisons

The two-angle norm cancels without changing the signed angle. The
negative-surplus comparison uses the stated sine condition; the
positive-surplus comparison uses the coefficient ratio at most 1.7.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SameBlock
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity CorrelatedSameBlock

theorem negative_difference (p q P N : ℝ) :
    mixedBlock R p q P N-V R p q (N-P)=
      (p-q*Real.cos N)*(Real.cos P-1)+(p-q*Real.sin N)*Real.sin P := by
  dsimp [mixedBlock,V,PositiveAngularEnvelope.phi]
  rw [show -(N-P)=P-N by ring,Real.cos_sub]
  ring

theorem positive_difference (p q P N : ℝ) :
    mixedBlock R p q P N-U R p q (P-N)=
      p*(PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N))-q*(1-Real.cos N) := by
  dsimp [mixedBlock,U]
  ring

theorem negative_surplus {p q P N : ℝ} (hp : 0≤p)
    (hP : P∈Icc 0 N) (hN : N∈Icc 0 frameCap)
    (hsine : q*Real.sin N≤p) :
    V R p q (N-P)≤ mixedBlock R p q P N := by
  have hP' : P∈Icc 0 frameCap := ⟨hP.1,hP.2.trans hN.2⟩
  have htP := transport_trig hP'
  have htN := transport_trig hN
  have hcosN : 0<Real.cos N := by linarith [htN.1]
  have hcosP : Real.cos P-1≤0 := by linarith [Real.cos_le_one P]
  have he := negative_difference p q P N
  by_cases hlarge : p≤q*Real.cos N
  · have hfirst := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hlarge) hcosP
    have hsecond := mul_nonneg (sub_nonneg.mpr hsine) htP.2.2.1
    linarith
  · have hsmall : 0≤p-q*Real.cos N := by linarith
    have harg : N-P∈Icc 0 frameCap :=
      ⟨by linarith [hP.2],by linarith [hN.2,hP.1]⟩
    have hcos := cos_anti harg hN (by linarith [hP.1])
    have hfactor := mul_nonneg hsmall (sub_nonneg.mpr hcos)
    have hpositive := mul_nonneg
      (mul_nonneg hp (sub_nonneg.mpr htN.2.2.2.2.le)) htP.2.2.1
    have hid :
        ((p-q*Real.cos N)*(Real.cos P-1)+(p-q*Real.sin N)*Real.sin P)*Real.cos N=
        (p-q*Real.cos N)*(Real.cos (N-P)-Real.cos N)+
          p*(Real.cos N-Real.sin N)*Real.sin P := by
      rw [Real.cos_sub]
      ring
    have hnum : 0≤ mixedBlock R p q P N-V R p q (N-P) := by
      apply nonneg_of_mul_nonneg_left (b:=Real.cos N) _ hcosN
      rw [he,hid]
      exact add_nonneg hfactor hpositive
    linarith

theorem phi_slope_at_cap : (3/25:ℝ)<Real.cos frameCap-Real.sin frameCap := by
  have hc := cos_lower_six (x:=frameCap) (by norm_num [frameCap])
  have hs := sin_upper_five (x:=frameCap) (by norm_num [frameCap])
  norm_num [frameCap] at hc hs ⊢
  linarith

theorem phi_cap_difference {N : ℝ} (hN : N∈Icc 0 frameCap) :
    0≤PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)-(17/10)*(1-Real.cos N) := by
  have hsin := (transport_trig hN).2.2.1
  have hcos := sub_nonneg.mpr (Real.cos_le_one N)
  have hhalf := PositiveANegativeTD.one_sub_cos_upper hN
  have hp := mul_le_mul_of_nonneg_right phi_cap_lower.le hcos
  have hd := mul_le_mul_of_nonneg_right phi_slope_at_cap.le hsin
  have hid : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)=
      PositiveAngularEnvelope.phi frameCap*(1-Real.cos N)+
        (Real.cos frameCap-Real.sin frameCap)*Real.sin N := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  rw [hid]
  nlinarith

theorem positive_surplus {p q P N : ℝ} (hp : 0≤p)
    (hratio : q≤(17/10)*p)
    (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 P) :
    U R p q (P-N)≤ mixedBlock R p q P N := by
  have hN' : N∈Icc 0 frameCap := ⟨hN.1,hN.2.trans hP.2⟩
  have hinc := phi_increment_anti hN'
    (show P-N∈Icc 0 (frameCap-N) by constructor <;> linarith [hN.2,hP.2])
    (show frameCap-N∈Icc 0 (frameCap-N) by
      exact ⟨by linarith [hN'.2],le_rfl⟩)
    (by linarith [hP.2])
  have hinc' : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) := by
    convert hinc using 1 <;> congr 1 <;> ring
  have hpinc := mul_le_mul_of_nonneg_left hinc' hp
  have hbase := mul_nonneg hp (phi_cap_difference hN')
  have hqcos := mul_le_mul_of_nonneg_right hratio
    (sub_nonneg.mpr (Real.cos_le_one N))
  have he := positive_difference p q P N
  nlinarith

end SquaresInCircles.Eight.GlobalGA.NegativeAPositiveTD.SameBlock
end
end
end

section
/-!
## Every ordinary same-block alternative in the negative-DE / BT3 stress

The positive
surplus comparison uses the whole ratio bound 341/200 and the actual
cap 7/10. Low H/G negative surplus retains its correlated low-family
correction. The high family and the low B pair use the exact signed
same-block identity. Neither signed mass is discarded prematurely.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.SameBlock
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

lemma cap_cosine_loss {t : ℝ} (ht : t∈Icc 0 frameCap) :
    1-Real.cos t≤(183/500)*Real.sin t := by
  have hd (x : ℝ) : HasDerivAt
      (fun x => (183/500)*Real.sin x+Real.cos x-1)
      ((183/500)*Real.cos x-Real.sin x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (183/500)).add
      (Real.hasDerivAt_cos x)).sub_const 1 using 1
  have hdd (x : ℝ) : HasDerivAt
      (fun x => (183/500)*Real.cos x-Real.sin x)
      (-(183/500)*Real.sin x-Real.cos x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (183/500)).sub
      (Real.hasDerivAt_sin x) using 1
    ring
  have hc : ConcaveOn ℝ (Icc 0 frameCap)
      (fun x => (183/500)*Real.sin x+Real.cos x-1) := by
    apply concave_of_deriv2 (fun x _ => hd x) (fun x _ => hdd x)
    intro x hx
    have hh := transport_trig hx
    linarith [hh.1,hh.2.2.1]
  have he : 0≤(183/500)*Real.sin frameCap+Real.cos frameCap-1 := by
    have hs := sin_lower_seven (show 0≤frameCap by norm_num [frameCap])
    have hh := cos_lower_six (show 0≤frameCap by norm_num [frameCap])
    norm_num [frameCap] at hs hh ⊢
    linarith
  have hh := hc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) ht
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,zero_add,sub_self,
    min_eq_left he] at hh
  linarith

/-- Whole-cap positive-surplus comparison, including either zero mass. -/
theorem positive {p q P N : ℝ} (hp : 0≤p) (hqp : q≤(341/200)*p)
    (hN : 0≤N) (hNP : N≤P) (hP : P≤frameCap) :
    U R p q (P-N)≤ mixedBlock R p q P N := by
  have hn : N∈Icc 0 frameCap := ⟨hN,hNP.trans hP⟩
  have hsin := (transport_trig hn).2.2.1
  have hloss := cap_cosine_loss hn
  have hloss0 : 0≤1-Real.cos N := sub_nonneg.mpr (Real.cos_le_one N)
  have hcap := NegativeEH.SameBlock.cap_phi
  have hfirst := mul_le_mul_of_nonneg_right hcap.1.le hloss0
  have hsecond := mul_le_mul_of_nonneg_right hcap.2.le hsin
  have hid : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)+
      (341/200)*(Real.cos N-1)=
      (PositiveAngularEnvelope.phi frameCap-341/200)*(1-Real.cos N)+
        (Real.cos frameCap-Real.sin frameCap)*Real.sin N := by
    simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
    ring
  have hbracket : 0≤PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)+
      (341/200)*(Real.cos N-1) := by
    rw [hid]
    nlinarith only [hfirst,hsecond,hloss,hsin,hloss0]
  have hscaled := mul_nonneg hp hbracket
  have hdiff := mul_le_mul_of_nonneg_left
    (NegativeEH.SameBlock.phi_difference hN hNP hP) hp
  have hcoef := mul_le_mul_of_nonpos_right hqp
    (sub_nonpos.mpr (Real.cos_le_one N))
  have he : mixedBlock R p q P N-U R p q (P-N)=
      p*(PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N))+q*(Real.cos N-1) := by
    dsimp [mixedBlock,U]
    ring
  rw [←sub_nonneg,he]
  nlinarith only [hscaled,hdiff,hcoef]

lemma family_ratio (f : Family) {θ : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f)) (i : Fin 3) :
    Explicit.q f θ i≤(341/200)*Explicit.p f θ i := by
  cases f
  · have hb := Explicit.low_bounds hθ
    have hm : 1≤Explicit.m .low θ := by linarith [hb.2.1]
    fin_cases i
    · change (1:ℝ)≤(341/200)*Explicit.k .low θ
      linarith [hb.1.1]
    · change (1:ℝ)≤(341/200)*Explicit.k .low θ
      linarith [hb.1.1]
    · change max 1 (Explicit.m .low θ) ≤ (341/200)*min 1 (Explicit.m .low θ)
      rw [min_eq_left hm,max_eq_right hm]
      linarith [hb.2.2]
  · have hh := Explicit.high_pairs hθ i
    linarith [hh.1,hh.2.2]

lemma sine_monotone : MonotoneOn Real.sin (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
    (fun x _ => (Real.hasDerivAt_sin x).continuousAt.continuousWithinAt)
    (fun x _ => Real.hasDerivAt_sin x)
  intro x hx
  linarith [(transport_trig (Ioo_subset_Icc_self hx)).1]

lemma shifted_cosine_difference {θ s : ℝ}
    (hθ : θ∈Icc 0 frameCap) (hs : s∈Icc 0 θ) :
    Real.cos frameCap-Real.cos θ≤Real.cos (frameCap-s)-Real.cos (θ-s) := by
  have hcos : Real.cos frameCap≤Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
      (by norm_num [frameCap]; linarith [Real.pi_gt_three]) hθ.2
  have hsin := sine_monotone hθ
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hθ.2
  have hss := (transport_trig (show s∈Icc 0 frameCap from ⟨hs.1,hs.2.trans hθ.2⟩)).2.2.1
  have h₁ := mul_nonneg_of_nonpos_of_nonpos
    (sub_nonpos.mpr hcos) (sub_nonpos.mpr (Real.cos_le_one s))
  have h₂ := mul_nonneg (sub_nonneg.mpr hsin) hss
  rw [Real.cos_sub,Real.cos_sub]
  nlinarith only [h₁,h₂]

theorem low_H_negative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 θ) :
    V R (Explicit.k .low θ) 1 (θ-s)≤
      mixedBlock R (Explicit.k .low θ) 1 (frameCap-θ) (frameCap-s) := by
  have ht := Explicit.frame_domain .low hθ
  have hc := PositiveBT3.LowEnvelope.correction_positive hθ
  have hh := shifted_cosine_difference ht hs
  have he : mixedBlock R (Explicit.k .low θ) 1 (frameCap-θ) (frameCap-s)-
      V R (Explicit.k .low θ) 1 (θ-s)=
      Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+
        Real.cos (frameCap-s)-Real.cos (θ-s) := by
    dsimp [mixedBlock,V]
    rw [show frameCap-θ-(frameCap-s)= -(θ-s) by ring]
    ring
  dsimp [PositiveBT3.LowEnvelope.correction] at hc
  change 0<Explicit.k .low θ*(PositiveAngularEnvelope.phi (frameCap-θ)-1)+Real.cos frameCap-Real.cos θ at hc
  rw [←sub_nonneg,he]
  linarith

theorem low_negative {θ s : ℝ} (hθ : θ∈Icc (0:ℝ) (1/6))
    (hs : s∈Icc 0 θ) (i : Fin 3) :
    Explicit.V .low θ i (θ-s)≤ mixedBlock R (Explicit.p .low θ i)
      (Explicit.q .low θ i) (frameCap-θ) (frameCap-s) := by
  have ht := Explicit.frame_domain .low hθ
  have hm := (Explicit.low_bounds hθ).2
  have hm1 : 1≤Explicit.m .low θ := by linarith [hm.1]
  fin_cases i
  · exact low_H_negative hθ hs
  · simpa [Explicit.V,Explicit.p,Explicit.q,Explicit.l] using low_H_negative hθ hs
  · have hN : frameCap-s∈Icc 0 frameCap :=
      ⟨by linarith [hs.2,ht.2],by linarith [hs.1]⟩
    have hsin := mul_le_mul_of_nonneg_left (transport_trig hN).2.2.2.1.le
      (show 0≤Explicit.m .low θ by linarith [hm.1])
    have hh := NegativeAPositiveTD.SameBlock.negative_surplus
      (p:=(1:ℝ)) (q:=Explicit.m .low θ) (by norm_num)
      (show frameCap-θ∈Icc 0 (frameCap-s) from
        ⟨by linarith [ht.2],by linarith [hs.2]⟩) hN
      (show Explicit.m .low θ*Real.sin (frameCap-s)≤1 by nlinarith [hm.2])
    change V R (min 1 (Explicit.m .low θ)) (max 1 (Explicit.m .low θ)) (θ-s) ≤
      mixedBlock R (min 1 (Explicit.m .low θ)) (max 1 (Explicit.m .low θ)) (frameCap-θ) (frameCap-s)
    rw [min_eq_left hm1,max_eq_right hm1,show θ-s=frameCap-s-(frameCap-θ) by ring]
    exact hh

theorem high_negative {θ P N : ℝ} (hθ : θ∈Icc (1/6:ℝ) (7/10))
    (hP : 0≤P) (hPN : P≤N) (hN : N≤frameCap) (i : Fin 3) :
    Explicit.V .high θ i (N-P)≤
      mixedBlock R (Explicit.p .high θ i) (Explicit.q .high θ i) P N := by
  have hp := Explicit.high_pairs hθ i
  have hn : N∈Icc 0 frameCap := ⟨hP.trans hPN,hN⟩
  have hsin := mul_le_mul_of_nonneg_left (transport_trig hn).2.2.2.1.le
    (hp.1.trans_le hp.2.1).le
  exact NegativeAPositiveTD.SameBlock.negative_surplus hp.1.le ⟨hP,hPN⟩ hn
    (by nlinarith [hp.2.2])

/-- All ordinary same-block endpoints, with no restriction on the surplus sign. -/
theorem ordinary_saturated_lower (f : Family) {θ z s : ℝ}
    (hθ : θ∈Icc (Explicit.left f) (Explicit.right f))
    (hs : s∈Icc 0 frameCap) (i : Fin 3) :
    Blocks.pure f θ z s i.castSucc i.castSucc≤
      Blocks.saturated f θ z s i.castSucc i.castSucc := by
  have ht := Explicit.frame_domain f hθ
  have hP : 0≤frameCap-θ := sub_nonneg.mpr ht.2
  have hN : 0≤frameCap-s := sub_nonneg.mpr hs.2
  have hsat : Blocks.saturated f θ z s i.castSucc i.castSucc=
      Blocks.block f θ z s (frameCap-θ) (frameCap-s) i.castSucc := by
    simp only [Blocks.saturated,ChargedHybridConcentration.saturated,
      Blocks.block,↓reduceIte]
  rw [hsat,Blocks.block_ordinary]
  by_cases he : s≤θ
  · have hpure : Blocks.pure f θ z s i.castSucc i.castSucc=
        Blocks.negative f θ (θ-s) i.castSucc := by
      simp only [Blocks.pure,ChargedHybridConcentration.pure,ite_eq_left he,Blocks.negative]
    rw [hpure,Blocks.negative_ordinary]
    cases f
    · exact low_negative hθ ⟨hs.1,he⟩ i
    · have hh := high_negative hθ hP (by linarith : frameCap-θ≤frameCap-s)
        (by linarith [hs.1] : frameCap-s≤frameCap) i
      simpa only [show frameCap-s-(frameCap-θ)=θ-s by ring] using hh
  · have hpure : Blocks.pure f θ z s i.castSucc i.castSucc=
        Blocks.positive f θ z s (s-θ) i.castSucc := by
      simp only [Blocks.pure,ChargedHybridConcentration.pure,ite_eq_right he,Blocks.positive]
    rw [hpure,Blocks.positive_ordinary]
    have hp := Explicit.family_pairs f hθ i
    have hh := positive hp.1.le (family_ratio f hθ i) hN
      (by linarith : frameCap-s≤frameCap-θ) (by linarith [ht.1] : frameCap-θ≤frameCap)
    simpa only [show frameCap-θ-(frameCap-s)=s-θ by ring,Explicit.U] using hh

end SquaresInCircles.Eight.GlobalGA.NegativeDEPositiveBT.SameBlock
end
end
end

section
/-!
## Intrinsic endpoint certificates for the large-A negative-E stress

The three ordinary pairs are H, G, B. The fourth repeats H for the
negative part of the sorted-D minorant. All norm comparisons use positive
squaring and alternating Taylor bounds at the displayed intrinsic angles.
The two combined gains have independent positive endpoint certificates.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
open Secondary PositiveAngularEnvelope PairNormCalculus OrdinaryAngleConcavity
open Arithmetic HighOrderTaylor

abbrev L : ℝ := 1/6
abbrev u : ℝ := 1/4
abbrev span : ℝ := 8/15
abbrev radiusLo : ℝ := 1978787507/1000000000
abbrev radiusHi : ℝ := 494696877/250000000
abbrev diagonalHi : ℝ := 449607033/500000000

def p : Fin 4→ℝ := ![k,k,l,k]
def q : Fin 4→ℝ := ![1,l,c,1]
def base : ℝ := k+2*l+2*c+2-
  fullSupport 1 k-fullSupport l k-fullSupport c l-(1+c)*GlobalGA.Secondary.diagonal
def g (s : ℝ) : ℝ := K*Real.sin s-beta*(1-Real.cos s)
def jointGain (w : ℝ) : ℝ := if w≤u then g w else g u+M*(w-u)

def normZeroLower : Fin 4→ℝ := ![1230483/1000000,1161673/1000000,751439/500000,1230483/1000000]
def normZeroUpper : Fin 4→ℝ := ![307621/250000,580837/500000,1502879/1000000,307621/250000]
def normLeftUpper : Fin 4→ℝ := ![141211/125000,1063979/1000000,275453/200000,141211/125000]
def normCapUpper : Fin 4→ℝ := ![384149/500000,355361/500000,923977/1000000,384149/500000]
def normCutPositiveUpper : Fin 4→ℝ := ![639033/500000,603859/500000,195263/125000,639033/500000]
def normCutNegativeUpper : Fin 4→ℝ := ![117948/125000,88283/100000,143073/125000,117948/125000]
def normSpanUpper : Fin 4→ℝ := ![748857/500000,354951/250000,458761/250000,748857/500000]

theorem coefficients (i : Fin 4) :
    0<p i ∧ p i≤q i ∧ (2/3)*q i≤p i ∧ k≤p i ∧ l≤q i ∧ q i≤c := by
  fin_cases i <;> norm_num [p,q,k,l,c]

theorem radius_tight : radiusLo<R ∧ R<radiusHi := by
  have h := radius_sq
  have hpos := Real.sqrt_nonneg qCap
  constructor <;> norm_num [radiusLo,radiusHi,qCap] at * <;> nlinarith

theorem diagonal_tight : GlobalGA.Secondary.diagonal<diagonalHi := by
  have h := diagonal_circle
  have hpos : 0≤GlobalGA.Secondary.diagonal+1/2 := by linarith [diagonal_bounds.1]
  norm_num [diagonalHi,qCap] at *
  nlinarith

theorem norm_zero (i : Fin 4) :
    normZeroLower i<pairNorm (p i) (q i) 0 ∧
      pairNorm (p i) (q i) 0<normZeroUpper i := by
  rw [pairNorm_zero]
  have hl : 0≤normZeroLower i := by fin_cases i <;> norm_num [normZeroLower]
  have hu : 0<normZeroUpper i := by fin_cases i <;> norm_num [normZeroUpper]
  rw [Real.lt_sqrt hl,Real.sqrt_lt' hu]
  fin_cases i <;> norm_num [p,q,normZeroLower,normZeroUpper,k,l,c]

theorem norm_negative_endpoints (i : Fin 4) :
    pairNorm (p i) (q i) (-L)<normLeftUpper i ∧
    pairNorm (p i) (q i) (-frameCap)<normCapUpper i ∧
    pairNorm (p i) (q i) (-(frameCap-u))<normCutNegativeUpper i := by
  have hc := coefficients i
  have hL := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:= -L) (by norm_num [L,frameCap])
  have hh := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:= -frameCap) (by norm_num [frameCap])
  have hu := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:= -(frameCap-u))
    (by norm_num [u,frameCap])
  have hLp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:= -L) (by norm_num [L,frameCap])
  have hhp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:= -frameCap) (by norm_num [frameCap])
  have hup := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:= -(frameCap-u))
    (by norm_num [u,frameCap])
  have hSL := S11_le_sin (show (0:ℝ)≤L by norm_num [L])
  have hSh := S11_le_sin (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hSu := S11_le_sin (show (0:ℝ)≤frameCap-u by norm_num [u,frameCap])
  fin_cases i <;>
    norm_num [p,q,normLeftUpper,normCapUpper,normCutNegativeUpper,k,l,c,L,u,frameCap,
      pairEnergy,pairProduct,Real.sin_neg,S11,sin9,sin7] at hL hh hu hLp hhp hup hSL hSh hSu ⊢ <;>
    constructor <;> first | nlinarith | constructor <;> nlinarith

theorem norm_positive_endpoints (i : Fin 4) :
    pairNorm (p i) (q i) (u-L)<normCutPositiveUpper i ∧
    pairNorm (p i) (q i) span<normSpanUpper i := by
  have hc := coefficients i
  have hu := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:=u-L) (by norm_num [u,L,frameCap])
  have hh := pairNorm_sq hc.1 (hc.1.trans_le hc.2.1) (t:=span) (by norm_num [span,frameCap])
  have hup := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:=u-L) (by norm_num [u,L,frameCap])
  have hhp := pairNorm_pos hc.1 (hc.1.trans_le hc.2.1) (t:=span) (by norm_num [span,frameCap])
  have hSu := sin_le_sin9 (show (0:ℝ)≤u-L by norm_num [u,L])
  have hSh := sin_le_sin9 (show (0:ℝ)≤ span by norm_num [span])
  fin_cases i <;>
    norm_num [p,q,normCutPositiveUpper,normSpanUpper,k,l,c,u,L,span,
      pairEnergy,pairProduct,sin9,sin7] at hu hh hup hhp hSu hSh ⊢ <;>
    constructor <;> nlinarith

theorem radius_norm_upper {n b : ℝ} (hb : 0<b) (hn : n≤b) : R*n<radiusHi*b := by
  have h₁ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg qCap)
  have h₂ := mul_lt_mul_of_pos_right radius_tight.2 hb
  exact h₁.trans_lt h₂

theorem radius_norm_zero_lower (i : Fin 4) :
    radiusLo*normZeroLower i<R*pairNorm (p i) (q i) 0 := by
  have hlo : 0<normZeroLower i := by fin_cases i <;> norm_num [normZeroLower]
  have h₁ := mul_lt_mul_of_pos_right radius_tight.1 hlo
  have h₂ := mul_le_mul_of_nonneg_left (norm_zero i).1.le (Real.sqrt_nonneg qCap)
  exact h₁.trans_le h₂

theorem base_lower : -(2093/100000:ℝ)<base := by
  have hH := radius_norm_upper
    (show 0<normZeroUpper 0 by norm_num [normZeroUpper]) (norm_zero 0).2.le
  have hG := radius_norm_upper
    (show 0<normZeroUpper 1 by norm_num [normZeroUpper]) (norm_zero 1).2.le
  have hB := radius_norm_upper
    (show 0<normZeroUpper 2 by norm_num [normZeroUpper]) (norm_zero 2).2.le
  have hd := diagonal_tight
  rw [base,fullSupport_pair k 1,fullSupport_pair k l,fullSupport_pair l c]
  norm_num [p,q,normZeroUpper,k,l,c,radiusHi,diagonalHi] at hH hG hB hd ⊢
  linarith

theorem charge_short {a : ℝ} (ha : a=L ∨ a=u) :
    (if a=L then -(7933/50000:ℝ) else -(12091/50000))<TwoPositive.ASupport.charge a := by
  have ha0 : 0≤a := by rcases ha with rfl|rfl <;> norm_num [L,u]
  have haα : a≤TwoPositive.ASupport.alpha := by
    rcases ha with rfl|rfl <;> dsimp [L,u] <;> linarith [TwoPositive.ASupport.alpha_bounds.1]
  rw [TwoPositive.ASupport.charge,ite_eq_left haα]
  have hC := cos10_le_cos ha0
  have hS := sin_le_sin9 ha0
  have hs0 : 0≤Real.sin a := (transport_trig (show a∈Icc 0 frameCap by
    rcases ha with rfl|rfl <;> norm_num [L,u,frameCap])).2.2.1
  have hm := mul_le_mul_of_nonneg_right
    (show axial-1/2≤114322/125000 by linarith [axial_bounds.2]) hs0
  rcases ha with rfl|rfl <;>
    norm_num [L,u,cos10,cos8,sin9,sin7,TwoPositive.ASupport.axialCharge] at hC hS hm ⊢ <;>
    linarith

theorem charge_cap_lower : -(71283/100000:ℝ)<TwoPositive.ASupport.charge frameCap := by
  rw [TwoPositive.ASupport.charge,ite_eq_right (not_le.mpr TwoPositive.ASupport.alpha_bounds.2)]
  dsimp only [TwoPositive.ASupport.circleCharge]
  rw [show frameCap/2=7/20 by norm_num [frameCap],show frameCap=7/10 from rfl]
  have hS := S11_le_sin (show (0:ℝ)≤7/10 by norm_num)
  have hH := sin_le_sin9 (show (0:ℝ)≤7/20 by norm_num)
  have hs0 := (TwoPositive.ASupport.half_trig
    (show (7/10:ℝ)∈Icc 0 frameCap by norm_num [frameCap])).1
  rw [show (7/10:ℝ)/2=7/20 by norm_num] at hs0
  have hm := mul_le_mul_of_nonneg_right radius_tight.2.le hs0
  norm_num [S11,sin9,sin7] at hS hH
  simp only [radiusHi] at hm
  linarith

theorem gain_endpoints : (17063/100000:ℝ)<g L ∧ (12381/50000:ℝ)<g u := by
  have hSL := S11_le_sin (show (0:ℝ)≤L by norm_num [L])
  have hCL := cos10_le_cos (show (0:ℝ)≤L by norm_num [L])
  have hSu := S11_le_sin (show (0:ℝ)≤u by norm_num [u])
  have hCu := cos10_le_cos (show (0:ℝ)≤u by norm_num [u])
  norm_num [L,u,S11,sin9,sin7,cos10,cos8] at hSL hCL hSu hCu
  constructor <;> dsimp [g,K,beta] <;> linarith

def leftReserve : Fin 4→ℝ := ![491/25000,147/10000,413/6250,491/25000]
def capReserve : Fin 4→ℝ := ![139/20000,247/50000,4813/25000,139/20000]
def cutPositiveReserve : Fin 4→ℝ := ![4471/100000,191/4000,1869/50000,4471/100000]
def cutNegativeReserve : Fin 4→ℝ := ![1083/25000,1797/50000,8269/50000,1083/25000]
def jointCapReserve : Fin 4→ℝ := ![28807/100000,3826/12500,23237/100000,28807/100000]
def linearCapReserve : Fin 4→ℝ := ![3017/10000,31971/100000,123/500,3017/10000]

theorem negative_endpoint_reserves (i : Fin 4) :
    leftReserve i<base+l*TwoPositive.ASupport.charge L+V R (p i) (q i) L ∧
    capReserve i<base+l*TwoPositive.ASupport.charge frameCap+V R (p i) (q i) frameCap ∧
    cutNegativeReserve i<base+l*TwoPositive.ASupport.charge frameCap+g u+
      V R (p i) (q i) (frameCap-u) := by
  have hn0 := radius_norm_zero_lower i
  have hnL := radius_norm_upper
    (show 0<normLeftUpper i by fin_cases i <;> norm_num [normLeftUpper]) (norm_negative_endpoints i).1.le
  have hnh := radius_norm_upper
    (show 0<normCapUpper i by fin_cases i <;> norm_num [normCapUpper]) (norm_negative_endpoints i).2.1.le
  have hnu := radius_norm_upper
    (show 0<normCutNegativeUpper i by fin_cases i <;> norm_num [normCutNegativeUpper])
    (norm_negative_endpoints i).2.2.le
  have hAL : -(7933/50000:ℝ)<TwoPositive.ASupport.charge L := by
    simpa using charge_short (a:=L) (Or.inl rfl)
  have hAh := charge_cap_lower
  have hgu := gain_endpoints.2
  have hCL := cos10_le_cos (show (0:ℝ)≤L by norm_num [L])
  have hCh := cos10_le_cos (show (0:ℝ)≤frameCap by norm_num [frameCap])
  have hCu := cos10_le_cos (show (0:ℝ)≤frameCap-u by norm_num [frameCap,u])
  have hb := base_lower
  simp only [V]
  fin_cases i <;>
    norm_num [p,q,normZeroLower,normLeftUpper,normCapUpper,normCutNegativeUpper,
      k,l,c,L,u,frameCap,radiusLo,radiusHi,cos10,cos8,leftReserve,capReserve,cutNegativeReserve]
      at hn0 hnL hnh hnu hAL hAh hgu hCL hCh hCu hb ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;> linarith

theorem positive_endpoint_reserves (i : Fin 4) :
    cutPositiveReserve i<base+l*TwoPositive.ASupport.charge L+g u+U R (p i) (q i) (u-L) ∧
    jointCapReserve i<base+l*TwoPositive.ASupport.charge L+g u+M*(frameCap-u)+
      U R (p i) (q i) span ∧
    linearCapReserve i<base+l*TwoPositive.ASupport.charge L+M*frameCap+
      U R (p i) (q i) span := by
  have hn0 := radius_norm_zero_lower i
  have hnu := radius_norm_upper
    (show 0<normCutPositiveUpper i by fin_cases i <;> norm_num [normCutPositiveUpper])
    (norm_positive_endpoints i).1.le
  have hnh := radius_norm_upper
    (show 0<normSpanUpper i by fin_cases i <;> norm_num [normSpanUpper])
    (norm_positive_endpoints i).2.le
  have hAL : -(7933/50000:ℝ)<TwoPositive.ASupport.charge L := by
    simpa using charge_short (a:=L) (Or.inl rfl)
  have hgu := gain_endpoints.2
  have hCu := cos10_le_cos (show (0:ℝ)≤u-L by norm_num [u,L])
  have hSu := S11_le_sin (show (0:ℝ)≤u-L by norm_num [u,L])
  have hCh := cos10_le_cos (show (0:ℝ) ≤ span by norm_num [span])
  have hSh := S11_le_sin (show (0:ℝ) ≤ span by norm_num [span])
  have hb := base_lower
  simp only [U,PositiveAngularEnvelope.phi]
  fin_cases i <;>
    norm_num [p,q,normZeroLower,normCutPositiveUpper,normSpanUpper,k,l,c,M,L,u,span,frameCap,
      radiusLo,radiusHi,cos10,cos8,S11,sin9,sin7,cutPositiveReserve,jointCapReserve,linearCapReserve]
      at hn0 hnu hnh hAL hgu hCu hSu hCh hSh hb ⊢ <;>
    refine ⟨?_,?_,?_⟩ <;> linarith

theorem zero_increment_reserves :
    (117/25000:ℝ)<base+l*TwoPositive.ASupport.charge L+g L ∧
    (283/50000:ℝ)<base+l*TwoPositive.ASupport.charge u+g u ∧
    (907/20000:ℝ)<base+l*TwoPositive.ASupport.charge frameCap+g u+M*(frameCap-u) ∧
    (411/50000:ℝ)<base+l*TwoPositive.ASupport.charge L+M*L ∧
    (369/6250:ℝ)<base+l*TwoPositive.ASupport.charge frameCap+M*frameCap := by
  have hb := base_lower
  have hAL : -(7933/50000:ℝ)<TwoPositive.ASupport.charge L := by
    simpa using charge_short (a:=L) (Or.inl rfl)
  have hAu : -(12091/50000:ℝ)<TwoPositive.ASupport.charge u := by
    simpa [L,u] using charge_short (a:=u) (Or.inr rfl)
  have hAh := charge_cap_lower
  have hgL := gain_endpoints.1
  have hgu := gain_endpoints.2
  norm_num [l,L,u,M,frameCap] at *
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
end
end
end

section
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.GlobalGA.NegativeELargeA
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
    simp only [positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
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
    simp only [positive,PositiveTD.Hybrid.positive,ite_eq_right hi]
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

/-- The pure signed excess comes from the two independent sign totals, before any scalar gain is
chosen. -/
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
    rw [ite_eq_left hwa]
    have hh := line_negative_excess i j ⟨hP0,by linarith⟩ ⟨hN0,by linarith [hw.1]⟩
    rw [hbalance] at hh
    exact hh.trans hij
  · refine ⟨i,?_⟩
    rw [ite_eq_right hwa]
    have hh := line_positive_excess i j
      ⟨hP0,by dsimp [L,span,frameCap] at ha hPt ⊢; linarith [ha.1]⟩
      ⟨hN0,by linarith⟩
    have he : (∑k,P k)-(∑k,N k)=w-a := by linarith
    rw [he] at hh
    exact hh.trans hij

end SquaresInCircles.Eight.GlobalGA.NegativeELargeA
end
end
end
