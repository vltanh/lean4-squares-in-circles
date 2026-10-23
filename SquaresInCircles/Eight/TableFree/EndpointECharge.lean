module

public import SquaresInCircles.Eight.TableFree.EndpointBudgetScalars
public import SquaresInCircles.Eight.TableFree.EPairMinimum
public import SquaresInCircles.Eight.TableFree.MiddleAngularPenalty

/-!
# Original E remainders in the endpoint stress

Uncompiled source draft.  The positive charge uses the actual E circle
and its transverse corner floor.  Negative EH1 charges retain the actual
EH1 inequality when obtaining the stronger tangent bounds.  The DE3
negative charge needs no substituted EH witness.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EndpointECharge
open PositiveAngularEnvelope CorrelatedSameBlock MiddleAngularPenalty
open EndpointRotationPenalty EndpointBudgetScalars

def JH (E : SignedPoint) (r : ℝ) : ℝ :=
  (E.a+1/2)*Real.sin r+(-E.y+1/2)*(1-Real.cos r)-max (Real.sin r) 0

def JD (E : SignedPoint) (r : ℝ) : ℝ :=
  (E.a+1/2)*Real.sin r+(E.y+1/2)*(1-Real.cos r)-max (Real.sin r) 0

theorem JD_le_JH {E : SignedPoint} (hy : E.y≤0) (r : ℝ) : JD E r≤JH E r := by
  have hp := mul_nonneg (neg_nonneg.mpr hy)
    (show 0≤1-Real.cos r by linarith [Real.cos_le_one r])
  dsimp [JD,JH]
  nlinarith

theorem JH_positive {E : SignedPoint} (hy : E.y≤0) {r : ℝ}
    (hr : r∈Icc 0 frameCap) : JH E r=EPairMinimum.J E.a E.y r := by
  simp [JH,EPairMinimum.J,abs_of_nonpos hy,max_eq_left (transport_trig hr).2.2.1]
  ring

theorem short_half_slope {r : ℝ} (hr : r∈Icc 0 (1/2 : ℝ)) :
    1-Real.cos r≤(13/50)*Real.sin r := by
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have hh : (1/2 : ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have hS := sin_upper_five (show (0:ℝ)≤1/2 by norm_num)
  have hC := cos_lower_six (show (0:ℝ)≤1/2 by norm_num)
  have hSm := sin_mono hr' hh hr.2
  have hCm := cos_anti hr' hh hr.2
  norm_num at hS hC
  have hhalf : halfRatio r≤13/50 := by
    dsimp [halfRatio]
    apply (div_le_iff₀ (by linarith : 0<1+Real.cos r)).2
    linarith
  have hr8 : 0≤r ∧ r≤4/5 := ⟨hr.1,by linarith [hr.2]⟩
  have hm := mul_le_mul_of_nonneg_right hhalf (transport_trig hr').2.2.1
  rw [(halfRatio_identities hr8).2] at hm
  exact hm

/-- The transverse floor `Y≥1/2` is used algebraically.  The full-circle
support direction lies below that floor throughout the short span. -/
theorem restricted_support {X Y r : ℝ} (hX : 0≤X) (hY : 1/2≤Y)
    (hc : X^2+Y^2≤qCap) (hr : r∈Icc 0 (1/2 : ℝ)) :
    (X-1)*Real.sin r+Y*(1-Real.cos r)≤positiveGain r := by
  let M : ℝ := Real.sqrt (qCap-1/4)
  have hM0 : 0≤M := Real.sqrt_nonneg _
  have hM2 : M^2=qCap-1/4 := Real.sq_sqrt (by norm_num [qCap])
  have hMu : M<383/200 := by
    have hk := radical_bounds.2.1
    change M-1<914576/1000000 at hk
    linarith
  have hY2 : (1/2 : ℝ)^2≤Y^2 := pow_le_pow_left₀ (by norm_num) hY 2
  have hXM : X≤M := by nlinarith
  have hdiff : 0≤M-X := sub_nonneg.mpr hXM
  have hsum : X+M≤2*M := by linarith
  have hprod := mul_le_mul_of_nonneg_left hsum hdiff
  have hfloor : Y-1/2≤(M-X)*(M+X) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hY) (sub_nonneg.mpr hY)]
  have htransverse : (13/50)*(Y-1/2)≤M-X := by
    have hm := mul_nonneg (show 0≤1-(13/25)*M by linarith) hdiff
    nlinarith
  have hr' : r∈Icc 0 frameCap := ⟨hr.1,by dsimp [frameCap]; linarith [hr.2]⟩
  have hsin0 := (transport_trig hr').2.2.1
  have hhalf := mul_le_mul_of_nonneg_left (short_half_slope hr) (sub_nonneg.mpr hY)
  have hm := mul_le_mul_of_nonneg_right htransverse hsin0
  dsimp [positiveGain,k0]
  change (X-1)*Real.sin r+Y*(1-Real.cos r)≤(M-1)*Real.sin r+(1-Real.cos r)/2
  nlinarith

theorem positive_J_short {E : SignedPoint} (hs : E.Sorted)
    (hc : E.circle≤qCap) {r : ℝ} (hr : r∈Icc 0 (1/2 : ℝ)) :
    EPairMinimum.J E.a E.y r≤positiveGain r := by
  have h := restricted_support
    (show 0≤E.a+1/2 by linarith [hs.1])
    (show 1/2≤|E.y|+1/2 by linarith [abs_nonneg E.y]) hc hr
  simpa [EPairMinimum.J] using h

theorem circle_chord_support {X Y r : ℝ} (hc : X^2+Y^2≤qCap)
    (hr : r∈Icc 0 frameCap) :
    (X-1)*Real.sin r+Y*(1-Real.cos r)≤2*R*Real.sin (r/2)-Real.sin r := by
  have hc' : normSq (X,Y)≤R^2 := by simpa [normSq,R_sq] using hc
  have h := dot_le_radius (v := (Real.sin r,1-Real.cos r)) R_nonneg hc'
  have hsin0 : 0≤Real.sin (r/2) := (half_trig
    (show r/2∈Icc 0 (frameCap/2) by constructor <;> linarith [hr.1,hr.2])).2.1
  have hdouble := cosine_double_shift (r/2)
  have hdouble' : Real.cos r-1= -2*(Real.sin (r/2))^2 := by
    simpa only [show 2*(r/2)=r by ring] using hdouble
  have hn : vectorLength (Real.sin r,1-Real.cos r)=2*Real.sin (r/2) := by
    have hn0 := vectorLength_nonneg (Real.sin r,1-Real.cos r)
    have hn2 := vectorLength_sq (Real.sin r,1-Real.cos r)
    dsimp [normSq] at hn2
    nlinarith [Real.sin_sq_add_cos_sq r]
  rw [hn] at h
  dsimp [dot] at h
  linarith

theorem chord_linear_upper {r : ℝ} (hr : r∈Icc 0 frameCap) :
    2*R*Real.sin (r/2)-Real.sin r≤(41/40)*r := by
  have hRu : R≤1979/1000 := by
    have hR := R_sq
    dsimp [qCap] at hR
    nlinarith [R_nonneg]
  have hhalf : r/2∈Icc 0 (frameCap/2) := by
    constructor <;> linarith [hr.1,hr.2]
  have hsh := (half_trig hhalf).2.1
  have hupper := sin_upper_five hhalf.1
  have hlower := Real.sin_ge_sub_cube hr.1
  have hmul := mul_le_mul hRu hupper hsh (by norm_num : (0:ℝ)≤1979/1000)
  have hr2 : r^2≤(7/10 : ℝ)^2 := by
    exact pow_le_pow_left₀ hr.1 hr.2 2
  have hr4 : r^4≤(7/10 : ℝ)^4 := by
    exact pow_le_pow_left₀ hr.1 hr.2 4
  have hp : 0≤(41/40 : ℝ)-(1979/1000-1)-
      (1/6-(1979/1000)/24)*r^2-((1979/1000)/1920)*r^4 := by
    nlinarith
  have hpr := mul_nonneg hp hr.1
  nlinarith

theorem positive_J_long {E : SignedPoint} (hc : E.circle≤qCap)
    {r : ℝ} (hr : r∈Icc 0 frameCap) :
    EPairMinimum.J E.a E.y r≤(41/40)*r := by
  have h := circle_chord_support hc hr
  have h' := chord_linear_upper hr
  dsimp [EPairMinimum.J]
  linarith

theorem negative_EH_tangent {q r : ℝ} {E H : SignedPoint}
    (hEs : E.Sorted) (hEc : E.AvoidsCore) (hEcont : E.Contained q)
    (hHs : H.Sorted) (hHc : H.AvoidsCore) (hHcont : H.Contained q)
    (hq : q≤qCap) (hy : E.y≤0) (hr : r∈Icc 0 frameCap)
    (hEH : quarterFeasible E H (-r) 1) :
    -E.y<83/200 ∧ (3/25≤r → -E.y<3/10) := by
  obtain ⟨hEa,_,_⟩ := SignedPoint.coordinate_bounds hEs hEc hEcont hq
  obtain ⟨_,hHa,_⟩ := SignedPoint.coordinate_bounds hHs hHc hHcont hq
  have hb : 0≤-E.y := neg_nonneg.mpr hy
  have hsort : -E.y≤E.a := by simpa [abs_of_nonpos hy] using hEs.2
  have hfeas : 1/2+(E.a+1/2)*Real.sin r+(-E.y+1/2)*Real.cos r≤H.a := by
    have hw : edgeWidth (-r)≤H.a+E.a*Real.sin (-r)+E.y*Real.cos (-r) := by
      simpa [quarterFeasible,quarterProjection] using hEH
    rw [edgeWidth_negative_formula hr,Real.sin_neg,Real.cos_neg] at hw
    linarith
  have hφ := one_le_phi hr
  have hsin0 := (transport_trig hr).2.2.1
  have hsorted := mul_nonneg (show 0≤E.a+E.y by linarith) hsin0
  have hphi := mul_le_mul_of_nonneg_left hφ (show 0≤-E.y+1/2 by linarith)
  have hfirst : -E.y<83/200 := by dsimp [phi] at hphi; nlinarith
  refine ⟨hfirst,?_⟩
  intro hr0
  by_contra! hb0
  have hlower : (183/200 : ℝ)<K*Real.sin r+(4/5)*Real.cos r := by
    apply trig_concave_gt (α := 0) (by norm_num [K]) (by norm_num) (by norm_num)
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) ⟨hr0,hr.2⟩
    · have hsin := Real.sin_ge_sub_cube (show (0:ℝ)≤3/25 by norm_num)
      have hcos := Real.one_sub_sq_div_two_le_cos (x := (3/25 : ℝ))
      norm_num [K] at *
      linarith
    · have hsin := sin_lower_seven (show (0:ℝ)≤frameCap by norm_num [frameCap])
      have hcos := cos_lower_six (show (0:ℝ)≤frameCap by norm_num [frameCap])
      norm_num [K,frameCap] at *
      linarith
  have hEprim := mul_nonneg (show 0≤E.a+1/2-K by dsimp [K]; linarith) hsin0
  have hcos0 : 0≤Real.cos r := by linarith [(transport_trig hr).1]
  have hEtan := mul_nonneg (show 0≤-E.y+1/2-4/5 by linarith) hcos0
  nlinarith

theorem JD_negative_bound {q d r : ℝ} {E : SignedPoint}
    (hs : E.Sorted) (hcore : E.AvoidsCore) (hc : E.Contained q)
    (hq : q≤qCap) (hy : E.y≤0) (hd : 1/2≤d) (hr : r∈Icc 0 frameCap) :
    JD E (-r)≤negativeGain d r := by
  obtain ⟨ha,_,_⟩ := SignedPoint.coordinate_bounds hs hcore hc hq
  have hsin0 := (transport_trig hr).2.2.1
  have hprim := mul_nonneg (show 0≤E.a+1/2-K by dsimp [K]; linarith) hsin0
  have htan := mul_nonneg (show 0≤d-(E.y+1/2) by linarith)
    (show 0≤1-Real.cos r by linarith [Real.cos_le_one r])
  simp [JD,negativeGain,Real.sin_neg,Real.cos_neg,
    max_eq_right (neg_nonpos.mpr hsin0)]
  nlinarith

theorem JH_negative_bound {q d r : ℝ} {E : SignedPoint}
    (hs : E.Sorted) (hcore : E.AvoidsCore) (hc : E.Contained q)
    (hq : q≤qCap) (hd : -E.y+1/2≤d) (hr : r∈Icc 0 frameCap) :
    JH E (-r)≤negativeGain d r := by
  obtain ⟨ha,_,_⟩ := SignedPoint.coordinate_bounds hs hcore hc hq
  have hsin0 := (transport_trig hr).2.2.1
  have hprim := mul_nonneg (show 0≤E.a+1/2-K by dsimp [K]; linarith) hsin0
  have htan := mul_nonneg (sub_nonneg.mpr hd)
    (show 0≤1-Real.cos r by linarith [Real.cos_le_one r])
  simp [JH,negativeGain,Real.sin_neg,Real.cos_neg,
    max_eq_right (neg_nonpos.mpr hsin0)]
  nlinarith

end SquaresInCircles.Eight.TableFree.EndpointECharge
