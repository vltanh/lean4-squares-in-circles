module

public import SquaresInCircles.Eight.TableFree.MiddleStress
public import SquaresInCircles.Eight.TableFree.AlignedNegativeAssembly

/-!
# The original aligned-negative H--D span with actual TD0

Uncompiled source draft. The middle stress is applied to the unchanged
cycle and the sorted D support is proved on the entire signed angle
interval. Three finite scalar comparisons eliminate T's frame; they do
not assert a geometric replacement of T. A strict endpoint reserve then
bounds the original H--D span, before any contact or E transport.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace TD0Span
open SpanNormBounds MiddleAngularStress
open OrdinaryNegativeEnvelope OrdinaryNegativeSlope PositiveAngularEnvelope

abbrev lambda : ℝ := 13/20

def f (t : ℝ) : ℝ := 1/2+(3/2-c)*Real.cos t+(13/12)*Real.sin t

def charge (w : ℝ) : ℝ := edgeWidth w-c*(Real.sin w+Real.cos w)
def positiveCharge (w : ℝ) : ℝ := 1/2-(c-1/2)*(Real.sin w+Real.cos w)
def negativeCharge (r : ℝ) : ℝ := 1/2+(c+1/2)*Real.sin r-(c-1/2)*Real.cos r

theorem sorted_support {q w : ℝ} {D : SignedPoint}
    (hs : D.Sorted) (hc : D.Contained q) (hq : q≤qCap)
    (hy : D.y≤0) (hw : |w|≤frameCap) :
    D.a*Real.sin w-D.y*Real.cos w≤c*(Real.sin w+Real.cos w) := by
  let b := -D.y
  have hb0 : 0≤b := neg_nonneg.mpr hy
  have hba : b≤D.a := by simpa [b,abs_of_nonpos hy] using hs.2
  have hbc : b≤c := by
    simpa [b,c,abs_of_nonpos hy] using
      SignedPoint.contained_minor_le_diagonal hs (hc.trans hq)
  have hroot := Real.sqrt_nonneg (qCap/2)
  have hroot2 := Real.sq_sqrt (show 0≤qCap/2 by norm_num [qCap])
  have hcircle : (D.a+1/2)^2+(b+1/2)^2≤qCap := by
    simpa [SignedPoint.Contained,SignedPoint.circle,b,abs_of_nonpos hy] using hc.trans hq
  have hsum : D.a+b≤2*c := by
    dsimp [c,diagonalCoordinate]
    nlinarith [sq_nonneg (D.a-b),hs.1]
  by_cases hw0 : 0≤w
  · have hwi : w∈Icc 0 frameCap := ⟨hw0,(le_abs_self w).trans hw⟩
    obtain ⟨hcos,hcos1,hsin0,hsin,hsc⟩ := transport_trig hwi
    have h1 := mul_le_mul_of_nonneg_right hsum hsin0
    have h2 := mul_le_mul_of_nonneg_right hbc (sub_nonneg.mpr hsc.le)
    dsimp [b] at *
    nlinarith
  · have hwi : -w∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs w).trans hw⟩
    obtain ⟨hcos,hcos1,hsin0,hsin,hsc⟩ := transport_trig hwi
    simp only [Real.sin_neg,Real.cos_neg] at hcos hcos1 hsin0 hsin hsc
    have h1 := mul_le_mul_of_nonpos_right hba (by linarith : Real.sin w≤0)
    have h2 := mul_le_mul_of_nonneg_right hbc (by linarith : 0≤Real.sin w+Real.cos w)
    dsimp [b] at *
    nlinarith

@[simp] theorem positiveCharge_zero : positiveCharge 0=1-c := by simp [positiveCharge]; ring
@[simp] theorem negativeCharge_zero : negativeCharge 0=1-c := by simp [negativeCharge]; ring

theorem charge_of_nonneg {w : ℝ} (hw : w∈Icc 0 frameCap) :
    charge w=positiveCharge w := by
  rw [charge,edgeWidth_positive_formula hw]
  unfold positiveCharge
  ring

theorem charge_of_nonpos {r : ℝ} (hr : r∈Icc 0 frameCap) :
    charge (-r)=negativeCharge r := by
  rw [charge,edgeWidth_negative_formula hr]
  simp only [Real.sin_neg,Real.cos_neg]
  unfold negativeCharge
  ring

theorem positiveCharge_deriv (w : ℝ) :
    HasDerivAt positiveCharge ((c-1/2)*(Real.sin w-Real.cos w)) w := by
  have hsc : HasDerivAt (fun x => Real.sin x+Real.cos x) (Real.cos w+-Real.sin w) w :=
    (Real.hasDerivAt_sin w).add (Real.hasDerivAt_cos w)
  have h : HasDerivAt (fun x => 1/2-(c-1/2)*(Real.sin x+Real.cos x))
      (0-(c-1/2)*(Real.cos w+-Real.sin w)) w :=
    (hasDerivAt_const w (1/2:ℝ)).sub (hsc.const_mul (c-1/2))
  exact h.congr_deriv (by ring)

theorem negativeCharge_deriv (r : ℝ) :
    HasDerivAt negativeCharge ((c+1/2)*Real.cos r+(c-1/2)*Real.sin r) r := by
  have h : HasDerivAt (fun x => 1/2+(c+1/2)*Real.sin x-(c-1/2)*Real.cos x)
      (0+(c+1/2)*Real.cos r-(c-1/2)*(-Real.sin r)) r :=
    ((hasDerivAt_const r (1/2:ℝ)).add
      ((Real.hasDerivAt_sin r).const_mul (c+1/2))).sub
      ((Real.hasDerivAt_cos r).const_mul (c-1/2))
  exact h.congr_deriv (by ring)

theorem positiveCharge_derivative_lower {w : ℝ} (hw : w∈Icc 0 frameCap) :
    -(2/5:ℝ)<(c-1/2)*(Real.sin w-Real.cos w) := by
  obtain ⟨hcos,hcos1,hsin0,hsin,hsc⟩ := transport_trig hw
  have hcoef : 0≤c-1/2 := by linarith [diagonal_bounds.1]
  have hm := mul_le_mul_of_nonneg_left (show Real.cos w-Real.sin w≤1 by linarith) hcoef
  linarith [diagonal_bounds.2]

theorem negativeCharge_derivative_lower {r : ℝ} (hr : r∈Icc 0 frameCap) :
    (33/25:ℝ)<(c+1/2)*Real.cos r+(c-1/2)*Real.sin r := by
  have hcoef : 0<c-1/2 := by linarith [diagonal_bounds.1]
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) (SquaresInCircles.harmonic (c+1/2) (c-1/2)) := by
    apply harmonic_concave
    intro z hz
    obtain ⟨hcos,hcos1,hsin0,hsin,hsc⟩ := transport_trig hz
    have h1 := mul_nonneg (by linarith : 0≤c+1/2) (by linarith : 0≤Real.cos z)
    have h2 := mul_nonneg hcoef.le hsin0
    linarith
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by norm_num [frameCap]) hr
  have hleft : (33/25:ℝ)<SquaresInCircles.harmonic (c+1/2) (c-1/2) 0 := by
    simp only [SquaresInCircles.harmonic,Real.cos_zero,Real.sin_zero,mul_one,mul_zero,add_zero]
    linarith [diagonal_bounds.1]
  have hright : (33/25:ℝ)<SquaresInCircles.harmonic (c+1/2) (c-1/2) frameCap := by
    have hc := (transport_trig (show frameCap∈Icc 0 frameCap by norm_num [frameCap])).1
    have hs := OrdinaryNegativeEnvelope.cap_sin_lower
    have hm1 : (699607/500000:ℝ)*(7648/10000)<(c+1/2)*Real.cos frameCap := by
      calc
        (699607/500000:ℝ)*(7648/10000)<(699607/500000)*Real.cos frameCap :=
          mul_lt_mul_of_pos_left hc (by norm_num)
        _≤(c+1/2)*Real.cos frameCap := mul_le_mul_of_nonneg_right
          (by linarith [diagonal_bounds.1]) (by linarith)
    have hm2 : (199607/500000:ℝ)*(3221/5000)<(c-1/2)*Real.sin frameCap := by
      calc
        (199607/500000:ℝ)*(3221/5000)<(199607/500000)*Real.sin frameCap :=
          mul_lt_mul_of_pos_left hs (by norm_num)
        _≤(c-1/2)*Real.sin frameCap := mul_le_mul_of_nonneg_right
          (by linarith [diagonal_bounds.1]) (by linarith)
    simp only [SquaresInCircles.harmonic]
    linarith
  have hfinal := (lt_min hleft hright).trans_le hmin
  simpa only [SquaresInCircles.harmonic] using hfinal

theorem positiveCharge_lower {w : ℝ} (hw : w∈Icc 0 frameCap) :
    1-c-(2/5)*w≤positiveCharge w := by
  have hh := derivative_reserve
    (by unfold positiveCharge; fun_prop)
    (fun z _ => positiveCharge_deriv z)
    (fun z hz => (positiveCharge_derivative_lower (Ioo_subset_Icc_self hz)).le)
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hw hw.1
  simp only [positiveCharge_zero,sub_zero] at hh
  linarith

theorem negativeCharge_lower {r : ℝ} (hr : r∈Icc 0 frameCap) :
    1-c+(33/25)*r≤negativeCharge r := by
  have hh := derivative_reserve
    (by unfold negativeCharge; fun_prop)
    (fun z _ => negativeCharge_deriv z)
    (fun z hz => (negativeCharge_derivative_lower (Ioo_subset_Icc_self hz)).le)
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hr hr.1
  simp only [negativeCharge_zero,sub_zero] at hh
  linarith

theorem V_upper_growth {x y : ℝ}
    (hx : x∈Icc 0 frameCap) (hy : y∈Icc 0 frameCap) (hxy : x≤y) :
    V lambda y-V lambda x≤(1079/1000)*(y-x) := by
  have hd (z : ℝ) (hz : z∈Icc 0 frameCap) :
      HasDerivAt (V lambda) (Vd lambda z) z :=
    OrdinaryNegativeSlope.V_hasDerivAt (R := R) (by norm_num) (by norm_num) hz
  have hh := derivative_reserve
    (fun z hz => (hd z hz).neg.continuousAt.continuousWithinAt)
    (fun z hz => (hd z (Ioo_subset_Icc_self hz)).neg)
    (fun z hz => neg_le_neg (SpanNormBounds.V_base_upper (Ioo_subset_Icc_self hz)).le)
    hx hy hxy
  simp only [Pi.neg_apply] at hh
  linarith

/-- This scalar minimization retains the original T frame and works with
either sign of its tangent. Every comparison stays inside the original
three-frame interval. -/
theorem eliminate_T_frame {u s : ℝ}
    (hu : u∈Icc 0 frameCap) (hs : |s|≤frameCap) (hw : |-u-s|≤frameCap) :
    V lambda u+1-c≤B lambda s+charge (-u-s) := by
  have hl : lambda∈Icc (13/20:ℝ) (23/25) := by constructor <;> norm_num [lambda]
  have hzero : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  by_cases hs0 : 0 ≤ s
  · have hsi : s∈Icc 0 frameCap := ⟨hs0,(le_abs_self s).trans hs⟩
    have hui : u+s∈Icc 0 frameCap := ⟨add_nonneg hu.1 hs0,by
      have hh := (neg_le_abs (-u-s)).trans hw
      linarith⟩
    have hU := U_growth hl hzero hsi hs0
    have hV := V_upper_growth hzero hu hu.1
    have hC := negativeCharge_lower hui
    rw [B_of_nonneg hs0,show -u-s= -(u+s) by ring,charge_of_nonpos hui]
    change V lambda u+1-c≤U lambda s+negativeCharge (u+s)
    have hUz : U lambda 0=0 := by simp [U,OrdinaryAngleConcavity.U]
    have hVz : V lambda 0=0 := by simp [V,OrdinaryAngleConcavity.V]
    rw [hUz] at hU
    rw [hVz] at hV
    linarith [hu.1]
  · have hv : -s∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs s).trans hs⟩
    rw [B_of_nonpos (by linarith : s≤0)]
    change V lambda u+1-c≤V lambda (-s)+charge (-u-s)
    by_cases hsu : -s≤u
    · have hri : u+s∈Icc 0 frameCap := ⟨by linarith,by linarith [hu.2]⟩
      have hV := V_upper_growth hv hu hsu
      have hC := negativeCharge_lower hri
      rw [show -u-s= -(u+s) by ring,charge_of_nonpos hri]
      linarith
    · have hwi : -u-s∈Icc 0 frameCap := ⟨by linarith,(le_abs_self (-u-s)).trans hw⟩
      have hV := V_growth hl hu hv (by linarith)
      have hC := positiveCharge_lower hwi
      rw [charge_of_nonneg hwi]
      linarith [hwi.1]

theorem f_deriv (t : ℝ) :
    HasDerivAt f (-(3/2-c)*Real.sin t+(13/12)*Real.cos t) t := by
  have h : HasDerivAt (fun x => 1/2+(3/2-c)*Real.cos x+(13/12)*Real.sin x)
      (0+(3/2-c)*(-Real.sin t)+(13/12)*Real.cos t) t :=
    ((hasDerivAt_const t (1/2:ℝ)).add
      ((Real.hasDerivAt_cos t).const_mul (3/2-c))).add
      ((Real.hasDerivAt_sin t).const_mul (13/12:ℝ))
  exact h.congr_deriv (by ring)

theorem f_derivative_lower {t : ℝ} (ht : t∈Icc 0 (9/100:ℝ)) :
    (128/125:ℝ)< -(3/2-c)*Real.sin t+(13/12)*Real.cos t := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,Real.pi_gt_three])
  have hs : Real.sin t≤9/100 :=
    ((le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg ht.1))).trans ht.2
  have hcoef : 0≤3/2-c := by linarith [diagonal_bounds.2]
  have hcoefu : 3/2-c≤601/1000 := by linarith [diagonal_bounds.1]
  have hprod := mul_le_mul hcoefu hs hs0 (by norm_num : (0:ℝ)≤601/1000)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
  have ht2 := pow_le_pow_left₀ ht.1 ht.2 2
  linarith

def endpoint (t : ℝ) : ℝ := f t+3+2*lambda-c-2*R*N lambda 0+V lambda (11/50-t)

theorem endpoint_deriv {t : ℝ} (ht : t∈Icc 0 (9/100:ℝ)) :
    HasDerivAt endpoint
      (-(3/2-c)*Real.sin t+(13/12)*Real.cos t-SpanNormBounds.Vd lambda (11/50-t)) t := by
  have hv : 11/50-t∈Icc 0 frameCap := by
    simp only [frameCap]; constructor <;> linarith [ht.1,ht.2]
  have hV : HasDerivAt (V lambda) (SpanNormBounds.Vd lambda (11/50-t)) (11/50-t) :=
    OrdinaryNegativeSlope.V_hasDerivAt (R := R)
      (show (0:ℝ)<lambda by norm_num [lambda]) (show (0:ℝ)<1 by norm_num) hv
  have hin : HasDerivAt (fun x : ℝ => 11/50-x) (0-1) t :=
    (hasDerivAt_const t (11/50:ℝ)).sub (hasDerivAt_id' t)
  have hd : HasDerivAt (fun x => V lambda (11/50-x))
      (SpanNormBounds.Vd lambda (11/50-t)*(0-1)) t := hV.comp t hin
  have hsum : HasDerivAt (fun x => f x+3+2*lambda-c-2*R*N lambda 0+V lambda (11/50-x))
      ((-(3/2-c)*Real.sin t+(13/12)*Real.cos t)+
        SpanNormBounds.Vd lambda (11/50-t)*(0-1)) t :=
    ((((f_deriv t).add_const 3).add_const (2*lambda)).sub_const c).sub_const
      (2*R*N lambda 0) |>.add hd
  exact hsum.congr_deriv (by ring)

theorem endpoint_increasing : MonotoneOn endpoint (Icc 0 (9/100:ℝ)) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact fun t ht => (endpoint_deriv ht).continuousAt.continuousWithinAt
  · exact fun t ht => endpoint_deriv (Ioo_subset_Icc_self ht)
  · intro t ht
    have hti := Ioo_subset_Icc_self ht
    have hv : 11/50-t∈Icc 0 frameCap := by
      simp only [frameCap]; constructor <;> linarith [hti.1,hti.2]
    have hanti := OrdinaryNegativeSlope.Vd_antitone (R := R) (q := 1) (Real.sqrt_nonneg qCap)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
      (show (0:ℝ)<lambda by norm_num [lambda]) (by norm_num [lambda]) (by norm_num [lambda])
    have hupper := hanti (show (13/100:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hv
      (show 13/100≤11/50-t by linarith [hti.2])
    have hfixed := V_at_013_upper
    have hf := f_derivative_lower hti
    change OrdinaryNegativeSlope.Vd R lambda 1 (11/50-t)≤
      OrdinaryNegativeSlope.Vd R lambda 1 (13/100) at hupper
    change OrdinaryNegativeSlope.Vd R (13/20) 1 (13/100)<101/100 at hfixed
    change 0≤ -(3/2-c)*Real.sin t+(13/12)*Real.cos t-
      OrdinaryNegativeSlope.Vd R lambda 1 (11/50-t)
    simp only [lambda] at hupper ⊢
    linarith

theorem endpoint_zero : (57/10000:ℝ)<endpoint 0 := by
  have hN0 := fixed_norm_bounds.2.1
  have hN22 := fixed_norm_bounds.2.2.2.2.1
  have hsum0 : 0≤N lambda 0+N lambda (-(11/50)) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hprod := mul_le_mul radius_bounds.2.le (add_le_add hN0.le hN22.le)
    hsum0 (by norm_num : (0:ℝ)≤494697/250000)
  have hc := cos_lower_six (show (0:ℝ)≤11/50 by norm_num)
  have hid : endpoint 0=4+2*lambda+Real.cos (11/50)-2*c-
      R*(N lambda 0+N lambda (-(11/50))) := by
    simp [endpoint,f,SpanNormBounds.V,OrdinaryAngleConcavity.V,
      PositiveAngularEnvelope.phi,SpanNormBounds.N,lambda]
    ring
  rw [hid]
  norm_num at hc
  dsimp [lambda] at *
  linarith [diagonal_bounds.2]

/-- Positive on the full original domain; no E state or motion is used. -/
theorem scalar_reserve {t u : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hu : u∈Icc 0 frameCap) (htu : 11/50≤t+u) :
    (57/10000:ℝ)<f t+3+2*lambda-c-2*R*N lambda 0+V lambda u := by
  have hv : 11/50-t∈Icc 0 frameCap := by constructor <;> norm_num [frameCap] at * <;> linarith [ht.1,ht.2]
  have hg := V_growth (show lambda∈Icc (13/20:ℝ) (23/25) by norm_num [lambda])
    hv hu (by linarith)
  have hm := endpoint_increasing (show (0:ℝ)∈Icc 0 (9/100:ℝ) by norm_num) ht ht.1
  have hp := endpoint_zero
  unfold endpoint at hm hp
  linarith

theorem scalar_positive {t u : ℝ}
    (ht : t∈Icc 0 (9/100:ℝ)) (hu : u∈Icc 0 frameCap) (htu : 11/50≤t+u) :
    0<f t+3+2*lambda-c-2*R*N lambda 0+V lambda u :=
  lt_trans (by norm_num) (scalar_reserve ht hu htu)

end TD0Span

open Candidate
namespace AlignedNegative

/-- GA1 and aligned HG give a lower bound for the unchanged A primary. -/
theorem Source.primary_lower {q t : ℝ} {H G A : SignedPoint}
    (I : Source q t H G A) (hq : q≤qCap) : TD0Span.f t≤A.a := by
  have hcuts := I.cuts hq
  have hHy := SignedPoint.contained_minor_le_diagonal I.H_sorted (I.H_contained.trans hq)
  rw [abs_of_nonneg I.H_nonneg] at hHy
  have hHG : 1≤H.y-G.y := by simpa [zeroFeasible,zeroProjection] using I.HG
  have hwi : t∈Icc 0 frameCap := ⟨I.tilt_pos.le,I.tilt_cap⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hwi
  have h1 := mul_le_mul_of_nonneg_right hcuts.1 hs0
  have h2 := mul_le_mul_of_nonneg_right
    (show 1-SpanNormBounds.c≤ -G.y by simp only [SpanNormBounds.c]; linarith)
    (show 0≤Real.cos t by linarith)
  have hga := I.GA
  rw [quarterFeasible,edgeWidth_negative_formula hwi] at hga
  simp only [quarterProjection,Matrix.cons_val,Real.sin_neg,Real.cos_neg] at hga
  unfold TD0Span.f
  linarith

/-- Actual original-cycle TD0 span, with no E hypothesis and no endpoint
certificate passed as a premise. -/
theorem aligned_negative_TD0_span {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (halign : C.theta G=C.theta H)
    (ht : C.theta A<C.theta H) (hyG : (C.point G).y≤0)
    (hGA : C.Feasible G 1) (hnot : ¬C.Feasible G 0)
    (hBT : C.Feasible B 2) (hTD : C.Feasible T 0) :
    C.theta H-C.theta D<11/50 := by
  let I := sourceOfCycle hn ha w halign ht hyG hGA hnot
  let t := C.theta H-C.theta A
  let u := C.theta A-C.theta D
  let s := C.theta T-C.theta A
  have hcuts := I.cuts hq
  have hti : t∈Icc 0 (9/100:ℝ) := ⟨sub_nonneg.mpr ht.le,hcuts.2.2.2.2.2.1.le⟩
  have hstress := SignedCycle.middle_stress hq hn ha w hBT (I.primary_lower hq)
    (show TD0Span.lambda∈Icc (13/20:ℝ) (23/25) by norm_num [TD0Span.lambda])
  have hTDactual : zeroFeasible (C.point T) (C.point D) (-u-s) 0 := by
    simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,delta,next,
      T,D,zeroFeasible,u,s,sub_nonneg] using hTD
  have hwi : |-u-s|≤frameCap := by
    convert hn.spread D T using 1 <;> congr 1 <;> dsimp [u,s] <;> ring
  have hDsup := TD0Span.sorted_support (hn.sorted D) (hn.contained D) hq ha.D_nonpos hwi
  have hcharge : TD0Span.charge (-u-s)≤(C.point T).y := by
    have hh : edgeWidth (-u-s)≤(C.point T).y+(C.point D).a*Real.sin (-u-s)-
        (C.point D).y*Real.cos (-u-s) := by simpa [zeroFeasible,zeroProjection] using hTDactual
    dsimp [TD0Span.charge]
    linarith
  by_contra! hlong
  have hui : u∈Icc 0 frameCap := ⟨by dsimp [u,t] at *; linarith [hti.2],
    (le_abs_self u).trans (hn.spread A D)⟩
  have hsi : |s|≤frameCap := hn.spread T A
  have helim := TD0Span.eliminate_T_frame hui hsi hwi
  have hpos := TD0Span.scalar_positive hti hui (by dsimp [t,u]; linarith)
  have hN0 : SpanNormBounds.N TD0Span.lambda 0=Real.sqrt (1+TD0Span.lambda^2) := by
    simp [SpanNormBounds.N,PositiveAngularEnvelope.pairNorm_zero,add_comm]
  change TD0Span.f t+2+2*TD0Span.lambda-
    2*Real.sqrt qCap*Real.sqrt (1+TD0Span.lambda^2)+MiddleAngularStress.B TD0Span.lambda s+
      (C.point T).y≤0 at hstress
  rw [hN0] at hpos
  dsimp [SpanNormBounds.R] at hpos
  linarith

end AlignedNegative
end SquaresInCircles.Eight.TableFree
