module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3LowSaturatedG

/-!
# The low separated H and G reference curves

Uncompiled Section 5. Their positive allowance is the fixed .68125(h-z).
The widened AB baseline slope is greater than 1.03l; the fixed-G slope
is less than .93l, and the two H comparisons retain their original
1.032 and .964 upper slopes. Each combined curve minimizes at s=0.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open Angular NegativeAPositiveTD.NegativeSlope

inductive Case where
  | abG | abH | gaH
  deriving DecidableEq
def atG : Case→Bool | .gaH=>true | _=>false
def larger (e : Case) (l : ℝ) : ℝ := if e=.abG then l else 1
def upperValue : Case→ℝ | .abG=>93/100 | .abH=>129/125 | .gaH=>241/250
def curve (e : Case) (k l c z s : ℝ) : ℝ :=
  extension (atG e) k l c s z+V R k (larger e l) (frameCap-s)
def first (e : Case) (k l c z s : ℝ) : ℝ :=
  angleSlope l (ratio (atG e) k l c) s-Vd R k (larger e l) (frameCap-s)
def allowance (z : ℝ) : ℝ := (109/160)*(frameCap-z)

theorem curve_hasDerivAt (e : Case) {k l c z s : ℝ}
    (hk : 0<k) (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (curve e k l c z) (first e k l c z s) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hq : 0<larger e l := by cases e <;> simp [larger] <;> positivity
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd := (extension_hasDerivAt (atG e) hl hc).add
    ((V_hasDerivAt hk hq hN).comp s ((hasDerivAt_id s).const_sub frameCap))
  convert hd using 1
  · rfl
  · dsimp [first]
    ring

theorem upper_original (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    Vd R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s)<
      upperValue e*larger e (Explicit.l .low z) := by
  have hb := Explicit.low_ranges hz
  have hp := Explicit.family_positive .low hz
  have hkl := (Explicit.family_basic_domain .low hz).2.2.2.1
  have hratio := Explicit.low_ratio hz
  cases e
  · apply LowSlopes.G_upper hp.1 hkl.le (by linarith [hratio.1]) hratio.2.le
    dsimp [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  · apply NegativeAPositiveTD.NegativeSlope.upper_bound .H32 hp.1
      (by linarith [hb.1.2]) (by linarith [hb.1.1])
      (by norm_num [upperRatio]; linarith [hb.1.2])
    dsimp [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  · apply NegativeAPositiveTD.NegativeSlope.upper_bound .H45 hp.1
      (by linarith [hb.1.2]) (by linarith [hb.1.1])
      (by norm_num [upperRatio]; linarith [hb.1.2])
    dsimp [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

theorem first_positive (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    0<first e (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z s := by
  have hV := upper_original e hz hs
  have hl := (Explicit.low_ranges hz).2.1.1
  cases e
  · have hB := LowSlopes.AB_original hz hs
    dsimp [first,atG,larger,upperValue,ratio,affected] at hV ⊢
    linarith
  · have hB := LowSlopes.AB_original hz hs
    dsimp [first,atG,larger,upperValue,ratio,affected] at hV ⊢
    linarith
  · have hB := LowSlopes.GA_original hz hs
    dsimp [first,atG,larger,upperValue,ratio,affected] at hV ⊢
    linarith

theorem fixed_zero_le (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) 0 z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) frameCap≤
      baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s) := by
  have hp := Explicit.family_positive .low hz
  have hzero : (0:ℝ)∈Icc 0 (Explicit.angleCut (atG e)) := by
    cases e <;> norm_num [atG,Explicit.angleCut,NegativeAPositiveTD.Explicit.angleCut]
  have hm : MonotoneOn (curve e (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) z)
      (Icc (0:ℝ) (Explicit.angleCut (atG e))) := by
    apply monoOn_of_hasDeriv_nonneg
      (fun s hs => (curve_hasDerivAt e hp.1 hp.2.1 (Explicit.angle_domain _ hs).2).continuousAt.continuousWithinAt)
      (fun s hs => curve_hasDerivAt e hp.1 hp.2.1 (Explicit.angle_domain _ (Ioo_subset_Icc_self hs)).2)
    intro s hs
    exact (first_positive e hz (Ioo_subset_Icc_self hs)).le
  have hh := hm hzero hs hs.1
  dsimp [curve] at hh
  rw [←baseline_eq_extension (atG e) _ _ _ _ (Explicit.angle_domain _ hzero).2,
    ←baseline_eq_extension (atG e) _ _ _ _ (Explicit.angle_domain _ hs).2,sub_zero] at hh
  exact hh

theorem H_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z-
      allowance z+V R (Explicit.k .low z) 1 (frameCap-s) := by
  have hzero := (low_endpoints hz).2.2.1
  cases atG
  · have hh := fixed_zero_le .abH hz hs
    simp only [atG,larger,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith
  · have hh := fixed_zero_le .gaH hz hs
    simp only [atG,larger,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith

theorem G_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/4:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.m .low z) s z-
      allowance z+V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s) := by
  have hzero := (low_endpoints hz).2.2.2.1
  cases atG
  · have hh := fixed_zero_le .abG hz hs
    simp only [atG,larger,↓reduceIte,baseline_zero] at hh
    dsimp [allowance,lambdaG,NegativeAPositiveTD.lambdaG]
    linarith
  · have hh := LowSaturatedG.GA_negative_zero_le hz hs
    simp only [LowSaturatedG.negative,NegativeAPositiveTD.secant,Real.cos_zero,div_one,
      sub_zero,baseline_zero] at hh
    dsimp [allowance,lambdaG,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.secant]
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3.LowSeparated
