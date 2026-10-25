module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2LowSaturatedG

/-!
# The low separated H and G minima

Uncompiled transcription of (51)--(54). The positive allowance remains
independent of s. The three unaffected derivatives retain the hand
reserves `.127 l`, `.03192`, and `.032`; the affected GA-G case uses
the exact increasing secant curve from (47)--(49).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowSeparated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryNegativeSlope
open SecantBaseline NegativeSlope

private lemma r71_low_dom {z : ℝ} (hz : z∈Icc 0 (1/5:ℝ)) :
    z∈Icc (Certificate.left .low:ℝ) (Certificate.right .low:ℝ) := by
  norm_num [Certificate.left,Certificate.right,Certificate.split]
  exact hz

inductive Case where
  | abG | abH | gaH
  deriving DecidableEq
def atG : Case→Bool | .gaH=>true | _=>false
def larger (e : Case) (l : ℝ) : ℝ := if e=.abG then l else 1
def upperCase : Case→Upper | .abG=>.G32 | .abH=>.H32 | .gaH=>.H45
def curve (e : Case) (k l c z s : ℝ) : ℝ :=
  angularBaseline (atG e) k l c s z+V R k (larger e l) (frameCap-s)
def first (e : Case) (k l c z s : ℝ) : ℝ :=
  angleSlope l (basicRatio (atG e) k l c z) s-Vd R k (larger e l) (frameCap-s)
def allowance (z : ℝ) : ℝ := (109/200)*(Explicit.m .low z+(2/5)*z)*(frameCap-z)

theorem curve_hasDerivAt (e : Case) {k l c z s : ℝ}
    (hk : 0<k) (hl : 0<l) (hs : s∈Icc 0 frameCap) :
    HasDerivAt (curve e k l c z) (first e k l c z s) s := by
  have hc : 0<Real.cos s := by linarith [(transport_trig hs).1]
  have hq : 0<larger e l := by cases e <;> simp [larger] <;> positivity
  have hN : frameCap-s∈Icc 0 frameCap := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have h1 := angularBaseline_hasDerivAt (k:=k) (c:=c) (z:=z) (atG e) hl hc
  have h2 : HasDerivAt (fun s => V R k (larger e l) (frameCap-s))
      (Vd R k (larger e l) (frameCap-s)*(-1)) s :=
    (V_hasDerivAt (R:=R) hk hq hN).comp s ((hasDerivAt_id s).const_sub frameCap)
  refine (h1.fun_add h2).congr_deriv ?_
  simp only [first]
  ring

theorem upper_original (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    Vd R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s)<
      (upperValue (upperCase e):ℝ)*larger e (Explicit.l .low z) := by
  obtain ⟨hklo,hkhi,hllo,hlhi,hclo,hchi⟩ := Explicit.low_ranges hz
  have hp := Explicit.family_positive .low (r71_low_dom hz)
  have hkl := (Explicit.family_basic_domain .low (r71_low_dom hz)).2.2.2.1
  have hratio := Explicit.low_ratio hz
  cases e
  · apply upper_bound .G32 hp.1 hkl.le
      (by linarith [hratio.1])
      (by simpa [upperRatio] using hratio.2.le)
    dsimp [atG,Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  · rw [show larger .abH (Explicit.l .low z)=1 by simp [larger]]
    apply upper_bound .H32 hp.1 (by linarith) (by linarith)
      (by simpa [upperRatio] using hkhi)
    dsimp [atG,Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]
  · rw [show larger .gaH (Explicit.l .low z)=1 by simp [larger]]
    apply upper_bound .H45 hp.1 (by linarith) (by linarith)
      (by simpa [upperRatio] using hkhi)
    dsimp [atG,Explicit.angleCut,upperAngle,frameCap] at hs ⊢
    constructor <;> linarith [hs.1,hs.2]

theorem first_positive (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    0<first e (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z s := by
  have hV := upper_original e hz hs
  have hl := (Explicit.low_ranges hz).2.2.1
  cases e
  · have hB := LowABSlope.original hz hs
    dsimp [first,atG,larger,upperCase,upperValue,basicRatio,affected,Explicit.m] at hV hB ⊢
    have hmargin : (127/1000)*Explicit.l .low z<
        angleSlope (Explicit.l .low z) (PositiveTD.tilted (Explicit.c .low z) z/Explicit.l .low z) s-
          Vd R (Explicit.k .low z) (Explicit.l .low z) (frameCap-s) := by linarith
    nlinarith
  · have hB := LowABSlope.original hz hs
    dsimp [first,atG,larger,upperCase,upperValue,basicRatio,affected,Explicit.m] at hV hB ⊢
    have hmargin : (399/12500:ℝ)<
        angleSlope (Explicit.l .low z) (PositiveTD.tilted (Explicit.c .low z) z/Explicit.l .low z) s-
          Vd R (Explicit.k .low z) 1 (frameCap-s) := by linarith
    linarith
  · have hB := LowGASlope.original hz hs
    dsimp [first,atG,larger,upperCase,upperValue,basicRatio,affected] at hV hB ⊢
    have hmargin : (4/125:ℝ)<
        angleSlope (Explicit.l .low z) (Explicit.k .low z/Explicit.l .low z) s-
          Vd R (Explicit.k .low z) 1 (frameCap-s) := by linarith
    linarith

theorem fixed_zero_le (e : Case) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut (atG e))) :
    baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) 0 z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) frameCap≤
      baseline (atG e) (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z+
        V R (Explicit.k .low z) (larger e (Explicit.l .low z)) (frameCap-s) := by
  have hp := Explicit.family_positive .low (r71_low_dom hz)
  have hzero : (0:ℝ)∈Icc 0 (Explicit.angleCut (atG e)) := by
    cases e <;> norm_num [atG,Explicit.angleCut]
  have hm : MonotoneOn (curve e (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) z)
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
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z-
      allowance z+V R (Explicit.k .low z) 1 (frameCap-s) := by
  have hzero := (Certificate.low_endpoints hz).2.2.1
  cases atG
  · have hh := fixed_zero_le .abH hz hs
    simp only [atG,larger,reduceCtorEq,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith
  · have hh := fixed_zero_le .gaH hz hs
    simp only [atG,larger,reduceCtorEq,↓reduceIte,baseline_zero] at hh
    dsimp [allowance]
    linarith

theorem G_positive (atG : Bool) {s z : ℝ}
    (hz : z∈Icc 0 (1/5:ℝ)) (hs : s∈Icc 0 (Explicit.angleCut atG)) :
    0<baseline atG (Explicit.k .low z) (Explicit.l .low z) (Explicit.c .low z) s z-
      allowance z+V R (Explicit.k .low z) (lambdaG atG (Explicit.l .low z) s) (frameCap-s) := by
  have hzero := (Certificate.low_endpoints hz).2.2.2.1
  cases atG
  · have hh := fixed_zero_le .abG hz hs
    simp only [atG,larger,↓reduceIte,baseline_zero] at hh
    dsimp [allowance,lambdaG]
    linarith
  · have hh := LowSaturatedG.GA_negative_zero_le hz hs
    simp only [LowSaturatedG.negative,NegativeAPositiveTD.secant,Real.cos_zero,div_one,
      sub_zero,baseline_zero] at hh
    dsimp [allowance,lambdaG,NegativeAPositiveTD.secant]
    linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeAPositiveTD.LowSeparated
