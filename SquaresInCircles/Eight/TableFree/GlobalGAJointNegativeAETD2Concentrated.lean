module

public import SquaresInCircles.Eight.TableFree.GlobalGAJointNegativeAETD2SeparatedSlopes
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeATD2Concentration

/-!
# Every concentrated joint-negative TD2 alternative is positive

Uncompiled transcription of Sections 6--7 of the joint-negative
exclusion. The two negative magnitudes are merged while charging the
selected secant. The same endpoint principle is used at z for pure
terms and at h for separated saturated terms.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Concentrated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity Source
open Certificate (Row)

def p (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 4→ℝ :=
  pWeights atG atH (Explicit.k f z) (Explicit.m f z) r s
def q (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 4→ℝ :=
  qWeights atG atH (Explicit.k f z) (Explicit.m f z) r s
def base (f : Row) (r s z : ℝ) : ℝ :=
  baseline (Explicit.k f z) (Explicit.c f z) z+F (Explicit.k f z) r+F (Explicit.k f z) s
def positive (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 4) : ℝ :=
  PositiveTD.Hybrid.positive R (GlobalGA.Secondary.diagonal-1/2) (p f atG atH r s z) (q f atG atH r s z) 3 i d
def negative (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 4) : ℝ :=
  V R (p f atG atH r s z i) (q f atG atH r s z i) d
def mixed (f : Row) (atG atH : Bool) (r s z P N : ℝ) (i : Fin 4) : ℝ :=
  PositiveTD.Hybrid.block R (GlobalGA.Secondary.diagonal-1/2) (p f atG atH r s z) (q f atG atH r s z) 3 i P N
def pure (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 4) : ℝ :=
  NegativeAPositiveTD.Concentration.pure R (GlobalGA.Secondary.diagonal-1/2)
    (p f atG atH r s z) (q f atG atH r s z) 3 i j (r+s) z
def saturated (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 4) : ℝ :=
  NegativeAPositiveTD.Concentration.saturated R (GlobalGA.Secondary.diagonal-1/2)
    (p f atG atH r s z) (q f atG atH r s z) 3 i j (r+s) z
def scalar (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 4) : ℝ :=
  base f r s z+min (pure f atG atH r s z i j) (saturated f atG atH r s z i j)

theorem canonical_merge {k r s t : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (ht : t∈Icc 0 frameCap) (hS : r+s≤t) (j : Fin 3) :
    min (V R k 1 t) (F k t)≤
      F k r+F k s+V R k (BlockBounds.canonicalQ r s j) (t-(r+s)) := by
  have he := CommonGain.endpoint hk ht ⟨add_nonneg hr hs,hS⟩
  have hd : 0≤t-(r+s) := by linarith
  have hcap : r+s+(t-(r+s))≤frameCap := by linarith [ht.2]
  fin_cases j
  · have hm := CommonGain.merge hk hr hs (hS.trans ht.2)
    have hmin := min_le_left (V R k 1 (t-(r+s)))
      (V R k (SecantNormCurvature.secant (r+s)) (t-(r+s)))
    simp only [BlockBounds.canonicalQ,Fin.zero_eta,Matrix.cons_val_zero]
    linarith
  · have hm := CommonGain.merge_charged hk hr hs hd hcap
    simpa [BlockBounds.canonicalQ] using he.trans hm
  · have hm := CommonGain.merge_charged_right hk hr hs hd hcap
    simpa [BlockBounds.canonicalQ] using he.trans hm

theorem negative_merge (f : Row) (atG atH : Bool) {r s z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ht : t∈Icc 0 frameCap) (hS : r+s≤t) (i : Fin 4) :
    min (V R (Explicit.k f z) 1 t) (F (Explicit.k f z) t)≤
      F (Explicit.k f z) r+F (Explicit.k f z) s+negative f atG atH r s z (t-(r+s)) i := by
  obtain ⟨j,hj⟩ := BlockBounds.negative_index f atG atH hz hr hs hH
    (show t-(r+s)∈Icc 0 frameCap from ⟨by linarith,by linarith [ht.2,hr.1,hs.1]⟩) i
  have hh := canonical_merge (Explicit.ranges f hz).1 hr.1 hs.1 ht hS j
  change _≤negative f atG atH r s z (t-(r+s)) i at hj
  linarith

theorem pure_negative_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 4) :
    0<base f r s z+negative f atG atH r s z (z-(r+s)) i := by
  have hh := negative_merge f atG atH hz hr hs hH (Explicit.frame_domain f hz) hS i
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) z+
      min (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) := by
    rcases le_total (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) with h|h
    · rw [min_eq_left h]; exact he.1
    · rw [min_eq_right h]; exact he.2
  dsimp [base]
  linarith

theorem pure_positive_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 4) :
    0<base f r s z+positive f atG atH r s z (r+s-z) i := by
  have hk := (Explicit.ranges f hz).1
  have hz' := Explicit.frame_domain f hz
  have hd : r+s-z∈Icc 0 frameCap := ⟨by linarith [hS.1],by linarith [hS.2,hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hd i
  change -BlockBounds.charge f z*(r+s-z)≤positive f atG atH r s z (r+s-z) i at hu
  have hm := CommonGain.merge hk hr.1 hs.1 hS.2
  have hg := CommonGain.growth hk.1 hz' ⟨add_nonneg hr.1 hs.1,hS.2⟩ hS.1
  have hc := mul_le_mul_of_nonneg_right
    (show BlockBounds.charge f z≤9/10 by linarith [(BlockBounds.charge_bounds f hz).2.1]) hd.1
  have he := (scalar_endpoints f hz).2
  dsimp [base]
  linarith

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i : Fin 4) :
    0<base f r s z+mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i := by
  by_cases horder : r+s≤z
  · have hl := BlockBounds.same_negative f atG atH hz hr hs hH horder i
    have hp := pure_negative_positive f atG atH hz hr hs hH horder i
    change negative f atG atH r s z (z-(r+s)) i≤
      mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
    linarith
  · have horder' : z≤r+s := le_of_lt (lt_of_not_ge horder)
    have hl := BlockBounds.same_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i
    have hp := pure_positive_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i
    change positive f atG atH r s z (r+s-z) i≤
      mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
    linarith

theorem separated_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 4) :
    0<base f r s z+positive f atG atH r s z (frameCap-z) i+
      negative f atG atH r s z (frameCap-(r+s)) j := by
  have hz' := Explicit.frame_domain f hz
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz'.2],by linarith [hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hP i
  change -BlockBounds.charge f z*(frameCap-z)≤positive f atG atH r s z (frameCap-z) i at hu
  have hn := negative_merge f atG atH hz hr hs hH hcap hS j
  have hV := BlockBounds.separated_V_charge f hz
  have hF := CommonGain.growth (Explicit.ranges f hz).1.1 hz' hcap hz'.2
  have hcharge := mul_le_mul_of_nonneg_right
    (show BlockBounds.charge f z≤9/10 by linarith [(BlockBounds.charge_bounds f hz).2.1]) hP.1
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) z-
      BlockBounds.charge f z*(frameCap-z)+
      min (V R (Explicit.k f z) 1 frameCap) (F (Explicit.k f z) frameCap) := by
    rcases le_total (V R (Explicit.k f z) 1 frameCap) (F (Explicit.k f z) frameCap) with h|h
    · rw [min_eq_left h]; linarith [he.1]
    · rw [min_eq_right h]
      have he2 := he.2
      simp only [frameCap] at hF hcharge he2 ⊢
      linarith
  dsimp [base]
  linarith

theorem all_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 4) :
    0<scalar f atG atH r s z i j := by
  have hp : 0<base f r s z+pure f atG atH r s z i j := by
    by_cases hh : r+s≤z
    · simpa [pure,NegativeAPositiveTD.Concentration.pure,hh,negative] using
        pure_negative_positive f atG atH hz hr hs hH hh j
    · have hh' : z≤r+s := le_of_lt (lt_of_not_ge hh)
      simpa [pure,NegativeAPositiveTD.Concentration.pure,hh,positive] using
        pure_positive_positive f atG atH hz hr hs hH ⟨hh',hS⟩ i
  have hsaturated : 0<base f r s z+saturated f atG atH r s z i j := by
    by_cases hij : i=j
    · simpa [saturated,NegativeAPositiveTD.Concentration.saturated,hij,mixed] using
        same_positive f atG atH hz hr hs hH hS j
    · have hh := separated_positive f atG atH hz hr hs hH hS i j
      simpa [saturated,NegativeAPositiveTD.Concentration.saturated,hij,positive,negative,add_assoc] using hh
  unfold scalar
  rcases le_total (pure f atG atH r s z i j) (saturated f atG atH r s z i j) with h|h
  · rw [min_eq_left h]; exact hp
  · rw [min_eq_right h]; exact hsaturated

end SquaresInCircles.Eight.TableFree.GlobalGA.JointNegativeAETD2.Concentrated
