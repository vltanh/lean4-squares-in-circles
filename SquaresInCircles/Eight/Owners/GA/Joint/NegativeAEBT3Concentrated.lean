module

public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3BlockBounds
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3Chords
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAEBT3Scalar
public import SquaresInCircles.Eight.Owners.GA.Joint.NegativeAETD2Concentrated

/-!
# Eight squares: positivity of every concentrated joint-negative BT3 alternative

The selected secant is charged before the penalty endpoint principle. The distinguished D
same-block alternative is itself a separated term and uses that argument directly. Ordinary
same-block terms reduce to their pure surplus (`same_positive`), and `all_positive` collects every
alternative.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Concentrated
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity Source
open Certificate (Row)
open JointNegativeAETD2

def p (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 5→ℝ :=
  pWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s
def q (f : Row) (atG atH : Bool) (r s z : ℝ) : Fin 5→ℝ :=
  qWeights atG atH (Explicit.k f z) (Explicit.m f z) (Explicit.c f z) r s
def cost (f : Row) (r s z : ℝ) : ℝ := Penalty.cost (Explicit.c f z) (r+s)
def selected (f : Row) (atH : Bool) (z : ℝ) : Fin 5 := distinguished atH (Explicit.c f z)
def base (f : Row) (r s z : ℝ) : ℝ :=
  baseline (Explicit.k f z) (Explicit.c f z) (Explicit.eta f z) z+
    F (Explicit.k f z) r+F (Explicit.k f z) s
def positive (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 5) : ℝ :=
  PositiveTD.Hybrid.positive R (cost f r s z) (p f atG atH r s z) (q f atG atH r s z)
    (selected f atH z) i d
def negative (f : Row) (atG atH : Bool) (r s z d : ℝ) (i : Fin 5) : ℝ :=
  V R (p f atG atH r s z i) (q f atG atH r s z i) d
def mixed (f : Row) (atG atH : Bool) (r s z P N : ℝ) (i : Fin 5) : ℝ :=
  PositiveTD.Hybrid.block R (cost f r s z) (p f atG atH r s z) (q f atG atH r s z)
    (selected f atH z) i P N
def pure (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 5) : ℝ :=
  NegativeAPositiveTD.Concentration.pure R (cost f r s z)
    (p f atG atH r s z) (q f atG atH r s z) (selected f atH z) i j (r+s) z
def saturated (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 5) : ℝ :=
  NegativeAPositiveTD.Concentration.saturated R (cost f r s z)
    (p f atG atH r s z) (q f atG atH r s z) (selected f atH z) i j (r+s) z
def scalar (f : Row) (atG atH : Bool) (r s z : ℝ) (i j : Fin 5) : ℝ :=
  base f r s z+min (pure f atG atH r s z i j) (saturated f atG atH r s z i j)

theorem canonical_allocation {k r s d : ℝ} (hk : k∈Icc (13/20:ℝ) (751/1000))
    (hr : 0≤r) (hs : 0≤ s) (hd : 0≤d) (hcap : r+s+d≤frameCap) (j : Fin 3) :
    F k (r+s)+min (V R k 1 d) (V R k (sec (r+s)) d)≤
      F k r+F k s+V R k (BlockBounds.canonicalQ r s j) d := by
  fin_cases j
  · have hm : F k (r+s)≤F k r+F k s := CommonGain.merge hk hr hs (by linarith)
    have hmin := min_le_left (V R k 1 d) (V R k (sec (r+s)) d)
    simp only [BlockBounds.canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ,
      Fin.zero_eta,Fin.isValue,Matrix.cons_val_zero]
    linarith
  · simpa [BlockBounds.canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ] using
      CommonGain.merge_charged hk hr hs hd hcap
  · simpa [BlockBounds.canonicalQ,JointNegativeAETD2.BlockBounds.canonicalQ] using
      CommonGain.merge_charged_right hk hr hs hd hcap

theorem negative_merge (f : Row) (atG atH : Bool) {r s z t : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (ht : t∈Icc 0 frameCap) (hS : r+s≤t) (i : Fin 5) :
    min (V R (Explicit.k f z) 1 t) (F (Explicit.k f z) t)≤
      F (Explicit.k f z) r+F (Explicit.k f z) s+negative f atG atH r s z (t-(r+s)) i := by
  obtain ⟨j,hj⟩ := BlockBounds.negative_index f atG atH hz hr hs hH
    (show t-(r+s)∈Icc 0 frameCap from ⟨by linarith,by linarith [ht.2,hr.1,hs.1]⟩) i
  have hh := JointNegativeAETD2.Concentrated.canonical_merge
    (Explicit.ranges f hz).k_domain hr.1 hs.1 ht hS j
  change _≤negative f atG atH r s z (t-(r+s)) i at hj
  linarith

theorem pure_negative_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤z) (i : Fin 5) :
    0<base f r s z+negative f atG atH r s z (z-(r+s)) i := by
  have hh := negative_merge f atG atH hz hr hs hH (Explicit.frame_domain f hz) hS i
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) (Explicit.eta f z) z+
      min (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) := by
    rcases le_total (V R (Explicit.k f z) 1 z) (F (Explicit.k f z) z) with h|h
    · rw [min_eq_left h]; exact he.1
    · rw [min_eq_right h]; exact he.2
  dsimp [base]
  linarith

theorem pure_positive_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s∈Icc z frameCap) (i : Fin 5) :
    0<base f r s z+positive f atG atH r s z (r+s-z) i := by
  have hc := Explicit.ranges f hz
  have hz' := Explicit.frame_domain f hz
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS.2⟩
  have hd : r+s-z∈Icc 0 frameCap := ⟨by linarith [hS.1],by linarith [hS.2,hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hS.2 hd i
  change -cost f r s z*(r+s-z)≤positive f atG atH r s z (r+s-z) i at hu
  have hm := CommonGain.merge hc.k_domain hr.1 hs.1 hS.2
  have hg := CommonGain.growth hc.k_domain.1 hz' htotal hS.1
  have hcost : cost f r s z≤9/10 := by
    dsimp [cost]; linarith [(Penalty.cost_bounds hc.c_domain.2 htotal).2]
  have hcharge := mul_le_mul_of_nonneg_right hcost hd.1
  have he := (scalar_endpoints f hz).2
  dsimp [base]
  linarith

theorem negative_allocation (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i : Fin 5) :
    F (Explicit.k f z) (r+s)+
      min (V R (Explicit.k f z) 1 (frameCap-(r+s)))
        (V R (Explicit.k f z) (sec (r+s)) (frameCap-(r+s)))≤
      F (Explicit.k f z) r+F (Explicit.k f z) s+
        negative f atG atH r s z (frameCap-(r+s)) i := by
  have hd : frameCap-(r+s)∈Icc 0 frameCap :=
    ⟨by linarith,by linarith [hr.1,hs.1]⟩
  obtain ⟨j,hj⟩ := BlockBounds.negative_index f atG atH hz hr hs hH hd i
  have hh := canonical_allocation (Explicit.ranges f hz).k_domain hr.1 hs.1 hd.1
    (show r+s+(frameCap-(r+s))≤frameCap by linarith) j
  change _≤negative f atG atH r s z (frameCap-(r+s)) i at hj
  linarith

theorem separated_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 5) :
    0<base f r s z+positive f atG atH r s z (frameCap-z) i+
      negative f atG atH r s z (frameCap-(r+s)) j := by
  have hc := Explicit.ranges f hz
  have hz' := Explicit.frame_domain f hz
  have hcap : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have htotal : r+s∈Icc 0 frameCap := ⟨add_nonneg hr.1 hs.1,hS⟩
  have hP : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz'.2],by linarith [hz'.1]⟩
  have hu := BlockBounds.positive_lower f atG atH hz hr hs hH hS hP i
  change -cost f r s z*(frameCap-z)≤positive f atG atH r s z (frameCap-z) i at hu
  have hn := negative_allocation f atG atH hz hr hs hH hS j
  have hp : min (V R (Explicit.k f z) 1 frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) 0)
        (F (Explicit.k f z) frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) frameCap)≤
      F (Explicit.k f z) (r+s)+min (V R (Explicit.k f z) 1 (frameCap-(r+s)))
        (V R (Explicit.k f z) (sec (r+s)) (frameCap-(r+s)))-
        (frameCap-z)*Penalty.cost (Explicit.c f z) (r+s) :=
    Penalty.endpoint (c:=Explicit.c f z) hc.k_domain hP.1 htotal
  have hV := Chords.cost_zero_chord hc.k_domain hc.c_domain.2 hz'
    (fun h => (hc.diagonal_cut h).1) hc.later_c
  have hF : 9/10*(frameCap-z)≤F (Explicit.k f z) frameCap-F (Explicit.k f z) z :=
    CommonGain.growth hc.k_domain.1 hz' hcap hz'.2
  have hch : Penalty.cost (Explicit.c f z) frameCap≤9/10 := by
    linarith [(Penalty.cost_bounds hc.c_domain.2 hcap).2]
  have hcharge := mul_le_mul_of_nonneg_right hch hP.1
  have he := scalar_endpoints f hz
  have hmin : 0<baseline (Explicit.k f z) (Explicit.c f z) (Explicit.eta f z) z+
      min (V R (Explicit.k f z) 1 frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) 0)
        (F (Explicit.k f z) frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) frameCap) := by
    rcases le_total
      (V R (Explicit.k f z) 1 frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) 0)
      (F (Explicit.k f z) frameCap-(frameCap-z)*Penalty.cost (Explicit.c f z) frameCap) with h|h
    · rw [min_eq_left h]
      nlinarith [he.1]
    · rw [min_eq_right h]
      simp only [frameCap] at hF hcharge ⊢
      linarith [he.2]
  dsimp only [base,cost] at hu ⊢
  linarith

theorem same_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i : Fin 5) :
    0<base f r s z+mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i := by
  by_cases hi : i=selected f atH z
  · have hh := separated_positive f atG atH hz hr hs hH hS i i
    simpa [mixed,positive,negative,PositiveTD.Hybrid.block,PositiveTD.Hybrid.positive,hi,add_assoc] using hh
  · by_cases horder : r+s≤z
    · have hl := BlockBounds.same_negative f atG atH hz hr hs hH horder i hi
      have hp := pure_negative_positive f atG atH hz hr hs hH horder i
      change negative f atG atH r s z (z-(r+s)) i≤
        mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
      linarith
    · have horder' : z≤r+s := le_of_lt (lt_of_not_ge horder)
      have hl := BlockBounds.same_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i hi
      have hp := pure_positive_positive f atG atH hz hr hs hH ⟨horder',hS⟩ i
      change positive f atG atH r s z (r+s-z) i≤
        mixed f atG atH r s z (frameCap-z) (frameCap-(r+s)) i at hl
      linarith

theorem all_positive (f : Row) (atG atH : Bool) {r s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hr : r∈Icc (0:ℝ) (19/50)) (hs : s∈Icc 0 frameCap)
    (hH : atH=true → s≤1/4) (hS : r+s≤frameCap) (i j : Fin 5) :
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

end SquaresInCircles.Eight.GlobalGA.JointNegativeAEBT3.Concentrated
