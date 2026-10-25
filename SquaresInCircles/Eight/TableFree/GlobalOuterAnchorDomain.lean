module

public import SquaresInCircles.Eight.TableFree.GlobalOuterAnchorScalar
public import SquaresInCircles.Eight.TableFree.GlobalQuarterSignSupport

/-!
# Actual endpoint domains beside a putative core quarter anchor

The retained zero and high-quarter projections determine the only
exceptional marker cases.  A negative left endpoint forces the actual
zero owner 2, a positive error and an outer left point; a positive
right endpoint forces the actual quarter owner 3, a positive error
and an outer right point.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalOuterAnchor

open FramePair ZeroPrimary GlobalZeroSign GlobalQuarterSign

def width (d : ℝ) : ℝ := (1+Real.cos d+|Real.sin d|)/2
def transverse (s : State) : ℝ := sign s.positive*s.b
def mass (bad : Bool) : ℝ := if bad then m else k
def leftOwner (primary : Bool) : Fin 4 := if primary then 2 else 0
def rightOwner (primary : Bool) : Fin 4 := if primary then 3 else 2

def leftProjection (primary : Bool) (s c : State) (d : ℝ) : ℝ :=
  if primary then s.a*Real.sin d+transverse s*Real.cos d+c.b
  else transverse s+c.a*Real.sin d+c.b*Real.cos d

def rightProjection (primary : Bool) (c t : State) (d : ℝ) : ℝ :=
  if primary then c.a+t.a*Real.sin d-transverse t*Real.cos d
  else c.a*Real.cos d+c.b*Real.sin d-transverse t

theorem width_ge_one {d : ℝ} (hd : |d|≤frameCap) : 1≤width d := by
  rw [width,← CommonQuarter.signed_width (by simpa only [frameCap] using hd)]
  exact CommonQuarter.width_ge_one d

theorem left_margin (s c : State) (p : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hc : transverse c≤0) :
    s.Feasible c (leftOwner p) d ↔ width d≤leftProjection p s c d := by
  have hy := transverse_nonpos_eq c hc
  cases p <;>
    simp [leftOwner,leftProjection,transverse,State.Feasible,forwardMargin,
      CommonQuarter.signed_width (by simpa only [frameCap] using hd),width,hy] <;>
    constructor <;> intro hh <;> linarith

theorem right_margin (c t : State) (p : Bool) {d : ℝ} (hd : |d|≤frameCap)
    (hc : transverse c≤0) :
    c.Feasible t (rightOwner p) (Real.pi/2+d) ↔ width d≤rightProjection p c t d := by
  have hy := transverse_nonpos_eq c hc
  cases p <;>
    simp [rightOwner,rightProjection,transverse,State.Feasible,forwardMargin,
      Real.sin_add,Real.cos_add,
      CommonQuarter.quarter_width (by simpa only [frameCap] using hd),width,hy] <;>
    constructor <;> intro hh <;> linarith

theorem core_bounds (c : State) (hc : c.branch.type=0) :
    c.a≤7/12 ∧ c.b≤7/12 ∧ c.a^2+c.b^2<1 := by
  have ha := (FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart c hc)).2.1
  have hb := c.canonical.trans ha
  have h1 := pow_le_pow_left₀ c.a_pos.le ha 2
  have h2 := pow_le_pow_left₀ c.b_nonneg hb 2
  exact ⟨ha,hb,by norm_num at h1 h2; linarith⟩

theorem sine_nonpos {d : ℝ} (hd : |d|≤frameCap) (hn : d≤0) : Real.sin d≤0 := by
  have hx : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
  have hh := (transport_trig hx).2.2.1
  simpa only [Real.sin_neg,neg_nonneg] using hh

theorem left_negative_domain (s c : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (hs : transverse s<0) (hm : width d≤leftProjection p s c d) :
    p=true ∧ 0<d ∧ s.branch.type≠0 := by
  have hcb := core_bounds c hcore
  have hw := width_ge_one hd
  have hcos : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  cases p with
  | false =>
      exfalso
      have hproj := FrameCoreArc.projection_lt (a:=c.a) (b:=c.b)
        (by norm_num : (0:ℝ)<1) (by rw [one_pow]; exact hcb.2.2) d
      simp only [leftProjection,Bool.false_eq_true,ite_false] at hm
      linarith
  | true =>
      simp only [leftProjection,ite_true] at hm
      have hnegprod := mul_nonpos_of_nonpos_of_nonneg hs.le hcos
      have hdpos : 0<d := by
        by_contra! hn
        have hsin := sine_nonpos hd hn
        have hprod := mul_nonpos_of_nonneg_of_nonpos s.a_pos.le hsin
        linarith [hcb.2.1]
      have ht := transport_trig ⟨hdpos.le,(le_abs_self d).trans hd⟩
      have houter : s.branch.type≠0 := by
        intro hsCore
        have ha := (core_bounds s hsCore).1
        have hp := mul_le_mul ha
          (show Real.sin d≤13/20 by linarith [ht.2.2.2.1]) ht.2.2.1
          (by norm_num : (0:ℝ)≤7/12)
        linarith [hcb.2.1]
      exact ⟨rfl,hdpos,houter⟩

theorem right_positive_domain (c t : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (ht : 0<transverse t) (hm : width d≤rightProjection p c t d) :
    p=true ∧ 0<d ∧ t.branch.type≠0 := by
  have hcb := core_bounds c hcore
  have hw := width_ge_one hd
  have hcos : 0≤Real.cos d := by linarith [(signed_trig hd).1]
  cases p with
  | false =>
      exfalso
      have hproj := FrameCoreArc.projection_lt (a:=c.b) (b:=c.a)
        (by norm_num : (0:ℝ)<1) (by nlinarith [hcb.2.2]) d
      simp only [rightProjection,Bool.false_eq_true,ite_false] at hm
      linarith
  | true =>
      simp only [rightProjection,ite_true] at hm
      have hposprod := mul_nonneg ht.le hcos
      have hdpos : 0<d := by
        by_contra! hn
        have hsin := sine_nonpos hd hn
        have hprod := mul_nonpos_of_nonneg_of_nonpos t.a_pos.le hsin
        linarith [hcb.1]
      have tr := transport_trig ⟨hdpos.le,(le_abs_self d).trans hd⟩
      have houter : t.branch.type≠0 := by
        intro htCore
        have ha := (core_bounds t htCore).1
        have hp := mul_le_mul ha
          (show Real.sin d≤13/20 by linarith [tr.2.2.2.1]) tr.2.2.1
          (by norm_num : (0:ℝ)≤7/12)
        linarith [hcb.1]
      exact ⟨rfl,hdpos,houter⟩

theorem transverse_of_nonneg (s : State) (hs : 0≤transverse s) : transverse s=s.b := by
  cases hp : s.positive <;> simp [transverse,FramePair.sign,hp] at hs ⊢
  linarith [s.b_nonneg]

/-- The chosen coefficient bounds the unchanged signed source marker. -/
theorem left_mass_exists (s c : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (hm : width d≤leftProjection p s c d) :
    ∃bad : Bool, mass bad*transverse s≤ s.signedLabel ∧
      (bad=true → p=true ∧ 0<d) := by
  by_cases hs : 0≤transverse s
  · refine ⟨false,?_,by simp⟩
    rw [signed_of_nonneg s hs,transverse_of_nonneg s hs]
    exact marker_lower s
  · have hn : transverse s<0 := by linarith
    obtain ⟨hp,hdpos,houter⟩ := left_negative_domain s c p hcore hd hn hm
    refine ⟨true,?_,fun _ => ⟨hp,hdpos⟩⟩
    have hy := transverse_nonpos_eq s hn.le
    have hu := marker_outer_upper s houter
    rw [signed_of_nonpos s hn.le]
    change m*(sign s.positive*s.b)≤ -unsigned s
    rw [hy]
    dsimp [m]
    linarith

/-- The right endpoint uses the same actual unsigned marker, with its
sign reversed in the telescoping path charge. -/
theorem right_mass_exists (c t : State) (p : Bool) {d : ℝ}
    (hcore : c.branch.type=0) (hd : |d|≤frameCap)
    (hm : width d≤rightProjection p c t d) :
    ∃bad : Bool, -(mass bad*transverse t)≤ -t.signedLabel ∧
      (bad=true → p=true ∧ 0<d) := by
  by_cases ht : transverse t≤0
  · refine ⟨false,?_,by simp⟩
    have hy := transverse_nonpos_eq t ht
    rw [signed_of_nonpos t ht]
    change -(k*(sign t.positive*t.b))≤ -(-unsigned t)
    rw [hy]
    linarith [marker_lower t]
  · have hp : 0<transverse t := by linarith
    obtain ⟨hq,hdpos,houter⟩ := right_positive_domain c t p hcore hd hp hm
    refine ⟨true,?_,fun _ => ⟨hq,hdpos⟩⟩
    rw [signed_of_nonneg t hp.le,transverse_of_nonneg t hp.le]
    have hu := marker_outer_upper t houter
    dsimp [mass,m]
    linarith

end SquaresInCircles.Eight.TableFree.GlobalOuterAnchor
