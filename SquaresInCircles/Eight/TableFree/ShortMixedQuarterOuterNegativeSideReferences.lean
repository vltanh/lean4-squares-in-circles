module

public import SquaresInCircles.Eight.TableFree.ShortMixedQuarterOuterNegativeSideData

/-!
# Exact endpoint-chord constants and the four named references

Uncompiled source for (21)--(23). The fixed norm chord uses cos(.7),
the aligned norm, and their exact positive radicals. The four intrinsic
role references are the ones in the hand proof. Six positive-square
refinements enclose the fixed radicals; the existing alternating Taylor
enclosures supply each fixed sine and cosine.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.SideChord.Reference
open CommonQuarter Arithmetic StationaryPrimitives
open MixedQuarter.Reference

def radiusBox : Interval CommonQuarter.radius :=
  rootSix (Interval.point Q0) 2 (by norm_num) (by norm_num [Interval.point,Q0])
def k0Box : Interval k0 := cosine (by norm_num : (0:ℝ)≤7/10)
def radicandBox (r : Row) {k : ℝ} (Y : Interval k) :
    Interval ((ocG r-ocP r*k)^2+(ocQ r*k)^2) :=
  (((Interval.point (ocG r)).sub ((Interval.point (ocP r)).mul Y)).square).add (((Interval.point (ocQ r)).mul Y).square)
theorem one_radicand (r : Row) (hr : Rows r) :
    0≤(radicandBox r (Interval.point (1:ℝ))).lo := by
  rcases hr with rfl|rfl|rfl|rfl <;> dsimp [radicandBox] <;> mixed_fixed
theorem k0_radicand (r : Row) (hr : Rows r) : 0≤(radicandBox r k0Box).lo := by
  rcases hr with rfl|rfl|rfl|rfl <;> dsimp [radicandBox,k0Box] <;> mixed_fixed
def normOneBox (r : Row) (hr : Rows r) : Interval (norm r 1) :=
  rootSix (radicandBox r (Interval.point (1:ℝ))) 2 (by norm_num) (one_radicand r hr)
def normK0Box (r : Row) (hr : Rows r) : Interval (norm r k0) :=
  rootSix (radicandBox r k0Box) 2 (by norm_num) (k0_radicand r hr)
def denominatorBox : Interval (1-k0) := (Interval.point 1).sub k0Box
theorem denominator_positive : 0<denominatorBox.lo := by
  dsimp [denominatorBox,k0Box]
  mixed_fixed
def betaBox (r : Row) (hr : Rows r) : Interval (beta r) :=
  ((normOneBox r hr).sub (normK0Box r hr)).div denominatorBox denominator_positive
def alphaBox (r : Row) (hr : Rows r) : Interval (alpha r) :=
  (normOneBox r hr).sub (betaBox r hr)
def KBox (r : Row) : Interval (K r) :=
  ((halfPi.add (Interval.point (ocC r))).add
    (Interval.point ((-ocP r+ocQ r+ocG r)/2))).sub (Interval.point (449/500))
def ABox (r : Row) (hr : Rows r) : Interval (A r) :=
  (KBox r).sub (radiusBox.mul (betaBox r hr))
def BBox (r : Row) (hr : Rows r) : Interval (B r) :=
  (Interval.point (ocG r)).sub (radiusBox.mul (alphaBox r hr))
def JBox (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x) : Interval (J r x) :=
  ((((ABox r hr).sub (Interval.point x)).mul (cosine hx)).add (BBox r hr)).add ((Interval.point (C r)).mul (sine hx))
def J1Box (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x) : Interval (J1 r x) :=
  ((Interval.point (C r-1)).mul (cosine hx)).sub (((ABox r hr).sub (Interval.point x)).mul (sine hx))
def J2Box (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x) : Interval (J2 r x) :=
  ((Interval.point (2-C r)).mul (sine hx)).sub (((ABox r hr).sub (Interval.point x)).mul (cosine hx))

macro "side_chord_fixed" : tactic => `(tactic|
  (dsimp [radiusBox,k0Box,radicandBox,normOneBox,normK0Box,denominatorBox,
    betaBox,alphaBox,KBox,ABox,BBox,JBox,J1Box,J2Box,k0,K,C,reference]; mixed_fixed))

theorem coefficient_bounds (r : Row) (hr : Rows r) :
    (479/1000:ℝ)<A r ∧ A r<691/1000 ∧ (129/125:ℝ)<C r ∧ C r<43/40 := by
  have hl : (479/1000:ℝ)<(ABox r hr).lo := by
    rcases hr with rfl|rfl|rfl|rfl <;> side_chord_fixed
  have hu : (ABox r hr).hi<(691/1000:ℝ) := by
    rcases hr with rfl|rfl|rfl|rfl <;> side_chord_fixed
  refine ⟨hl.trans_le (ABox r hr).mem.1,(ABox r hr).mem.2.trans_lt hu,?_⟩
  rcases hr with rfl|rfl|rfl|rfl <;> norm_num [C,ocG]

theorem initial_shape (r : Row) (hr : Rows r) :
    (37/5000:ℝ)<J r 0 ∧ J1 r (2/5)< -(1/1000:ℝ) ∧ (9/100:ℝ)<J2 r (2/5) := by
  have h : (37/5000:ℝ)<(JBox r hr (by norm_num : (0:ℝ)≤0)).lo ∧
      (J1Box r hr (by norm_num : (0:ℝ)≤2/5)).hi< -(1/1000:ℝ) ∧
        (9/100:ℝ)<(J2Box r hr (by norm_num : (0:ℝ)≤2/5)).lo := by
    rcases hr with rfl|rfl|rfl|rfl <;> side_chord_fixed
  exact ⟨h.1.trans_le (JBox r hr _).mem.1,(J1Box r hr _).mem.2.trans_lt h.2.1,
    h.2.2.trans_le (J2Box r hr _).mem.1⟩

theorem reference_mem (r : Row) : reference r∈Icc (2/5:ℝ) (7/10) := by
  dsimp [reference]
  split_ifs <;> norm_num

private lemma r83_reference_eval (r : Row) (hr : Rows r) {x : ℝ} (hx : 0≤x)
    (hv : (r=4 ∧ x=52/125) ∨ (r=12 ∧ x=1147/2000) ∨ (r=19 ∧ x=287/500) ∨ (r=23 ∧ x=807/2000)) :
    (31/50000:ℝ)<(JBox r hr hx).lo ∧ -(1/20000:ℝ)<(J1Box r hr hx).lo ∧
      (J1Box r hr hx).hi<1/20000 := by
  rcases hv with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> side_chord_fixed

theorem reference_reserve (r : Row) (hr : Rows r) :
    (31/50000:ℝ)<J r (reference r) ∧ |J1 r (reference r)|<1/20000 := by
  have hx : 0≤reference r := (by norm_num : (0:ℝ)≤2/5).trans (reference_mem r).1
  have h := r83_reference_eval r hr hx
    (by rcases hr with rfl|rfl|rfl|rfl <;> norm_num [reference])
  exact ⟨h.1.trans_le (JBox r hr hx).mem.1,
    abs_lt.mpr ⟨h.2.1.trans_le (J1Box r hr hx).mem.1,(J1Box r hr hx).mem.2.trans_lt h.2.2⟩⟩

end SquaresInCircles.Eight.TableFree.ShortWord.MixedQuarter.OuterNegative.SideChord.Reference
