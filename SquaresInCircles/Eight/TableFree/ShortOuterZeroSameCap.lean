module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroSameAxial
public import SquaresInCircles.Eight.TableFree.SecondOuterOppositeZeroReferences

/-!
# The three complete final-angle target intervals

Uncompiled transcription of Section 6. The target curvature is greater
than .33 throughout each actual final-angle contact interval. Its one
written value-and-slope reference gives the complete interval minimum
by a single square completion.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Cap
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (sinBox cosBox)
open SecondWord.OppositeZero.Reference (rootAt rootAt_lo_positive)

def reference : Row→ℝ := ![124677/400000,28470147/100000000,0,1434277/4000000]

lemma reference_mem (r : Row) : reference r∈Icc (0:ℝ) (9/10) := by
  fin_cases r <;> norm_num [reference]

def targetU (r : Row) : Interval (U (reference r)) := rootAt (reference r) (reference_mem r)
def sourceBox (r : Row) : Interval (contact (reference r) (7/10)) :=
  ((Interval.point (1/2)).add (((Interval.point (reference r)).add (Interval.point (1/2))).
    mul (cosBox (7/10) (by norm_num)))).sub
      (((targetU r).sub (Interval.point 1)).mul (sinBox (7/10) (by norm_num)))

macro "cap_reference_arithmetic" : tactic => `(tactic|
  norm_num [reference,targetU,sourceBox,SecondWord.OppositeZero.Reference.rootAt,
    rootThree,rootStep,shifted,radicand,coordinate,labelBox,firstBox,ratioBox,
    source,target,c,p,q,P,t]
  <;> Event.event_reference_arithmetic)

def sourceU (r : Row) : Interval (U (contact (reference r) (7/10))) :=
  shifted (sourceBox r) (8/5) (by norm_num) (by fin_cases r <;> cap_reference_arithmetic)

lemma targetU_positive (r : Row) : 0<(targetU r).lo := rootAt_lo_positive (reference_mem r)
lemma sourceU_positive (r : Row) : 0<(sourceU r).lo := by
  fin_cases r <;> dsimp [sourceU] <;> cap_reference_arithmetic

def valueBox (r : Row) : Interval (Same.cost r (reference r) (7/10)) := by
  let V := ((Interval.point (7/10)).add (labelBox (source r) (sourceBox r) (sourceU r))).sub
    (labelBox (target r) (Interval.point (reference r)) (targetU r))
  rw [cost_value]
  exact V

def firstBoxAt (r : Row) : Interval (Same.targetFirst r (reference r) (7/10)) := by
  let L : Interval (l r (contact (reference r) (7/10))) := by
    rw [←source_derivative]
    exact firstBox (source r) (sourceBox r) (sourceU r) (sourceU_positive r)
  let R := ratioBox (Interval.point (reference r)) (targetU r) (targetU_positive r)
  let K := (cosBox (7/10) (by norm_num)).add (R.mul (sinBox (7/10) (by norm_num)))
  exact ((L.mul K).add ((Interval.point (P r)).mul R)).sub (Interval.point (t r))

lemma references (r : Row) (hr : Coupled r) : Domain (reference r) (7/10) ∧
    (89809/100000:ℝ)<Same.cost r (reference r) (7/10) ∧
      |Same.targetFirst r (reference r) (7/10)|<(1/1000000:ℝ) := by
  have hsourceLo : (0:ℝ)<(sourceBox r).lo := by fin_cases r <;> cap_reference_arithmetic
  have hsourceHi : (sourceBox r).hi<(899/1000:ℝ) := by fin_cases r <;> cap_reference_arithmetic
  have htarget : reference r∈Icc 0 outerDiagonal := by
    fin_cases r <;> apply SecondWord.Asymmetric.rational_outer_mem <;> norm_num [reference]
  have hvalue : (89809/100000:ℝ)<(valueBox r).lo := by
    fin_cases r <;> norm_num [Coupled] at hr <;>
      dsimp [valueBox,sourceU] <;> cap_reference_arithmetic
  have hfirstLo : -(1/1000000:ℝ)<(firstBoxAt r).lo := by
    fin_cases r <;> norm_num [Coupled] at hr <;>
      dsimp [firstBoxAt,sourceU] <;> cap_reference_arithmetic
  have hfirstHi : (firstBoxAt r).hi<(1/1000000:ℝ) := by
    fin_cases r <;> norm_num [Coupled] at hr <;>
      dsimp [firstBoxAt,sourceU] <;> cap_reference_arithmetic
  exact ⟨⟨htarget,by norm_num,⟨hsourceLo.le.trans (sourceBox r).mem.1,
    ((sourceBox r).mem.2.trans_lt (hsourceHi.trans SecondWord.fine_outer_endpoint_bounds.2)).le⟩⟩,
    hvalue.trans_le (valueBox r).mem.1,
    abs_lt.mpr ⟨hfirstLo.trans_le (firstBoxAt r).mem.1,
      (firstBoxAt r).mem.2.trans_lt hfirstHi⟩⟩

lemma curvature (r : Row) (hr : Coupled r) {B : ℝ} (hd : Domain B (7/10)) :
    (33/100:ℝ)<targetSecond r B (7/10) := by
  have ha := alpha_nonneg r hr hd.2.2
  have hfirst := mul_nonneg ha (sq_nonneg (projection B (7/10)))
  have hratio := (SecondWord.outer_ratio_bounds hd.2.2).1
  have hp := mul_nonpos_of_nonpos_of_nonneg (coupled_signs r hr).1
    (by linarith [hratio] : 0≤ratio (contact B (7/10)))
  have hl : q r≤l r (contact B (7/10)) := by dsimp [l]; linarith
  have hs : (161/250:ℝ)<Real.sin (7/10) := by linarith [CommonQuarter.cap_trig.1]
  have hproduct := mul_le_mul hl hs.le (by norm_num)
    (l_positive r hd.2.2).le
  have hP := (coefficient_signs r).2.2
  have hbracket : q r*(161/250)+P r≤l r (contact B (7/10))*Real.sin (7/10)+P r := by linarith
  have hbracket0 : 0≤q r*(161/250)+P r := by
    have hq := (coefficient_signs r).1
    positivity
  have hlast := mul_le_mul hbracket (Axial.ratioD_lower hd.1).le
    (by norm_num : (0:ℝ)≤557/1000) (hbracket0.trans hbracket)
  have href : (33/100:ℝ)<(q r*(161/250)+P r)*(557/1000) := by
    fin_cases r <;> norm_num [Coupled] at hr <;> norm_num [q,P]
  dsimp [targetSecond]
  linarith

/-- The named tangent controls the whole genuine final-angle contact interval. -/
theorem lower (r : Row) (hr : Coupled r) {B : ℝ} (hd : Domain B (7/10)) :
    (11226/12500:ℝ)<Same.cost r B (7/10) := by
  let a := reference r
  let lo := min B a
  let hi := max B a
  have href := references r hr
  have hB : B∈Icc lo hi := ⟨min_le_left _ _,le_max_left _ _⟩
  have ha : a∈Icc lo hi := ⟨min_le_right _ _,le_max_right _ _⟩
  have hdom {u : ℝ} (hu : u∈Icc lo hi) : Domain u (7/10) := by
    have hui : u∈Icc 0 outerDiagonal :=
      ⟨(le_min hd.1.1 href.1.1.1).trans hu.1,hu.2.trans (max_le hd.1.2 href.1.1.2)⟩
    have hupper : contact u (7/10)≤outerDiagonal := by
      rcases le_total B a with h | h
      · have hle : u≤a := by simpa [hi,max_eq_right h] using hu.2
        exact (SecondWord.SameZero.b_target_monotone hd.2.1 hui href.1.1 hle).
          trans href.1.2.2.2
      · have hle : u≤B := by simpa [hi,max_eq_left h] using hu.2
        exact (SecondWord.SameZero.b_target_monotone hd.2.1 hui hd.1 hle).trans hd.2.2.2
    exact ⟨hui,hd.2.1,⟨by linarith [SecondWord.SameZero.b_lower hui hd.2.1],hupper⟩⟩
  have hh := curvature_tangent (f := fun u => Same.cost r u (7/10))
    (d := fun u => Same.targetFirst r u (7/10))
    (dd := fun u => targetSecond r u (7/10)) (κ := (33/100:ℝ)) hB ha
    (fun u hu => cost_target_hasDerivAt r (hdom hu))
    (fun u hu => targetFirst_hasDerivAt r (hdom hu))
    (fun u hu => (curvature r hr (hdom hu)).le)
  have hs := abs_lt.mp href.2.2
  have hsq : (Same.targetFirst r a (7/10))^2<(1/1000000:ℝ)^2 := by
    dsimp [a]
    nlinarith
  nlinarith [href.2.1,
    sq_nonneg ((33/100)*(B-a)+Same.targetFirst r a (7/10))]

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Same.Cap
