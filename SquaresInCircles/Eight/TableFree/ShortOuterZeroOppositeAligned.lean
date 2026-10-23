module

public import SquaresInCircles.Eight.TableFree.ShortOuterZeroOppositeData

/-!
# The six aligned opposite-sign short-word contacts

Uncompiled transcription of Section 1 of the opposite-sign hand proof.
The physical interval is [1-d,d]. Four rows are concave on the whole
interval and two are monotone. Their two actual geometric endpoint
values are enclosed directly from the literal labels and circle roots.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite
open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)
open SecondWord (U W outer_domain outer_zero_mem UW_circle U_positive)
open StationaryPrimitives (Interval)
open SecondWord.OppositeThree.ReferenceAlgebra
open SecondWord.SameZero.PJ.Reference (dBox dUBox)
open SecondWord.OppositeZero.AlignedPJ (sourceBox sourceUBox)

lemma low_mem : low∈Icc 0 outerDiagonal := by
  dsimp [low]
  constructor <;> linarith [outer_endpoint_bounds.2.2.1,outer_endpoint_bounds.2.2.2]

lemma low_radical : (377/200:ℝ)<U low ∧ U low<(943/500:ℝ) := by
  have hc := UW_circle (outer_domain low_mem)
  have hu := U_positive (outer_domain low_mem)
  have hd := ShortMixedZero.fine_diagonal_bounds
  dsimp [W,low] at hc
  norm_num [Q0] at hc
  constructor <;> nlinarith [hd.1,hd.2]

lemma U_antitone : AntitoneOn U (Icc 0 outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => ((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).
      add_const (1/2)).continuousAt.continuousWithinAt)
    (fun b hb => (ShortOuterOne.SameContact.arc_hasDerivAt
      (outer_domain (Ioo_subset_Icc_self hb))).add_const (1/2))
    (fun b hb => neg_nonpos.mpr
      (ShortOuterOne.SameContact.ratio_pos (outer_domain (Ioo_subset_Icc_self hb))).le)

lemma band_root {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    (1399/1000:ℝ)<U b ∧ U b<(943/500:ℝ) := by
  have hbi := (aligned_domains hb).1
  have hdiag : outerDiagonal∈Icc 0 outerDiagonal := ⟨outer_zero_mem.2,le_rfl⟩
  have hlo := U_antitone hbi hdiag hb.2
  have hhi := U_antitone low_mem hbi hb.1
  rw [U,ShortOuterOne.SameContact.arc_diagonal] at hlo
  exact ⟨by linarith [SecondWord.fine_outer_endpoint_bounds.2],hhi.trans_lt low_radical.2⟩

lemma band_derivative_ratio {b B : ℝ} (hb : b∈Icc low outerDiagonal)
    (hB : B∈Icc low outerDiagonal) : ratioD b<(123/50:ℝ)*ratioD B := by
  have hu := band_root hb
  have hU := band_root hB
  have hulo := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hu.1.le 3
  have hUhi := pow_le_pow_left₀ (by linarith [hU.1] : 0≤U B) hU.2.le 3
  have hp : (U B)^3<(123/50:ℝ)*(U b)^3 := by
    have href : (943/500:ℝ)^3<(123/50)*(1399/1000)^3 := by norm_num
    nlinarith
  have hub : 0<U b := by linarith [hu.1]
  have huB : 0<U B := by linarith [hU.1]
  change Q0/(U b)^3<(123/50)*(Q0/(U B)^3)
  apply (div_lt_iff₀ (pow_pos hub 3)).2
  apply (lt_of_mul_lt_mul_right _ (pow_nonneg huB.le 3))
  field_simp [huB.ne']
  have hq := mul_lt_mul_of_pos_left hp (by norm_num [Q0] : 0<Q0)
  nlinarith

lemma low_ratio : ratio low<(319/1000:ℝ) := by
  have hu := low_radical.1
  have hd := ShortMixedZero.fine_diagonal_bounds.1
  change (low+1/2)/U low<319/1000
  apply (div_lt_iff₀ (by linarith : 0<U low)).2
  dsimp [low]
  linarith

lemma aligned_endpoints (r : Row) : (89809/100000:ℝ)<aligned r low ∧
    (89809/100000:ℝ)<aligned r outerDiagonal := by
  let A := ((Interval.point (c r)).add
    (labelBox (source r) sourceBox sourceUBox)).add
      (labelBox (target r) dBox dUBox)
  let B := ((Interval.point (c r)).add
    (labelBox (source r) dBox dUBox)).add
      (labelBox (target r) sourceBox sourceUBox)
  have hA : (89809/100000:ℝ)<A.lo := by
    fin_cases r <;> dsimp [A] <;>
      norm_num [source,target,c,p,q,v,t,
        SecondWord.OppositeZero.AlignedPJ.sourceBox,SecondWord.OppositeZero.AlignedPJ.sourceUBox,
        SecondWord.SameZero.PJ.Reference.dBox,SecondWord.SameZero.PJ.Reference.dUBox,
        labelBox,coordinate,shifted,radicand,rootThree,rootStep,
        Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
        Interval.mul,Interval.square,Interval.div,Interval.inv,Q0]
  have hB : (89809/100000:ℝ)<B.lo := by
    fin_cases r <;> dsimp [B] <;>
      norm_num [source,target,c,p,q,v,t,
        SecondWord.OppositeZero.AlignedPJ.sourceBox,SecondWord.OppositeZero.AlignedPJ.sourceUBox,
        SecondWord.SameZero.PJ.Reference.dBox,SecondWord.SameZero.PJ.Reference.dUBox,
        labelBox,coordinate,shifted,radicand,rootThree,rootStep,
        Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
        Interval.mul,Interval.square,Interval.div,Interval.inv,Q0]
  exact ⟨by simpa [aligned,low] using hA.trans_le A.mem.1,
    by simpa [aligned,low] using hB.trans_le B.mem.1⟩

def ConcaveRow (r : Row) : Prop := r=0 ∨ r=1 ∨ r=4 ∨ r=5

lemma aligned_curvature (r : Row) (hr : ConcaveRow r)
    {b : ℝ} (hb : b∈Icc low outerDiagonal) : alignedSecond r b<0 := by
  have hother : 1-b∈Icc low outerDiagonal :=
    ⟨by dsimp [low] at *; linarith [hb.2],by dsimp [low] at *; linarith [hb.1]⟩
  have hleft := ShortOuterOne.SameContact.ratioD_pos (outer_domain (aligned_domains hb).1)
  have hright := ShortOuterOne.SameContact.ratioD_pos (outer_domain (aligned_domains hb).2)
  have hLR := band_derivative_ratio hb hother
  have hRL := band_derivative_ratio hother hb
  rcases hr with rfl | rfl | rfl | rfl <;>
    norm_num [alignedSecond,p,v] <;> nlinarith

lemma aligned_monotone_two : MonotoneOn (aligned 2) (Icc low outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (aligned_hasDerivAt 2 hb).continuousAt.continuousWithinAt)
    (fun b hb => aligned_hasDerivAt 2 (Ioo_subset_Icc_self hb))
    (fun b hb => by
      have hh := SecondWord.outer_ratio_bounds (aligned_domains (Ioo_subset_Icc_self hb)).2
      norm_num [alignedFirst,l,h,p,q,v,t]
      linarith [hh.2.1])

lemma aligned_antitone_three : AntitoneOn (aligned 3) (Icc low outerDiagonal) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (aligned_hasDerivAt 3 hb).continuousAt.continuousWithinAt)
    (fun b hb => aligned_hasDerivAt 3 (Ioo_subset_Icc_self hb))
    (fun b hb => by
      have hh := SecondWord.outer_ratio_bounds (aligned_domains (Ioo_subset_Icc_self hb)).1
      norm_num [alignedFirst,l,h,p,q,v,t]
      linarith [hh.2.1])

/-- All six aligned minima, on the complete geometric interval. -/
theorem aligned_lower (r : Row) {b : ℝ} (hb : b∈Icc low outerDiagonal) :
    (89809/100000:ℝ)<aligned r b := by
  by_cases htwo : r=2
  · subst r
    exact (aligned_endpoints 2).1.trans_le
      (aligned_monotone_two ⟨le_rfl,low_mem.2⟩ hb hb.1)
  by_cases hthree : r=3
  · subst r
    exact (aligned_endpoints 3).2.trans_le
      (aligned_antitone_three hb ⟨low_mem.2,le_rfl⟩ hb.2)
  have hr : ConcaveRow r := by
    fin_cases r <;> simp_all [ConcaveRow]
  have hc : ConcaveOn ℝ (Icc low outerDiagonal) (aligned r) :=
    concave_of_deriv2 (fun b hb => aligned_hasDerivAt r hb)
      (fun b hb => alignedFirst_hasDerivAt r hb)
      (fun b hb => (aligned_curvature r hr hb).le)
  exact concave_gt_of_endpoints hc hb (aligned_endpoints r).1 (aligned_endpoints r).2

theorem aligned_original (r : Row) {b B : ℝ}
    (hb : b∈Icc 0 outerDiagonal) (hB : B∈Icc 0 outerDiagonal) (he : b+B=1) :
    (89809/100000:ℝ)<c r+(source r).outer b+(target r).outer B := by
  have hband : b∈Icc low outerDiagonal := ⟨by dsimp [low]; linarith [hB.2],hb.2⟩
  have hB' : B=1-b := by linarith
  simpa [aligned,hB'] using aligned_lower r hband

end SquaresInCircles.Eight.TableFree.ShortOuterZero.Opposite
