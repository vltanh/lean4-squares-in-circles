module

public import SquaresInCircles.Eight.TableFree.CommonQuarterTrig
public import SquaresInCircles.Common.Analysis

/-!
# The actual outer-circle chart shared by the word proofs

This reconstruction contains only the analytic circle chart and its
exact derivatives.  The chart includes both the transverse and primary
coordinate intervals.  Actual states are recovered from their original
circle equation, with diagonal and axial endpoints retained.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.ShortOuterOne.SameContact

open CommonQuarter CorePairGeometry Arithmetic

def arc (b : ℝ) : ℝ := Real.sqrt (Q0-(b+1/2)^2)-1/2
def ratio (b : ℝ) : ℝ := (b+1/2)/(arc b+1/2)
def ratioD (b : ℝ) : ℝ := Q0/(arc b+1/2)^3
def ratioDD (b : ℝ) : ℝ := 3*Q0*(b+1/2)/(arc b+1/2)^5

lemma diagonal_le_axial : outerDiagonal≤outerAxial := by
  linarith [outer_endpoint_bounds.1,outer_endpoint_bounds.2.2.2]

lemma outer_domain {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    b∈Icc 0 outerAxial := ⟨hb.1,hb.2.trans diagonal_le_axial⟩

lemma radicand_pos {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    0<Q0-(b+1/2)^2 := by
  have hp := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤outerAxial+1/2 by linarith [hb.2]) 2
  nlinarith [axial_circle]

lemma shifted_positive {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    0<arc b+1/2 := by
  simpa [arc] using Real.sqrt_pos.mpr (radicand_pos hb)

lemma arc_circle {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    (arc b+1/2)^2+(b+1/2)^2=Q0 := by
  have hh := Real.sq_sqrt (radicand_pos hb).le
  dsimp [arc]
  nlinarith

lemma arc_nonneg {b : ℝ} (hb : b∈Icc 0 outerAxial) : 0≤arc b := by
  have hp := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤outerAxial+1/2 by linarith [hb.2]) 2
  have hc := arc_circle hb
  have hs := shifted_positive hb
  nlinarith [axial_circle]

lemma arc_zero : arc 0=outerAxial := by
  norm_num [arc,outerAxial]

lemma arc_diagonal : arc outerDiagonal=outerDiagonal := by
  have hp : 0≤outerDiagonal+1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have he : Q0-(outerDiagonal+1/2)^2=(outerDiagonal+1/2)^2 := by
    nlinarith [diagonal_circle]
  rw [arc,he,Real.sqrt_sq hp]
  ring

lemma arc_axial : arc outerAxial=0 := by
  have he : Q0-(outerAxial+1/2)^2=(1/2:ℝ)^2 := by
    nlinarith [axial_circle]
  rw [arc,he,Real.sqrt_sq (by norm_num : (0:ℝ)≤1/2)]
  ring

lemma arc_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt arc (-ratio b) b := by
  have hd := (((((hasDerivAt_id b).add_const (1/2)).pow 2).const_sub Q0).sqrt
    (radicand_pos hb).ne').sub_const (1/2)
  convert hd using 1 <;> dsimp [arc,ratio] <;> ring

lemma ratio_pos {b : ℝ} (hb : b∈Icc 0 outerAxial) : 0<ratio b := by
  exact div_pos (by linarith [hb.1]) (shifted_positive hb)

lemma ratioD_pos {b : ℝ} (hb : b∈Icc 0 outerAxial) : 0<ratioD b := by
  exact div_pos (by norm_num [Q0]) (pow_pos (shifted_positive hb) 3)

lemma ratio_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratio (ratioD b) b := by
  have hp := shifted_positive hb
  have hd := ((hasDerivAt_id b).add_const (1/2)).div
    ((arc_hasDerivAt hb).add_const (1/2)) hp.ne'
  convert hd using 1
  · rfl
  · dsimp [ratioD,ratio]
    field_simp [hp.ne']
    nlinarith [arc_circle hb]

lemma ratioD_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerAxial) :
    HasDerivAt ratioD (ratioDD b) b := by
  have hp := shifted_positive hb
  have hd := (hasDerivAt_const b Q0).div
    (((arc_hasDerivAt hb).add_const (1/2)).pow 3) (pow_ne_zero _ hp.ne')
  convert hd using 1
  · rfl
  · dsimp [ratioD,ratioDD,ratio]
    field_simp [hp.ne']
    ring

lemma arc_antitone : AntitoneOn arc (Icc 0 outerAxial) :=
  antiOn_of_hasDeriv_nonpos
    (fun b hb => (arc_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun b hb => arc_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun b hb => neg_nonpos.mpr (ratio_pos (Ioo_subset_Icc_self hb)).le)

lemma ratio_monotone : MonotoneOn ratio (Icc 0 outerAxial) :=
  monoOn_of_hasDeriv_nonneg
    (fun b hb => (ratio_hasDerivAt hb).continuousAt.continuousWithinAt)
    (fun b hb => ratio_hasDerivAt (Ioo_subset_Icc_self hb))
    (fun b hb => (ratioD_pos (Ioo_subset_Icc_self hb)).le)

lemma actual_arc {a b : ℝ} (hs : OuterState a b) :
    arc b=a ∧ arc a=b := by
  have ha : 0≤a+1/2 := by linarith [hs.1,hs.2.1]
  have hb : 0≤b+1/2 := by linarith [hs.1]
  have he : Q0-(b+1/2)^2=(a+1/2)^2 := by linarith [hs.2.2]
  have he' : Q0-(a+1/2)^2=(b+1/2)^2 := by linarith [hs.2.2]
  constructor
  · rw [arc,he,Real.sqrt_sq ha]
    ring
  · rw [arc,he',Real.sqrt_sq hb]
    ring

lemma arc_state {b : ℝ} (hb : b∈Icc 0 outerDiagonal) : OuterState (arc b) b := by
  have hd : outerDiagonal∈Icc 0 outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],diagonal_le_axial⟩
  have hm := arc_antitone (outer_domain hb) hd hb.2
  rw [arc_diagonal] at hm
  exact ⟨hb.1,hb.2.trans hm,arc_circle (outer_domain hb)⟩

lemma primary_state {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    OuterState a (arc a) := by
  have had : a∈Icc 0 outerAxial :=
    ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.1],ha.2⟩
  have hd : outerDiagonal∈Icc 0 outerAxial :=
    ⟨by linarith [outer_endpoint_bounds.2.2.1],diagonal_le_axial⟩
  have hm := arc_antitone hd had ha.1
  rw [arc_diagonal] at hm
  refine ⟨arc_nonneg had,hm.trans ha.1,?_⟩
  nlinarith [arc_circle had]

lemma primary_secondary_mem {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    arc a∈Icc 0 outerDiagonal :=
  ⟨(primary_state ha).1,(CommonQuarter.outer_bounds (primary_state ha)).2.2.2.1⟩

end SquaresInCircles.Eight.TableFree.ShortOuterOne.SameContact

