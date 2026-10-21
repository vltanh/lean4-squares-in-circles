module

public import SquaresInCircles.Eight.Arithmetic.WordProblems
public import SquaresInCircles.Eight.CycleActions
public import SquaresInCircles.Eight.Arithmetic.CoreWordGeometry
public import SquaresInCircles.Eight.Candidate.GeometricCoreQuarter

/-!
# Original physical data for table-free quarter-word inequalities

This module carries the original signed centers, frame lift, positive gaps
and feasible separating axes into the word argument. A label is evaluated
once at each original vertex and cancels with that same value on the next
edge. The integer/sign classification and physical dihedral action retain
all weak contacts and both nearest-axis representations at a tie.

Only the exact coefficient definitions are imported from `WordProblems`.
No generated word certificate or interval conclusion is used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.TableFreeWordGeometry

open Arithmetic WordProblems

def positiveOf (C : BoundaryCycle Q0) (i : Vertex) : Bool :=
  if C.sigma i=1 then true else false

lemma positiveOf_spec (C : BoundaryCycle Q0) (i : Vertex) :
    (WordProblems.sign (positiveOf C i) : ℝ)=C.sigma i := by
  rcases C.sigma_sign i with h | h <;> simp [positiveOf,WordProblems.sign,h]

lemma alpha_formula (C : BoundaryCycle Q0) (i : Vertex) :
    C.alpha i=(WordProblems.sign (positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i) := by
  rw [positiveOf_spec]
  rcases C.sigma_sign i with h | h <;>
    simp [BoundaryCycle.alpha,BoundaryCycle.tangent,h,neg_div,Real.arctan_neg]

lemma unsigned_angle_nonneg (C : BoundaryCycle Q0) (i : Vertex) :
    0 ≤ Real.arctan (C.b i/C.a i) := by
  have h := Real.arctan_mono (div_nonneg (C.b_nonneg i) (C.a_pos i).le)
  simpa using h

lemma alpha_nonpos (C : BoundaryCycle Q0) (i : Vertex) (h : positiveOf C i=false) :
    C.alpha i ≤ 0 := by
  rw [alpha_formula,h]
  simp only [WordProblems.sign,Bool.false_eq_true,if_false,Rat.cast_neg,Rat.cast_one,neg_one_mul]
  exact neg_nonpos.mpr (unsigned_angle_nonneg C i)

lemma alpha_nonneg (C : BoundaryCycle Q0) (i : Vertex) (h : positiveOf C i=true) :
    0 ≤ C.alpha i := by
  rw [alpha_formula,h]
  simpa [WordProblems.sign] using unsigned_angle_nonneg C i

lemma positiveOf_of_alpha_pos (C : BoundaryCycle Q0) (i : Vertex) (h : 0<C.alpha i) :
    positiveOf C i=true := by
  cases hp : positiveOf C i
  · exact (not_lt_of_ge (alpha_nonpos C i hp) h).elim
  · rfl

lemma positiveOf_of_alpha_neg (C : BoundaryCycle Q0) (i : Vertex) (h : C.alpha i<0) :
    positiveOf C i=false := by
  cases hp : positiveOf C i
  · rfl
  · exact (not_lt_of_ge (alpha_nonneg C i hp) h).elim

def difference {C : BoundaryCycle Q0} (F : QuarterLift C) (i : Vertex) : ℝ :=
  F.theta (next i)-F.theta i

def phaseValue {C : BoundaryCycle Q0} (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) : ℝ :=
  difference F i+((F.word hgap pi_lt_22_over_7 i).val:ℝ)*Real.pi/2

lemma theta_spread {C : BoundaryCycle Q0} (F : QuarterLift C) (i j : Vertex) :
    |F.theta j-F.theta i|<7/10 := by
  apply abs_lt.mpr
  constructor <;> linarith [(F.theta_range i).1,(F.theta_range i).2,
    (F.theta_range j).1,(F.theta_range j).2,F.small]

lemma difference_small {C : BoundaryCycle Q0} (F : QuarterLift C) (i : Vertex) :
    |difference F i|<7/10 := theta_spread F i (next i)

lemma phase_gap (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    phaseValue F hgap i+C.alpha i-C.alpha (next i)=angleGap C.beta i := by
  have hk : ((F.word hgap pi_lt_22_over_7 i).val:ℝ)=
      (integerQuarterIncrement F.quarter i:ℝ) := by
    exact_mod_cast F.word_cast hgap pi_lt_22_over_7 i
  rw [phaseValue,hk]
  have hh := F.edge_identity i
  dsimp [difference]
  linarith

lemma phase_sum (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    (∑ i,phaseValue F hgap i)=2*Real.pi := by
  have he (i : Vertex) : phaseValue F hgap i=
      angleGap C.beta i-C.alpha i+C.alpha (next i) := by
    linarith [phase_gap C F hgap i]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_next,angleGap_sum]
  ring

lemma canonical_phase (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    C.canonicalAngle (next i)-C.canonicalAngle i=
      phaseValue F hgap i-if i=6 then 2*Real.pi else 0 := by
  have h := phase_gap C F hgap i
  by_cases hi : i=6 <;>
    simp [BoundaryCycle.canonicalAngle,angleGap,hi] at * <;> linarith

lemma relative_phase (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) :
    relativeC (C.square i) (C.square (next i))=Real.cos (phaseValue F hgap i) ∧
    relativeS (C.square i) (C.square (next i))=Real.sin (phaseValue F hgap i) := by
  have hci : (C.square i).cosine=Real.cos (C.canonicalAngle i) := C.frame_cos i
  have hsi : (C.square i).sine=Real.sin (C.canonicalAngle i) := C.frame_sin i
  have hcj : (C.square (next i)).cosine=Real.cos (C.canonicalAngle (next i)) := C.frame_cos _
  have hsj : (C.square (next i)).sine=Real.sin (C.canonicalAngle (next i)) := C.frame_sin _
  have hc : relativeC (C.square i) (C.square (next i))=
      Real.cos (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeC,hci,hsi,hcj,hsj,Real.cos_sub] <;> ring
  have hs : relativeS (C.square i) (C.square (next i))=
      Real.sin (C.canonicalAngle (next i)-C.canonicalAngle i) := by
    simp [relativeS,hci,hsi,hcj,hsj,Real.sin_sub] <;> ring
  rw [canonical_phase C F hgap i] at hc hs
  by_cases hi : i=6 <;>
    simpa [hi,Real.cos_sub,Real.sin_sub] using And.intro hc hs

lemma original_margin (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    0 ≤ forwardMargin j (C.a i) (C.b i) (C.a (next i)) (C.b (next i))
      (WordProblems.sign (positiveOf C i)) (WordProblems.sign (positiveOf C (next i)))
      (phaseValue F hgap i) := by
  rw [positiveOf_spec,positiveOf_spec]
  have he := canonical_margin_identity j _ _ _ _ _ _ _ _ (phaseValue F hgap i)
    (C.center_eq i) (C.center_eq (next i)) (relative_phase C F hgap i).1
    (relative_phase C F hgap i).2
  rw [← he]
  exact sub_nonneg.mpr hj

/-- The original feasible axis cannot belong to any excluded core class.
The quarter lift remains arbitrary; no candidate word or tangent cut is
assumed, and zero transverse coordinates keep their actual signed value. -/
lemma original_not_core_excluded (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    ¬ CoreSeparatorExcluded (F.word hgap pi_lt_22_over_7 i)
      (C.kind i) (C.kind (next i)) (positiveOf C i) (positiveOf C (next i)) j := by
  have hm := original_margin C F hgap i j hj
  rw [positiveOf_spec,positiveOf_spec] at hm
  have hσ : |C.sigma i*C.b i| ≤ C.a i := by
    rw [Candidate.signed_b_abs]
    exact C.b_le_a i
  have hτ : |C.sigma (next i)*C.b (next i)| ≤ C.a (next i) := by
    rw [Candidate.signed_b_abs]
    exact C.b_le_a (next i)
  rintro (⟨hk,⟨rfl,ht⟩ | ⟨rfl,hs⟩⟩ | ⟨rfl,hnegative,ht⟩ | ⟨rfl,hpositive,hs⟩ |
    ⟨hk,hs,ht,hpositive,hnegative⟩)
  · have hsmall : |phaseValue F hgap i| ≤ 7/10 := by
      simpa [phaseValue,hk] using (difference_small F i).le
    have hp := Candidate.Geometric.primary_margin_upper (C.a_pos i).le hσ hsmall
      (X := C.a (next i))
    have hcore := Candidate.Geometric.core_primary_upper C (next i) ht
    simp [forwardMargin] at hm
    nlinarith [C.a_pos i]
  · have hsmall : |phaseValue F hgap i| ≤ 7/10 := by
      simpa [phaseValue,hk] using (difference_small F i).le
    have hp := Candidate.Geometric.primary_margin_upper (C.a_pos (next i)).le
      (v := -(C.sigma (next i)*C.b (next i)))
      (by simpa only [abs_neg] using hτ) hsmall (X := C.a i)
    have hcore := Candidate.Geometric.core_primary_upper C i hs
    simp [forwardMargin] at hm
    nlinarith [C.a_pos (next i)]
  · have hsource : C.sigma i*C.b i ≤ 0 := by
      rw [← positiveOf_spec C i,hnegative]
      simpa [WordProblems.sign] using neg_nonpos.mpr (C.b_nonneg i)
    have hn := Candidate.Geometric.target_core_secondary_margin (a := C.a i)
      hsource (C.a_pos (next i)).le (Candidate.Geometric.core_primary_upper C (next i) ht)
      hτ (t := phaseValue F hgap i)
    linarith
  · have htarget : 0 ≤ C.sigma (next i)*C.b (next i) := by
      rw [← positiveOf_spec C (next i),hpositive]
      simpa [WordProblems.sign] using C.b_nonneg (next i)
    have hn := Candidate.Geometric.source_core_secondary_margin (A := C.a (next i))
      htarget (C.a_pos i).le (Candidate.Geometric.core_primary_upper C i hs)
      hσ (t := phaseValue F hgap i)
    linarith
  · have hsourceSign : C.sigma i=1 := by
      rw [← positiveOf_spec C i,hpositive]
      norm_num [WordProblems.sign]
    have htargetSign : C.sigma (next i)= -1 := by
      rw [← positiveOf_spec C (next i),hnegative]
      norm_num [WordProblems.sign]
    have hsourceAngle : C.alpha i=Real.arctan (C.b i/C.a i) := by
      rw [alpha_formula C i,hpositive]
      norm_num [WordProblems.sign]
    have htargetAngle : C.alpha (next i)= -Real.arctan (C.b (next i)/C.a (next i)) := by
      rw [alpha_formula C (next i),hnegative]
      norm_num [WordProblems.sign]
    have hphase : phaseValue F hgap i=Real.pi/2+difference F i := by
      simp [phaseValue,hk,add_comm]
    have he := phase_gap C F hgap i
    rw [hphase,hsourceAngle,htargetAngle] at he
    have hg := Candidate.Geometric.cycle_gap_lt_seven_quarters C hgap i
    have hn := Candidate.Geometric.core_quarter_opposite_margin
      ⟨(Candidate.Geometric.canonical_primary_gt_half C i).le,
        Candidate.Geometric.core_primary_upper C i hs⟩
      ⟨(Candidate.Geometric.canonical_primary_gt_half C (next i)).le,
        Candidate.Geometric.core_primary_upper C (next i) ht⟩
      ⟨C.b_nonneg i,C.b_le_a i⟩ ⟨C.b_nonneg (next i),C.b_le_a (next i)⟩
      (difference_small F i).le (by linarith) j
    rw [hsourceSign,htargetSign,hphase] at hm
    linarith

/-- Common label on the original primary and transverse coordinates. -/
def commonValue (kind : RadialKind) (σ : Bool) (a b : ℝ) : ℝ :=
  (WordProblems.sign σ:ℝ)*(if kind=.outer then -9/100+(13/200)*a+(203/200)*b
    else (73/10)*(7/12-a)+(291/250)*b)

def commonMarker (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  commonValue (C.kind i) (positiveOf C i) (C.a i) (C.b i)

lemma commonMarker_core_eq (C : BoundaryCycle Q0) (i : Vertex)
    (hk : C.kind i≠.outer) :
    commonMarker C i=C.sigma i*CoreWordGeometry.label (C.a i) (C.b i) := by
  simp [commonMarker,commonValue,positiveOf_spec,hk,CoreWordGeometry.label]

/-- Both wrong-word label polynomials, evaluated without replacing the
actual primary coordinate by a chart or radical representative. -/
def wrongValue (w : WrongWord) (i : Vertex) (kind : RadialKind)
    (σ : Bool) (a b : ℝ) : ℝ :=
  match w with
  | .short =>
      let v := shortCoefficients i (radialIndex kind) (signIndex σ)
      (v 0:ℝ)/100000+(v 1:ℝ)/100000*a+
        (WordProblems.sign σ:ℝ)*(v 2:ℝ)/100000*b
  | .second =>
      let v := secondCoefficients i (radialIndex kind) (signIndex σ)
      (WordProblems.sign σ:ℝ)*((v 0:ℝ)/100000+(v 1:ℝ)/100000*a+
        (v 2:ℝ)/100000*b+(v 3:ℝ)/100000*b^2+(v 4:ℝ)/100000*a*b)

def wrongMarker (C : BoundaryCycle Q0) (w : WrongWord) (i : Vertex) : ℝ :=
  wrongValue w i (C.kind i) (positiveOf C i) (C.a i) (C.b i)

/-- One original vertex value occurs with each sign in the cyclic sum. -/
lemma marker_budget (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (marker : Vertex→ℝ) :
    (∑i,phaseValue F hgap i+marker i-marker (next i))=2*Real.pi := by
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_next,phase_sum C F hgap]
  ring

lemma common_core_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀i,19/25<angleGap C.beta i) (i : Vertex)
    (hi : C.kind i≠.outer) (hj : C.kind (next i)≠.outer) :
    (commonGamma (F.word hgap pi_lt_22_over_7 i):ℝ)<
      phaseValue F hgap i+commonMarker C i-commonMarker C (next i) := by
  have h := CoreWordGeometry.common_core_cost C i hi hj
  rw [← commonMarker_core_eq C i hi,← commonMarker_core_eq C (next i) hj] at h
  have hγ : (commonGamma (F.word hgap pi_lt_22_over_7 i):ℝ)≤391/400 := by
    generalize F.word hgap pi_lt_22_over_7 i=k
    fin_cases k <;> norm_num [commonGamma]
  linarith [phase_gap C F hgap i]

lemma zero_not_negative_positive (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex)
    (hz : F.word hgap pi_lt_22_over_7 i=0) :
    ¬ (positiveOf C i=false ∧ positiveOf C (next i)=true) := by
  rintro ⟨hs,ht⟩
  have hs' := alpha_nonpos C i hs
  have ht' := alpha_nonneg C (next i) ht
  have hd := (abs_lt.mp (difference_small F i)).2
  have he := phase_gap C F hgap i
  simp only [phaseValue,hz,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at he
  linarith [hgap i]

/-- The two initial zero increments force strictly positive alpha at role
0 and strictly negative alpha at role 2, without a sign choice by search. -/
lemma initial_signs (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) :
    positiveOf C 0=true ∧ positiveOf C 2=false := by
  have hz0 : F.word hgap pi_lt_22_over_7 0=0 := by cases w <;> simp [hw,wrongWord]
  have hz1 : F.word hgap pi_lt_22_over_7 1=0 := by cases w <;> simp [hw,wrongWord]
  have h0 := phase_gap C F hgap 0
  have h1 := phase_gap C F hgap 1
  simp only [phaseValue,hz0,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at h0
  simp only [phaseValue,hz1,Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,add_zero] at h1
  norm_num [difference,next] at h0 h1
  have ht := (abs_lt.mp (theta_spread F 0 2)).2
  have hd : 41/50<C.alpha 0-C.alpha 2 := by linarith [hgap 0,hgap 1]
  have ha := C.alpha_range 0
  have hb := C.alpha_range 2
  have hapos : 0<C.alpha 0 := by linarith [pi_lt_22_over_7]
  have hbneg : C.alpha 2<0 := by linarith [pi_lt_22_over_7]
  exact ⟨positiveOf_of_alpha_pos C 0 hapos,positiveOf_of_alpha_neg C 2 hbneg⟩

lemma actual_allowed (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) (i : Vertex) :
    allowed w i (positiveOf C i) (positiveOf C (next i)) := by
  obtain ⟨h0,h2⟩ := initial_signs C F hgap w hw
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro rfl
    exact h0
  · rintro rfl
    exact h2
  · intro hi
    simpa [hi] using h0
  · intro hi
    simpa [hi] using h2
  · intro hz
    exact zero_not_negative_positive C F hgap i (by simpa [hw] using hz)

/-- Normalizing the EDGE word requires an extra vertex shift in the
reflected case.  The physical action itself is the shared actual-square
action, with its complete signed-axis transport. -/
def normalizingAction (shift : Vertex) (reversed : Bool) : CycleAction where
  shift := if reversed then shift+1 else -shift
  reversed := reversed
  rotation := 0

lemma normalizing_edge (shift : Vertex) (reversed : Bool) (i : Vertex) :
    (if reversed then shift-(normalizingAction shift reversed).edge i
      else (normalizingAction shift reversed).edge i+shift)=i := by
  cases reversed <;>
    simp [normalizingAction,CycleAction.edge,CycleAction.index,next] <;> abel

lemma word_act (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (G : CycleAction) :
    (F.act G).word (boundary_gap_lower (G.boundary C) le_rfl) pi_lt_22_over_7=
      fun i => F.word hgap pi_lt_22_over_7 (G.edge i) := by
  funext i
  apply Fin.ext
  change (integerQuarterIncrement (G.quarter F.quarter) i).toNat=
    (integerQuarterIncrement F.quarter (G.edge i)).toNat
  rw [G.quarter_increment]

lemma normalize_word (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (v : QuarterWord)
    (hv : (F.word hgap pi_lt_22_over_7).DihedralEquivalent v) :
    ∃ G : CycleAction,
      (F.act G).word (boundary_gap_lower (G.boundary C) le_rfl) pi_lt_22_over_7=v := by
  obtain ⟨shift,reversed,hword⟩ := hv
  refine ⟨normalizingAction shift reversed,?_⟩
  rw [word_act C F hgap]
  funext i
  rw [hword]
  change v (if reversed then shift-(normalizingAction shift reversed).edge i
    else (normalizingAction shift reversed).edge i+shift)=v i
  rw [normalizing_edge]


end SquaresInCircles.Eight.TableFreeWordGeometry
