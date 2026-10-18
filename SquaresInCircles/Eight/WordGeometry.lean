module

public import SquaresInCircles.Eight.Generated.WordCertificates
public import SquaresInCircles.Eight.CycleActions

/-!
# Actual geometric exclusion of the six noncandidate quarter words

The common increment table first excludes every word containing a two.
The two remaining wrong words use their separate role-dependent label
systems.  A marker is evaluated once per vertex, so the target value on
one edge is exactly the source value on the next edge.

The finite interval problems receive the actual radial states, frame
increments, physical gaps and original separating-axis margins.  The
nineteen allowed sign cases follow from the two initial zero increments
and the impossibility of a negative-to-positive zero edge.

Dihedral normalization acts on actual squares and lifts through
`CycleAction.boundary` and `QuarterLift.act`.  In particular reflection
reverses an edge before transporting its separating axis.  The extra one
in the reflected vertex shift accounts for that endpoint reversal.

Uncompiled source draft.  None of the finite proof scripts imported from
`Generated.WordCertificates` has been evaluated in this session.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace SquaresInCircles.Eight.WordGeometry

open Arithmetic Arithmetic.RealBox WordProblems

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

lemma environment (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (pairBox (C.kind i) (C.kind (next i))).Mem ![C.b i,C.b (next i),difference F i] ∧
      (∀ e ∈ pairHypotheses (F.word hgap pi_lt_22_over_7 i)
        (C.kind i) (C.kind (next i)) (positiveOf C i) (positiveOf C (next i)) j,
        0 ≤ e.eval ![C.b i,C.b (next i),difference F i]) := by
  have ha : 1/2<C.a i := by linarith [(Candidate.canonical_bounds C le_rfl i).1]
  have hA : 1/2<C.a (next i) := by
    linarith [(Candidate.canonical_bounds C le_rfl (next i)).1]
  have hδ : difference F i+((F.word hgap pi_lt_22_over_7 i).val:ℝ)*Real.pi/2+
      (WordProblems.sign (positiveOf C i):ℝ)*Real.arctan (C.b i/C.a i)-
      (WordProblems.sign (positiveOf C (next i)):ℝ)*Real.arctan (C.b (next i)/C.a (next i))=
        angleGap C.beta i := by
    rw [← alpha_formula,← alpha_formula]
    exact phase_gap C F hgap i
  apply local_environment (C.kind i) (C.kind (next i)) (positiveOf C i)
    (positiveOf C (next i)) (F.word hgap pi_lt_22_over_7 i) j
    ha hA (C.b_nonneg i) (C.b_nonneg (next i)) (C.b_le_a i) (C.b_le_a (next i))
    (C.boundary i) (C.boundary (next i)) (difference_small F i).le
  · rw [hδ]
    exact ⟨(hgap i).le,(boundary_gap_upper C le_rfl i).le⟩
  · exact original_margin C F hgap i j hj

def commonValue (kind : RadialKind) (σ : Bool) (b : ℝ) : ℝ :=
  let a := primaryValue kind b
  (WordProblems.sign σ:ℝ)*(if kind=.outer then -9/100+(13/200)*a+(203/200)*b
    else (73/10)*(7/12-a)+(291/250)*b)

lemma commonLabel_eval (kind : RadialKind) (σ : Bool) (b : E) (env : Fin 3→ℝ) :
    (commonLabel kind σ b).eval env=commonValue kind σ (b.eval env) := by
  cases kind <;> simp [commonLabel,commonValue,Expr.eval,primary_eval] <;> ring

def commonMarker (C : BoundaryCycle Q0) (i : Vertex) : ℝ :=
  commonValue (C.kind i) (positiveOf C i) (C.b i)

def wrongValue (w : WrongWord) (i : Vertex) (kind : RadialKind) (σ : Bool) (b : ℝ) : ℝ :=
  let a := primaryValue kind b
  match w with
  | .short =>
      let v := shortCoefficients i (radialIndex kind) (signIndex σ)
      (v 0:ℝ)/100000+(v 1:ℝ)/100000*a+(WordProblems.sign σ:ℝ)*(v 2:ℝ)/100000*b
  | .second =>
      let v := secondCoefficients i (radialIndex kind) (signIndex σ)
      (WordProblems.sign σ:ℝ)*((v 0:ℝ)/100000+(v 1:ℝ)/100000*a+
        (v 2:ℝ)/100000*b+(v 3:ℝ)/100000*b^2+(v 4:ℝ)/100000*a*b)

lemma wrongLabel_eval (w : WrongWord) (i : Vertex) (kind : RadialKind)
    (σ : Bool) (b : E) (env : Fin 3→ℝ) :
    (wrongLabel w i kind σ b).eval env=wrongValue w i kind σ (b.eval env) := by
  cases w <;> simp [wrongLabel,wrongValue,Expr.eval,primary_eval] <;> push_cast <;> ring

def wrongMarker (C : BoundaryCycle Q0) (w : WrongWord) (i : Vertex) : ℝ :=
  wrongValue w i (C.kind i) (positiveOf C i) (C.b i)

lemma phase_eval (k : Fin 3) (env : Fin 3→ℝ) :
    (phase k).eval env=env 2+(k.val:ℝ)*Real.pi/2 := by
  simp [phase,Expr.eval] <;> ring

lemma marker_budget (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (marker : Vertex→ℝ) :
    (∑ i,(phaseValue F hgap i+marker i-marker (next i)))=2*Real.pi := by
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sum_next,phase_sum C F hgap]
  ring

/-- The common table is applied to the original owner chosen by geometry;
every other feasible owner also satisfies the same conclusion. -/
lemma common_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (commonGamma (F.word hgap pi_lt_22_over_7 i):ℝ)<
      phaseValue F hgap i+commonMarker C i-commonMarker C (next i) := by
  obtain ⟨hbox,hhyps⟩ := environment C F hgap i j hj
  have h := certify_sound
    (common_certificates (F.word hgap pi_lt_22_over_7 i) (C.kind i) (C.kind (next i))
      (positiveOf C i) (positiveOf C (next i)) j)
    ![C.b i,C.b (next i),difference F i] hbox hhyps
  change 0 < (phase (F.word hgap pi_lt_22_over_7 i)+
    commonLabel (C.kind i) (positiveOf C i) (.var 0)-
    commonLabel (C.kind (next i)) (positiveOf C (next i)) (.var 1)-
    (.const (commonGamma (F.word hgap pi_lt_22_over_7 i)))).eval
      ![C.b i,C.b (next i),difference F i] at h
  simp only [Expr.eval,phase_eval,commonLabel_eval] at h
  simpa [phaseValue,commonMarker,Expr.eval] using sub_pos.mp h

lemma commonGamma_numerator (k : Fin 3) :
    (commonGamma k:ℝ)=(doubleWordCostNumerator k:ℝ)/10000 := by
  fin_cases k <;> norm_num [commonGamma,doubleWordCostNumerator]

theorem no_double (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    ¬ ∃ i,F.word hgap pi_lt_22_over_7 i=2 := by
  apply no_double_word_of_cost_bound (F.word hgap pi_lt_22_over_7)
    (F.word_admissible hgap pi_lt_22_over_7)
    (fun i => phaseValue F hgap i+commonMarker C i-commonMarker C (next i))
  · intro i
    obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
    have h := common_pair C F hgap i j (by simpa [← hj] using C.feasible i)
    rw [commonGamma_numerator] at h
    exact h.le
  · exact (marker_budget C F hgap (commonMarker C)).le
  · exact pi_lt_22_over_7

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

lemma wrong_pair (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord)
    (hw : F.word hgap pi_lt_22_over_7=wrongWord w) (i : Vertex) (j : Fin 4)
    (hj : (forwardAxis j).Feasible (C.square i) (C.square (next i))) :
    (wrongGamma w i:ℝ)<phaseValue F hgap i+wrongMarker C w i-wrongMarker C w (next i) := by
  obtain ⟨hbox,hhyps⟩ := environment C F hgap i j hj
  rw [hw] at hhyps
  have h := certify_sound
    (wrong_certificates w i (C.kind i) (C.kind (next i)) (positiveOf C i)
      (positiveOf C (next i)) j (actual_allowed C F hgap w hw i))
    ![C.b i,C.b (next i),difference F i] hbox hhyps
  change 0 < (phase (wrongWord w i)+
    wrongLabel w i (C.kind i) (positiveOf C i) (.var 0)-
    wrongLabel w (next i) (C.kind (next i)) (positiveOf C (next i)) (.var 1)-
    (.const (wrongGamma w i))).eval ![C.b i,C.b (next i),difference F i] at h
  simp only [Expr.eval,phase_eval,wrongLabel_eval] at h
  simpa [phaseValue,hw,wrongMarker,Expr.eval] using sub_pos.mp h

lemma wrongGamma_sum (w : WrongWord) :
    (710/113:ℝ)<∑ i,(wrongGamma w i:ℝ) := by
  cases w <;> norm_num [wrongGamma,Fin.sum_univ_succ]

theorem wrong_word_impossible (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (w : WrongWord) :
    F.word hgap pi_lt_22_over_7 ≠ wrongWord w := by
  intro hw
  have hcost (i : Vertex) : (wrongGamma w i:ℝ) ≤
      phaseValue F hgap i+wrongMarker C w i-wrongMarker C w (next i) := by
    obtain ⟨j,hj⟩ := boundary_forward_complete C le_rfl i (C.selected i) (C.feasible i)
    exact (wrong_pair C F hgap w hw i j (by simpa [← hj] using C.feasible i)).le
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcost i)
  rw [marker_budget C F hgap (wrongMarker C w)] at hh
  linarith [wrongGamma_sum w,two_pi_lt_710_over_113]

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

/-- All six representatives are excluded as actual geometric cycles,
including every cyclic shift and every reflected orientation. -/
theorem six_exclusions (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) (j : Fin 6) :
    ¬ (F.word hgap pi_lt_22_over_7).DihedralEquivalent (quarterRepresentatives j.castSucc) := by
  intro heq
  obtain ⟨G,hword⟩ := normalize_word C F hgap (quarterRepresentatives j.castSucc) heq
  let D := G.boundary C
  let H := F.act G
  have hg : ∀ i,19/25<angleGap D.beta i := boundary_gap_lower D le_rfl
  have he : H.word hg pi_lt_22_over_7=quarterRepresentatives j.castSucc := hword
  fin_cases j
  · apply no_double D H hg
    exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply no_double D H hg
    exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply no_double D H hg
    exact ⟨4,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply no_double D H hg
    exact ⟨6,by rw [he]; norm_num [quarterRepresentatives]⟩
  · apply wrong_word_impossible D H hg .short
    simpa [quarterRepresentatives,wrongWord] using he
  · apply wrong_word_impossible D H hg .second
    simpa [quarterRepresentatives,wrongWord] using he

end SquaresInCircles.Eight.WordGeometry

namespace SquaresInCircles.Eight

/-- The complete quarter-word reduction, now supplied with all six actual
continuous exclusions.  No word-exclusion premise remains. -/
theorem quarter_word_candidate (C : BoundaryCycle Q0) (F : QuarterLift C)
    (hgap : ∀ i,19/25<angleGap C.beta i) :
    (F.word hgap pi_lt_22_over_7).DihedralEquivalent candidateQuarterWord := by
  exact candidate_word_after_six_exclusions _ (F.word_admissible hgap pi_lt_22_over_7)
    (WordGeometry.six_exclusions C F hgap)

end SquaresInCircles.Eight
