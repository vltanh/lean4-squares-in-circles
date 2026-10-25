module

public import SquaresInCircles.Eight.TableFree.ShortOuterOneSameContact
public import SquaresInCircles.Eight.TableFree.CommonOneSecondary

/-!
# Exact original-coordinate labels for the second wrong word

Only the literal role polynomials from WordProblems are used.  Every
label is evaluated on the original physical primary and transverse
coordinates; passing to the circle chart is an explicitly proved
identity.  Reflection reverses the edge, swaps the states, and changes
both signs with its complete label identity.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD ratioDD)

structure RoleLabel where
  c : ℝ
  p : ℝ
  q : ℝ
  r : ℝ
  s : ℝ

def RoleLabel.eval (H : RoleLabel) (a b : ℝ) : ℝ :=
  H.c+H.p*a+H.q*b+H.r*b^2+H.s*a*b

def RoleLabel.outer (H : RoleLabel) (b : ℝ) : ℝ := H.eval (arc b) b

def RoleLabel.d1 (H : RoleLabel) (b : ℝ) : ℝ :=
  H.q+2*H.r*b+H.s*arc b-(H.p+H.s*b)*ratio b

def RoleLabel.d2 (H : RoleLabel) (b : ℝ) : ℝ :=
  2*H.r-2*H.s*ratio b-(H.p+H.s*b)*ratioD b

def RoleLabel.d3 (H : RoleLabel) (b : ℝ) : ℝ :=
  -3*H.s*ratioD b-(H.p+H.s*b)*ratioDD b

def RoleLabel.primary (H : RoleLabel) : RoleLabel :=
  ⟨-H.c-H.r*(Q0-1/2),H.r-H.q,H.r-H.p,H.r,-H.s⟩

def coefficients (i : Vertex) (kind : RadialKind) (σ : Bool) : RoleLabel :=
  let v := WordProblems.secondCoefficients i (WordProblems.radialIndex kind)
    (WordProblems.signIndex σ)
  ⟨(v 0:ℝ)/100000,(v 1:ℝ)/100000,(v 2:ℝ)/100000,
    (v 3:ℝ)/100000,(v 4:ℝ)/100000⟩

def label (i : Vertex) (kind : RadialKind) (σ : Bool) (a b : ℝ) : ℝ :=
  TableFreeWordGeometry.wrongValue .second i kind σ a b

def cost (i : Vertex) (source target : RadialKind) (σ τ : Bool)
    (a b A B φ : ℝ) : ℝ :=
  φ+label i source σ a b-label (next i) target τ A B

def threshold (i : Vertex) : ℝ := WordProblems.wrongGamma .second i

def PLabel : RoleLabel := ⟨2478/100000,0,93015/100000,2363/100000,-11055/100000⟩
def RLabel : RoleLabel := ⟨394/100000,0,33945/100000,0,39635/100000⟩
def JLabel : RoleLabel := ⟨0,-26/100000,83194/100000,-11864/100000,17627/100000⟩
def VLabel : RoleLabel := ⟨0,-1025/100000,16031/100000,0,63457/100000⟩
def TLabel : RoleLabel := ⟨1670/100000,0,242322/100000,-91744/100000,-95769/100000⟩
def LLabel : RoleLabel := ⟨3965/100000,0,385510/100000,-149748/100000,-189442/100000⟩
def KLabel : RoleLabel := ⟨0,-2112/100000,29090/100000,0,44642/100000⟩

def P (b : ℝ) : ℝ := PLabel.outer b
def R (b : ℝ) : ℝ := RLabel.outer b
def J (b : ℝ) : ℝ := JLabel.outer b
def V (b : ℝ) : ℝ := VLabel.outer b
def T (b : ℝ) : ℝ := TLabel.outer b
def L (b : ℝ) : ℝ := LLabel.outer b
def K (b : ℝ) : ℝ := KLabel.outer b

def PPrimaryLabel : RoleLabel := PLabel.primary

def U (b : ℝ) : ℝ := arc b+1/2
def W (b : ℝ) : ℝ := b+1/2

lemma outer_domain {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    b∈Icc 0 outerAxial := ShortOuterOne.SameContact.outer_domain hb

lemma primary_domain {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    a∈Icc 0 outerAxial :=
  ⟨by linarith [ha.1,outer_endpoint_bounds.2.2.1],ha.2⟩

lemma outer_zero_mem : (0:ℝ)∈Icc 0 outerDiagonal :=
  ⟨le_rfl,by linarith [outer_endpoint_bounds.2.2.1]⟩

lemma primary_one_mem : (1:ℝ)∈Icc outerDiagonal outerAxial :=
  ⟨by linarith [outer_endpoint_bounds.2.2.2],by linarith [outer_endpoint_bounds.1]⟩

lemma primary_state {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    OuterState a (arc a) := ShortOuterOne.SameContact.primary_state ha

lemma primary_secondary_mem {a : ℝ} (ha : a∈Icc outerDiagonal outerAxial) :
    arc a∈Icc 0 outerDiagonal := ShortOuterOne.SameContact.primary_secondary_mem ha

lemma U_positive {b : ℝ} (hb : b∈Icc 0 outerAxial) : 0<U b :=
  ShortOuterOne.SameContact.shifted_positive hb

lemma UW_circle {b : ℝ} (hb : b∈Icc 0 outerAxial) : (U b)^2+(W b)^2=Q0 :=
  ShortOuterOne.SameContact.arc_circle hb

lemma UW_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1399/1000:ℝ)<U b ∧ U b<383/200 ∧ (1/2:ℝ)≤W b ∧ W b<7/5 := by
  have hs := CommonQuarter.outer_bounds (ShortOuterOne.SameContact.arc_state hb)
  dsimp [U,W]
  exact ⟨by linarith [hs.1,fine_outer_endpoint_bounds.2],
    by linarith [hs.2.1,outer_endpoint_bounds.2.1],
    by linarith [hb.1],by linarith [hb.2,outer_endpoint_bounds.2.2.2]⟩

lemma outer_ratio_bounds {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (261/1000:ℝ)<ratio b ∧ ratio b≤1 ∧ 0<ratioD b ∧ ratioD b<36/25 := by
  have hp := U_positive (outer_domain hb)
  have hu := UW_bounds hb
  have hs := ShortOuterOne.SameContact.arc_state hb
  refine ⟨?_,?_,ShortOuterOne.SameContact.ratioD_pos (outer_domain hb),?_⟩
  · change (261/1000:ℝ)<W b/U b
    apply (lt_div_iff₀ hp).2
    nlinarith [hu.2.1,hu.2.2.1]
  · change W b/U b≤1
    apply (div_le_one hp).2
    dsimp [W,U]
    linarith [hs.2.1]
  · change Q0/(U b)^3<36/25
    apply (div_lt_iff₀ (pow_pos hp 3)).2
    have hc := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1399/1000) hu.1.le 3
    norm_num [Q0]
    nlinarith

lemma RoleLabel.outer_hasDerivAt (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) : HasDerivAt H.outer (H.d1 b) b := by
  have ha := ShortOuterOne.SameContact.arc_hasDerivAt hb
  have hp2 : HasDerivAt (fun y : ℝ => y^2) (2*b) b := by
    simpa using hasDerivAt_pow 2 b
  have hd := ((((hasDerivAt_const b H.c).fun_add (ha.const_mul H.p)).fun_add
    ((hasDerivAt_id' (x := b)).const_mul H.q)).fun_add
      (hp2.const_mul H.r)).fun_add
        ((ha.const_mul H.s).fun_mul (hasDerivAt_id' (x := b)))
  refine hd.congr_deriv ?_
  simp only [RoleLabel.d1]
  ring

lemma RoleLabel.d1_hasDerivAt (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) : HasDerivAt H.d1 (H.d2 b) b := by
  have ha := ShortOuterOne.SameContact.arc_hasDerivAt hb
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt hb
  have hd := (((hasDerivAt_const b H.q).fun_add
    ((hasDerivAt_id' (x := b)).const_mul (2*H.r))).fun_add (ha.const_mul H.s)).fun_sub
      ((((hasDerivAt_id' (x := b)).const_mul H.s).const_add H.p).fun_mul hr)
  refine hd.congr_deriv ?_
  simp only [RoleLabel.d2]
  ring

lemma RoleLabel.d2_hasDerivAt (H : RoleLabel) {b : ℝ}
    (hb : b∈Icc 0 outerAxial) : HasDerivAt H.d2 (H.d3 b) b := by
  have hr := ShortOuterOne.SameContact.ratio_hasDerivAt hb
  have hr' := ShortOuterOne.SameContact.ratioD_hasDerivAt hb
  have hd := ((hasDerivAt_const b (2*H.r)).fun_sub (hr.const_mul (2*H.s))).fun_sub
    ((((hasDerivAt_id' (x := b)).const_mul H.s).const_add H.p).fun_mul hr')
  refine hd.congr_deriv ?_
  simp only [RoleLabel.d3]
  ring

lemma RoleLabel.outer_actual (H : RoleLabel) {a b : ℝ} (hs : OuterState a b) :
    H.outer b=H.eval a b := by
  rw [RoleLabel.outer,(ShortOuterOne.SameContact.actual_arc hs).1]

lemma RoleLabel.primary_actual (H : RoleLabel) {a b : ℝ} (hs : OuterState a b) :
    H.primary.outer a= -H.outer b := by
  rw [RoleLabel.outer,RoleLabel.outer,
    (ShortOuterOne.SameContact.actual_arc hs).2,
    (ShortOuterOne.SameContact.actual_arc hs).1]
  dsimp [RoleLabel.primary,RoleLabel.eval]
  linear_combination H.r*hs.2.2

lemma label_coefficients (i : Vertex) (kind : RadialKind) (σ : Bool) (a b : ℝ) :
    label i kind σ a b=(WordProblems.sign σ:ℝ)*(coefficients i kind σ).eval a b := by
  rfl

lemma label_outer_actual (i : Vertex) (σ : Bool) {a b : ℝ} (hs : OuterState a b) :
    label i .outer σ a b=(WordProblems.sign σ:ℝ)*(coefficients i .outer σ).outer b := by
  rw [label_coefficients,RoleLabel.outer_actual _ hs]

lemma threshold_value (i : Vertex) : threshold i=(17953/20000:ℝ) := by
  norm_num [threshold,WordProblems.wrongGamma]

def mirror (i : Vertex) : Vertex := 2-i
def reverseEdge (i : Vertex) : Vertex := 1-i

lemma label_reflection (i : Vertex) (kind : RadialKind) (σ : Bool) (a b : ℝ) :
    label (mirror i) kind (!σ) a b= -label i kind σ a b := by
  fin_cases i <;> cases kind <;> cases σ <;>
    norm_num [mirror,label,TableFreeWordGeometry.wrongValue,
      WordProblems.secondCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign] <;> ring

lemma cost_reflection (i : Vertex) (source target : RadialKind) (σ τ : Bool)
    (a b A B φ : ℝ) :
    cost (reverseEdge i) target source (!τ) (!σ) A B a b φ=
      cost i source target σ τ a b A B φ := by
  have hs : reverseEdge i=mirror (next i) := by fin_cases i <;> rfl
  have ht : next (reverseEdge i)=mirror i := by fin_cases i <;> rfl
  unfold cost
  rw [ht,hs,label_reflection,label_reflection]
  ring

lemma core_two_to_positive_outer {kind : RadialKind} (hk : kind≠.outer)
    {a b A B φ : ℝ} (ht : OuterState A B) :
    cost 2 kind .outer false true a b A B φ=
      φ-(1/800+(103981/100000)*b)-V B := by
  rw [show V B=VLabel.eval A B from VLabel.outer_actual ht]
  cases kind
  · exact absurd rfl hk
  all_goals
    norm_num [cost,label,TableFreeWordGeometry.wrongValue,next,
      WordProblems.secondCoefficients,WordProblems.radialIndex,
      WordProblems.signIndex,WordProblems.sign,VLabel,RoleLabel.eval]
    ring

end SquaresInCircles.Eight.TableFree.SecondWord

