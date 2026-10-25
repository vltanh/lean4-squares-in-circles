module

public import SquaresInCircles.Eight.Words.Second.WordData

/-!
# Eight squares: the literal negative edge-three cost and its original projections

The source label is `T` and the target label is `K`, both evaluated on
the original common circle.  The weak owner inequalities are the same
physical projections as the preceding negative-quarter family.
-/

section
/-!
## Rational differential identities for a fixed-circle contact

The inverse rotation uses the physical shifted primary coordinate.  Its
rational derivative and its derivative in the target coordinate are
kept exact; no label bound or contact-minimum assumption enters here.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

namespace NegativeTwo.Inverse

def q (u : ℝ) : ℝ := Q0+1-2*u
def N (u : ℝ) : ℝ := 4*Q0*u-2*u^2-Q0*(Q0+1)
def factor (u : ℝ) : ℝ := (Q0-u)/(u*q u)
def factorD (u : ℝ) : ℝ := N u/(u^2*(q u)^2)
def K (u : ℝ) : ℝ := 3*u^3-5*Q0*u+Q0*(Q0+1)
def brace (u r v : ℝ) : ℝ := Q0/u^3-2*r^2/q u-r^2/v^2

lemma q_hasDerivAt (u : ℝ) : HasDerivAt q (-2) u := by
  have h : HasDerivAt (fun y : ℝ => Q0+1-2*y) (-(2*1)) u :=
    ((hasDerivAt_id' u).const_mul (2:ℝ)).const_sub (Q0+1)
  exact h.congr_deriv (by ring)

lemma factor_hasDerivAt {u : ℝ} (hu : u≠0) (hq : q u≠0) :
    HasDerivAt factor (factorD u) u := by
  have hd := ((hasDerivAt_id u).const_sub Q0).div
    ((hasDerivAt_id u).mul (q_hasDerivAt u)) (mul_ne_zero hu hq)
  convert hd using 1
  · rfl
  · dsimp [factorD,N]
    field_simp [hu,hq]
    dsimp [q]
    ring

lemma brace_identity {u r z v : ℝ} (hu : u≠0) (hq : q u≠0)
    (hv : v≠0) (hc : u^2+r^2*u^2=Q0) (hn : z^2+v^2=q u) :
    brace u r v=K u/(u^3*q u)-r^2*z^2/(q u*v^2) := by
  have hK : K u=Q0*q u-3*r^2*u^3 := by
    dsimp [K,q]
    linear_combination 3*u*hc
  have hrec : 1/v^2=1/q u+z^2/(q u*v^2) := by
    field_simp [hq,hv]
    linarith
  dsimp [brace]
  rw [show r^2/v^2=r^2*(1/v^2) by ring,hrec,hK]
  field_simp [hu,hq,hv]
  ring

lemma actual_q_positive {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    (1357/1250:ℝ)<q (U b) := by
  have hu := (UW_bounds hb).2.1
  norm_num [q,Q0]
  linarith

lemma factor_lower {u : ℝ} (hu : 0<u) (hq : 0<q u) :
    (4/5:ℝ)<factor u := by
  apply (lt_div_iff₀ (mul_pos hu hq)).2
  have he : Q0-u-(4/5)*u*q u=
      (8/5)*(u-7707/5000)^2+1783401/15625000 := by
    norm_num [q,Q0]
    ring
  have hh := sq_nonneg (u-7707/5000)
  nlinarith

end NegativeTwo.Inverse

namespace PJCritical

abbrev heightFactorD := NegativeTwo.Inverse.factorD

def inverseTarget (u r z v : ℝ) : ℝ :=
  -r*heightFactorD u+z/(NegativeTwo.Inverse.q u*v)*
    NegativeTwo.Inverse.brace u r v

end PJCritical

end SquaresInCircles.Eight.SecondWord
end
end
end

section
/-!
## The original secondary contact on an outer circle

Both the source-coordinate and angle derivatives are derived from the
same original circle chart.  The norm identity retains the exact
contact speed and gives the inverse-angle radical without a new radius.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo.TargetContact

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio ratioD)

def B (b x : ℝ) : ℝ :=
  1/2-(arc b-1/2)*Real.cos x+(b+1/2)*Real.sin x
def v (b x : ℝ) : ℝ :=
  (arc b-1/2)*Real.sin x+(b+1/2)*Real.cos x
def k (b x : ℝ) : ℝ := ratio b*Real.cos x+Real.sin x
def Domain (b x : ℝ) : Prop :=
  b∈Icc 0 outerDiagonal ∧ x∈Icc 0 (7/10) ∧ B b x∈Icc 0 outerDiagonal

lemma B_zero (b : ℝ) : B b 0=1-arc b := by norm_num [B]; ring

lemma B_source_hasDerivAt {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    HasDerivAt (fun t => B t x) (k b x) b := by
  have hd := ((((ShortOuterOne.SameContact.arc_hasDerivAt (outer_domain hb)).sub_const
    (1/2)).mul_const (Real.cos x)).const_sub (1/2)).fun_add
      (((hasDerivAt_id' b).add_const (1/2)).mul_const (Real.sin x))
  exact hd.congr_deriv (by dsimp [k]; ring)

lemma B_angle_hasDerivAt (b x : ℝ) : HasDerivAt (B b) (v b x) x := by
  have hd := (((Real.hasDerivAt_cos x).const_mul (arc b-1/2)).const_sub
    (1/2)).fun_add ((Real.hasDerivAt_sin x).const_mul (b+1/2))
  exact hd.congr_deriv (by dsimp [v]; ring)

lemma v_angle_hasDerivAt (b x : ℝ) :
    HasDerivAt (v b) (1/2-B b x) x := by
  have hd := ((Real.hasDerivAt_sin x).const_mul (arc b-1/2)).fun_add
    ((Real.hasDerivAt_cos x).const_mul (b+1/2))
  exact hd.congr_deriv (by dsimp [B]; ring)

lemma k_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<k b x := by
  have hr := ShortOuterOne.SameContact.ratio_pos (outer_domain hb)
  have ht := positive_trig hx
  have hp := mul_pos hr (show 0<Real.cos x by linarith [ht.1])
  dsimp [k]
  linarith [ht.2.2.1]

lemma v_positive {b x : ℝ} (hb : b∈Icc 0 outerDiagonal)
    (hx : x∈Icc 0 (7/10)) : 0<v b x := by
  have hu := UW_bounds hb
  have ht := positive_trig hx
  have hsin := mul_nonneg (show 0≤arc b-1/2 by dsimp [U] at hu; linarith [hu.1])
    ht.2.2.1
  have hcos := mul_pos (show 0<b+1/2 by linarith [hb.1])
    (show 0<Real.cos x by linarith [ht.1])
  dsimp [v]
  linarith

lemma B_source_monotone {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    MonotoneOn (fun b => B b x) (Icc 0 outerDiagonal) :=
  monoOn_of_hasDeriv_nonneg
    (fun _ hb => (B_source_hasDerivAt hb x).continuousAt.continuousWithinAt)
    (fun _ hb => B_source_hasDerivAt (Ioo_subset_Icc_self hb) x)
    (fun _ hb => (k_positive (Ioo_subset_Icc_self hb) hx).le)

lemma B_angle_monotone {b : ℝ} (hb : b∈Icc 0 outerDiagonal) :
    MonotoneOn (B b) (Icc 0 (7/10)) :=
  monoOn_of_hasDeriv_nonneg
    (fun x _ => (B_angle_hasDerivAt b x).continuousAt.continuousWithinAt)
    (fun x _ => B_angle_hasDerivAt b x)
    (fun _ hx => (v_positive hb (Ioo_subset_Icc_self hx)).le)

lemma norm_identity {b : ℝ} (hb : b∈Icc 0 outerDiagonal) (x : ℝ) :
    (B b x-1/2)^2+(v b x)^2=Inverse.q (U b) := by
  have hc := UW_circle (outer_domain hb)
  have ht := Real.sin_sq_add_cos_sq x
  dsimp [B,v,Inverse.q,U,W] at *
  linear_combination hc+((arc b-1/2)^2+(b+1/2)^2)*ht

end SquaresInCircles.Eight.SecondWord.NegativeTwo.TargetContact
end
end
end

section
/-!
## The original negative outer quarter edge and its four weak projections

The cost is the literal role-two source label minus the literal role-three
target label.  Each cut below is an algebraic rearrangement of one of
the original weak axes at the original common radius.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.NegativeTwo

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc)

def value (b B φ : ℝ) : ℝ := φ-P b+T B
def upperTarget (a b x : ℝ) : ℝ :=
  1/2-(a-1/2)*Real.cos x-(b-1/2)*Real.sin x
def lowerSource (A B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x+(A+1/2)*Real.sin x
def upperSource (A B x : ℝ) : ℝ :=
  1/2+(1/2-B)*Real.cos x-(A-1/2)*Real.sin x

lemma source_mem {a b : ℝ} (hs : OuterState a b) : b∈Icc 0 outerDiagonal :=
  ⟨hs.1,(CommonQuarter.outer_bounds hs).2.2.2.1⟩

lemma primary_mem {a b : ℝ} (hs : OuterState a b) : a∈Icc outerDiagonal outerAxial :=
  ⟨(CommonQuarter.outer_bounds hs).1,(CommonQuarter.outer_bounds hs).2.1⟩

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 2 .outer .outer false false a b A B φ=value b B φ := by
  unfold value
  rw [show P b=PLabel.eval a b from PLabel.outer_actual hs,
    show T B=TLabel.eval A B from TLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,PLabel,TLabel,RoleLabel.eval]
  ring

lemma upper_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2+x)=(1+Real.cos x+Real.sin x)/2 := by
  rw [quarter_width (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩),
    abs_of_nonneg (positive_trig hx).2.2.1]

lemma lower_width {x : ℝ} (hx : x∈Icc 0 (7/10)) :
    pairWidth (Real.pi/2-x)=(1+Real.cos x+Real.sin x)/2 := by
  have hh := quarter_width (x := -x)
    (abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  simpa only [sub_eq_add_neg,Real.cos_neg,Real.sin_neg,abs_neg,
    abs_of_nonneg (positive_trig hx).2.2.1] using hh

lemma lower_target_cut {a b A B x : ℝ} (hs : OuterState a b)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2-x)) :
    TargetContact.B b x≤B := by
  have hw := lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [TargetContact.B]
  rw [(ShortOuterOne.SameContact.actual_arc hs).1]
  linarith

lemma upper_target_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 2 a b A B (-1) (-1) (Real.pi/2+x)) :
    upperTarget a b x≤B := by
  have hw := upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperTarget]
  linarith

lemma lower_source_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2-x)) :
    lowerSource A B x≤a := by
  have hw := lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  dsimp [lowerSource]
  linarith

lemma upper_source_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 3 a b A B (-1) (-1) (Real.pi/2+x)) :
    upperSource A B x≤a := by
  have hw := upper_width hx
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hw] at hm
  dsimp [upperSource]
  linarith

end SquaresInCircles.Eight.SecondWord.NegativeTwo
end
end
end

section
@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord

def TPrimaryLabel : RoleLabel := TLabel.primary

namespace NegativeThree

open CommonQuarter CorePairGeometry Arithmetic

def value (b B φ : ℝ) : ℝ := φ-T b+K B

lemma cost_identity {a b A B φ : ℝ} (hs : OuterState a b) (ht : OuterState A B) :
    SecondWord.cost 3 .outer .outer false false a b A B φ=value b B φ := by
  unfold value
  rw [show T b=TLabel.eval a b from TLabel.outer_actual hs,
    show K B=KLabel.eval A B from KLabel.outer_actual ht]
  norm_num [SecondWord.cost,label,QuarterWordGeometry.wrongValue,next,
    WordProblems.secondCoefficients,WordProblems.radialIndex,WordProblems.signIndex,
    WordProblems.sign,TLabel,KLabel,RoleLabel.eval]
  ring

lemma lower_first_cut {a b A B x : ℝ} (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x)) :
    b≤(A-1/2)*Real.cos x+(B-1/2)*Real.sin x-1/2 := by
  have hw := NegativeTwo.lower_width hx
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hw] at hm
  linarith

lemma upper_first_implies_lower {a b A B x : ℝ} (ht : OuterState A B)
    (hx : x∈Icc 0 (7/10))
    (hm : 0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2+x)) :
    0≤Eight.forwardMargin 0 a b A B (-1) (-1) (Real.pi/2-x) := by
  have hu := NegativeTwo.upper_width hx
  have hl := NegativeTwo.lower_width hx
  have hprod := mul_nonneg ht.1 (positive_trig hx).2.2.1
  norm_num [Eight.forwardMargin,Real.sin_add,Real.cos_add,hu] at hm
  norm_num [Eight.forwardMargin,Real.sin_sub,Real.cos_sub,hl]
  nlinarith

lemma primary_actual {a b : ℝ} (hs : OuterState a b) : TPrimaryLabel.outer a= -T b :=
  TLabel.primary_actual hs

end NegativeThree

end SquaresInCircles.Eight.SecondWord
end
end
end
