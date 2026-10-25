module

public import SquaresInCircles.Eight.Frames.High.HighFixedReferences

/-!
# Eight squares: the two circle-target high/high supports

One norm curvature argument applies to both actual multipliers on the
whole interval `[1.2,π/2]`.  The fixed source is the axial positive state
or the negative cut state.  Positive-square endpoint reserves prove the
two complete scalar bounds, including the narrow final tail cut.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.FrameHighHighCircleScalars
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels
open FrameHighHighFixedCalculus (gamma endA endB endpoint_A)
open FrameMidHighTargetCalculus (energyA energyB energyC)
open StationaryPrimitives (Interval)

def Allowed (l : ℝ) : Prop := l=39/100 ∨ l=73/200
def N (l x : ℝ) : ℝ := FrameMidHighTargetCalculus.N true l x
def N1 (l x : ℝ) : ℝ := FrameMidHighTargetCalculus.N1 true l x
def N2 (l x : ℝ) : ℝ := FrameMidHighTargetCalculus.N2 true l x
def K (i cut : Bool) (l : ℝ) : ℝ :=
  9/100+l+(1-sign i)*u*FrameDiagonalArc.a0+u+(sign i*u-l)*endA cut+sign i*(v-l)*endB cut
def F (i cut : Bool) (l x : ℝ) : ℝ :=
  K i cut l+x+(2*l-9/100)*Real.sin x-(9/100)*Real.cos x-R*N l x
def Fd (l x : ℝ) : ℝ := 1+(2*l-9/100)*Real.cos x+(9/100)*Real.sin x-R*N1 l x
def Fdd (l x : ℝ) : ℝ := -(2*l-9/100)*Real.sin x+(9/100)*Real.cos x-R*N2 l x

theorem allowed_bounds {l : ℝ} (hl : Allowed l) : 0<l ∧ (16/25:ℝ)≤2*l-9/100 := by
  rcases hl with rfl | rfl <;> norm_num

theorem coefficient_strict {l : ℝ} (hl : Allowed l) :
    (energyB true l)^2+(energyC true l)^2<(energyA l)^2 := by
  rcases hl with rfl | rfl <;> norm_num [energyA,energyB,energyC,sign,u,v]

theorem energy_pos {l : ℝ} (hl : Allowed l) (x : ℝ) :
    0<CircularNorm.energy (energyA l) (energyB true l) (energyC true l) x := by
  have hA : 0<energyA l := by dsimp [energyA,u,v]; positivity
  have hid : (energyB true l*Real.cos x+energyC true l*Real.sin x)^2+
      (energyB true l*Real.sin x-energyC true l*Real.cos x)^2=
        (energyB true l)^2+(energyC true l)^2 := by
    linear_combination ((energyB true l)^2+(energyC true l)^2)*(Real.sin_sq_add_cos_sq x)
  have hc := coefficient_strict hl
  dsimp [CircularNorm.energy]
  nlinarith [sq_nonneg (energyB true l*Real.sin x-energyC true l*Real.cos x)]

theorem N_pos {l : ℝ} (hl : Allowed l) (x : ℝ) : 0<N l x :=
  CircularNorm.norm_pos (energy_pos hl x)
theorem N_sq {l : ℝ} (hl : Allowed l) (x : ℝ) :
    (N l x)^2=energyA l+energyB true l*Real.cos x+energyC true l*Real.sin x :=
  CircularNorm.norm_sq (energy_pos hl x).le
theorem N_deriv {l : ℝ} (hl : Allowed l) (x : ℝ) : HasDerivAt (N l) (N1 l x) x :=
  CircularNorm.norm_hasDerivAt (energy_pos hl x)
theorem N1_deriv {l : ℝ} (hl : Allowed l) (x : ℝ) : HasDerivAt (N1 l) (N2 l x) x :=
  CircularNorm.d1_hasDerivAt (energy_pos hl x)
theorem norm_curvature {l : ℝ} (hl : Allowed l) (x : ℝ) : -N l x/4≤N2 l x :=
  CircularNorm.curvature_lower (energy_pos hl x) (coefficient_strict hl).le

theorem N_literal (l x : ℝ) : N l x=
    Real.sqrt ((u+l*(Real.sin x-Real.cos x))^2+(l*(Real.sin x+Real.cos x)-v)^2) := by
  dsimp [N,FrameMidHighTargetCalculus.N,CircularNorm.norm]
  congr 1
  dsimp [CircularNorm.energy,energyA,energyB,energyC,sign]
  linear_combination -2*l^2*(Real.sin_sq_add_cos_sq x)

theorem support_formula (i cut : Bool) (l : ℝ) {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    FrameDiagonalSupport.base false false i true l x+
      FrameDiagonalSupport.source false i l (endB cut)+
      FrameDiagonalSupport.targetCircle false true l x=F i cut l x := by
  rw [FrameDiagonalSupport.base_first false false i true l hx]
  have hnorm : (FrameDiagonalSupport.targetU false true l x)^2+
      (FrameDiagonalSupport.targetV false true l x)^2=
        (u+l*(Real.sin x-Real.cos x))^2+(l*(Real.sin x+Real.cos x)-v)^2 := by
    dsimp [FrameDiagonalSupport.targetU,FrameDiagonalSupport.targetV,primary,transverse,sign]
    ring
  rw [FrameDiagonalSupport.targetCircle,hnorm,← N_literal]
  dsimp [FrameDiagonalSupport.source,linear]
  rw [endpoint_A]
  dsimp [F,K,constant,FrameDiagonalSupport.sourceU,FrameDiagonalSupport.sourceV,
    FrameDiagonalSupport.targetU,primary,transverse,sign]
  ring

theorem F_deriv (i cut : Bool) {l : ℝ} (hl : Allowed l) (x : ℝ) :
    HasDerivAt (F i cut l) (Fd l x) x := by
  have h := ((((hasDerivAt_id x).const_add (K i cut l)).add
    ((Real.hasDerivAt_sin x).const_mul (2*l-9/100))).sub
    ((Real.hasDerivAt_cos x).const_mul (9/100))).sub ((N_deriv hl x).const_mul R)
  convert h using 1
  · funext y
    simp only [F,Pi.add_apply,Pi.sub_apply,id]
  · dsimp only [Fd]
    ring

theorem Fd_deriv {l : ℝ} (hl : Allowed l) (x : ℝ) : HasDerivAt (Fd l) (Fdd l x) x := by
  have h := ((((Real.hasDerivAt_cos x).const_mul (2*l-9/100)).const_add 1).add
    ((Real.hasDerivAt_sin x).const_mul (9/100))).sub ((N1_deriv hl x).const_mul R)
  convert h using 1
  · funext y
    simp only [Fd,Pi.add_apply,Pi.sub_apply]
  · dsimp only [Fdd]
    ring

theorem norm_monotone {l : ℝ} (hl : Allowed l) :
    MonotoneOn (N l) (Icc (6/5:ℝ) (Real.pi/2)) := by
  have href := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤6/5 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at href
  have hleft : 0≤(u+v)*Real.sin (6/5)-(v-u)*Real.cos (6/5) := by
    dsimp [u,v]
    nlinarith
  apply monoOn_of_hasDeriv_nonneg
  · exact fun x _ => (N_deriv hl x).continuousAt.continuousWithinAt
  · exact fun x _ => N_deriv hl x
  · intro x hx
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi/2)≤(6/5:ℝ)) hx.2.le hx.1.le
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤6/5)
      (by linarith [hx.2,Real.pi_pos] : x≤Real.pi) hx.1.le
    have hsp := mul_le_mul_of_nonneg_left hs (show 0≤u+v by norm_num [u,v])
    have hcp := mul_le_mul_of_nonneg_left hc (show 0≤v-u by norm_num [u,v])
    rw [N1,FrameMidHighTargetCalculus.N1_formula]
    simp only [sign,ite_true,one_mul]
    exact div_nonneg (mul_nonneg (allowed_bounds hl).1.le (by linarith)) (N_pos hl x).le

theorem norm_upper {l x : ℝ} (hl : Allowed l) (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    N l x<(1/2:ℝ) := by
  have hh := norm_monotone hl hx ⟨by linarith [FrameLowPair.pi_lower],le_rfl⟩ hx.2
  have hn := N_pos hl (Real.pi/2)
  have hs := N_sq hl (Real.pi/2)
  have hlast : N l (Real.pi/2)<(1/2:ℝ) := by
    rcases hl with rfl | rfl <;> norm_num [energyA,energyB,energyC,sign,u,v] at hs <;> nlinarith
  exact hh.trans_lt hlast

theorem curvature_negative {l x : ℝ} (hl : Allowed l) (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    Fdd l x<0 := by
  have href := FrameMidHighConstantScalars.trigonometric_reference
    (show (0:ℝ)≤6/5 by norm_num)
  norm_num [HighOrderTaylor.S11,Arithmetic.sin9,Arithmetic.sin7,
    SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8] at href
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi/2)≤(6/5:ℝ)) hx.2 hx.1
  have hsl : (93/100:ℝ)≤Real.sin x := by linarith
  have hp := mul_le_mul (allowed_bounds hl).2 hsl (by norm_num : (0:ℝ)≤93/100)
    (by linarith [(allowed_bounds hl).2] : 0≤2*l-9/100)
  have hn := norm_upper hl hx
  have hprod := mul_le_mul R_precise.2.le hn.le (N_pos hl x).le
    (by norm_num : (0:ℝ)≤139921407/50000000)
  have hcurv := mul_le_mul_of_nonneg_left (norm_curvature hl x) R_pos.le
  dsimp [Fdd]
  nlinarith [Real.cos_le_one x]

theorem concave (i cut : Bool) {l : ℝ} (hl : Allowed l) :
    ConcaveOn ℝ (Icc (6/5:ℝ) (Real.pi/2)) (F i cut l) :=
  concave_of_deriv2 (fun x _ => F_deriv i cut hl x) (fun x _ => Fd_deriv hl x)
    (fun x hx => (curvature_negative hl hx).le)

open FrameHighHighFixedReferences (a0Box endpointABox endpointBBox)
open FrameMidHighVaryingReferences (rBox piBox sinBox cosBox)

def constantBox (i cut : Bool) (l : ℝ) : Interval (K i cut l) :=
  (((((Interval.point (9/100+l)).add ((Interval.point ((1-sign i)*u)).mul a0Box)).add (Interval.point u)).add ((Interval.point (sign i*u-l)).mul (endpointABox cut))).add ((Interval.point (sign i*(v-l))).mul (endpointBBox cut)))
def baseBox (i cut : Bool) (l : ℝ) {x : ℝ}
    (X : Interval x) (S : Interval (Real.sin x)) (C : Interval (Real.cos x)) :
    Interval (K i cut l+x+(2*l-9/100)*Real.sin x-(9/100)*Real.cos x) :=
  ((((constantBox i cut l).add X).add ((Interval.point (2*l-9/100)).mul S)).sub ((Interval.point (9/100)).mul C))

theorem reference_lower (i cut : Bool) {l x : ℝ} (hl : Allowed l)
    (X : Interval x) (S : Interval (Real.sin x)) (C : Interval (Real.cos x))
    (hreserve : gamma<(baseBox i cut l X S C).lo)
    (hsquare : (FrameMidHighTargetReferences.energyBox true l S C).hi<
      (((baseBox i cut l X S C).lo-gamma)/(139921407/50000000:ℝ))^2) :
    gamma<F i cut l x := by
  let B := baseBox i cut l X S C
  let E := FrameMidHighTargetReferences.energyBox true l S C
  let cap : ℝ := (B.lo-gamma)/(139921407/50000000:ℝ)
  have hcap : 0<cap := div_pos (sub_pos.mpr hreserve) (by norm_num)
  have hn := N_pos hl x
  have hs : (N l x)^2<cap^2 := by rw [N_sq hl]; exact E.mem.2.trans_lt hsquare
  have hnorm : N l x<cap := by nlinarith
  have hprod : R*N l x<(139921407/50000000:ℝ)*cap :=
    (mul_lt_mul_of_pos_left hnorm R_pos).trans (mul_lt_mul_of_pos_right R_precise.2 hcap)
  have heq : (139921407/50000000:ℝ)*cap=B.lo-gamma := by dsimp [cap]; ring
  rw [heq] at hprod
  dsimp [F]
  linarith [B.mem.1]

private lemma r55_mpr_lo {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).lo=S.lo := by subst e; rfl
private lemma r55_mpr_hi {x y : ℝ} (e : x=y) (h : Interval x=Interval y) (S : Interval y) :
    (Eq.mpr h S).hi=S.hi := by subst e; rfl

private lemma r55_bBox_lo : FrameMidHighTargetReferences.bBox.lo=
    ((Interval.point (2/5:ℝ)).mul FrameMidHighTargetReferences.aBox).lo :=
  r55_mpr_lo b1_eq _ _
private lemma r55_bBox_hi : FrameMidHighTargetReferences.bBox.hi=
    ((Interval.point (2/5:ℝ)).mul FrameMidHighTargetReferences.aBox).hi :=
  r55_mpr_hi b1_eq _ _

private lemma r55_eA_lo_t : (endpointABox true).lo=FrameMidHighTargetReferences.aBox.lo := rfl
private lemma r55_eA_hi_t : (endpointABox true).hi=FrameMidHighTargetReferences.aBox.hi := rfl
private lemma r55_eA_lo_f : (endpointABox false).lo=a0Box.lo := rfl
private lemma r55_eA_hi_f : (endpointABox false).hi=a0Box.hi := rfl
private lemma r55_eB_lo_t : (endpointBBox true).lo=FrameMidHighTargetReferences.bBox.lo := rfl
private lemma r55_eB_hi_t : (endpointBBox true).hi=FrameMidHighTargetReferences.bBox.hi := rfl
private lemma r55_eB_lo_f : (endpointBBox false).lo=0 := rfl
private lemma r55_eB_hi_f : (endpointBBox false).hi=0 := rfl

local macro "hh_circle_arithmetic" : tactic => `(tactic|
  norm_num [baseBox,constantBox,FrameMidHighTargetReferences.energyBox,
    a0Box,r55_eA_lo_t,r55_eA_hi_t,r55_eA_lo_f,r55_eA_hi_f,r55_eB_lo_t,r55_eB_hi_t,
    r55_eB_lo_f,r55_eB_hi_f,FrameMidHighTargetReferences.aBox,
    r55_bBox_lo,r55_bBox_hi,rBox,piBox,sinBox,cosBox,
    gamma,energyA,energyB,energyC,sign,u,v,
    Interval.point,Interval.of_bounds,Interval.add,Interval.sub,Interval.neg,
    Interval.mul,Interval.div,Interval.inv,HighOrderTaylor.S11,Arithmetic.sin9,
    Arithmetic.sin7,SecondWord.ReferenceTrig.cos12,Arithmetic.cos10,Arithmetic.cos8])

theorem positive_left : gamma<F true false (39/100) (6/5) := by
  apply reference_lower true false (Or.inl rfl) (Interval.point (6/5))
    (sinBox (show (0:ℝ)≤6/5 by norm_num)) (cosBox (show (0:ℝ)≤6/5 by norm_num)) <;>
    hh_circle_arithmetic

theorem positive_right : gamma<F true false (39/100) (Real.pi/2) := by
  apply reference_lower true false (Or.inl rfl)
    (piBox.div (Interval.point 2) (by norm_num [Interval.point]))
    (Interval.of_bounds (a := 1) (b := 1) (by simp))
    (Interval.of_bounds (a := 0) (b := 0) (by simp)) <;>
    hh_circle_arithmetic

theorem opposite_left : gamma<F false true (73/200) (13/10) := by
  apply reference_lower false true (Or.inr rfl) (Interval.point (13/10))
    (sinBox (show (0:ℝ)≤13/10 by norm_num)) (cosBox (show (0:ℝ)≤13/10 by norm_num)) <;>
    hh_circle_arithmetic

theorem opposite_right : gamma<F false true (73/200) (15543/10000) := by
  apply reference_lower false true (Or.inr rfl) (Interval.point (15543/10000))
    (sinBox (show (0:ℝ)≤15543/10000 by norm_num))
    (cosBox (show (0:ℝ)≤15543/10000 by norm_num)) <;> hh_circle_arithmetic

theorem positive_lower {x : ℝ} (hx : x∈Icc (6/5:ℝ) (Real.pi/2)) :
    (9099/10000:ℝ)<F true false (39/100) x :=
  concave_gt_of_endpoints (concave true false (Or.inl rfl)) hx positive_left positive_right

theorem opposite_lower {x : ℝ} (hx : x∈Icc (13/10:ℝ) (15543/10000)) :
    (9099/10000:ℝ)<F false true (73/200) x := by
  have hc : ConcaveOn ℝ (Icc (13/10:ℝ) (15543/10000)) (F false true (73/200)) := by
    apply concave_of_deriv2 (fun x _ => F_deriv false true (Or.inr rfl) x)
      (fun x _ => Fd_deriv (Or.inr rfl) x)
    intro x hx
    exact (curvature_negative (Or.inr rfl)
      ⟨by linarith [hx.1],by linarith [hx.2,Arithmetic.pi_hand_enclosure.1]⟩).le
  exact concave_gt_of_endpoints hc hx opposite_left opposite_right

end SquaresInCircles.Eight.FrameHighHighCircleScalars
