module

public import SquaresInCircles.Eight.TableFree.FrameDiagonalSupport
public import SquaresInCircles.Eight.TableFree.SecondOuterMinimumCalculus
public import SquaresInCircles.Eight.TableFree.FrameHighHighVaryingReferences

/-!
# All fixed-target high/high scalar forms

The source is either its actual axial endpoint or its unconditional
circle support; the target is either intrinsic high-arc endpoint.
The endpoint-minimum principle and the amplitude derivative bound are
applied to these literal expressions.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighHighFixedCalculus
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels

def gamma : ℝ := 9099/10000
def endA (cut : Bool) : ℝ := if cut then a1 else FrameDiagonalArc.a0
def endB (cut : Bool) : ℝ := if cut then b1 else 0
def sourceU (i : Bool) (l : ℝ) : ℝ := sign i*u-l
def sourceV (i : Bool) (l : ℝ) : ℝ := sign i*(v-l)
def sourceBase (circle i : Bool) (l : ℝ) : ℝ :=
  if circle then -sourceU i l else sourceU i l*FrameDiagonalArc.a0
def sourceEnergy (circle i : Bool) (l : ℝ) : ℝ :=
  if circle then (sourceU i l)^2+(sourceV i l)^2 else 0
def sourceNorm (circle i : Bool) (l : ℝ) : ℝ := Real.sqrt (sourceEnergy circle i l)
def sourceValue (circle i : Bool) (l : ℝ) : ℝ := sourceBase circle i l-R*sourceNorm circle i l
def constantBase (circle i j cut : Bool) (l : ℝ) : ℝ :=
  9/100+l-sign i*u*FrameDiagonalArc.a0-sign j*H (endB cut)+sourceBase circle i l
def Cc (j cut : Bool) (l : ℝ) : ℝ := l*(1+endA cut+sign j*endB cut)-9/100
def Ss (j cut : Bool) (l : ℝ) : ℝ := l*(1-endA cut+sign j*endB cut)-9/100
def F (circle i j cut : Bool) (l x : ℝ) : ℝ :=
  x+constantBase circle i j cut l+Cc j cut l*Real.cos x+Ss j cut l*Real.sin x-
    R*sourceNorm circle i l
def Fd (j cut : Bool) (l x : ℝ) : ℝ :=
  1-Cc j cut l*Real.sin x+Ss j cut l*Real.cos x
def Fdd (j cut : Bool) (l x : ℝ) : ℝ :=
  -Cc j cut l*Real.cos x-Ss j cut l*Real.sin x
def Fddd (j cut : Bool) (l x : ℝ) : ℝ :=
  Cc j cut l*Real.sin x-Ss j cut l*Real.cos x

theorem endpoint_circle (cut : Bool) : (endA cut+1)^2+(endB cut)^2=2*Q0 := by
  cases cut
  · simp only [endA,endB,Bool.false_eq_true,↓reduceIte,FrameDiagonalArc.a0]
    rw [← R_sq]
    ring
  · exact first_circle

theorem endpoint_A (cut : Bool) : A (endB cut)=endA cut := by
  cases cut <;> simp [endA,endB]

theorem sourceNorm_nonneg (circle i : Bool) (l : ℝ) : 0≤ sourceNorm circle i l :=
  Real.sqrt_nonneg _
theorem sourceNorm_sq (circle i : Bool) (l : ℝ) :
    (sourceNorm circle i l)^2=sourceEnergy circle i l := by
  apply Real.sq_sqrt
  cases circle <;> dsimp [sourceEnergy] <;> positivity

theorem sourceValue_eq (circle i : Bool) (l : ℝ) :
    sourceValue circle i l=
      if circle then FrameDiagonalSupport.sourceCircle false i l
      else FrameDiagonalSupport.source false i l 0 := by
  cases circle <;> simp [sourceValue,sourceBase,sourceNorm,sourceEnergy,sourceU,sourceV,
    FrameDiagonalSupport.sourceCircle,FrameDiagonalSupport.source,
    FrameDiagonalSupport.sourceU,FrameDiagonalSupport.sourceV,
    primary,transverse,linear,A_zero] <;> ring

theorem support_formula (circle i j cut : Bool) (l : ℝ) {x : ℝ}
    (hx : x∈Icc 0 (Real.pi/2)) :
    FrameDiagonalSupport.base false false i j l x+sourceValue circle i l+
      FrameDiagonalSupport.target false j l x (endB cut)=F circle i j cut l x := by
  rw [FrameDiagonalSupport.fixed_target_first false false i j l (endB cut)
    (sourceValue circle i l) hx,endpoint_A]
  dsimp [F,constantBase,Cc,Ss,sourceValue,constant,marker]
  ring

theorem F_deriv (circle i j cut : Bool) (l x : ℝ) :
    HasDerivAt (F circle i j cut l) (Fd j cut l x) x := by
  have h := ((((hasDerivAt_id x).add_const (constantBase circle i j cut l)).add
    ((Real.hasDerivAt_cos x).const_mul (Cc j cut l))).add
    ((Real.hasDerivAt_sin x).const_mul (Ss j cut l))).sub_const
    (R*sourceNorm circle i l)
  convert h using 1
  · funext y
    simp only [F,id,Pi.add_apply]
  · dsimp only [Fd]
    ring

theorem Fd_deriv (j cut : Bool) (l x : ℝ) : HasDerivAt (Fd j cut l) (Fdd j cut l x) x := by
  have h := (((Real.hasDerivAt_sin x).const_mul (-Cc j cut l)).const_add 1).add
    ((Real.hasDerivAt_cos x).const_mul (Ss j cut l))
  convert h using 1
  · funext y
    simp only [Fd,Pi.add_apply]
    ring
  · dsimp only [Fdd]
    ring

theorem Fdd_deriv (j cut : Bool) (l x : ℝ) : HasDerivAt (Fdd j cut l) (Fddd j cut l x) x := by
  have h := ((Real.hasDerivAt_cos x).const_mul (-Cc j cut l)).sub
    ((Real.hasDerivAt_sin x).const_mul (Ss j cut l))
  convert h using 1
  · funext y
    simp only [Fdd,Pi.sub_apply]
  · dsimp only [Fddd]
    ring

theorem endpoint_minimum (circle i j cut : Bool) {l a b x : ℝ}
    (ha : 0≤a) (hb : b≤Real.pi/2) (hx : x∈Icc a b)
    (hC : 0≤Cc j cut l) (hS : Ss j cut l≤0) (hd : Fd j cut l b<0) :
    min (F circle i j cut l a) (F circle i j cut l b)≤F circle i j cut l x := by
  apply SecondWord.MinimumCalculus.endpoint_minimum hx
    (fun t _ => F_deriv circle i j cut l t)
    (fun t _ => Fd_deriv j cut l t) (fun t _ => Fdd_deriv j cut l t) _ hd
  intro t ht
  have hq := FrameLowPair.quadrant ⟨ha.trans ht.1,ht.2.trans hb⟩
  have h1 := mul_nonneg hC hq.1
  have h2 := mul_nonpos_of_nonpos_of_nonneg hS hq.2.2.1
  dsimp [Fddd]
  linarith

theorem amplitude_monotone (circle i j cut : Bool) {l : ℝ}
    (hamp : (Cc j cut l)^2+(Ss j cut l)^2<1) : Monotone (F circle i j cut l) := by
  apply monotone_of_hasDerivAt_nonneg (fun x => F_deriv circle i j cut l x)
  intro x
  have hh : Cc j cut l*Real.sin x+(-Ss j cut l)*Real.cos x<1 := by
    apply FrameCoreArc.projection_lt (by norm_num : (0:ℝ)<1)
    simpa only [neg_sq,one_pow] using hamp
  dsimp [Fd]
  linarith

theorem small_multiplier_amplitude (cut : Bool) :
    (Cc false cut (17/50))^2+(Ss false cut (17/50))^2<1 := by
  have hc := endpoint_circle cut
  have ha0 := a0_precise
  have ha1 := a1_precise
  cases cut
  · dsimp [Cc,Ss,endA,endB,sign] at *
    norm_num [Q0] at hc
    nlinarith
  · dsimp [Cc,Ss,endA,endB,sign] at *
    rw [b1_eq] at *
    norm_num [Q0] at hc
    nlinarith

end SquaresInCircles.Eight.TableFree.FrameHighHighFixedCalculus
