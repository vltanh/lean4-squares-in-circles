module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Polynomial
public import SquaresInCircles.Eight.TableFree.GlobalGANegativeABT3Coefficients

/-!
# Exact radical forms of the fourteen reference endpoints

Uncompiled Sections 2 and 6--7. The secant cancellation is exact
before any Taylor bound. The native polynomial variable is always
the actual endpoint parameter minus its stated left endpoint.
-/

@[expose] public section
noncomputable section
open Set Polynomial
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def nonradical (f : Certificate.Family) (z : ℝ) : ℝ :=
  if f=.low then 2*Explicit.k f z+3*Explicit.l f z+5/2-diagonal+
    Explicit.m f z*(1+(3/2-diagonal)*Real.cos z+
      (1/2+PositiveTD.eta*(1-diagonal)-PositiveTD.sigma)*Real.sin z)
  else 2*Explicit.k f z+3*Explicit.l f z+3+
    Explicit.m f z*(1+2*Real.cos z+(1/2+3*PositiveTD.eta/2-PositiveTD.sigma)*Real.sin z)

theorem reduced_identity (f : Certificate.Family) (atG : Bool) {s z : ℝ}
    (hz : z∈Icc (Certificate.left f:ℝ) (Certificate.right f:ℝ))
    (hs : s∈Icc 0 frameCap) :
    reducedBaseline f atG s z=nonradical f z+secant (Explicit.l f z) s-Explicit.l f z+
      (13/12)*Explicit.l f z*Real.tan s-
      R*normSum f (norms atG (Explicit.k f z) (Explicit.l f z) (Explicit.m f z) s z) := by
  have hwidth := NegativeAPositiveTD.secant_width_identity (l:=Explicit.l f z) hs
  have hzf := Explicit.frame_domain f hz
  cases f
  · have hc := (Explicit.low_rotation hz).1.le
    cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,NegativeAPositiveTD.normSum,norms,
        lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,↓reduceIte,
        Matrix.cons_val_zero,Matrix.cons_val_succ,fullSupport_pair,clippedSupport,
        if_pos hc,diagonalSupport,edgeWidth_positive_formula hzf,Explicit.c,PositiveBT3.tilted]
      <;> linear_combination hwidth
  · cases atG <;>
      simp only [reducedBaseline,baseline,nonradical,normSum,NegativeAPositiveTD.normSum,norms,
        lambdaG,lambdaB,NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,↓reduceIte,
        Matrix.cons_val_zero,Matrix.cons_val_succ,fullSupport_pair,
        pairNorm_symm (PositiveBT3.tilted (Explicit.m .high z) z) 1,
        edgeWidth_positive_formula hzf,Explicit.c,PositiveBT3.tilted]
      <;> linear_combination hwidth

namespace Analytic
open Certificate (Curve)

def Domain (e : Curve) (z : ℝ) : Prop := z∈Icc (Certificate.start e:ℝ) (Certificate.right (Certificate.family e):ℝ)
def angle : Curve→ℝ→ℝ
  | .lowGA,z | .highGA,z | .highAB,z => z
  | .gaH,_ | .gaB,_ => 1/4
  | .abG,_ | .abH,_ => 19/50
  | _,_ => 0
def negativeAngle (e : Curve) (z : ℝ) : ℝ :=
  match e with
  | .lowSH | .lowSG => frameCap
  | .gaH | .gaB | .abG | .abH => z-angle e z
  | _ => z
def cost (e : Curve) (z : ℝ) : ℝ :=
  match Certificate.selected e with
  | none => 0
  | some j => if j=0 then 1 else Explicit.l (Certificate.family e) z
def extra (e : Curve) (z : ℝ) : ℝ :=
  if e=.lowM then Explicit.k .low z*(phi (frameCap-z)-1)+Explicit.l .low z*(Real.cos frameCap-1)
  else cost e z*(Real.cos (negativeAngle e z)-1)-
    if Certificate.separated e then (109/160)*(frameCap-z) else 0
def p (e : Curve) (z : ℝ) : Fin 4→ℝ :=
  ![Explicit.k (Certificate.family e) z,Explicit.k (Certificate.family e) z,
    Explicit.m (Certificate.family e) z,1]
def q (e : Curve) (z : ℝ) : Fin 4→ℝ :=
  ![1,lambdaG (Certificate.atG e) (Explicit.l (Certificate.family e) z) (angle e z),
    lambdaB (Certificate.atG e) (Explicit.l (Certificate.family e) z) (angle e z),
    Explicit.c (Certificate.family e) z]
def norm (e : Curve) (z : ℝ) (i : Fin 4) : ℝ :=
  pairNorm (p e z i) (q e z i) (if Certificate.selected e=some i then -negativeAngle e z else 0)
def scale (e : Curve) (z : ℝ) : ℝ := if Certificate.scaled e then Real.cos (angle e z) else 1
def scaledNorm (e : Curve) (z : ℝ) (i : Fin 4) : ℝ := scale e z*norm e z i
def nonradical (e : Curve) (z : ℝ) : ℝ :=
  if Certificate.scaled e then Real.cos (angle e z)*(NegativeABT3.nonradical (Certificate.family e) z-
      Explicit.l (Certificate.family e) z)+Explicit.l (Certificate.family e) z+
      (13/12)*Explicit.l (Certificate.family e) z*Real.sin (angle e z)+Real.cos (angle e z)*extra e z
  else NegativeABT3.nonradical (Certificate.family e) z+extra e z
def charge (e : Curve) (z : ℝ) : ℝ :=
  match e with
  | .lowM => mixedG (Explicit.k .low z) (Explicit.l .low z) z
  | .lowSH => -(109/160)*(frameCap-z)+V R (Explicit.k .low z) 1 frameCap
  | .lowSG => -(109/160)*(frameCap-z)+V R (Explicit.k .low z) (Explicit.l .low z) frameCap
  | .lowH | .highH | .gaH | .abH => V R (Explicit.k (Certificate.family e) z) 1 (negativeAngle e z)
  | .highG | .abG => V R (Explicit.k .high z) (Explicit.l .high z) (negativeAngle e z)
  | .highB | .gaB => V R (Explicit.m .high z) (Explicit.l .high z) (negativeAngle e z)
  | _ => 0
def curve (e : Curve) (z : ℝ) : ℝ :=
  reducedBaseline (Certificate.family e) (Certificate.atG e) (angle e z) z+charge e z

theorem native_domain (e : Curve) {z : ℝ} (hz : Domain e z) :
    z-(Certificate.start e:ℝ)∈Icc 0 (Certificate.length e:ℝ) := by
  dsimp [Domain,Certificate.length] at *
  push_cast
  exact ⟨by linarith [hz.1],by linarith [hz.2]⟩

theorem domains (e : Curve) {z : ℝ} (hz : Domain e z) :
    z∈Icc (Certificate.left (Certificate.family e):ℝ) (Certificate.right (Certificate.family e):ℝ) ∧
    angle e z∈Icc 0 frameCap ∧ negativeAngle e z∈Icc 0 frameCap ∧ frameCap-z∈Icc 0 frameCap := by
  cases e <;> norm_num [Domain,Certificate.start,Certificate.family,Certificate.left,Certificate.right,
    Certificate.split,angle,negativeAngle,frameCap] at hz ⊢ <;>
    repeat' constructor <;> linarith [hz.1,hz.2]

@[simp] theorem native_z (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.z e)=z := by
  simp [Certificate.z]
@[simp] theorem native_k (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.kAt e)=Explicit.k (Certificate.family e) z := by
  simp [Certificate.kAt,aeval_comp]
@[simp] theorem native_l (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.lAt e)=Explicit.l (Certificate.family e) z := by
  simp [Certificate.lAt,aeval_comp]
@[simp] theorem native_m (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.mAt e)=Explicit.m (Certificate.family e) z := by
  simp [Certificate.mAt,aeval_comp]
@[simp] theorem native_angle (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.angle e)=angle e z := by
  cases e <;> simp [Certificate.angle,angle]
@[simp] theorem native_negativeAngle (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.negativeAngle e)=negativeAngle e z := by
  cases e <;> simp [Certificate.negativeAngle,negativeAngle,PositiveTD.Certificate.h,frameCap]
@[simp] theorem native_cost (e : Curve) (z : ℝ) :
    aeval (z-(Certificate.start e:ℝ)) (Certificate.cost e)=cost e z := by
  cases e <;> simp [Certificate.cost,Certificate.selected,cost]

theorem scale_positive (e : Curve) {z : ℝ} (hz : Domain e z) : 0<scale e z := by
  have hc : 0<Real.cos (angle e z) := by linarith [(transport_trig (domains e hz).2.1).1]
  dsimp [scale]
  split_ifs <;> positivity

theorem curve_identity (e : Curve) {z : ℝ} (hz : Domain e z) :
    scale e z*curve e z=nonradical e z-R*normSum (Certificate.family e) (scaledNorm e z) := by
  have hd := domains e hz
  have he := reduced_identity (Certificate.family e) (Certificate.atG e) hd.1 hd.2.1
  have hc : Real.cos (angle e z)≠0 := (show 0<Real.cos (angle e z) by
    linarith [(transport_trig hd.2.1).1]).ne'
  unfold curve
  rw [he]
  cases e <;>
    simp [scale,scaledNorm,norm,nonradical,extra,charge,angle,negativeAngle,p,q,cost,
      Certificate.scaled,Certificate.family,Certificate.atG,Certificate.selected,Certificate.separated,
      normSum,NegativeAPositiveTD.normSum,norms,lambdaG,lambdaB,secant,
      NegativeAPositiveTD.lambdaG,NegativeAPositiveTD.lambdaB,NegativeAPositiveTD.secant,
      mixedG,NegativeAPositiveTD.mixedG,V,Real.tan_eq_sin_div_cos,Explicit.c] at hc ⊢ <;>
    field_simp [hc] <;> ring

end Analytic
end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeABT3
