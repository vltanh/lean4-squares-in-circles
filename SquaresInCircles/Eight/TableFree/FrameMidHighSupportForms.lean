module

public import SquaresInCircles.Eight.TableFree.FrameHighMidSupports
public import SquaresInCircles.Eight.TableFree.FrameMidHighTargetScalars
public import SquaresInCircles.Eight.TableFree.FrameMidHighFixedScalars

/-!
# Literal scalar forms of the middle/high supports

The old and diagonal circle norms agree by an exact orthogonal coordinate
identity.  Their positive square roots retain the actual common radius.
The scalar expressions below are therefore precisely the signed support
of the original weak central witness.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameMidHighSupportForms
open FramePair FramePairCalculus FrameDiagonalArc FrameDiagonalLabels
open FrameDiagonalSupport

theorem middle_target_norm {l x : ℝ} (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2)) :
    R*Real.sqrt ((targetU true false l x)^2+(targetV true false l x)^2)=
      FrameCircleArc.R*FrameMidHighNormMonotonicity.NF (2*l) x := by
  have hN := FrameMidHighNormMonotonicity.NF_sq (by linarith : 0≤2*l) hx
  have hNpos := FrameMidHighNormMonotonicity.NF_pos (by linarith : 0≤2*l) hx
  have he : (FrameMidHighNormMonotonicity.NF (2*l) x)^2=
      2*((targetU true false l x)^2+(targetV true false l x)^2) := by
    rw [hN]
    dsimp [targetU,targetV,primary,transverse,sign,k,q,FrameMidArc.p,FrameMidArc.q]
    linear_combination -4*l^2*(Real.sin_sq_add_cos_sq x)
  have hsq : (R*Real.sqrt ((targetU true false l x)^2+(targetV true false l x)^2))^2=
      (FrameCircleArc.R*FrameMidHighNormMonotonicity.NF (2*l) x)^2 := by
    rw [mul_pow,mul_pow,R_sq,FrameCircleArc.R_sq,Real.sq_sqrt (by positivity),he]
    ring
  have hleft := mul_nonneg R_pos.le
    (Real.sqrt_nonneg ((targetU true false l x)^2+(targetV true false l x)^2))
  have hright := mul_nonneg FrameCircleArc.R_pos.le hNpos.le
  nlinarith

theorem positive_constant {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    base false true true false (43/100) x+source false true (43/100) 0+
      targetCircle true false (43/100) x=FrameMidHighConstantScalars.P x := by
  have hn := middle_target_norm (l := (43/100:ℝ)) (by norm_num) hx
  rw [base_first false true true false (43/100) hx,targetCircle,hn]
  dsimp [source,linear,sourceU,sourceV,targetU,primary,transverse,constant,
    sign,FrameMidHighConstantScalars.P,FrameMidHighNormMonotonicity.F]
  rw [A_zero]
  norm_num only
  ring

theorem negative_constant {l x : ℝ} (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2)) :
    base false true false false l x+sourceCircle false false l+
      targetCircle true false l x=FrameMidHighConstantScalars.N l x := by
  have hn := middle_target_norm hl hx
  have hs : Real.sqrt ((sourceU false false l)^2+(sourceV false false l)^2)=
      FrameMidHighConstantScalars.sourceNorm l := by
    dsimp [sourceU,sourceV,primary,transverse,sign,FrameMidHighConstantScalars.sourceNorm]
    congr 1
    ring
  rw [base_first false true false false l hx,targetCircle,hn,sourceCircle,hs]
  dsimp [sourceU,targetU,primary,transverse,constant,sign,FrameDiagonalArc.a0,
    FrameMidHighConstantScalars.N,FrameMidHighConstantScalars.negativeK,
    FrameMidHighNormMonotonicity.F]
  ring

theorem varying_source_norm (i : Bool) (x : ℝ) :
    Real.sqrt ((sourceU false i (FrameMidHighVaryingCalculus.lam i x))^2+
      (sourceV false i (FrameMidHighVaryingCalculus.lam i x))^2)=
        FrameMidHighVaryingCalculus.N i x := by
  dsimp [FrameMidHighVaryingCalculus.N]
  congr 1
  cases i <;> dsimp [sourceU,sourceV,primary,transverse,sign] <;> ring

theorem varying_form (i : Bool) {x : ℝ}
    (hx : x∈FrameMidHighVaryingCalculus.domain i) :
    base false true i false (FrameMidHighVaryingCalculus.lam i x) x+
      sourceCircle false i (FrameMidHighVaryingCalculus.lam i x)+
      target true false (FrameMidHighVaryingCalculus.lam i x) x b2=
        FrameMidHighVaryingCalculus.F i x := by
  rw [fixed_target_first false true i false (FrameMidHighVaryingCalculus.lam i x)
    b2 (sourceCircle false i (FrameMidHighVaryingCalculus.lam i x))
    (FrameMidHighVaryingCalculus.domain_quadrant hx)]
  rw [sourceCircle,varying_source_norm,A_b2]
  dsimp [FrameMidHighVaryingCalculus.F,FrameMidHighVaryingCalculus.X,
    FrameMidHighVaryingCalculus.Y,M2,constant,marker,sourceU,primary,sign,FrameDiagonalArc.a0]
  cases i <;> dsimp [sign] <;> ring

theorem high_target_norm (j : Bool) {l : ℝ}
    (hl : FrameMidHighTargetCalculus.Allowed l) (x : ℝ) :
    Real.sqrt ((targetU false j l x)^2+(targetV false j l x)^2)=
      FrameMidHighTargetCalculus.N j l x := by
  rw [FrameMidHighTargetCalculus.N_literal hl x]
  congr 1
  cases j <;> dsimp [targetU,targetV,primary,transverse,sign] <;> ring

theorem high_target_first (i j : Bool) {l x : ℝ}
    (hl : FrameMidHighTargetCalculus.Allowed l) (hx : x∈Icc 0 (Real.pi/2)) :
    base true false i j l x+source true i l b1+targetCircle false j l x=
      FrameMidHighTargetCalculus.F i j l x := by
  rw [base_first true false i j l hx,targetCircle,high_target_norm j hl x]
  dsimp [source,linear]
  rw [A_b1]
  dsimp [sourceU,sourceV,targetU,primary,transverse,constant,FrameDiagonalArc.a0,
    FrameMidHighTargetCalculus.F,FrameMidHighTargetCalculus.K]
  ring

theorem high_target_second (i j : Bool) {l x : ℝ}
    (hl : FrameMidHighTargetCalculus.Allowed l) (hx : x∈Icc (Real.pi/2) Real.pi) :
    base true false i j l x+source true i l b1+targetCircle false j l x=
      FrameMidHighTargetCalculus.after i j l x := by
  rw [base_second true false i j l hx,targetCircle,high_target_norm j hl x]
  dsimp [source,linear]
  rw [A_b1]
  dsimp [sourceU,sourceV,targetU,primary,transverse,constant,FrameDiagonalArc.a0,
    FrameMidHighTargetCalculus.after,FrameMidHighTargetCalculus.K]
  ring

end SquaresInCircles.Eight.TableFree.FrameMidHighSupportForms
