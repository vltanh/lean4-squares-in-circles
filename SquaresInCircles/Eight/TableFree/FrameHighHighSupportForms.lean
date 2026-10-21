module

public import SquaresInCircles.Eight.TableFree.FrameHighHighSupports
public import SquaresInCircles.Eight.TableFree.FrameHighHighFixedScalars
public import SquaresInCircles.Eight.TableFree.FrameHighHighCircleScalars
public import SquaresInCircles.Eight.TableFree.FrameHighHighVaryingScalars

/-!
# Exact transfer of the high/high support forms

The fixed supports and the moving negative-source support are connected
to the literal retained margin before the scalar interval conclusions
are used.  Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighHighSupportForms
open FramePair FrameDiagonalArc FrameDiagonalLabels FrameDiagonalTransport
open FrameDiagonalSupport

theorem circle_source (i : Bool) (l : ℝ) {b : ℝ} (hb : b∈arc false) :
    FrameHighHighFixedCalculus.sourceValue true i l≤source false i l b := by
  rw [FrameHighHighFixedCalculus.sourceValue_eq]
  exact source_circle_lower false i l hb

theorem axial_source {l b : ℝ} (hb : b∈arc false)
    (hl : l∈Icc (17/50:ℝ) (43/100)) :
    FrameHighHighFixedCalculus.sourceValue false true l≤source false true l b := by
  rw [FrameHighHighFixedCalculus.sourceValue_eq]
  exact FrameMidHighSupports.positive_high_source hb hl

theorem fixed_support (circle i j cut : Bool) {l b B x : ℝ}
    (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2))
    (hm : 0≤central i j (A b) b (A B) B x)
    (hs : FrameHighHighFixedCalculus.sourceValue circle i l≤source false i l b)
    (ht : target false j l x (FrameHighHighFixedCalculus.endB cut)≤target false j l x B) :
    FrameHighHighFixedCalculus.F circle i j cut l x≤cost false false i j b B x := by
  have h := support hl hm hs ht
  rwa [FrameHighHighFixedCalculus.support_formula circle i j cut l hx] at h

theorem fixed_endpoints (circle i j : Bool) {l b B x : ℝ}
    (hl : 0≤l) (hx : x∈Icc 0 (Real.pi/2))
    (hm : 0≤central i j (A b) b (A B) B x)
    (hs : FrameHighHighFixedCalculus.sourceValue circle i l≤source false i l b)
    (ht : min (target false j l x 0) (target false j l x b1)≤target false j l x B)
    (hval : ∀ cut : Bool, (9099/10000:ℝ)<FrameHighHighFixedCalculus.F circle i j cut l x) :
    (9099/10000:ℝ)<cost false false i j b B x := by
  by_cases he : target false j l x 0≤target false j l x b1
  · rw [min_eq_left he] at ht
    exact (hval false).trans_le (fixed_support circle i j false hl hx hm hs ht)
  · rw [min_eq_right (lt_of_not_ge he).le] at ht
    exact (hval true).trans_le (fixed_support circle i j true hl hx hm hs ht)

theorem varying_form {x : ℝ} (hx : x∈Icc 0 (Real.pi/2)) :
    base false false false false (FrameHighHighVaryingCalculus.lam x) x+
      sourceCircle false false (FrameHighHighVaryingCalculus.lam x)+
      target false false (FrameHighHighVaryingCalculus.lam x) x b1=
        FrameHighHighVaryingCalculus.F x := by
  have hn : Real.sqrt
      ((sourceU false false (FrameHighHighVaryingCalculus.lam x))^2+
       (sourceV false false (FrameHighHighVaryingCalculus.lam x))^2)=
        FrameHighHighVaryingCalculus.N x := by
    rw [FrameHighHighVaryingCalculus.N_literal]
    congr 1
    dsimp [sourceU,sourceV,primary,transverse,sign]
    ring
  rw [fixed_target_first false false false false (FrameHighHighVaryingCalculus.lam x)
    b1 (sourceCircle false false (FrameHighHighVaryingCalculus.lam x)) hx]
  rw [sourceCircle,hn,A_b1]
  dsimp [FrameHighHighVaryingCalculus.F,FrameHighHighVaryingCalculus.X,
    FrameHighHighVaryingCalculus.Y,constant,marker,H,sourceU,primary,sign]
  ring

end SquaresInCircles.Eight.TableFree.FrameHighHighSupportForms
