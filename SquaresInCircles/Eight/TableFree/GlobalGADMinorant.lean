module

public import SquaresInCircles.Eight.TableFree.GlobalGADMinorantCalculus
public import SquaresInCircles.Eight.TableFree.GlobalGAOneAngleFunctions

/-!
# The variable-coefficient D minorant at the unchanged original anchor

Uncompiled source.  The baseline is the exact diagonal/full-circle support
at `(1,c)`.  The negative-angle comparison joins its two continuous support
formulas at equality.  The positive-angle comparison follows from an
explicit support point and the original circle inequality.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
open Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

def dSupportIncrement (c x : ℝ) : ℝ :=
  edgeWidth x-1-clippedSupport (Real.cos x) (c+Real.sin x)+clippedSupport 1 c

def actualDIncrement (c x : ℝ) (P : SignedPoint) : ℝ :=
  edgeWidth x-1-(Real.cos x*P.a+(c+Real.sin x)*P.y)+clippedSupport 1 c

@[simp] theorem dSupportIncrement_zero (c : ℝ) : dSupportIncrement c 0=0 := by
  simp [dSupportIncrement,edgeWidth,pairWidth]

theorem negative_diagonal_identity {k c s : ℝ} (hs : s∈Icc 0 frameCap) :
    negativeDiagonalResidual k c s=
      edgeWidth (-s)-1-diagonalSupport (Real.cos s) (c-Real.sin s)+
        clippedSupport 1 c-V R k 1 s := by
  rw [edgeWidth_negative_formula hs]
  dsimp [negativeDiagonalResidual,diagonalSupport]
  ring

theorem negative_full_identity {k c s : ℝ} (hs : s∈Icc 0 frameCap) :
    negativeFullResidual k c s=
      edgeWidth (-s)-1-fullSupport (Real.cos s) (c-Real.sin s)+
        clippedSupport 1 c-V R k 1 s := by
  have hnorm : Real.sqrt ((Real.cos s)^2+(c-Real.sin s)^2)=pairNorm c 1 (-s) := by
    simpa only [Real.cos_neg,Real.sin_neg,one_mul,← sub_eq_add_neg] using
      one_force_norm c 1 (-s)
  have hsupport : fullSupport (Real.cos s) (c-Real.sin s)=
      R*pairNorm c 1 (-s)-(Real.cos s+c-Real.sin s)/2 := by
    dsimp [fullSupport]
    rw [hnorm]
    ring
  rw [edgeWidth_negative_formula hs,hsupport]
  dsimp [negativeFullResidual]
  rw [fullSupport_pair c 1]
  dsimp [V]
  ring

theorem negative_switch_identity {k c s : ℝ} (hs : s∈Icc 0 frameCap) :
    (if Real.cos s-(c-Real.sin s)≤0 then negativeDiagonalResidual k c s
      else negativeFullResidual k c s)=dSupportIncrement c (-s)-V R k 1 s := by
  by_cases h : Real.cos s≤c-Real.sin s
  · have h' : Real.cos s-(c-Real.sin s)≤0 := sub_nonpos.mpr h
    simp only [h',↓reduceIte]
    rw [negative_diagonal_identity hs,dSupportIncrement]
    simp only [Real.cos_neg,Real.sin_neg,← sub_eq_add_neg,clippedSupport,h,↓reduceIte]
  · have h' : ¬Real.cos s-(c-Real.sin s)≤0 := by simpa only [sub_nonpos] using h
    simp only [h',↓reduceIte]
    rw [negative_full_identity hs,dSupportIncrement]
    simp only [Real.cos_neg,Real.sin_neg,← sub_eq_add_neg,clippedSupport,h,↓reduceIte]

theorem negative_D_support_minorant {k c s : ℝ}
    (hk : k∈Icc (1/2) (17/20)) (hc : c∈Icc k 2)
    (hs : s∈Icc 0 frameCap) : V R k 1 s≤dSupportIncrement c (-s) := by
  have hmono := monotone_continuous_switch
    (e:=fun x => Real.cos x-(c-Real.sin x))
    (by fun_prop) (negativeDiagonalResidual_monotone hk)
    (negativeFullResidual_monotone hk hc)
    (fun x hx he => by
      rw [negative_diagonal_identity hx,negative_full_identity hx]
      have heq : Real.cos x=c-Real.sin x := by linarith
      have hsum : 0≤Real.cos x+(c-Real.sin x) := by
        rw [← heq]
        linarith [(transport_trig hx).1]
      rw [full_at_diagonal heq hsum])
  have hz : (0:ℝ)∈Icc 0 frameCap := by norm_num [frameCap]
  have h := hmono hz hs hs.1
  simp only at h
  rw [negative_switch_identity hz,negative_switch_identity hs] at h
  simp only [neg_zero,dSupportIncrement_zero,V_zero,sub_zero] at h
  linarith

theorem positive_D_support_minorant {c s : ℝ}
    (hc : 1/2≤c) (hs : s∈Icc 0 frameCap) :
    -(GlobalGA.Secondary.diagonal-1/2)*s≤dSupportIncrement c s := by
  obtain ⟨hcos,_,hsin,_,_⟩ := transport_trig hs
  have hg : 0<c+Real.sin s := by linarith
  have hsum : 0≤Real.cos s+(c+Real.sin s) := by linarith
  let K := clippedPoint hsum hg
  have hbase := raw_clipped_support (f:=1) (g:=c) K.circle.le K.sorted
    (by linarith [K.corners_nonneg.1,K.corners_nonneg.2]) (by linarith)
  have hfirst := mul_nonneg
    (show 0≤K.a-1/2 by linarith [K.primary_lower,diagonal_bounds.1])
    (sub_nonneg.mpr (Real.cos_le_one s))
  have hsecond := mul_le_mul_of_nonneg_right K.tangent_upper hsin
  have hthird := mul_le_mul_of_nonneg_left (Real.sin_le hs.1)
    (show 0≤GlobalGA.Secondary.diagonal-1/2 by linarith [diagonal_bounds.1])
  rw [dSupportIncrement,edgeWidth_positive_formula hs,K.supports]
  nlinarith

theorem actual_D_increment_lower {q c x : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hcoef : 1/2≤c) (hx : |x|≤frameCap) :
    dSupportIncrement c x≤actualDIncrement c x P := by
  have ht := small_angle hx
  have hsum : 0≤Real.cos x+(c+Real.sin x) := by
    have hsin := (abs_le.mp ht.2).1
    norm_num [frameCap] at ht hsin
    linarith [ht.1]
  have hsupport := actual_clipped_support hs hy hc hq hsum
  dsimp [dSupportIncrement,actualDIncrement]
  linarith

/-- The fourth ordinary block has a linear positive part and the actual
ordinary H negative part.  Both arguments are the original signed error. -/
theorem actual_D_signed_minorant {q k c x : ℝ} {P : SignedPoint}
    (hs : P.Sorted) (hy : 0≤P.y) (hc : P.Contained q) (hq : q≤qCap)
    (hk : k∈Icc (1/2) (17/20)) (hcoef : c∈Icc k 2)
    (hx : |x|≤frameCap) :
    -(GlobalGA.Secondary.diagonal-1/2)*positivePart x+V R k 1 (negativePart x)≤actualDIncrement c x P := by
  have hc0 : 1/2≤c := hk.1.trans hcoef.1
  have hactual := actual_D_increment_lower hs hy hc hq hc0 hx
  by_cases hp : 0≤x
  · have h := positive_D_support_minorant hc0
      ⟨hp,by simpa only [abs_of_nonneg hp] using hx⟩
    simpa [positivePart,negativePart,max_eq_left hp,
      max_eq_right (by linarith : -x≤0)] using h.trans hactual
  · have hn : x≤0 := (lt_of_not_ge hp).le
    have hs' : -x∈Icc 0 frameCap :=
      ⟨neg_nonneg.mpr hn,(neg_le_abs x).trans hx⟩
    have h := negative_D_support_minorant hk hcoef hs'
    simp only [neg_neg] at h
    simpa [positivePart,negativePart,max_eq_right hn,
      max_eq_left (neg_nonneg.mpr hn)] using h.trans hactual

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveTD
