module

public import SquaresInCircles.Eight.TableFree.GlobalGANegativeFlatEGainReserve
public import SquaresInCircles.Eight.TableFree.GlobalGANegativePrimaryScalar

/-!
# The separate A and T gains at the lower E charge

Uncompiled transcription of Section 3 and equations (17)--(19) of the
negative-flat-E note. The A quadratic has its exact positive completed
square reserve; the TD gain uses the complete concave sine-cosine arc.
The E gains keep their own secant and exact flat-core primary 7/12.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
open Secondary Arithmetic

def commonJ (s : ℝ) : ℝ := ((847/800)*Real.sin s-a*(1-Real.cos s))/Real.cos s
def commonJd (s : ℝ) : ℝ := ((847/800)-a*Real.sin s)/Real.cos s^2
def primaryGain (d A B : ℝ) : ℝ :=
  lowL/Real.cos d*(edgeWidth d-B-A*Real.sin d)-lowL*(1-B)
def tdGain (d : ℝ) (T : SignedPoint) : ℝ :=
  lowC*(edgeWidth d-1-T.a*Real.sin d-T.y*(Real.cos d-1))
def eGain (d A : ℝ) : ℝ :=
  (edgeWidth d-A-(7/12)*Real.sin d)/Real.cos d-(1-A)

theorem commonJ_hasDerivAt {s : ℝ} (hs : s∈Icc 0 frameCap) :
    HasDerivAt commonJ (commonJd s) s := by
  have hc := (cosine_pos hs).ne'
  have hh := (((Real.hasDerivAt_sin s).const_mul (847/800:ℝ)).sub
    (((Real.hasDerivAt_cos s).const_sub 1).const_mul a)).div (Real.hasDerivAt_cos s) hc
  convert hh using 1
  · rfl
  · dsimp [commonJd]
    field_simp [hc]
    nlinarith only [congrArg (fun x : ℝ => (847/800)*x) (Real.sin_sq_add_cos_sq s)]

theorem commonJ_quadratic (x : ℝ) :
    (79/100)*x^2-(183/200)*x+847/800-79/100=
      (79/100)*(x-183/316)^2+481/126400 := by ring

theorem commonJd_lower {s : ℝ} (hs : s∈Icc 0 frameCap) : (79/100:ℝ)<commonJd s := by
  have hc := cosine_pos hs
  have hunit := Real.sin_sq_add_cos_sq s
  have hq := commonJ_quadratic (Real.sin s)
  dsimp [commonJd,a]
  apply (lt_div_iff₀ (sq_pos_of_pos hc)).2
  nlinarith [sq_nonneg (Real.sin s-183/316)]

theorem commonJ_lower {s : ℝ} (hs : s∈Icc 0 frameCap) : (79/100)*s≤commonJ s := by
  have hm : MonotoneOn (fun z => commonJ z-(79/100)*z) (Icc 0 frameCap) :=
    monoOn_of_hasDeriv_nonneg
      (fun z hz => ((commonJ_hasDerivAt hz).sub ((hasDerivAt_id z).const_mul (79/100:ℝ))).
        continuousAt.continuousWithinAt)
      (fun z hz => (commonJ_hasDerivAt (Ioo_subset_Icc_self hz)).
        sub ((hasDerivAt_id z).const_mul (79/100:ℝ)))
      (fun z hz => by linarith [commonJd_lower (Ioo_subset_Icc_self hz)])
  have hh := hm (by norm_num [frameCap] : (0:ℝ)∈Icc 0 frameCap) hs hs.1
  norm_num [commonJ] at hh
  linarith

theorem primaryGain_lower {s A B : ℝ} (hs : s∈Icc 0 frameCap)
    (hA : (447/800:ℝ)≤A) (hB : B≤283/200) :
    (charge+247/5000)*s≤primaryGain (-s) A B := by
  have hc := cosine_pos hs
  have ht := transport_trig hs
  have hAprod := mul_nonneg (sub_nonneg.mpr hA) ht.2.2.1
  have hBprod := mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr (Real.cos_le_one s))
  have he : primaryGain (-s) A B*Real.cos s=
      lowL*((A+1/2)*Real.sin s+(1/2-B)*(1-Real.cos s)) := by
    rw [primaryGain,edgeWidth_negative_formula hs]
    simp only [Real.sin_neg,Real.cos_neg]
    field_simp [hc.ne']
    ring
  have hJ : lowL*commonJ s≤primaryGain (-s) A B := by
    apply (mul_le_mul_right hc).mp
    rw [he]
    dsimp [commonJ,a]
    field_simp [hc.ne']
    dsimp [lowL] at *
    nlinarith
  have hl := mul_le_mul_of_nonneg_left (commonJ_lower hs) (by norm_num [lowL] : 0≤lowL)
  dsimp [charge,lowL] at *
  linarith

theorem td_arc_charge {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (charge+37/350)*s≤lowC*(Real.sin s+Real.cos s-1) := by
  let f : ℝ→ℝ := fun z => lowC*(Real.sin z+Real.cos z-1)-(charge+37/350)*z
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) f := by
    apply concave_of_deriv2
      (f':=fun z => lowC*(Real.cos z-Real.sin z)-(charge+37/350))
      (f'':=fun z => -lowC*(Real.sin z+Real.cos z))
    · intro z _
      convert ((((Real.hasDerivAt_sin z).add (Real.hasDerivAt_cos z)).sub_const 1).
        const_mul lowC).sub ((hasDerivAt_id z).const_mul (charge+37/350))
        using 1 <;> dsimp [f] <;> ring
    · intro z _
      convert (((Real.hasDerivAt_cos z).sub (Real.hasDerivAt_sin z)).const_mul lowC).
        sub_const (charge+37/350) using 1 <;> ring
    · intro z hz
      have ht := transport_trig hz
      dsimp [lowC]
      linarith [ht.1,ht.2.2.1]
  have hright : 0≤f frameCap := by
    have ht := CommonQuarter.cap_trig
    dsimp [f,lowC,charge,frameCap]
    linarith [ht.1,ht.2.2.1]
  have hleft : f 0=0 := by norm_num [f]
  have hmin := hconc.min_le_of_mem_Icc (by norm_num [frameCap]) (by norm_num [frameCap]) hs
  have hh : 0≤min (f 0) (f frameCap) := le_min (by rw [hleft]) hright
  dsimp [f] at *
  linarith

theorem tdGain_lower {s : ℝ} {T : SignedPoint} (hs : s∈Icc 0 frameCap)
    (hT : T.Sorted) (hcore : T.AvoidsCore) :
    (charge+37/350)*s≤tdGain (-s) T := by
  have ht := transport_trig hs
  have hphi : 0≤Real.sin s+Real.cos s-1 := by
    have hh := one_le_abs_cos_add_abs_sin s
    rw [abs_of_pos (cosine_pos hs),abs_of_nonneg ht.2.2.1] at hh
    linarith
  have hprimary := SignedPoint.primary_gt_half hT hcore
  have hY := (abs_le.mp hT.2).1
  have hYprod := mul_le_mul_of_nonpos_right hY
    (show Real.cos s-1≤0 by linarith [ht.2.1])
  have hAprod := mul_nonneg (show 0≤T.a-1/2 by linarith) hphi
  have hh := td_arc_charge hs
  rw [tdGain,edgeWidth_negative_formula hs]
  simp only [Real.sin_neg,Real.cos_neg]
  dsimp [lowC] at *
  nlinarith

theorem eGain_lower {s A : ℝ} (hs : s∈Icc 0 frameCap) (hA : A≤283/200) :
    g s≤eGain (-s) A := by
  have hc := cosine_pos hs
  have hprod := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr (Real.cos_le_one s))
  apply (mul_le_mul_right hc).mp
  rw [eGain,edgeWidth_negative_formula hs]
  simp only [Real.cos_neg,Real.sin_neg]
  dsimp [g,K,a]
  field_simp [hc.ne']
  nlinarith

end SquaresInCircles.Eight.TableFree.GlobalGA.NegativeFlatE
