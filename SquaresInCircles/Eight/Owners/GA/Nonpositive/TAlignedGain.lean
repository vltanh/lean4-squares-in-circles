module

public import SquaresInCircles.Eight.Owners.GA.Nonpositive.TPairedBounds
public import SquaresInCircles.Eight.Owners.GA.Owners
public import SquaresInCircles.Eight.Owners.GA.Paired.ACharge
public import SquaresInCircles.Eight.Owners.GA.Two.PositiveScalar

/-!
# Eight squares: the T charge at the TD alignment

On the cycle with T moved to the TD alignment `delta T = 0`, both T primary witnesses BT3 and TD2
are feasible, and adding the two inequalities gives the short bound `s < M` (`aligned_short`). The
stronger linear gain `(9/10) s` for the core-E stresses (`genuine_linear`) follows from the BT3
entry, when BT2 is not feasible.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity

theorem aligned_work (P : SignedPoint) {s : ℝ} (hs : s∈Icc 0 frameCap) :
    PairedA.work P (-s) 0=
      (P.a+1/2)*Real.sin s-(P.y+1/2)*(1-Real.cos s) := by
  rw [PairedA.work,edgeWidth_negative_formula hs]
  simp only [edgeWidth_zero,Real.sin_zero,Real.cos_zero,Real.sin_neg,Real.cos_neg]
  ring

theorem aligned_work_sorted {P : SignedPoint} (hP : P.Sorted)
    {s : ℝ} (hs : s∈Icc 0 frameCap) :
    (P.a+1/2)*(PositiveAngularEnvelope.phi s-1)≤PairedA.work P (-s) 0 := by
  have hy : P.y≤P.a := (le_abs_self P.y).trans hP.2
  have hh := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr (Real.cos_le_one s))
  rw [aligned_work P hs]
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith only [hh]

theorem aligned_work_lower {Q s : ℝ} {P : SignedPoint}
    (hP : P.Sorted) (hcore : P.AvoidsCore) (hPc : P.Contained Q) (hQ : Q≤qCap)
    (hs : s∈Icc 0 frameCap) : kappa*(PositiveAngularEnvelope.phi s-1)≤PairedA.work P (-s) 0 := by
  have hb := SignedPoint.coordinate_bounds hP hcore hPc hQ
  have hphi : 0≤PositiveAngularEnvelope.phi s-1 := sub_nonneg.mpr (TwoPositive.Split.phi_ge_one hs)
  have hh := mul_le_mul_of_nonneg_right
    (show kappa≤P.a+1/2 by dsimp [kappa]; linarith [hb.1]) hphi
  exact hh.trans (aligned_work_sorted hP hs)

theorem aligned_work_weak {P : SignedPoint} (hP : P.Sorted) (hcore : P.AvoidsCore)
    {s : ℝ} (hs : s∈Icc 0 frameCap) : PositiveAngularEnvelope.phi s-1≤PairedA.work P (-s) 0 := by
  have ha := SignedPoint.primary_gt_half hP hcore
  have hphi : 0≤PositiveAngularEnvelope.phi s-1 := sub_nonneg.mpr (TwoPositive.Split.phi_ge_one hs)
  have hh := mul_nonneg (show 0≤P.a-1/2 by linarith) hphi
  have hb := aligned_work_sorted hP hs
  nlinarith only [hh,hb]

theorem phi_monotone : MonotoneOn PositiveAngularEnvelope.phi (Icc 0 frameCap) := by
  have hd (s : ℝ) : HasDerivAt PositiveAngularEnvelope.phi (Real.cos s-Real.sin s) s := by
    have h := (Real.hasDerivAt_cos s).add (Real.hasDerivAt_sin s)
    rw [show Real.cos s-Real.sin s=-Real.sin s+Real.cos s by ring]
    exact h
  apply monoOn_of_hasDeriv_nonneg (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => hd x)
  · intro s hs
    have ht := transport_trig (Ioo_subset_Icc_self hs)
    linarith [ht.1,ht.2.2.2.1]

theorem M_phi_reserve : (63/200:ℝ)<PositiveAngularEnvelope.phi M-1 := by
  have hs := sin_lower_seven (x:=M) (by norm_num [M])
  have hc := cos_lower_six (x:=M) (by norm_num [M])
  norm_num [M] at hs hc
  dsimp [PositiveAngularEnvelope.phi,M]
  linarith

theorem aligned_projection_upper {C : SignedCycle} {s : ℝ}
    (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hb : delta C.theta B=-s) (hd : delta C.theta T=0) :
    PairedA.work (C.point T) (-s) 0≤(C.point B).a-(C.point D).y-2 := by
  have hB : quarterFeasible (C.point B) (C.point T) (-s) 3 := by
    have hh : quarterFeasible (C.point B) (C.point T) (delta C.theta B) 3 := by
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
        quarterFeasible,delta,next,B,T,sub_nonneg] using hBT
    simpa [hb] using hh
  have hD : zeroFeasible (C.point T) (C.point D) 0 2 := by
    have hh : zeroFeasible (C.point T) (C.point D) (delta C.theta T) 2 := by
      simpa [SignedCycle.Feasible,SignedCycle.slack,SignedCycle.edge,word,
        zeroFeasible,delta,next,T,D,sub_nonneg] using hTD
    simpa [hd] using hh
  have hB' : edgeWidth (-s)≤(C.point B).a+(C.point T).a*Real.sin (-s)-
      (C.point T).y*Real.cos (-s) := by simpa [quarterFeasible,quarterProjection] using hB
  have hD' : 1≤(C.point T).y-(C.point D).y := by
    simpa [zeroFeasible,zeroProjection] using hD
  dsimp [PairedA.work]
  simp only [edgeWidth_zero,Real.sin_zero,Real.cos_zero] at ⊢
  linarith only [hB',hD']

theorem aligned_short {Q s : ℝ} {C : SignedCycle}
    (hsort : ∀i,(C.point i).Sorted) (hcoreT : (C.point T).AvoidsCore)
    (hc : ∀i,(C.point i).Contained Q) (hQ : Q≤qCap) (hDy : (C.point D).y≤0)
    (hs : s∈Icc 0 frameCap) (hBT : C.Feasible B 3) (hTD : C.Feasible T 2)
    (hb : delta C.theta B=-s) (hd : delta C.theta T=0) : s<M := by
  have hwork := aligned_work_weak (hsort T) hcoreT hs
  have hupper := aligned_projection_upper hBT hTD hb hd
  have hB := GlobalGA.primary_upper (hsort B) (hc B) hQ
  have hD := actual_coordinate_bounds (P:=(C.point D).reflect)
    (by simpa using hsort D) (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa using hc D) hQ
  have hD' : -(C.point D).y<(9/10:ℝ) := by
    dsimp [SignedPoint.reflect] at hD
    linarith [hD.2.1,diagonal_bounds.2]
  have hu : PositiveAngularEnvelope.phi s-1<(63/200:ℝ) := by linarith
  by_contra! hM
  have hm := phi_monotone (show M∈Icc 0 frameCap by norm_num [M,frameCap]) hs hM
  linarith [M_phi_reserve]

theorem genuine_linear {P : SignedPoint} (ha : P.a=7/12) (hy : P.y≤39/250)
    {s : ℝ} (hs : s∈Icc 0 M) : (9/10)*s≤PairedA.work P (-s) 0 := by
  let f : ℝ→ℝ := fun x => (13/12)*Real.sin x-(82/125)*(1-Real.cos x)-(9/10)*x
  have hf : ConcaveOn ℝ (Icc 0 M) f := by
    apply concave_of_deriv2
      (f':=fun x => (13/12)*Real.cos x-(82/125)*Real.sin x-9/10)
      (f'':=fun x => -(13/12)*Real.sin x-(82/125)*Real.cos x)
    · intro x _
      have h := (((Real.hasDerivAt_sin x).const_mul (13/12)).sub
        (((Real.hasDerivAt_cos x).const_sub 1).const_mul (82/125))).sub
          ((hasDerivAt_id x).const_mul (9/10))
      convert h using 1
      · rfl
      · ring
    · intro x _
      convert (((Real.hasDerivAt_cos x).const_mul (13/12)).sub
        ((Real.hasDerivAt_sin x).const_mul (82/125))).sub_const (9/10)
        using 1
      ring
    · intro x hx
      have ht := transport_trig (show x∈Icc 0 frameCap from
        ⟨hx.1,by norm_num [M,frameCap] at *; linarith [hx.2]⟩)
      linarith [ht.1,ht.2.2.1]
  have h0 : 0≤f 0 := by norm_num [f]
  have hM : 0≤f M := by
    have hS := sin_lower_seven (x:=M) (by norm_num [M])
    have hC := cos_lower_six (x:=M) (by norm_num [M])
    norm_num [M] at hS hC
    dsimp [f,M]
    linarith
  have hmin := hf.min_le_of_mem_Icc (show (0:ℝ)∈Icc 0 M by norm_num [M])
    (show M∈Icc 0 M by norm_num [M]) hs
  have hlower := (le_min h0 hM).trans hmin
  have hhy := mul_le_mul_of_nonneg_right hy (sub_nonneg.mpr (Real.cos_le_one s))
  rw [aligned_work P ⟨hs.1,by norm_num [M,frameCap] at *; linarith [hs.2]⟩,ha]
  dsimp [f] at hlower
  linarith

end SquaresInCircles.Eight.GlobalGA.NonpositiveT.Paired
