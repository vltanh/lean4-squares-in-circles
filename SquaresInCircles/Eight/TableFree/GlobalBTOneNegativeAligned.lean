module

public import SquaresInCircles.Eight.TableFree.GlobalBTOnePositivePath

/-!
# The complete AB0 prefix when its positive error dominates negative BT1

The two actual contacts share the original signed B circle.  Their
chord force has a nonnegative direction.  Its full interval support
and the established positive-zero gain yield the aligned prefix
charge, without claiming an aligned feasible pair or a high T cap.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative

open FramePair FrameCircleArc GlobalOuterAnchor GlobalZeroSign

theorem chord_force (b : State) {v z : ℝ}
    (hz : 0≤z) (hzv : z≤v) (hv : v≤frameCap) :
    b.a*(Real.sin v-Real.sin z)+transverse b*(Real.cos z-Real.cos v)≤
      2*Real.sin ((v-z)/2)*(R-(Real.cos ((v+z)/2)+Real.sin ((v+z)/2))/2) := by
  have hv' : v≤7/10 := by simpa only [frameCap] using hv
  let h := (v-z)/2
  let m := (v+z)/2
  have hh : h∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc]; exact ⟨by dsimp [h]; linarith,by dsimp [h]; linarith⟩
  have hm : m∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc]; exact ⟨by dsimp [m]; linarith,by dsimp [m]; linarith⟩
  have hV : v=m+h := by dsimp [m,h]; ring
  have hZ : z=m-h := by dsimp [m,h]; ring
  have hs := state_support b (Real.cos m) (Real.sin m)
  have hunit : (Real.cos m)^2+(Real.sin m)^2=1 := by
    linarith [Real.sin_sq_add_cos_sq m]
  rw [hunit,Real.sqrt_one,mul_one] at hs
  have hsign := mul_nonneg (transport_trig hm).2.2.1
    (show 0≤b.b-transverse b by linarith [(transverse_bounds b).2])
  have hB : Real.cos m*b.a+Real.sin m*transverse b≤R-(Real.cos m+Real.sin m)/2 := by
    change Real.cos m*b.a+Real.sin m*b.b≤R-(Real.cos m+Real.sin m)/2 at hs
    linarith only [hs,hsign]
  have hp := mul_le_mul_of_nonneg_left hB
    (show 0≤2*Real.sin h by linarith [(transport_trig hh).2.2.1])
  have hid : b.a*(Real.sin v-Real.sin z)+transverse b*(Real.cos z-Real.cos v)=
      2*Real.sin h*(Real.cos m*b.a+Real.sin m*transverse b) := by
    rw [hV,hZ,Real.sin_add,Real.sin_sub,Real.cos_add,Real.cos_sub]
    ring
  rw [hid]
  exact hp

theorem chord_width_reserve {v z : ℝ}
    (hz : 0≤z) (hzv : z≤v) (hv : v≤frameCap) :
    Real.sin (v-z)-2*R*Real.sin ((v-z)/2)≤
      GlobalOuterAnchor.width v+GlobalOuterAnchor.width (-z)-2-
        2*Real.sin ((v-z)/2)*(R-(Real.cos ((v+z)/2)+Real.sin ((v+z)/2))/2) := by
  have hv' : v≤7/10 := by simpa only [frameCap] using hv
  let h := (v-z)/2
  let m := (v+z)/2
  have hh : h∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc]; exact ⟨by dsimp [h]; linarith,by dsimp [h]; linarith⟩
  have hm : m∈Icc 0 frameCap := by
    simp only [frameCap,mem_Icc]; exact ⟨by dsimp [m]; linarith,by dsimp [m]; linarith⟩
  have hhm : h ≤ m := by dsimp [h,m]; linarith
  have hmono := sine_cosine_monotone hh hm hhm
  have hsum : 0≤Real.sin h+Real.cos h := by
    have tr := transport_trig hh
    linarith [tr.1,tr.2.2.1]
  have hprod := mul_le_mul_of_nonneg_left hmono hsum
  have hV : v=m+h := by dsimp [m,h]; ring
  have hZ : z=m-h := by dsimp [m,h]; ring
  have hEta : v-z=2*h := by dsimp [h]; ring
  have hsinV : Real.sin v=Real.sin m*Real.cos h+Real.cos m*Real.sin h := by
    rw [hV,Real.sin_add]
  have hcosV : Real.cos v=Real.cos m*Real.cos h-Real.sin m*Real.sin h := by
    rw [hV,Real.cos_add]
  have hsinZ : Real.sin z=Real.sin m*Real.cos h-Real.cos m*Real.sin h := by
    rw [hZ,Real.sin_sub]
  have hcosZ : Real.cos z=Real.cos m*Real.cos h+Real.sin m*Real.sin h := by
    rw [hZ,Real.cos_sub]
  have hsinEta : Real.sin (v-z)=2*Real.sin h*Real.cos h := by rw [hEta,Real.sin_two_mul]
  rw [width_positive (show v∈Icc 0 frameCap from ⟨by linarith,hv⟩),
    width_negative (show z∈Icc 0 frameCap from ⟨hz,hzv.trans hv⟩),
    hsinV,hcosV,hsinZ,hcosZ,hsinEta]
  change 2*Real.sin h*Real.cos h-2*R*Real.sin h≤
    (1+(Real.cos m*Real.cos h-Real.sin m*Real.sin h)+
      (Real.sin m*Real.cos h+Real.cos m*Real.sin h))/2+
    (1+(Real.cos m*Real.cos h+Real.sin m*Real.sin h)+
      (Real.sin m*Real.cos h-Real.cos m*Real.sin h))/2-2-
        2*Real.sin h*(R-(Real.cos m+Real.sin m)/2)
  nlinarith only [hprod,Real.sin_sq_add_cos_sq h]

/-- This is a charge comparison on the original A/B/T states.  It
does not assert the stronger necessary high-primary cap. -/
theorem AB0_dominating_charge (a b t : State) {v z : ℝ}
    (ha : 0≤transverse a) (hz : 0≤z) (hzv : z≤v) (hv : v≤frameCap)
    (hAB : GlobalOuterAnchor.width v≤projection false a b v 0)
    (hBT : GlobalOuterAnchor.width (-z)≤projection true b t (-z) 1) :
    kappa*(2-t.a)≤v-z+kappa*a.b := by
  have hforce := chord_force b hz hzv hv
  have hwidth := chord_width_reserve hz hzv hv
  have heta : v-z∈Icc 0 frameCap := ⟨by linarith,by linarith⟩
  have hgain := positive_zero_gain (lambda := kappa) (by norm_num [kappa]) le_rfl heta
  have hsum : GlobalOuterAnchor.width v+GlobalOuterAnchor.width (-z)≤a.b+t.a+
      b.a*(Real.sin v-Real.sin z)+transverse b*(Real.cos z-Real.cos v) := by
    have hay := transverse_of_nonneg a ha
    dsimp [projection] at hAB hBT
    rw [hay] at hAB
    simp only [Real.cos_neg,Real.sin_neg] at hBT
    nlinarith only [hAB,hBT]
  have hprefix : Real.sin (v-z)-2*R*Real.sin ((v-z)/2)≤a.b+t.a-2 := by
    linarith only [hforce,hwidth,hsum]
  have hm := mul_le_mul_of_nonneg_left hprefix (show 0≤kappa by norm_num [kappa])
  dsimp [positiveZeroGain] at hgain
  nlinarith only [hm,hgain]

end SquaresInCircles.Eight.TableFree.GlobalBT.OneNegative
