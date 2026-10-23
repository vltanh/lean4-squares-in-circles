module

public import SquaresInCircles.Eight.TableFree.OrdinaryAngleConcentration
public import SquaresInCircles.Eight.TableFree.PositiveStressCoefficients

/-!
# Correlated same-block saturation on the whole angular interval

Uncompiled source draft of Section 4 of the positive-GA angular envelope.
The coefficient lower bound is the actual correlated ratio
`117/200+(51/200)d`, including its small-d values below `2/3`.
Both comparisons keep the original two-angle norm exactly: it cancels
because the signed angle difference is unchanged.

The negative-surplus estimate uses a quadratic lower bound for its
trigonometric bracket. The positive-surplus estimate uses concavity of
one explicit sinusoid. Neither argument subdivides the angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CorrelatedSameBlock
open PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveStressCoefficients

theorem sin_mono {x y : ℝ} (hx : x∈Icc 0 frameCap)
    (hy : y∈Icc 0 frameCap) (hxy : x≤y) : Real.sin x≤Real.sin y :=
  Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos])
    (by dsimp [frameCap] at hy; linarith [hy.2,Real.pi_gt_three]) hxy

theorem cos_anti {x y : ℝ} (hx : x∈Icc 0 frameCap)
    (hy : y∈Icc 0 frameCap) (hxy : x≤y) : Real.cos y≤Real.cos x :=
  Real.cos_le_cos_of_nonneg_of_le_pi hx.1
    (by dsimp [frameCap] at hy; linarith [hy.2,Real.pi_gt_three]) hxy

theorem phi_hasDerivAt (x : ℝ) :
    HasDerivAt phi (Real.cos x-Real.sin x) x := by
  convert (Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x) using 1
  · rfl
  · ring

theorem phi_mono : MonotoneOn phi (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact (by unfold phi; fun_prop : Continuous phi).continuousOn
  · intro x _
    exact phi_hasDerivAt x
  · intro x hx
    exact sub_nonneg.mpr (transport_trig (Ioo_subset_Icc_self hx)).2.2.2.2.le

theorem one_le_phi {x : ℝ} (hx : x∈Icc 0 frameCap) : 1≤phi x := by
  simpa [phi] using phi_mono
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hx hx.1

/-- The elementary half-angle lower estimate follows from the global
fourth- and fifth-order Taylor inequalities. -/
theorem half_angle_lower {a : ℝ} (ha : a∈Icc 0 frameCap) :
    (a/2)*Real.sin a≤1-Real.cos a := by
  have hc := cos_upper_four ha.1
  have hs := mul_le_mul_of_nonneg_left (sin_upper_five ha.1) ha.1
  have ha2 : a^2≤(7/10 : ℝ)^2 := pow_le_pow_left₀ ha.1 ha.2 2
  have hp : 0≤a^4*(10-a^2) := mul_nonneg (pow_nonneg ha.1 4) (by linarith)
  nlinarith

/-- A rational lower bound for the full correlated trigonometric
bracket. Its endpoint reserve is `363/100000`. -/
theorem correlated_bracket {d : ℝ} (hd : d∈Icc 0 frameCap) :
    (363/100000 : ℝ)≤ratio d-Real.sin frameCap+
      (Real.cos frameCap-ratio d)*(frameCap-d)/2 := by
  let a : ℝ := frameCap-d
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [hd.2],
    by dsimp [a]; linarith [hd.1]⟩
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).1
  have hs := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).2.2.2.1
  have hmul := mul_le_mul_of_nonneg_right hc.le ha.1
  have hp : 0≤(7/10-a)*((1651/10000 : ℝ)-(51/400 : ℝ)*a) := by
    apply mul_nonneg (by dsimp [frameCap] at ha; linarith [ha.2])
    dsimp [frameCap] at ha
    linarith [ha.2]
  have he : ratio d=1527/2000-(51/200)*a := by
    dsimp [ratio,a,frameCap]
    ring
  change (363/100000 : ℝ)≤ratio d-Real.sin frameCap+
    (Real.cos frameCap-ratio d)*a/2
  rw [he]
  nlinarith

theorem correlated_saturated_trig {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0≤ratio d*(phi (frameCap-d)-1)+Real.cos frameCap-Real.cos d := by
  let a : ℝ := frameCap-d
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [hd.2],
    by dsimp [a]; linarith [hd.1]⟩
  have hsin := (transport_trig ha).2.2.1
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).1
  have hr : ratio d≤1527/2000 := by dsimp [ratio]; linarith [hd.2]
  have hfactor : 0≤Real.cos frameCap-ratio d := by linarith
  have hhalf := mul_le_mul_of_nonneg_left (half_angle_lower ha) hfactor
  have hbracket := correlated_bracket hd
  have hbr0 : 0≤ratio d-Real.sin frameCap+
      (Real.cos frameCap-ratio d)*a/2 := by
    dsimp [a]
    linarith
  have hpositive := mul_nonneg hsin hbr0
  have hcos : Real.cos d=Real.cos frameCap*Real.cos a+
      Real.sin frameCap*Real.sin a := by
    rw [← Real.cos_sub]
    congr 1
    dsimp [a]
    ring
  change 0≤ratio d*(phi a-1)+Real.cos frameCap-Real.cos d
  rw [hcos]
  dsimp [phi]
  nlinarith

/-- With the positive total fixed, the negative cosine increment is
smallest at the largest permitted negative surplus. -/
theorem cosine_increment_anti {a : ℝ} (ha : a∈Icc 0 frameCap) :
    AntitoneOn (fun w => Real.cos (a+w)-Real.cos w) (Icc 0 (frameCap-a)) := by
  apply antiOn_of_hasDeriv_nonpos
  · fun_prop
  · intro w _
    convert (((hasDerivAt_id w).const_add a).cos).sub (Real.hasDerivAt_cos w) using 1 <;> ring
  · intro w hw
    have hw' : w∈Icc 0 frameCap := ⟨hw.1.le,by linarith [hw.2,ha.1]⟩
    have hsum : a+w∈Icc 0 frameCap := ⟨by linarith [ha.1,hw.1],by linarith [hw.2]⟩
    linarith [sin_mono hw' hsum (by linarith [ha.1])]

/-- The negative-surplus saturated block dominates its original single
negative block for the full correlated coefficient domain. -/
theorem negative_surplus {R p q d s : ℝ} (hq : 0≤q)
    (hratio : ratio d*q≤p) (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d) :
    V R p q (d-s)≤mixedBlock R p q (frameCap-d) (frameCap-s) := by
  have ha : frameCap-d∈Icc 0 frameCap := ⟨by linarith [hd.2],by linarith [hd.1]⟩
  have hw : d-s∈Icc 0 (frameCap-(frameCap-d)) :=
    ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd' : d∈Icc 0 (frameCap-(frameCap-d)) := ⟨hd.1,by ring_nf⟩
  have hcos := cosine_increment_anti ha hw hd' (by linarith [hs.1])
  have hcos' : Real.cos frameCap-Real.cos d≤
      Real.cos (frameCap-s)-Real.cos (d-s) := by
    convert hcos using 1 <;> congr 1 <;> ring
  have hphi := sub_nonneg.mpr (one_le_phi ha)
  have hp := mul_le_mul_of_nonneg_right hratio hphi
  have hqcos := mul_le_mul_of_nonneg_left hcos' hq
  have htrig := mul_nonneg hq (correlated_saturated_trig hd)
  have harg : frameCap-d-(frameCap-s)= -(d-s) := by ring
  dsimp [V,mixedBlock]
  rw [harg]
  nlinarith

/-- For fixed negative amount, translating both positive arguments to
the right decreases the increment of `phi`. -/
theorem phi_increment_anti {N : ℝ} (hN : N∈Icc 0 frameCap) :
    AntitoneOn (fun w => phi (w+N)-phi w) (Icc 0 (frameCap-N)) := by
  apply antiOn_of_hasDeriv_nonpos
  · unfold phi
    fun_prop
  · intro w _
    convert ((phi_hasDerivAt (w+N)).comp w ((hasDerivAt_id w).add_const N)).sub
      (phi_hasDerivAt w) using 1 <;> ring
  · intro w hw
    have hw' : w∈Icc 0 frameCap := ⟨hw.1.le,by linarith [hw.2,hN.1]⟩
    have hsum : w+N∈Icc 0 frameCap := ⟨by linarith [hw.1,hN.1],by linarith [hw.2]⟩
    have hle : w≤w+N := by linarith [hN.1]
    linarith [cos_anti hw' hsum hle,sin_mono hw' hsum hle]

private def surplusTrig (N : ℝ) : ℝ :=
  (117/200)*(phi frameCap-phi (frameCap-N))+Real.cos N-1

private theorem surplusTrig_nonneg {N : ℝ} (hN : N∈Icc 0 frameCap) :
    0≤surplusTrig N := by
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) surplusTrig := by
    apply concave_of_deriv2
      (f' := fun t => (117/200)*(Real.cos (frameCap-t)-Real.sin (frameCap-t))-Real.sin t)
      (f'' := fun t => (117/200)*phi (frameCap-t)-Real.cos t)
    · intro t _
      have ha := (hasDerivAt_id t).const_sub frameCap
      have hraw := ((((hasDerivAt_const t (phi frameCap)).sub
        ((phi_hasDerivAt (frameCap-t)).comp t ha)).const_mul (117/200)).add
          (Real.hasDerivAt_cos t)).sub_const 1
      convert hraw using 1
      · rfl
      · ring
    · intro t _
      have ha := (hasDerivAt_id t).const_sub frameCap
      convert ((ha.cos.sub ha.sin).const_mul (117/200)).sub
        (Real.hasDerivAt_sin t) using 1 <;> dsimp [phi] <;> ring
    · intro t ht
      obtain ⟨hc,_,hs0,hs,hsc⟩ := transport_trig
        (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl)
      have hct : 0≤Real.cos t := by have h := (transport_trig ht).1; linarith
      have hst : 0≤Real.sin t := (transport_trig ht).2.2.1
      have hfirst : 0≤(1-(117/200)*phi frameCap)*Real.cos t := by
        apply mul_nonneg _ hct
        dsimp [phi]
        linarith [Real.cos_le_one frameCap]
      have hsecond := mul_nonneg (show 0≤(117/200)*(Real.cos frameCap-Real.sin frameCap) by
        linarith) hst
      have he : phi (frameCap-t)=phi frameCap*Real.cos t+
          (Real.sin frameCap-Real.cos frameCap)*Real.sin t := by
        simp only [phi,Real.cos_sub,Real.sin_sub]
        ring
      rw [he]
      nlinarith
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) hN
  have hz : surplusTrig 0=0 := by simp [surplusTrig]
  have hh : 0≤surplusTrig frameCap := by
    have hphi := phi_cap_lower
    have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
      constructor; norm_num [frameCap]; rfl)).1
    simp only [surplusTrig,sub_self,phi,Real.cos_zero,Real.sin_zero,add_zero]
    dsimp [phi] at hphi
    linarith
  rw [hz,min_eq_left hh] at hmin
  exact hmin

/-- Every ordinary block with ratio at least `.585` dominates the pure
positive surplus when its two nonnegative amounts fit in the frame. -/
theorem positive_surplus {R p q P N : ℝ} (hq : 0≤q)
    (hratio : (117/200)*q≤p) (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 P) :
    U R p q (P-N)≤mixedBlock R p q P N := by
  have hN' : N∈Icc 0 frameCap := ⟨hN.1,hN.2.trans hP.2⟩
  have hw : P-N∈Icc 0 frameCap := ⟨by linarith [hN.2],by linarith [hP.2,hN.1]⟩
  have hincrement : 0≤phi P-phi (P-N) :=
    sub_nonneg.mpr (phi_mono hw hP (by linarith [hN.1]))
  have hi := phi_increment_anti hN'
    (show P-N∈Icc 0 (frameCap-N) from ⟨hw.1,by linarith [hP.2]⟩)
    (show frameCap-N∈Icc 0 (frameCap-N) from ⟨by linarith [hN'.2],le_rfl⟩)
    (by linarith [hP.2])
  have hi' : phi frameCap-phi (frameCap-N)≤phi P-phi (P-N) := by
    convert hi using 1 <;> congr 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hratio hincrement
  have hmin := mul_le_mul_of_nonneg_left hi' (show 0≤(117/200 : ℝ)*q by positivity)
  have hbase := mul_nonneg hq (surplusTrig_nonneg hN')
  dsimp [surplusTrig] at hbase
  dsimp [U,mixedBlock]
  nlinarith

end SquaresInCircles.Eight.TableFree.CorrelatedSameBlock
