module

public import SquaresInCircles.Eight.TableFree.GlobalGATargetZeroErrors

/-!
# The larger reserve for a core high-GA target

Uncompiled transcription of Section 6 of the target note. The actual
GA3 inequality first forces the angle above 3/10. The remaining scalar
is concave on the entire interval, and only its two stated endpoints
are evaluated. The fixed force base is proved by positive squaring.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.Target.Core
open FramePair ZeroPrimary GlobalOuterAnchor Arithmetic

def weight : ℝ := 7/5
def angleSupport (u : ℝ) : ℝ := 1/2+Real.cos u-Real.sin u/12
def error (a : State) (u : ℝ) : ℝ :=
  u-weight*((a.b+1/2)*(1-Real.cos u)+(a.a-1/2)*Real.sin u)
def f (u : ℝ) : ℝ :=
  u-weight*((53/50)*(1-Real.cos u)+(1/12)*Real.sin u)
def fd (u : ℝ) : ℝ :=
  1-weight*((53/50)*Real.sin u+(1/12)*Real.cos u)
def fdd (u : ℝ) : ℝ :=
  -weight*((53/50)*Real.cos u-(1/12)*Real.sin u)
def base : ℝ := 2*m+2*weight-CommonQuarter.radius*Real.sqrt (weight^2+m^2)

theorem coordinate_bounds (a : State) (ha : a.branch.type=0) :
    a.a≤7/12 ∧ a.b<14/25 := by
  have hh := FrameCoreArc.core_bounds (FrameCoreArc.state_core_chart a ha)
  have hd := CoreAngleEndpoint.diagonal_bounds.2
  exact ⟨hh.2.1,by linarith [hh.2.2.2]⟩

theorem angleSupport_hasDerivAt (u : ℝ) :
    HasDerivAt angleSupport (-Real.sin u-Real.cos u/12) u :=
  ((Real.hasDerivAt_cos u).const_add (1/2)).sub ((Real.hasDerivAt_sin u).div_const 12)

theorem angleSupport_antitone : AntitoneOn angleSupport (Icc 0 frameCap) :=
  antiOn_of_hasDeriv_nonpos
    (fun u _ => (angleSupport_hasDerivAt u).continuousAt.continuousWithinAt)
    (fun u _ => angleSupport_hasDerivAt u)
    (fun u hu => by
      have ht := transport_trig (Ioo_subset_Icc_self hu)
      linarith [ht.1,ht.2.2.1])

theorem angleSupport_reference : (283/200:ℝ)<angleSupport (3/10) := by
  have hc := cos_lower_six (by norm_num : (0:ℝ)≤3/10)
  have hs := sin_upper_five (by norm_num : (0:ℝ)≤3/10)
  norm_num at hc hs
  dsimp [angleSupport]
  linarith

theorem angle_lower (g a : State) (ha : a.branch.type=0) (hb : (1/2:ℝ)≤a.b)
    {u : ℝ} (hu : u∈Icc 0 frameCap)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u) : (3/10:ℝ)<u := by
  have ht := transport_trig hu
  have hA := mul_le_mul_of_nonneg_right (coordinate_bounds a ha).1 ht.2.2.1
  have hB := mul_le_mul_of_nonneg_right hb (by linarith [ht.1] : 0≤Real.cos u)
  have hwidth : GlobalOuterAnchor.width u=(1+Real.cos u+Real.sin u)/2 := by
    simp only [GlobalOuterAnchor.width,abs_of_nonneg ht.2.2.1]
  have hlower : angleSupport u≤g.a := by
    rw [hwidth] at hGA
    dsimp [angleSupport]
    nlinarith
  by_contra! hsmall
  have hh := angleSupport_antitone hu (by norm_num [frameCap] : (3/10:ℝ)∈Icc 0 frameCap) hsmall
  linarith [angleSupport_reference,(coordinates g).2.1]

theorem f_hasDerivAt (u : ℝ) : HasDerivAt f (fd u) u := by
  have h := (hasDerivAt_id' u).fun_sub
    (((((Real.hasDerivAt_cos u).const_sub 1).const_mul (53/50:ℝ)).fun_add
      ((Real.hasDerivAt_sin u).const_mul (1/12:ℝ))).const_mul weight)
  exact h.congr_deriv (by dsimp [fd]; ring)

theorem fd_hasDerivAt (u : ℝ) : HasDerivAt fd (fdd u) u := by
  have h := ((((Real.hasDerivAt_sin u).const_mul (53/50:ℝ)).fun_add
    ((Real.hasDerivAt_cos u).const_mul (1/12:ℝ))).const_mul weight).const_sub 1
  exact h.congr_deriv (by dsimp [fdd]; ring)

theorem f_concave : ConcaveOn ℝ (Icc (3/10:ℝ) frameCap) f :=
  concave_of_deriv2 (fun u _ => f_hasDerivAt u) (fun u _ => fd_hasDerivAt u)
    (fun u hu => by
      have ht := transport_trig ⟨by linarith [hu.1],hu.2⟩
      dsimp [fdd,weight]
      linarith [ht.1,ht.2.2.2.1])

theorem f_left : (19/100:ℝ)<f (3/10) := by
  have hc := cos_lower_six (by norm_num : (0:ℝ)≤3/10)
  have hs := sin_upper_five (by norm_num : (0:ℝ)≤3/10)
  norm_num at hc hs
  dsimp [f,weight]
  linarith

theorem f_right : (19/100:ℝ)<f frameCap := by
  have hc := cos_lower_six (by norm_num [frameCap] : 0≤frameCap)
  have hs := sin_upper_five (by norm_num [frameCap] : 0≤frameCap)
  norm_num [frameCap] at hc hs
  dsimp [f,weight,frameCap]
  linarith

theorem f_lower {u : ℝ} (hu : u∈Icc (3/10:ℝ) frameCap) : (19/100:ℝ)<f u := by
  have hh := f_concave.min_le_of_mem_Icc (by norm_num [frameCap])
    (by norm_num [frameCap]) hu
  exact (lt_min f_left f_right).trans_le hh

theorem error_lower (a : State) (ha : a.branch.type=0) {u : ℝ}
    (hu : u∈Icc (3/10:ℝ) frameCap) : (19/100:ℝ)<error a u := by
  have hc := coordinate_bounds a ha
  have ht := transport_trig ⟨by linarith [hu.1],hu.2⟩
  have hA := mul_le_mul_of_nonneg_right (show a.a-1/2≤(1/12:ℝ) by linarith [hc.1]) ht.2.2.1
  have hB := mul_le_mul_of_nonneg_right (show a.b+1/2≤(53/50:ℝ) by linarith [hc.2])
    (sub_nonneg.mpr (Real.cos_le_one u))
  have hh := f_lower hu
  dsimp [f,error,weight] at *
  linarith

theorem error_separator (g a : State) {u : ℝ} (hu : u∈Icc 0 frameCap)
    (hGA : GlobalOuterAnchor.width u≤g.a+a.a*Real.sin u-a.b*Real.cos u) :
    error a u≤u+weight*(g.a-a.b-1) := by
  have ht := transport_trig hu
  dsimp [GlobalOuterAnchor.width] at hGA
  rw [abs_of_nonneg ht.2.2.1] at hGA
  dsimp [error,weight]
  nlinarith

theorem base_lower : (127/100:ℝ)<base := by
  obtain ⟨n,hndef⟩ : ∃ n : ℝ, n=Real.sqrt (weight^2+m^2) := ⟨_,rfl⟩
  obtain ⟨l,hldef⟩ : ∃ l : ℝ, l=2*m+2*weight-127/100 := ⟨_,rfl⟩
  have hn : n^2=weight^2+m^2 := by rw [hndef]; exact Real.sq_sqrt (by positivity)
  have hp : 0≤CommonQuarter.radius*n :=
    mul_nonneg (Real.sqrt_nonneg _) (by rw [hndef]; exact Real.sqrt_nonneg _)
  have hs : (CommonQuarter.radius*n)^2=Q0*(weight^2+m^2) := by
    rw [mul_pow,CommonQuarter.radius_sq,hn]
  have hl : 0<l := by norm_num [hldef,m,weight]
  have hr : Q0*(weight^2+m^2)<l^2 := by norm_num [Q0,hldef,m,weight]
  have hh : CommonQuarter.radius*n<l := by nlinarith
  have hb : base=2*m+2*weight-CommonQuarter.radius*n := by rw [hndef]; rfl
  rw [hb]
  rw [hldef] at hh
  linarith

end SquaresInCircles.Eight.TableFree.GlobalGA.Target.Core
