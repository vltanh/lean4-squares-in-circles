module

public import SquaresInCircles.Eight.TableFree.OutsideERates

/-!
# The decreasing-tangent arc on E's exact original circle

Uncompiled reconstruction.  The circle parameter is `E.circle`; it
need not be the working radius and need not exceed `qLow`.  The original
sorted point and its actual primary reserve prove all geometry along
the arc.  The strict simultaneous primary-DE/EH direction is obtained
from the exact radial identity at this original circle.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Eight.TableFree.OriginalECircle

def root (E : SignedPoint) (b : ℝ) : ℝ := Real.sqrt (E.circle-(b+1/2)^2)
def primary (E : SignedPoint) (b : ℝ) : ℝ := root E b-1/2
def point (E : SignedPoint) (b : ℝ) : SignedPoint := ⟨primary E b,-b⟩
def slope (E : SignedPoint) (b : ℝ) : ℝ := (b+1/2)/root E b

def eh (E H : SignedPoint) (p b : ℝ) : ℝ :=
  H.a-1/2+(primary E b-1/2)*Real.sin p-(b+1/2)*Real.cos p

def de (E D : SignedPoint) (α p b : ℝ) : ℝ :=
  D.a-1/2-(primary E b+1/2)*Real.sin (p-α)+(b-1/2)*Real.cos (p-α)

theorem root_bounds {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    0<root E b ∧ E.a+1/2≤root E b ∧
      (root E b)^2=E.circle-(b+1/2)^2 := by
  have hsource : E.circle=(E.a+1/2)^2+(-E.y+1/2)^2 := by
    simp [SignedPoint.circle,abs_of_nonpos hEy]
  have hminor := pow_le_pow_left₀ (show 0≤b+1/2 by linarith [hb.1])
    (show b+1/2≤ -E.y+1/2 by linarith [hb.2]) 2
  have hrad : 0<E.circle-(b+1/2)^2 := by
    rw [hsource]
    nlinarith [hEs.1]
  have hroot : 0<root E b := Real.sqrt_pos.mpr hrad
  have hsq : (root E b)^2=E.circle-(b+1/2)^2 := Real.sq_sqrt hrad.le
  refine ⟨hroot,?_,hsq⟩
  nlinarith [hEs.1]

theorem initial {E : SignedPoint} (hEs : E.Sorted) (hEy : E.y≤0) : point E (-E.y)=E := by
  have heq : E.circle-(-E.y+1/2)^2=(E.a+1/2)^2 := by
    simp [SignedPoint.circle,abs_of_nonpos hEy]
  have ha : primary E (-E.y)=E.a := by
    unfold primary root
    rw [heq,Real.sqrt_sq (show 0≤E.a+1/2 by linarith [hEs.1])]
    ring
  unfold point
  rw [ha,neg_neg]

theorem geometry {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 7/12<E.a)
    (hb : b∈Icc 0 (-E.y)) :
    (point E b).Sorted ∧ (point E b).AvoidsCore ∧
      (point E b).circle=E.circle ∧ E.a≤primary E b := by
  have hr := root_bounds hEs hEy hb
  have ha : E.a≤primary E b := by dsimp [primary]; linarith [hr.2.1]
  have hbs : -E.y≤E.a := by simpa [abs_of_nonpos hEy] using hEs.2
  have hsort : b≤primary E b := hb.2.trans (hbs.trans ha)
  have hprimary : 7/12<primary E b := hEa.trans_le ha
  refine ⟨⟨by dsimp [point]; linarith,
    by simpa [point,abs_neg,abs_of_nonneg hb.1] using hsort⟩,?_,?_,ha⟩
  · change (1/12:ℝ)^2≤(max (primary E b-1/2) 0)^2+(max (|-b|-1/2) 0)^2
    rw [max_eq_left (by linarith : 0≤primary E b-1/2)]
    nlinarith [sq_nonneg (max (|-b|-1/2) 0)]
  · have hc : (point E b).circle=(root E b)^2+(b+1/2)^2 := by
      simp only [point,SignedPoint.circle,primary,abs_neg,abs_of_nonneg hb.1]
      ring
    rw [hc,hr.2.2]
    ring

theorem continuous_primary (E : SignedPoint) : Continuous (primary E) := by
  unfold primary root
  fun_prop

theorem derivative {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (primary E) (-slope E b) b ∧ 0≤ slope E b ∧ slope E b≤1 := by
  have hr := root_bounds hEs hEy hb
  have hrad : E.circle-(b+1/2)^2≠0 := by nlinarith [hr.1,hr.2.2]
  have hd := ((hasDerivAt_const b E.circle).sub
    (((hasDerivAt_id b).add_const (1/2)).pow 2)).sqrt hrad
  refine ⟨?_,?_,?_⟩
  · convert hd.sub_const (1/2) using 1
    · rfl
    · dsimp [slope,root]
      field_simp [hr.1.ne']
      ring
  · exact div_nonneg (by linarith [hb.1]) hr.1.le
  · apply (div_le_one hr.1).2
    have hbs : -E.y≤E.a := by simpa [abs_of_nonpos hEy] using hEs.2
    linarith [hb.2,hr.2.1]

theorem radial_identity {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    b-slope E b*primary E b= -(1-slope E b)/2 := by
  have hr := (root_bounds hEs hEy hb).1
  dsimp [slope,primary]
  field_simp [hr.ne']
  ring

theorem eh_actual (E H : SignedPoint) {p : ℝ} (b : ℝ)
    (hp : p∈Icc 0 (7/10:ℝ)) :
    eh E H p b=quarterProjection (point E b) H p 1-edgeWidth p := by
  rw [edgeWidth_positive_formula hp]
  simp [eh,point,quarterProjection]
  ring

theorem de_actual (E D : SignedPoint) (α : ℝ) {p : ℝ} (b : ℝ)
    (hn : p-α∈Icc 0 (7/10:ℝ)) :
    de E D α p b=quarterProjection D (point E b) (-(p-α)) 3-edgeWidth (-(p-α)) := by
  rw [edgeWidth_negative_formula hn]
  simp only [de,point,quarterProjection,Matrix.cons_val,Real.sin_neg,Real.cos_neg]
  ring

theorem improving_speed {E : SignedPoint} {p n b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 7/12<E.a)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10:ℝ)) (hn : n∈Icc 0 (7/10:ℝ)) :
    ∃β, 0<β ∧
      0<β*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p) ∧
      0<(primary E b+1/2-β)*Real.cos n+
        (b-1/2-slope E b*β)*Real.sin n := by
  have hg := geometry hEs hEy hEa hb
  have hd := derivative hEs hEy hb
  have ha : 1/2<primary E b := by linarith [hg.2.2.2]
  have hdenβ := OutsideE.contactSpeed_positive ha hb.1 hd.2.1 hp
  have hW := OutsideE.de3_contact_rate_positive (a := primary E b) hb.1 hd.2 hp hn
    (Or.inr (radial_identity hEs hEy hb))
  obtain ⟨β₀,hβ₀⟩ : ∃ β₀,β₀=OutsideE.contactSpeed (primary E b) b (slope E b) p := ⟨_,rfl⟩
  rw [← hβ₀] at hW hdenβ
  obtain ⟨W,hWdef⟩ : ∃ W,W=(primary E b+1/2-β₀)*Real.cos n+
      (b-1/2-slope E b*β₀)*Real.sin n := ⟨_,rfl⟩
  rw [← hWdef] at hW
  obtain ⟨c,hcdef⟩ : ∃ c,c=Real.cos n+slope E b*Real.sin n := ⟨_,rfl⟩
  have hc : 0<c := by
    have ht := transport_trig hn
    rw [hcdef]
    exact add_pos_of_pos_of_nonneg (by linarith [ht.1]) (mul_nonneg hd.2.1 ht.2.2.1)
  obtain ⟨η,hηdef⟩ : ∃ η,η=W/(2*c) := ⟨_,rfl⟩
  have hη : 0<η := by rw [hηdef]; exact div_pos hW (mul_pos (by norm_num) hc)
  have hηc : η*c=W/2 := by rw [hηdef]; field_simp
  refine ⟨β₀+η,add_pos hdenβ.2 hη,?_,?_⟩
  · have hβc : β₀*(Real.cos p+slope E b*Real.sin p)=
        (primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p := by
      rw [hβ₀,OutsideE.contactSpeed,div_mul_cancel₀ _ hdenβ.1.ne']
    have heq : (β₀+η)*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p)=
        η*(Real.cos p+slope E b*Real.sin p) := by
      rw [add_mul,hβc]
      ring
    rw [heq]
    exact mul_pos hη hdenβ.1
  · have heq : (primary E b+1/2-(β₀+η))*Real.cos n+
        (b-1/2-slope E b*(β₀+η))*Real.sin n=W-η*c := by
      rw [hWdef,hcdef]
      ring
    rw [heq,hηc]
    linarith

theorem eh_direction_derivative {E H : SignedPoint} {p b β : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => eh E H (p-τ) (b-β*τ))
      (β*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 :=
    (((hasDerivAt_id' (0:ℝ)).const_mul β).const_sub b).congr_deriv (by ring)
  have hpder : HasDerivAt (fun τ : ℝ => p-τ) (-1) 0 :=
    (hasDerivAt_id' (0:ℝ)).const_sub p
  have ha0 : HasDerivAt (primary E) (-slope E b) (b-β*0) := by
    simpa using (derivative hEs hEy hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin (p-0)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos (p-0)).comp 0 hpder
  have F : HasDerivAt (fun τ => eh E H (p-τ) (b-β*τ))
      (0+(-slope E b*-β*Real.sin (p-0)+(primary E (b-β*0)-1/2)*(Real.cos (p-0)*-1))-
        (-β*Real.cos (p-0)+(b-β*0+1/2)*(-Real.sin (p-0)*-1))) 0 :=
    ((hasDerivAt_const (0:ℝ) (H.a-1/2)).fun_add
      ((hader.sub_const (1/2)).fun_mul hsder)).fun_sub
        ((hbder.add_const (1/2)).fun_mul hcder)
  convert F using 1
  simp only [sub_zero,mul_zero]
  ring

theorem de_direction_derivative {E D : SignedPoint} {α p b β : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => de E D α (p-τ) (b-β*τ))
      ((primary E b+1/2-β)*Real.cos (p-α)+
        (b-1/2-slope E b*β)*Real.sin (p-α)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 :=
    (((hasDerivAt_id' (0:ℝ)).const_mul β).const_sub b).congr_deriv (by ring)
  have hpder : HasDerivAt (fun τ : ℝ => (p-τ)-α) (-1) 0 :=
    ((hasDerivAt_id' (0:ℝ)).const_sub p).sub_const α
  have ha0 : HasDerivAt (primary E) (-slope E b) (b-β*0) := by
    simpa using (derivative hEs hEy hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin ((p-0)-α)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos ((p-0)-α)).comp 0 hpder
  have F : HasDerivAt (fun τ => de E D α (p-τ) (b-β*τ))
      (0-((-slope E b*-β)*Real.sin ((p-0)-α)+(primary E (b-β*0)+1/2)*
          (Real.cos ((p-0)-α)*-1))+
        (-β*Real.cos ((p-0)-α)+(b-β*0-1/2)*(-Real.sin ((p-0)-α)*-1))) 0 :=
    ((hasDerivAt_const (0:ℝ) (D.a-1/2)).fun_sub
      ((hader.add_const (1/2)).fun_mul hsder)).fun_add
        ((hbder.sub_const (1/2)).fun_mul hcder)
  convert F using 1
  simp only [sub_zero,mul_zero]
  ring

/-- A genuine small movement makes both original primary margins
strictly larger than their common retained reserve.  The speed is
constructed from the circle identity above, not supplied as a premise. -/
theorem improving_shift {E D H : SignedPoint} {α p b η : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 7/12<E.a)
    (hα : 0≤α) (hp : α<p) (hpu : p≤7/10)
    (hb : b∈Ioc 0 (-E.y)) (hEH : η≤eh E H p b) (hDE : η≤de E D α p b) :
    ∃p' b', p'∈Ioo α p ∧ b'∈Ioc 0 (-E.y) ∧
      η<eh E H p' b' ∧ η<de E D α p' b' := by
  have hbcc : b∈Icc 0 (-E.y) := ⟨hb.1.le,hb.2⟩
  have hpdom : p∈Icc 0 (7/10:ℝ) := ⟨by linarith,hpu⟩
  have hndom : p-α∈Icc 0 (7/10:ℝ) := ⟨by linarith,by linarith⟩
  obtain ⟨β,hβ,hErate,hDrate⟩ := improving_speed hEs hEy hEa hbcc hpdom hndom
  have hEd := eh_direction_derivative (H := H) (p := p) (β := β) hEs hEy hbcc
  have hDd := de_direction_derivative (D := D) (α := α) (p := p) (β := β) hEs hEy hbcc
  have hEevent : ∀ᶠτ in 𝓝[>] (0:ℝ), η<eh E H (p-τ) (b-β*τ) :=
    (NegativeContact.eventually_right_gt hEd hErate).mono (by
      intro τ hτ
      exact hEH.trans_lt (by simpa using hτ))
  have hDevent : ∀ᶠτ in 𝓝[>] (0:ℝ), η<de E D α (p-τ) (b-β*τ) :=
    (NegativeContact.eventually_right_gt hDd hDrate).mono (by
      intro τ hτ
      exact hDE.trans_lt (by simpa using hτ))
  have hangle : ∀ᶠτ in 𝓝[>] (0:ℝ), τ<p-α :=
    (eventually_lt_nhds (sub_pos.mpr hp)).filter_mono nhdsWithin_le_nhds
  have hcb : ContinuousAt (fun τ : ℝ => b-β*τ) 0 := by fun_prop
  have hval : (0:ℝ)<(fun τ : ℝ => b-β*τ) 0 := by simpa using hb.1
  have hfloor : ∀ᶠτ in 𝓝[>] (0:ℝ), 0<b-β*τ :=
    (hcb.tendsto.eventually (eventually_gt_nhds hval)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ,hτ,hangle,hfloor,hEevent,hDevent⟩ :=
    ((eventually_mem_nhdsWithin (s := Ioi (0:ℝ)) (a := 0)).and
      (hangle.and (hfloor.and (hEevent.and hDevent)))).exists
  have hτ0 : 0<τ := hτ
  have hprod := mul_pos hβ hτ0
  exact ⟨p-τ,b-β*τ,⟨by linarith,by linarith⟩,
    ⟨hfloor,by linarith [hb.2]⟩,hEevent,hDevent⟩

end SquaresInCircles.Eight.TableFree.OriginalECircle
