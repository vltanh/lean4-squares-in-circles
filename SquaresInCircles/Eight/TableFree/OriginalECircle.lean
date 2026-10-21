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
    dsimp [primary,root]
    rw [heq,Real.sqrt_sq (show 0≤E.a+1/2 by linarith [hEs.1])]
    ring
  apply SignedPoint.ext
  · exact ha
  · simp [point]

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
  · dsimp [point,SignedPoint.circle,primary]
    rw [abs_neg,abs_of_nonneg hb.1]
    nlinarith [hr.2.2]

theorem continuous_primary (E : SignedPoint) : Continuous (primary E) := by
  dsimp [primary,root]
  fun_prop

theorem derivative {E : SignedPoint} {b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (primary E) (-slope E b) b ∧ 0≤slope E b ∧ slope E b≤1 := by
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
  simp [de,point,quarterProjection]
  ring

theorem improving_speed {E : SignedPoint} {p n b : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 7/12<E.a)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10:ℝ)) (hn : n∈Icc 0 (7/10:ℝ)) :
    ∃β, 0<β ∧
      0<β*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p) ∧
      0<(primary E b+1/2-β)*Real.cos n+
        (b-1/2-slope E b*β)*Real.sin n := by
  let a := primary E b
  let v := slope E b
  let β₀ := OutsideE.contactSpeed a b v p
  let c := Real.cos n+v*Real.sin n
  let W := (a+1/2-β₀)*Real.cos n+(b-1/2-v*β₀)*Real.sin n
  have hg := geometry hEs hEy hEa hb
  have hd := derivative hEs hEy hb
  have ha : 1/2<a := by dsimp [a]; linarith [hg.2.2.2]
  have hdenβ := OutsideE.contactSpeed_positive ha hb.1 hd.2.1 hp
  have hW : 0<W := OutsideE.de3_contact_rate_positive hb.1 hd.2 hp hn
    (Or.inr (radial_identity hEs hEy hb))
  have hc : 0<c := by
    have ht := transport_trig hn
    exact add_pos_of_pos_of_nonneg (by linarith [ht.1])
      (mul_nonneg hd.2.1 ht.2.2.1)
  let η := W/(2*c)
  have hη : 0<η := div_pos hW (mul_pos (by norm_num) hc)
  have hηc : η*c=W/2 := by
    dsimp [η]
    field_simp [hc.ne']
    ring
  refine ⟨β₀+η,add_pos hdenβ.2 hη,?_,?_⟩
  · have heq : (β₀+η)*(Real.cos p+v*Real.sin p)-
        ((a-1/2)*Real.cos p+(b+1/2)*Real.sin p)=
        η*(Real.cos p+v*Real.sin p) := by
      dsimp [β₀,OutsideE.contactSpeed]
      field_simp [hdenβ.1.ne']
      ring
    rw [heq]
    exact mul_pos hη hdenβ.1
  · have heq : (a+1/2-(β₀+η))*Real.cos n+
        (b-1/2-v*(β₀+η))*Real.sin n=W-η*c := by
      dsimp [W,c]
      ring
    rw [heq,hηc]
    linarith

theorem eh_direction_derivative {E H : SignedPoint} {p b β : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => eh E H (p-τ) (b-β*τ))
      (β*(Real.cos p+slope E b*Real.sin p)-
        ((primary E b-1/2)*Real.cos p+(b+1/2)*Real.sin p)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => p-τ) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub p
  have ha0 : HasDerivAt (primary E) (-slope E b) (b-β*0) := by
    simpa using (derivative hEs hEy hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin (p-0)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos (p-0)).comp 0 hpder
  convert ((hasDerivAt_const (0:ℝ) (H.a-1/2)).add
    ((hader.sub_const (1/2)).mul hsder)).sub
      ((hbder.add_const (1/2)).mul hcder) using 1 <;> simp [eh] <;> ring

theorem de_direction_derivative {E D : SignedPoint} {α p b β : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => de E D α (p-τ) (b-β*τ))
      ((primary E b+1/2-β)*Real.cos (p-α)+
        (b-1/2-slope E b*β)*Real.sin (p-α)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => (p-τ)-α) (-1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_sub p).sub_const α
  have ha0 : HasDerivAt (primary E) (-slope E b) (b-β*0) := by
    simpa using (derivative hEs hEy hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin ((p-0)-α)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos ((p-0)-α)).comp 0 hpder
  convert ((hasDerivAt_const (0:ℝ) (D.a-1/2)).sub
    ((hader.add_const (1/2)).mul hsder)).add
      ((hbder.sub_const (1/2)).mul hcder) using 1 <;> simp [de] <;> ring

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
    (self_mem_nhdsWithin.and (hangle.and (hfloor.and (hEevent.and hDevent)))).exists
  have hprod := mul_pos hβ (show 0<τ from hτ)
  exact ⟨p-τ,b-β*τ,⟨by linarith,by linarith⟩,
    ⟨hfloor,by linarith [hb.2]⟩,hEevent,hDevent⟩

end SquaresInCircles.Eight.TableFree.OriginalECircle
