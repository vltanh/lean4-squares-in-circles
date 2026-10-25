module

public import SquaresInCircles.Eight.TableFree.FullEContact

/-!
# Strict directions for all original negative-DE and positive-EH owners

Uncompiled source. The full true-core and actual outer arcs have explicit
derivatives. For every retained weak owner pair a single positive radial
speed makes both physical margins strictly increase as E advances.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace FullE
open OutsideE (contactSpeed contactSpeed_positive)
open DirectNegativeE (lowSlack lowAngularRate lowSpeed)

theorem ArcSource.de3_improving_speed {q b p n : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y))
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    ∃ β, 0<β ∧
      0<β*(Real.cos p+kind.slope q b*Real.sin p)-
        ((kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p) ∧
      0<(kind.primary q b+1/2-β)*Real.cos n+
        (b-1/2-kind.slope q b*β)*Real.sin n := by
  have hg := I.geometry hq hb
  have hd := I.derivative hq hb
  have hdenβ := contactSpeed_positive hg.2.2.2.2.2.1 hb.1 hd.2.1 hp
  have hW := de3_contact_rate_positive hb.1 hd.2 hp hn (I.radial_identity hq hb)
  have hc : 0<Real.cos n+kind.slope q b*Real.sin n := by
    have ht := transport_trig hn
    exact add_pos_of_pos_of_nonneg (by linarith [ht.1]) (mul_nonneg hd.2.1 ht.2.2.1)
  have hS : contactSpeed (kind.primary q b) b (kind.slope q b) p*
      (Real.cos p+kind.slope q b*Real.sin p)=
      (kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p :=
    div_mul_cancel₀ _ hdenβ.1.ne'
  set a := kind.primary q b with ha
  set v := kind.slope q b with hv
  set β₀ := contactSpeed a b v p with hβ₀
  set W := (a+1/2-β₀)*Real.cos n+(b-1/2-v*β₀)*Real.sin n with hWdef
  set c := Real.cos n+v*Real.sin n with hcdef
  set η := W/(2*c) with hηdef
  have hη : 0<η := div_pos hW (mul_pos (by norm_num) hc)
  have hηc : η*c=W/2 := by rw [hηdef]; field_simp
  refine ⟨β₀+η,add_pos hdenβ.2 hη,?_,?_⟩
  · have heq : (β₀+η)*(Real.cos p+v*Real.sin p)-
        ((a-1/2)*Real.cos p+(b+1/2)*Real.sin p)=
        η*(Real.cos p+v*Real.sin p) := by
      linear_combination hS
    rw [heq]
    exact mul_pos hη hdenβ.1
  · have heq : (a+1/2-(β₀+η))*Real.cos n+
        (b-1/2-v*(β₀+η))*Real.sin n=W-η*c := by
      rw [hWdef,hcdef]
      ring
    rw [heq,hηc]
    linarith

theorem ArcSource.high_direction_derivative {q b p β : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind)
    (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => highSlack kind q H (p-τ) (b-β*τ))
      (β*(Real.cos p+kind.slope q b*Real.sin p)-
        ((kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => p-τ) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub p
  have ha0 : HasDerivAt (kind.primary q) (-kind.slope q b) (b-β*0) := by
    simpa using (I.derivative hq hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin (p-0)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos (p-0)).comp 0 hpder
  have h := (((hader.sub_const (1/2)).fun_mul hsder).const_add (H.a-1/2)).fun_sub
    ((hbder.add_const (1/2)).fun_mul hcder)
  exact h.congr_deriv (by simp only [Function.comp_apply,mul_zero,sub_zero]; ring)

theorem ArcSource.de3_direction_derivative {q α b p β : ℝ} {E D : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind)
    (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => de3Slack kind q α D (p-τ) (b-β*τ))
      ((kind.primary q b+1/2-β)*Real.cos (p-α)+
        (b-1/2-kind.slope q b*β)*Real.sin (p-α)) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => (p-τ)-α) (-1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_sub p).sub_const α
  have ha0 : HasDerivAt (kind.primary q) (-kind.slope q b) (b-β*0) := by
    simpa using (I.derivative hq hb).1
  have hader := ha0.comp 0 hbder
  have hsder := (Real.hasDerivAt_sin ((p-0)-α)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos ((p-0)-α)).comp 0 hpder
  have h := (((hader.add_const (1/2)).fun_mul hsder).const_sub (D.a-1/2)).fun_add
    ((hbder.sub_const (1/2)).fun_mul hcder)
  exact h.congr_deriv (by simp only [Function.comp_apply,mul_zero,sub_zero]; ring)

theorem ArcSource.mixed_direction_derivative {q b p β : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (j : Fin 4)
    (hqL : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => mixedSlack kind q H j (p-τ) (b-β*τ))
      (mixedRate kind q H j p b β) 0 := by
  by_cases hj : j=0
  · simpa [mixedSlack,mixedRate,hj] using DirectNegativeE.low_direction_derivative H p b β
  · simpa [mixedSlack,mixedRate,hj] using I.high_direction_derivative
      (H := H) (p := p) (β := β) hqL hb

theorem ArcSource.de_direction_derivative {q α b p β : ℝ} {E D : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (j : Fin 4)
    (hqL : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => deSlack kind q α D j (p-τ) (b-β*τ))
      (deRate kind q α D j p b β) 0 := by
  by_cases hj : j=2
  · simpa [deSlack,deRate,hj] using OutsideE.de2_direction_derivative D α b p β
  · simpa [deSlack,deRate,hj] using I.de3_direction_derivative
      (D := D) (α := α) (p := p) (β := β) hqL hb

/-- A common strict direction is obtained from the actual retained EH
inequality. H is any nonnegative sorted contained core-avoiding anchor. -/
theorem ArcSource.improving_below_speed {q α b p : ℝ} {E D H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q) (hHy : 0≤H.y)
    (hDs : D.Sorted) (hDy : 211/250< -D.y)
    (hb : b∈Icc 0 (-E.y)) (hp : p∈Icc 0 (7/10 : ℝ))
    (hn : p-α∈Icc 0 (7/10 : ℝ))
    (jDE jEH : Fin 4) (hDE : jDE=2 ∨ jDE=3) (hEH : jEH=0 ∨ jEH=1)
    (hf : quarterFeasible (kind.point q b) H p jEH) :
    ∃ β, 0<β ∧ 0< mixedRate kind q H jEH p b β ∧
      0<deRate kind q α D jDE p b β := by
  let V := (D.a-1/2)*Real.sin (p-α)+(1/2-D.y)*Real.cos (p-α)
  have hV : 1249/1000<V := DirectNegativeE.high_D_rate hDs hDy hn
  have hg := I.geometry hqL hb
  have hv := (I.derivative hqL hb).2
  rcases hEH with rfl | rfl
  · let β₀ := lowSpeed H p
    have hβ := lowSpeed_bounds hHs hHcore hHc hqU hp
    rcases hDE with rfl | rfl
    · refine ⟨(β₀+V)/2,by dsimp [β₀]; linarith [hβ.1],?_,?_⟩
      · simp only [mixedRate,ite_true]
        dsimp [β₀]
        linarith [hβ.2.1,hβ.2.2]
      · simp only [deRate,ite_true]
        dsimp [V,β₀] at *
        linarith [hβ.2.2]
    · let c := Real.cos (p-α)+kind.slope q b*Real.sin (p-α)
      let W := (kind.primary q b+1/2-β₀)*Real.cos (p-α)+
        (b-1/2-kind.slope q b*β₀)*Real.sin (p-α)
      have hW : 0<W := I.low_de3_rate hqL hqU hb hHs hHcore hHc hHy hp hn hf
      have hc : 0<c := by
        have ht := transport_trig hn
        exact add_pos_of_pos_of_nonneg (by linarith [ht.1])
          (mul_nonneg hv.1 ht.2.2.1)
      let η := W/(2*c)
      have hη : 0<η := div_pos hW (mul_pos (by norm_num) hc)
      have hηc : η*c=W/2 := by dsimp only [η]; field_simp
      refine ⟨β₀+η,by dsimp [β₀]; linarith [hβ.1],?_,?_⟩
      · simp only [mixedRate,ite_true]
        dsimp [β₀]
        linarith [hβ.2.1]
      · norm_num only [deRate,show (3:Fin 4)≠2 by decide,ite_false]
        have heq : (kind.primary q b+1/2-(β₀+η))*Real.cos (p-α)+
            (b-1/2-kind.slope q b*(β₀+η))*Real.sin (p-α)=W-η*c := by
          dsimp [W,c]; ring
        rw [heq,hηc]
        linarith
  · rcases hDE with rfl | rfl
    · let β₀ := contactSpeed (kind.primary q b) b (kind.slope q b) p
      let den := Real.cos p+kind.slope q b*Real.sin p
      let U := (kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p
      have hβ := contactSpeed_positive hg.2.2.2.2.2.1 hb.1 hv.1 hp
      have hβup : β₀<47/40 := I.high_speed_bound hqL hqU hb hp
      have hid : β₀*den=U := div_mul_cancel₀ _ hβ.1.ne'
      have hprod := mul_pos (show 0<(β₀+V)/2-β₀ by linarith) hβ.1
      refine ⟨(β₀+V)/2,by linarith [hβ.2],?_,?_⟩
      · norm_num only [mixedRate,show (1:Fin 4)≠0 by decide,ite_false]
        change 0<(β₀+V)/2*den-U
        nlinarith
      · simp only [deRate,ite_true]
        change 0<V-(β₀+V)/2
        linarith
    · obtain ⟨β,hβ,hEH,hDE⟩ := I.de3_improving_speed hqL hb hp hn
      exact ⟨β,hβ,by simpa [mixedRate] using hEH,by simpa [deRate] using hDE⟩

end FullE
end SquaresInCircles.Eight.TableFree
