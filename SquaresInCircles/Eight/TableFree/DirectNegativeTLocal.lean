module

public import SquaresInCircles.Eight.TableFree.DirectNegativeTEndpoint

/-!
# Complete direct negative-T local transport with E's original sign

Uncompiled source. The three actual positions of E relative to D are
exhausted. E below D reaches actual alignment on its radial arc; E above D
reaches BT2 or actual alignment on D's own circle; the aligned contact then
reaches BT2 with a paid strict D-circle loss. H and B are never changed.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace DirectNegativeT
open AlignedNegative PrimaryCap OutsideE DirectNegativeE

theorem original_eh_error_positive {H E : SignedPoint} {p : ℝ} {j : Fin 4}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hHa : H.a<1)
    (hEs : E.Sorted) (hEy : E.y≤0) (hp : |p|≤7/10)
    (hj : j=0 ∨ j=1) (hf : quarterFeasible E H p j) : 0<p := by
  by_contra! hnonpos
  have hn : -p∈Icc 0 (7/10 : ℝ) := by constructor <;> linarith [(abs_le.mp hp).1]
  have hsin : Real.sin p≤0 := by
    have hh := (transport_trig hn).2.2.1
    rwa [Real.sin_neg,neg_nonneg] at hh
  have hcos : 0<Real.cos p := transport_cos_pos hp
  have hwidth := edgeWidth_ge_one p
  rcases hj with rfl | rfl
  · have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one p) hHs.1.le
    have hs := mul_nonpos_of_nonneg_of_nonpos hHy hsin
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_zero] at hf
    linarith
  · have hs := mul_nonpos_of_nonneg_of_nonpos hEs.1.le hsin
    have hy := mul_nonpos_of_nonpos_of_nonneg hEy hcos.le
    simp only [quarterFeasible,quarterProjection,Matrix.cons_val_one] at hf
    linarith

/-- The original E position, either mixed error sign, and all four mixed
owner combinations are included. The near-H cuts and H--D span remain
explicit source hypotheses; no global owner-exclusion theorem is presumed. -/
theorem Source.direct_endpoint {q t e h : ℝ} {D T B E H : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHy : 211/250<H.y ∧ H.y<9/10) (hHs : H.Sorted) (hHa : H.a<1)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hDEwidth : |e+t|≤7/10) (hEHwidth : |h-e|≤7/10)
    (hspan : h+t<21/100)
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (e+t) jDE) (hEH : quarterFeasible E H (h-e) jEH) :
    Nonempty (LocalEndpoint I E H e h jDE jEH) := by
  have hp : 0<h-e := original_eh_error_positive hHs (by linarith [hHy.1]) hHa
    hEs hEy hEHwidth hjEH hEH
  have hpwide : h-e∈Ioc 0 (7/10 : ℝ) := ⟨hp,(abs_le.mp hEHwidth).2⟩
  have hDs : D.Sorted := by simpa using I.H_sorted
  have hcuts := I.cuts hqU
  have hDy : 211/250< -D.y := hcuts.2.2.2.1
  have hDa : D.a<1 := hcuts.2.2.2.2.1
  rcases lt_trichotomy (e+t) 0 with hbelow | haligned | habove
  · let n := -(e+t)
    have hn : n∈Ioc 0 (7/10 : ℝ) := by
      dsimp [n]
      constructor <;> linarith [(abs_le.mp hDEwidth).1]
    obtain ⟨O⟩ := DirectNegativeE.alignment_endpoint hqL hqU hHy hHs hHa hDy hDs hDa
      hEs hEy hEr hn hpwide jDE jEH hjDE hjEH (by simpa [n] using hDE) hEH
    have hα : h+t∈Ioc 0 (21/100 : ℝ) := by
      refine ⟨?_,hspan.le⟩
      have hh := O.positive_span
      dsimp [n] at hh
      linarith
    have hEHaligned : quarterFeasible O.point H (h+t) jEH := by
      have heq : (h-e)-n=h+t := by dsimp [n]; ring
      simpa only [heq] using O.EH
    obtain ⟨kind,J⟩ := arcSource_of_owner O.sorted O.nonpos O.radial hHy hHs hHa hjEH
      ⟨hα.1.le,by linarith [hα.2]⟩ hEHaligned
    obtain ⟨S⟩ := I.coupled_stop J hqL hqU hHy hHs hHa hα jDE jEH hjDE hjEH O.DE hEHaligned
    obtain ⟨K⟩ := S.hard_endpoint J hqL hqU hjDE hjEH O.DE
    exact ⟨{
      angle := K.angle
      angle_mem := K.angle_mem
      Dpoint := K.Dpoint
      Tpoint := K.Tpoint
      Epoint := K.Epoint
      Etheta := K.Etheta
      E_frame := by
        right
        rcases K.E_frame with heq | hrange
        · rw [heq]
          exact ⟨le_rfl,by linarith [I.tilt_pos]⟩
        · exact hrange
      E_advance := (show e≤ -t by linarith).trans K.E_advance
      D_sorted := K.D_sorted
      T_sorted := K.T_sorted
      E_sorted := K.E_sorted
      D_core := K.D_core
      T_core := K.T_core
      E_core := K.E_core
      D_circle_loss := K.D_circle_loss
      T_inside := K.T_inside
      E_contained := K.E_contained
      E_radial := K.E_radial
      E_circle_nonincrease := K.E_circle_nonincrease.trans O.circle_nonincrease
      D_negative := K.D_negative
      T_positive := K.T_positive
      E_nonpos := K.E_nonpos
      D_nondiagonal := K.D_nondiagonal
      T_nondiagonal := K.T_nondiagonal
      D_tangent_decreases := K.D_tangent_decreases
      TD0 := K.TD0
      TD2 := K.TD2
      BT2 := K.BT2
      DE := K.DE
      EH := K.EH }⟩
  · have heq : e= -t := by linarith
    have hα : h+t∈Ioc 0 (21/100 : ℝ) := ⟨by linarith,hspan.le⟩
    obtain ⟨kind,J⟩ := arcSource_of_owner hEs hEy hEr hHy hHs hHa hjEH
      ⟨hp.le,hpwide.2⟩ hEH
    have hDEaligned : quarterFeasible D E 0 jDE := by simpa [haligned] using hDE
    have hEHaligned : quarterFeasible E H (h+t) jEH := by simpa [heq] using hEH
    obtain ⟨O⟩ := I.coupled_stop J hqL hqU hHy hHs hHa hα jDE jEH hjDE hjEH
      hDEaligned hEHaligned
    simpa only [heq] using O.hard_endpoint J hqL hqU hjDE hjEH hDEaligned
  · have hd : e+t∈Ioc 0 (21/100 : ℝ) := ⟨habove,by linarith⟩
    obtain ⟨O⟩ := I.positive_de_stop hqU hEs hEc hEcore hEy hd jDE hjDE hDE
    by_cases hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0
    · exact O.hard_endpoint hqU hEs hEc hEcore hEr hEy hjDE hEH hhard
    · have hal : e+O.angle=0 := O.terminal.resolve_left hhard
      have hmpos : 0<O.angle := by
        apply lt_of_le_of_ne O.angle_mem.1
        intro hzero
        have hprimary : quarterFeasible (point (B.a-1/2) 0) B.reflect 0 1 := by
          simpa using (actual_primary_contact
            (show B.reflect.a=(B.a-1/2)+1/2 by dsimp [SignedPoint.reflect]; ring)
            (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
        exact hhard (by simpa [← hzero] using (quarter_low_tie (point (B.a-1/2) 0) B.reflect).2 hprimary)
      let D₁ := Dpath D.circle (B.a-1/2) O.angle
      let T₁ := Tpath (B.a-1/2) O.angle
      have hg := I.path_data hqU O.angle_mem
      let I₁ : Source q O.angle D₁ T₁ B := by
        simpa [D₁,T₁,Dpath,Tpath] using I.atAngle hqU ⟨hmpos,O.angle_mem.2.le⟩ hhard
      have hDEaligned : quarterFeasible D₁ E 0 jDE := by
        have hh := O.mixed_strict.le
        rw [positiveDESlack_actual E jDE hjDE
          ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
        simpa [D₁,hal] using sub_nonneg.mp hh
      have heq : e= -O.angle := by linarith
      have hα : h+O.angle∈Ioc 0 (21/100 : ℝ) := by
        constructor <;> linarith [O.angle_mem.2]
      have hEHaligned : quarterFeasible E H (h+O.angle) jEH := by simpa [heq] using hEH
      obtain ⟨kind,J⟩ := arcSource_of_owner hEs hEy hEr hHy hHs hHa hjEH
        ⟨hp.le,hpwide.2⟩ hEH
      obtain ⟨S⟩ := I₁.coupled_stop J hqL hqU hHy hHs hHa hα jDE jEH hjDE hjEH
        hDEaligned hEHaligned
      obtain ⟨K⟩ := S.hard_endpoint J hqL hqU hjDE hjEH hDEaligned
      exact ⟨{
        angle := K.angle
        angle_mem := ⟨K.angle_mem.1,K.angle_mem.2.trans O.angle_mem.2⟩
        Dpoint := K.Dpoint
        Tpoint := K.Tpoint
        Epoint := K.Epoint
        Etheta := K.Etheta
        E_frame := by
          rcases K.E_frame with hh | hh
          · exact Or.inl (hh.trans heq.symm)
          · exact Or.inr ⟨by linarith [hh.1,O.angle_mem.2],hh.2⟩
        E_advance := by rw [heq]; exact K.E_advance
        D_sorted := K.D_sorted
        T_sorted := K.T_sorted
        E_sorted := K.E_sorted
        D_core := K.D_core
        T_core := K.T_core
        E_core := K.E_core
        D_circle_loss := K.D_circle_loss.trans_eq hg.D_circle
        T_inside := K.T_inside
        E_contained := K.E_contained
        E_radial := K.E_radial
        E_circle_nonincrease := K.E_circle_nonincrease
        D_negative := K.D_negative
        T_positive := K.T_positive
        E_nonpos := K.E_nonpos
        D_nondiagonal := K.D_nondiagonal
        T_nondiagonal := K.T_nondiagonal
        D_tangent_decreases := K.D_tangent_decreases.trans hg.D_tangent
        TD0 := K.TD0
        TD2 := K.TD2
        BT2 := K.BT2
        DE := K.DE
        EH := K.EH }⟩

end DirectNegativeT
end SquaresInCircles.Eight.TableFree
