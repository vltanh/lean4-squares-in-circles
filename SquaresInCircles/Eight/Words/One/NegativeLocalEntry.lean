module

public import SquaresInCircles.Eight.Words.One.NegativeBarrierEndpoints
public import SquaresInCircles.Eight.Words.One.NegativeComposition
public import SquaresInCircles.Eight.Words.One.NegativeCoupledEndpoint
public import SquaresInCircles.Eight.Words.One.NegativeEAlignment
public import SquaresInCircles.Eight.Words.One.NegativePositiveDE

/-!
# Eight squares: exhaustive original-E positions in the one-negative BT construction

The original E may lie below, at or above D, and its EH error may have either sign. The same-q
construction returns either a hard endpoint with a strict loss on the original D or a negative-T
barrier state (`Source.full_aligned_endpoint_or_barrier`,
`Source.one_negative_endpoint_or_barrier`). H is arbitrary, and the true-core hypotheses are
kept through every stage.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace DirectNegativeT
open AlignedNegative PrimaryCap

theorem Source.full_aligned_endpoint_or_barrier {q t h : ℝ} {D T B E H : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q)
    (hEs : E.Sorted) (hEr : E.Boundary q) (hEy : E.y≤0)
    (hspan : h+t∈Ioc 0 (11/50 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E 0 jDE) (hEH : quarterFeasible E H (h+t) jEH) :
    Nonempty (LocalEndpoint I E H (-t) h jDE jEH) ∨
      Nonempty (LocalBarrier I E H (-t) h jDE jEH) := by
  obtain ⟨kind,J⟩ := FullE.arcSource_of_boundary hEs hEy hEr
  obtain ⟨O⟩ := I.full_coupled_stop J hqL hqU hHs hHcore hHc hspan
    jDE jEH hjDE hjEH hDE hEH
  by_cases hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0
  · exact Or.inl (O.hard_endpoint J hqL hqU hjDE hjEH hDE hhard)
  · exact Or.inr ⟨O.local_barrier J hqL hqU hjDE hjEH hhard⟩

theorem Source.one_negative_endpoint_or_barrier {q t e h : ℝ} {D T B E H : SignedPoint}
    (I : Source q t D T B) (hqL : qLow≤q) (hqU : q≤qCap)
    (hHs : H.Sorted) (hHcore : H.AvoidsCore) (hHc : H.Contained q) (hHy : 0≤H.y)
    (hEs : E.Sorted) (hEc : E.Contained q) (hEcore : E.AvoidsCore)
    (hEr : E.Boundary q) (hEy : E.y≤0)
    (hDEwidth : |e+t|≤7/10) (hEHwidth : |h-e|≤7/10)
    (hspan : h+t∈Ioc 0 (11/50 : ℝ))
    (jDE jEH : Fin 4) (hjDE : jDE=2 ∨ jDE=3) (hjEH : jEH=0 ∨ jEH=1)
    (hDE : quarterFeasible D E (e+t) jDE) (hEH : quarterFeasible E H (h-e) jEH) :
    Nonempty (LocalEndpoint I E H e h jDE jEH) ∨
      Nonempty (LocalBarrier I E H e h jDE jEH) := by
  have hDs : D.Sorted := by simpa using I.H_sorted
  have hcuts := I.cuts hqU
  have hDy : 211/250< -D.y := hcuts.2.2.2.1
  have hDa : D.a<1 := hcuts.2.2.2.2.1
  rcases lt_trichotomy (e+t) 0 with hbelow | haligned | habove
  · let n := -(e+t)
    have hn : n∈Ioc 0 (7/10 : ℝ) := by
      dsimp [n]
      constructor <;> linarith [(abs_le.mp hDEwidth).1]
    have hp : h-e∈Ioc 0 (7/10 : ℝ) := by
      constructor <;> linarith [hspan.1,(abs_le.mp hEHwidth).2]
    have hnp : n<h-e := by dsimp [n]; linarith [hspan.1]
    obtain ⟨O⟩ := FullE.alignment_endpoint_of_order hqL hqU hHs hHcore hHc hHy
      hDy hDs hDa hEs hEy hEr hn hp hnp jDE jEH hjDE hjEH
      (by simpa [n] using hDE) hEH
    have hEHaligned : quarterFeasible O.point H (h+t) jEH := by
      have heq : (h-e)-n=h+t := by dsimp [n]; ring
      simpa only [heq] using O.EH
    rcases I.full_aligned_endpoint_or_barrier hqL hqU hHs hHcore hHc
      O.sorted O.radial O.nonpos hspan jDE jEH hjDE hjEH O.DE hEHaligned with hK | hK
    · obtain ⟨K⟩ := hK
      exact Or.inl ⟨K.prepend_E_motion (by linarith) O.circle_nonincrease⟩
    · obtain ⟨K⟩ := hK
      exact Or.inr ⟨K.prepend_E_motion (by linarith) O.circle_nonincrease⟩
  · have heq : e= -t := by linarith
    have hDEaligned : quarterFeasible D E 0 jDE := by simpa [haligned] using hDE
    have hEHaligned : quarterFeasible E H (h+t) jEH := by simpa [heq] using hEH
    simpa only [heq] using I.full_aligned_endpoint_or_barrier hqL hqU hHs hHcore hHc
      hEs hEr hEy hspan jDE jEH hjDE hjEH hDEaligned hEHaligned
  · have hd : e+t∈Ioc 0 (7/10 : ℝ) := ⟨habove,(abs_le.mp hDEwidth).2⟩
    obtain ⟨O⟩ := I.positive_de_stop_full hqL hqU hEs hEc hEcore hEr hEy hd jDE hjDE hDE
    by_cases hhard : quarterFeasible (point (B.a-1/2) O.angle) B.reflect (-O.angle) 0
    · exact Or.inl (O.hard_endpoint hqU hEs hEc hEcore hEr hEy hjDE hEH hhard)
    · by_cases hbad : h+O.angle≤0
      · exact Or.inr ⟨O.local_barrier hqU hEs hEc hEcore hEr hEy hjDE hEH hhard hbad⟩
      · have hal : e+O.angle=0 := O.terminal.resolve_left hhard
        have hmpos : 0<O.angle := by
          apply lt_of_le_of_ne O.angle_mem.1
          intro hzero
          have hprimary : quarterFeasible (point (B.a-1/2) 0) B.reflect 0 1 := by
            have h := (actual_primary_contact
              (show B.reflect.a=(B.a-1/2)+1/2 by dsimp [SignedPoint.reflect]; ring)
              (show (0:ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)).ge
            rw [neg_zero] at h
            exact h
          apply hhard
          rw [← hzero,neg_zero]
          exact (quarter_low_tie (point (B.a-1/2) 0) B.reflect).2 hprimary
        let D₁ := Dpath D.circle (B.a-1/2) O.angle
        let T₁ := Tpath (B.a-1/2) O.angle
        have hg := I.path_data hqU O.angle_mem
        have I₁ : Source q O.angle D₁ T₁ B := by
          have h := I.atAngle hqU ⟨hmpos,O.angle_mem.2.le⟩ hhard
          simp only [Source,D₁,T₁,Dpath,Tpath,SignedPoint.reflect_reflect]
          rw [SignedPoint.reflect_circle] at h
          exact h
        have hDEaligned : quarterFeasible D₁ E 0 jDE := by
          have hh := O.mixed_strict.le
          rw [positiveDESlack_actual E jDE hjDE
            ⟨O.error_mem.1,by linarith [O.error_mem.2]⟩] at hh
          have h := sub_nonneg.mp hh
          rw [hal] at h
          exact h
        have heq : e= -O.angle := by linarith
        have hα : h+O.angle∈Ioc 0 (11/50 : ℝ) := by
          constructor <;> linarith [O.angle_mem.2,hspan.2]
        have hEHaligned : quarterFeasible E H (h+O.angle) jEH := by simpa [heq] using hEH
        rcases I₁.full_aligned_endpoint_or_barrier hqL hqU hHs hHcore hHc
          hEs hEr hEy hα jDE jEH hjDE hjEH hDEaligned hEHaligned with hK | hK
        · obtain ⟨K⟩ := hK
          have K' : LocalEndpoint I₁ E H e h jDE jEH := by rw [← heq] at K; exact K
          exact Or.inl ⟨LocalEndpoint.prepend_contact I K' O.angle_mem.2 hg.D_circle hg.D_tangent.le⟩
        · obtain ⟨K⟩ := hK
          have K' : LocalBarrier I₁ E H e h jDE jEH := by rw [← heq] at K; exact K
          exact Or.inr ⟨LocalBarrier.prepend_contact I K' O.angle_mem.2 hg.D_circle⟩

end DirectNegativeT
end SquaresInCircles.Eight
