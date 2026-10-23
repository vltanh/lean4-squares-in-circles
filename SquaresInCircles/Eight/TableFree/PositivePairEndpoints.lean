module

public import SquaresInCircles.Eight.TableFree.ZeroTangentPrimary
public import SquaresInCircles.Eight.TableFree.NecessaryCycle

/-!
# Complete nonnegative-error primary-pair endpoints

Uncompiled draft. The only remaining local exception is an actual positive
nearest-axis tie. The later global word theorem supplies its exclusion.
The zero-tangent join has already been eliminated by an actual same-radius
BT alignment with strict TD slack. There is no root search or interval grid.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace PairedPrimary

structure Endpoint (q B D t : ℝ) where
  point : SignedPoint
  firstError : ℝ
  first_mem : firstError∈Icc 0 t
  sorted : point.Sorted
  outer : point.Outer q
  avoids_core : point.AvoidsCore
  first_feasible : edgeWidth firstError≤
    B+point.a*Real.sin firstError-point.y*Real.cos firstError
  second_feasible : edgeWidth (t-firstError)≤
    point.a*Real.sin (t-firstError)+point.y*Real.cos (t-firstError)+D
  endpoint : firstError=0 ∨ firstError=t ∨ point.y=point.a

/-- The original pair has arbitrary signed tangent and radial kind. Only
its two actual weak inequalities and squared containment are used. -/
theorem nonnegative_pair_endpoint {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (hD : D≤diagonalCoordinate q)
    (hu : 0≤u) (hv : 0≤v) (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hs : p.Sorted) (hc : p.Contained q)
    (h₁ : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (h₂ : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    Nonempty (Endpoint q B D (u+v)) := by
  obtain ⟨hyp,hcp,hdp⟩ := outerization_preserves_pair hqL hs hc
    ⟨hu,by linarith⟩ ⟨hv,by linarith⟩ h₁ h₂
  obtain ⟨u',y,hu',hy,hf,hg,hcases,hcontact⟩ := intrinsic_endpoint
    hqL hqU hB ⟨ht0,ht⟩ ⟨hu,by linarith⟩ hyp hcp hdp
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hqL hy
  have hfirst : edgeWidth u'≤B+(arc q y).a*Real.sin u'-y*Real.cos u' := by
    dsimp [contact] at hf
    linarith
  have hsecond : edgeWidth (u+v-u')≤
      (arc q y).a*Real.sin (u+v-u')+y*Real.cos (u+v-u')+D := by
    dsimp [required] at hg
    linarith
  by_cases he0 : u'=0
  · exact ⟨⟨arc q y,u',hu',hps,hpo,hpc,hfirst,hsecond,Or.inl he0⟩⟩
  by_cases het : u'=u+v
  · exact ⟨⟨arc q y,u',hu',hps,hpo,hpc,hfirst,hsecond,Or.inr (Or.inl het)⟩⟩
  rcases hcases with h | h | h | h
  · exact (he0 h).elim
  · exact (het h).elim
  · subst y
    have hu0 : 0<u' := lt_of_le_of_ne hu'.1 (Ne.symm he0)
    have hv0 : 0<u+v-u' := by
      have hlt := lt_of_le_of_ne hu'.2 het
      linarith
    have hc0 : contact q B u' 0=0 := by
      rcases hcontact with hh | hh
      · have hd := (uniform_circle_reserves hqL hqU).1
        linarith
      · exact hh
    have hr := zero_tangent_alignment hqL hqU hB.1 hD hu0 hv0
      (by linarith) hc0 (by simpa using hg)
    obtain ⟨hss,hoo,hcc,hyy,hbt,htd⟩ := hr
    refine ⟨⟨arc q (B-1),0,⟨le_rfl,ht0.le⟩,hss,hoo,hcc,?_,?_,Or.inl rfl⟩⟩
    · simpa using hbt.ge
    · simpa using htd.le
  · have ha := (arc_diagonal hqL).1
    refine ⟨⟨arc q y,u',hu',hps,hpo,hpc,hfirst,hsecond,Or.inr (Or.inr ?_)⟩⟩
    simpa [h,arc,SignedPoint.outerAt] using ha.symm

/-- Once the actual diagonal has been excluded on the surrounding boundary
cycle, the local theorem gives a genuine original-axis alignment. -/
theorem nonnegative_pair_alignment {q B D u v : ℝ} {p : SignedPoint}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (hD : D≤diagonalCoordinate q)
    (hu : 0≤u) (hv : 0≤v) (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hs : p.Sorted) (hc : p.Contained q)
    (h₁ : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (h₂ : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D)
    (hdiag : ∀ E : Endpoint q B D (u+v), E.point.y≠E.point.a) :
    ∃ E : Endpoint q B D (u+v), E.firstError=0 ∨ E.firstError=u+v := by
  obtain ⟨E⟩ := nonnegative_pair_endpoint hqL hqU hB hD hu hv ht0 ht hs hc h₁ h₂
  refine ⟨E,?_⟩
  rcases E.endpoint with he | he | he
  · exact Or.inl he
  · exact Or.inr he
  · exact (hdiag E he).elim

/-- Alignment means a real tie between the original SAT axes. -/
theorem first_aligned_tie {q B D t : ℝ} (E : Endpoint q B D t)
    (h : E.firstError=0) : B-E.point.y≥1 := by
  have hh := E.first_feasible
  simpa [h] using hh

theorem second_aligned_tie {q B D t : ℝ} (E : Endpoint q B D t)
    (h : E.firstError=t) : 1≤E.point.y+D := by
  have hh := E.second_feasible
  simpa [h] using hh

theorem second_aligned_normal_sign {q B D t : ℝ} (E : Endpoint q B D t)
    (h : E.firstError=t) (hD : D<9/10) : 1/10<E.point.y := by
  have hh := E.second_aligned_tie h
  linarith

end PairedPrimary
end SquaresInCircles.Eight.TableFree