module

public import SquaresInCircles.Eight.TableFree.PositivePairEndpoints

/-!
# Ordered two-quarter positive-pair candidates at the original radius

Uncompiled source. Ordering the two primary anchor coordinates replaces
the old second-anchor diagonal ceiling. The zero-tangent candidate is
removed by the actual same-circle alignment with strict opposite slack.
A genuine diagonal candidate is retained explicitly for the subsequent
physical quarter-word argument. The strict coordinate guards needed for
both positive quarter gaps are included in the output.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.EPairOrderedEndpoint
open PairedPrimary

structure OrderedEndpoint (q B D t : ℝ) extends PairedPrimary.Endpoint q B D t where
  lower_strict : -point.a<point.y
  aligned_upper_strict : firstError=0 → point.y<point.a

theorem maximal_guards {q B u y : ℝ}
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q)
    (hu : u∈Icc 0 (7/10:ℝ)) (hy : |y|≤diagonalCoordinate q)
    (hf : 0≤contact q B u y)
    (hmax : y=diagonalCoordinate q ∨ contact q B u y=0) :
    -(arc q y).a<y ∧ (u=0 → y<(arc q y).a) := by
  obtain ⟨hcl,hcu,hAl,hAu⟩ := uniform_circle_reserves hQL hQU
  obtain ⟨hs,ho,hcore⟩ := SignedPoint.outerAt_spec hQL hy
  have ha := (SignedPoint.outer_bounds hs ho).1
  have hylo : -diagonalCoordinate q<y := by
    have hh := (abs_le.mp hy).1
    apply lt_of_le_of_ne hh
    intro heq
    have heq' : y= -diagonalCoordinate q := heq.symm
    rcases hmax with hp | hz
    · linarith
    · have hstrict := lower_diagonal_strict hQL hQU hB.1 hu
      rw [heq'] at hz
      linarith
  refine ⟨by linarith,?_⟩
  intro hu0
  have hyB : y≤B-1 := by
    have h := hf
    simp [hu0,contact] at h
    linarith
  have hBupper : B<283/200 := by
    dsimp [axisCoordinate] at hB
    linarith [hB.2]
  linarith

theorem ordered_endpoint {q B D u v : ℝ} {p : SignedPoint}
    (hQL : qLow≤q) (hQU : q≤qCap)
    (hB : diagonalCoordinate q≤B ∧ B≤axisCoordinate q) (hDB : D≤B)
    (hu : 0≤u) (hv : 0≤v) (ht0 : 0<u+v) (ht : u+v≤7/10)
    (hs : p.Sorted) (hc : p.Contained q)
    (hfirst : edgeWidth u≤B+p.a*Real.sin u-p.y*Real.cos u)
    (hsecond : edgeWidth v≤p.a*Real.sin v+p.y*Real.cos v+D) :
    Nonempty (OrderedEndpoint q B D (u+v)) := by
  obtain ⟨hy0,hf0,hg0⟩ := outerization_preserves_pair hQL hs hc
    ⟨hu,by linarith⟩ ⟨hv,by linarith⟩ hfirst hsecond
  obtain ⟨u',y,hu',hy,hf,hg,hcases,hmax⟩ := intrinsic_endpoint
    hQL hQU hB ⟨ht0,ht⟩ ⟨hu,by linarith⟩ hy0 hf0 hg0
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hQL hy
  have hguard := maximal_guards hQL hQU hB ⟨hu'.1,hu'.2.trans ht⟩ hy hf hmax
  have hfirst' : edgeWidth u'≤B+(arc q y).a*Real.sin u'-y*Real.cos u' := by
    dsimp [contact] at hf
    linarith
  have hsecond' : edgeWidth (u+v-u')≤
      (arc q y).a*Real.sin (u+v-u')+y*Real.cos (u+v-u')+D := by
    dsimp [required] at hg
    linarith
  have make (he : u'=0 ∨ u'=u+v ∨ (arc q y).y=(arc q y).a) :
      Nonempty (OrderedEndpoint q B D (u+v)) := by
    exact ⟨{
      point := arc q y
      firstError := u'
      first_mem := hu'
      sorted := hps
      outer := hpo
      avoids_core := hpc
      first_feasible := hfirst'
      second_feasible := hsecond'
      endpoint := he
      lower_strict := hguard.1
      aligned_upper_strict := hguard.2 }⟩
  by_cases hu0 : u'=0
  · exact make (Or.inl hu0)
  by_cases hut : u'=u+v
  · exact make (Or.inr (Or.inl hut))
  rcases hcases with h | h | h | h
  · exact (hu0 h).elim
  · exact (hut h).elim
  · subst y
    have huPos : 0<u' := lt_of_le_of_ne hu'.1 (Ne.symm hu0)
    have hvPos : 0<u+v-u' := by linarith [lt_of_le_of_ne hu'.2 hut]
    have hcontact : contact q B u' 0=0 := by
      rcases hmax with hh | hh
      · have hdiag := (uniform_circle_reserves hQL hQU).1
        linarith
      · exact hh
    obtain ⟨hss,hoo,hcc,hyy,hfnew,hgnew⟩ := zero_tangent_alignment_ordered
      hQL hQU hB.1 hDB huPos hvPos (by linarith) hcontact (by simpa using hg)
    have hdiag := (uniform_circle_reserves hQL hQU).1
    have hyneg : B-1<0 := by simpa [arc,SignedPoint.outerAt] using hyy
    have hyinner : |B-1|<diagonalCoordinate q := by
      rw [abs_of_neg hyneg]
      linarith [hB.1]
    have hstrict := strict_sorting_of_inner_tangent hQL hyinner
    refine ⟨{
      point := arc q (B-1)
      firstError := 0
      first_mem := ⟨le_rfl,ht0.le⟩
      sorted := hss
      outer := hoo
      avoids_core := hcc
      first_feasible := by simpa using hfnew.ge
      second_feasible := by simpa using hgnew.le
      endpoint := Or.inl rfl
      lower_strict := ?_
      aligned_upper_strict := ?_ }⟩
    · have hh := (abs_lt.mp hstrict).1
      simpa [arc,SignedPoint.outerAt] using hh
    · intro _
      have hh := (abs_lt.mp hstrict).2
      simpa [arc,SignedPoint.outerAt] using hh
  · apply make
    right; right
    have ha := (arc_diagonal hQL).1
    simpa [h,arc,SignedPoint.outerAt] using ha.symm

end SquaresInCircles.Eight.TableFree.EPairOrderedEndpoint
