module

public import SquaresInCircles.Eight.TableFree.CrossedCancelingBounds
public import SquaresInCircles.Eight.TableFree.CrossedGAOutput

/-!
# An actual same-q HG2-to-HG0 descendant at the common middle frame

Uncompiled source draft.  The composite continuation determines the new
G tangent.  The unchanged opposite budget proves it is below H's actual
tangent, so lifting G to its original q-circle supplies an actual HG0
witness.  A positive frame motion gives strict slack at aligned GA; a
decrease of the original A primary retains that slack and makes the
original A circle strictly smaller.  The free G loss is never used.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CrossedCancelingConstruction
open PositiveSmallScalar CrossedCancelingScalar CrossedCancelingBounds
open EndpointRotationPenalty EndpointBudgetScalars

theorem actual_cap {q z : ℝ} {G A : SignedPoint}
    (hq : q≤qCap) (hAs : A.Sorted) (hAc : A.AvoidsCore)
    (hAq : A.Contained q) (hAy : 1/2≤A.y) (hGy : G.y≤0)
    (hz : z∈Icc 0 frameCap) (hGA : quarterFeasible G A (-z) 0) :
    CrossedCancelingScalar.CapData q (A.a-1/2) (A.y+1/2) ∧
      1/2≤V (A.a-1/2) (A.y+1/2) z := by
  have ha := SignedPoint.primary_gt_half hAs hAc
  have hb := SignedOppositeHardEnvelope.negative_hard_contact hz hGA
  have ht := transport_trig hz
  have hp := mul_le_mul_of_nonneg_left ht.2.1 (show 0≤A.a-1/2 by linarith)
  have hy := mul_nonneg (show 0≤A.y+1/2 by linarith) ht.2.2.1
  have ha1 : 1≤A.a := by nlinarith
  have hcircle : (A.a-1/2+1)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,
      abs_of_nonneg (show 0≤A.y by linarith),show A.a-1/2+1=A.a+1/2 by ring] using hAq
  have hupper : A.a-1/2≤177/250 := by
    have hc := hcircle.trans hq
    dsimp [qCap] at hc
    nlinarith
  exact ⟨⟨⟨by linarith,hupper⟩,by linarith,hcircle,hq⟩,by dsimp [V]; linarith⟩

theorem actual_output {q r z u : ℝ} {H G A B T : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hAs : A.Sorted) (hBs : B.Sorted)
    (hAc : A.AvoidsCore) (hHq : H.Contained q) (hAq : A.Contained q)
    (hBq : B.Contained q) (hHy : 0≤H.y) (hAy : 1/2≤A.y) (hBy : B.y≤0)
    (hGy : G.y≤0) (hT : -(1/10:ℝ)<T.y) (hsum : A.y-B.y=1)
    (hr : r∈Ioc 0 frameCap) (hz : z∈Icc 0 frameCap)
    (hu : u∈Icc 0 frameCap) (hspan : z+r≤frameCap)
    (hHG : zeroFeasible H G (z+r) 2) (hGA : quarterFeasible G A (-z) 0)
    (hBT : quarterFeasible B T (-u) 2)
    (hbudget : H.y-T.y+charge*(r-u)<1-S0) :
    Nonempty (CrossedGAData q H G A r z) := by
  obtain ⟨C,hV⟩ := actual_cap hq hAs hAc hAq hAy hGy hz hGA
  have hpair := original_pair hr.1.le hz.1 hspan hHG hGA
  have hreserve := alignment_reserve C hHy hHq hr.1.le hz.1 hspan hV hpair
    0 ⟨le_rfl,hz.1⟩
  have hzero : 1≤A.a-1/2+S H r := by
    simpa [composite,V] using hreserve.1
  let g := max 0 (1/2-S H r)
  have hg0 : 0≤g := le_max_left _ _
  have hga : g+1≤A.a := by
    have hh : g≤A.a-1 := max_le
      (by linarith [C.P_mem.1]) (by linarith)
    linarith
  have hg : g∈Icc (0:ℝ) (26/125) := ⟨hg0,by linarith [C.P_mem.2]⟩
  have hhg : 1/2≤g+S H r := by have hh := le_max_right 0 (1/2-S H r); linarith
  have horder : g<H.y := tangent_order hHs hHy (hHq.trans hq)
    (by linarith) hBy hBs.1 (hAq.trans hq) (hBq.trans hq) hsum hg
    ⟨hr.1.le,hr.2⟩ hu hhg hga hBT hT hbudget
  let G' := SignedPoint.outerAt q (-g)
  have hdiag : |-g|≤diagonalCoordinate q := by
    rw [abs_neg,abs_of_nonneg hg0]
    linarith [hg.2,(uniform_circle_reserves hqL hq).1]
  obtain ⟨hGs,hGq,hGc⟩ := SignedPoint.outerAt_spec hqL hdiag
  have hGyEq : G'.y= -g := rfl
  have hGcircle : (G'.a+1/2)^2+(g+1/2)^2=q := by
    simpa [SignedPoint.Outer,SignedPoint.circle,hGyEq,abs_neg,abs_of_nonneg hg0] using hGq
  have hHcircle : (H.a+1/2)^2+(H.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hHy] using hHq
  have hminor := pow_lt_pow_left₀ (show 0≤g+1/2 by linarith)
    (show g+1/2<H.y+1/2 by linarith) (by decide : (2:ℕ)≠0)
  have hprimary : H.a<G'.a := by nlinarith [hHs.1,hGs.1]
  have hsin : 0<Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr.1
    (by dsimp [frameCap] at hr; linarith [hr.2,Real.pi_gt_three])
  have hpositive := mul_pos (sub_pos.mpr hprimary) hsin
  have hnonneg := mul_nonneg (sub_nonneg.mpr horder.le)
    (sub_nonneg.mpr (Real.cos_le_one r))
  have hHGzero : zeroFeasible H G' r 0 := by
    rw [zeroFeasible,edgeWidth_positive_formula ⟨hr.1.le,hr.2⟩]
    simp only [zeroProjection,Matrix.cons_val_zero,hGyEq]
    dsimp [S] at hhg
    nlinarith
  have hstrictGA : 0<z → g+1<A.a := by
    intro hzpos
    have ht := transport_trig hz
    have hsinz : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hzpos
      (by dsimp [frameCap] at hz; linarith [hz.2,Real.pi_gt_three])
    have hp := mul_le_mul_of_nonneg_left ht.2.1
      (show 0≤A.a-1/2 by linarith [C.P_mem.1])
    have hys := mul_pos (show 0<A.y+1/2 by linarith) hsinz
    have ha1 : 1<A.a := by dsimp [V] at hV; nlinarith
    have hf0 : 1<A.a-1/2+S H r := by
      have hh := hreserve.2
      rw [show composite H (A.a-1/2) (A.y+1/2) r 0=A.a-1/2+S H r by
        simp [composite,V],sub_zero] at hh
      nlinarith
    by_cases hs : 0≤1/2-S H r
    · dsimp [g]
      rw [max_eq_right hs]
      linarith
    · have heq : g=0 := max_eq_left (le_of_not_ge hs)
      rw [heq]
      linarith
  have hAout : ∃ A' : SignedPoint, A'.Sorted ∧ A'.AvoidsCore ∧
      A'.Contained q ∧ A'.y=A.y ∧ g+1≤A'.a ∧
      (0<z → A'.circle<q) ∧ (A.circle<q → A'.circle<q) := by
    by_cases hz0 : z=0
    · exact ⟨A,hAs,hAc,hAq,rfl,hga,by intro h; linarith,fun h => h⟩
    · have hzpos : 0<z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
      have hstrict := hstrictGA hzpos
      let A' : SignedPoint := ⟨(A.a+g+1)/2,A.y⟩
      have ha' : g+1<A'.a ∧ A'.a<A.a := by dsimp [A']; constructor <;> linarith
      have hay : A.y<9/10 := by
        have hh := (SignedPoint.coordinate_bounds hAs hAc hAq hq).2.2
        rw [abs_of_nonneg (show 0≤A.y by linarith)] at hh
        exact hh
      have hAs' : A'.Sorted := by
        refine ⟨by linarith [ha'.1],?_⟩
        change |A.y|≤A'.a
        rw [abs_of_nonneg (show 0≤A.y by linarith)]
        linarith [ha'.1]
      have hAc' : A'.AvoidsCore := by
        dsimp [SignedPoint.AvoidsCore,SignedPoint.coreDistance]
        rw [max_eq_left (by linarith [ha'.1] : 0≤A'.a-1/2)]
        nlinarith [sq_nonneg (max (|A'.y|-1/2) 0)]
      have hsq := pow_lt_pow_left₀ (show 0≤A'.a+1/2 by linarith [ha'.1])
        (show A'.a+1/2<A.a+1/2 by linarith [ha'.2]) (by decide : (2:ℕ)≠0)
      have hloss : A'.circle<A.circle := by
        change (A'.a+1/2)^2+(|A.y|+1/2)^2<
          (A.a+1/2)^2+(|A.y|+1/2)^2
        linarith
      have hstrictq : A'.circle<q := hloss.trans_le hAq
      exact ⟨A',hAs',hAc',hstrictq.le,rfl,ha'.1.le,fun _ => hstrictq,
        fun h => hloss.trans h⟩
  obtain ⟨A',hAs',hAc',hAq',hAy',hga',hstrict',hloss'⟩ := hAout
  exact ⟨{
    pointG := G'
    pointA := A'
    G_sorted := hGs
    G_avoids := hGc
    G_contained := hGq.le
    G_nonpos := by rw [hGyEq]; linarith
    A_sorted := hAs'
    A_avoids := hAc'
    A_contained := hAq'
    A_tangent := hAy'
    HG_zero := hHGzero
    GA_hard := by
      simpa [quarterFeasible,quarterProjection,hGyEq] using
        (show (1:ℝ)≤ -g+A'.a by linarith)
    A_strict := hstrict'
    A_loss := hloss' }⟩

end SquaresInCircles.Eight.TableFree.CrossedCancelingConstruction
