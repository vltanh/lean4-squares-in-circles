module

public import SquaresInCircles.Eight.TableFree.PairTransportAssembly
public import SquaresInCircles.Eight.TableFree.BoundaryRealization

/-!
# Physical winding after both primary-pair transports

Uncompiled source. Ordering is proved afresh from the actual endpoint
squares. Normal anchor signs and the actual selected zero owners first put
each unwrapped gap above -19/25. The geometric common-point theorem rules
out every nonpositive gap. It then gives all seven gaps above 19/25, and
their exact full-turn sum bounds each gap below π.

This argument also applies when a local output reaches a nearest-axis
diagonal. It establishes physical winding there; exclusion of the two
remaining diagonal signs is still a separate global word argument.
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.TableFree
open Candidate

/-- A nonnegative G on the HG0 axis needs a definite positive frame error.
The estimate uses only the true zero projection, its width, and the uniform
coordinate bounds. In particular it remains valid after radial transport. -/
theorem hg0_nonnegative_tangent_error_lower {H G : SignedPoint} {d : ℝ}
    (hH : H.y<9/10) (hGa : 0<G.a) (hGu : G.a<283/200)
    (hGy : 0≤G.y) (hd : |d|≤7/10)
    (hHG : zeroFeasible H G d 0) : 1/20<d := by
  have hdpos : 0<d := by
    by_contra! hd0
    exact (not_lt_of_ge hGy) (hg0_nonpositive_error_normal hH hGa hd hd0 hHG)
  by_contra! hdsmall
  have hs : Real.sin d≤1/20 := by
    have hsd : Real.sin d≤d := by
      exact (le_abs_self _).trans (Real.abs_sin_le_abs.trans_eq (abs_of_pos hdpos))
    exact hsd.trans hdsmall
  have hc := transport_cos_pos hd
  have hsecond := mul_nonneg hGy hc.le
  have hfirst := mul_le_mul_of_nonneg_left hs hGa.le
  have hp : edgeWidth d≤H.y+G.a*Real.sin d-G.y*Real.cos d := hHG
  nlinarith [edgeWidth_ge_one d]

/-- The reflected TD2 estimate keeps the same physical frame error. -/
theorem td2_nonpositive_tangent_error_lower {T D : SignedPoint} {d : ℝ}
    (hD : -D.y<9/10) (hTa : 0<T.a) (hTu : T.a<283/200)
    (hTy : T.y≤0) (hd : |d|≤7/10)
    (hTD : zeroFeasible T D d 2) : 1/20<d := by
  have hf : zeroFeasible D.reflect T.reflect d 0 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect T D d 2).2 hTD
  exact hg0_nonnegative_tangent_error_lower hD hTa hTu
    (neg_nonneg.mpr hTy) hd hf

namespace SignedCycle

theorem localAngle_nonneg {C : SignedCycle} {i : Vertex}
    (hs : (C.point i).Sorted) (hy : 0≤(C.point i).y) :
    0≤C.localAngle i :=
  Real.arctan_nonneg.mpr (div_nonneg hy hs.1.le)

theorem localAngle_nonpos {C : SignedCycle} {i : Vertex}
    (hs : (C.point i).Sorted) (hy : (C.point i).y≤0) :
    C.localAngle i≤0 := by
  have hd : (C.point i).y/(C.point i).a≤0 :=
    div_nonpos_of_nonpos_of_nonneg hy hs.1.le
  simpa only [Real.arctan_zero] using Real.arctan_le_arctan hd

/-- Actual neighboring squares have a separated polar direction even before
an ordering or a radial-boundary record has been constructed. -/
theorem necessary_direction_separation {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap)
    (w : C.Witnesses) (i : Vertex) :
    19/25<dist (C.polarAngle i : Direction) (C.polarAngle (next i) : Direction) := by
  have hr (j : Vertex) :
      0<Real.sqrt ((C.point j).a^2+|(C.point j).y|^2) := by
    apply Real.sqrt_pos.mpr
    nlinarith [(hn.sorted j).1,sq_nonneg |(C.point j).y|]
  have hcore (j : Vertex) : CoreAvoiding (C.actualSquare j) :=
    (SignedPoint.square_core_iff (hn.sorted j) (C.actualAngle j)).2 (hn.core j)
  have hf := (C.actualSquare_feasible i (w.owner i)).2 (w.feasible i)
  exact exterior_pair_gap (by simpa [qCap,Q0] using hq)
    (actualSquare_contained hn.sorted hn.contained i)
    (actualSquare_contained hn.sorted hn.contained (next i))
    (hcore i) (hcore (next i)) (hr i) (hr (next i))
    (actualSquare_polar hn.sorted i).1 (actualSquare_polar hn.sorted i).2
    (actualSquare_polar hn.sorted (next i)).1
    (actualSquare_polar hn.sorted (next i)).2 hf.disjoint

/-- The fixed quarter word, normal anchors, and the selected zero-owner
sign implications keep every real gap within the positive winding branch.
Only a lower bound is claimed here; positivity uses actual disjointness. -/
theorem normal_gap_above_negative_separation {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) (i : Vertex) :
    -(19/25 : ℝ)<C.physicalGap i := by
  have hdelta (j : Vertex) : -(7/10 : ℝ)≤delta C.theta j := by
    exact (abs_le.mp (hn.spread (next j) j)).1
  have hang := localAngle_mem hn.sorted
  have hHangle := localAngle_nonneg (hn.sorted H) ha.H_nonneg
  have hAangle := localAngle_nonneg (hn.sorted A) ha.A_nonneg
  have hBangle := localAngle_nonpos (hn.sorted B) ha.B_nonpos
  have hDangle := localAngle_nonpos (hn.sorted D) ha.D_nonpos
  have hquarter (j : Vertex) (hw : word j=1) :
      -(19/25 : ℝ)<C.physicalGap j := by
    have hsource := (hang j).1
    have htarget := (hang (next j)).2
    have hgap : C.physicalGap j=
        Real.pi/2+delta C.theta j+C.localAngle j-C.localAngle (next j) := by
      simp [physicalGap,hw]
    rw [hgap]
    linarith [hdelta j]
  have hHG : -(19/25 : ℝ)<C.physicalGap H := by
    have hgap : C.physicalGap H=
        delta C.theta H+C.localAngle H-C.localAngle G := by
      simp [physicalGap,word,next,H,G]
    rw [hgap]
    by_cases hy : (C.point G).y≤0
    · have hGangle := localAngle_nonpos (hn.sorted G) hy
      linarith [hdelta H]
    · have hypos : 0<(C.point G).y := lt_of_not_ge hy
      have hj : w.owner H=0 := by
        have hw : w.owner H=0 ∨ w.owner H=2 := by
          simpa [normalOwners,H] using w.allowed H
        rcases hw with hj | hj
        · exact hj
        · exact ((not_lt_of_ge hypos.le) (hz.HG_canceling hj)).elim
      have hf : zeroFeasible (C.point H) (C.point G) (delta C.theta H) 0 := by
        have hf := w.feasible H
        change 0≤C.slack H (w.owner H) at hf
        simpa [slack,edge,word,next,H,G,hj,zeroFeasible]
          using sub_nonneg.mp hf
      have hHb := (SignedPoint.coordinate_bounds (hn.sorted H)
        (hn.core H) (hn.contained H) hq).2.2
      have hGu := (SignedPoint.coordinate_bounds (hn.sorted G)
        (hn.core G) (hn.contained G) hq).2.1
      have hd : 1/20<delta C.theta H :=
        hg0_nonnegative_tangent_error_lower ((le_abs_self _).trans_lt hHb)
          (hn.sorted G).1 hGu hypos.le (hn.spread G H) hf
      linarith [(hang G).2,pi_lt_22_over_7]
  have hAB : -(19/25 : ℝ)<C.physicalGap A := by
    have hgap : C.physicalGap A=
        delta C.theta A+C.localAngle A-C.localAngle B := by
      simp [physicalGap,word,next,A,B]
    rw [hgap]
    linarith [hdelta A]
  have hTD : -(19/25 : ℝ)<C.physicalGap T := by
    have hgap : C.physicalGap T=
        delta C.theta T+C.localAngle T-C.localAngle D := by
      simp [physicalGap,word,next,T,D]
    rw [hgap]
    by_cases hy : 0≤(C.point T).y
    · have hTangle := localAngle_nonneg (hn.sorted T) hy
      linarith [hdelta T]
    · have hyneg : (C.point T).y<0 := lt_of_not_ge hy
      have hj : w.owner T=2 := by
        have hw : w.owner T=0 ∨ w.owner T=2 := by
          simpa [normalOwners,T] using w.allowed T
        rcases hw with hj | hj
        · exact ((not_lt_of_ge hyneg.le) (hz.TD_canceling hj)).elim
        · exact hj
      have hf : zeroFeasible (C.point T) (C.point D) (delta C.theta T) 2 := by
        have hf := w.feasible T
        change 0≤C.slack T (w.owner T) at hf
        simpa [slack,edge,word,next,T,D,hj,zeroFeasible]
          using sub_nonneg.mp hf
      have hDb := (SignedPoint.coordinate_bounds (hn.sorted D)
        (hn.core D) (hn.contained D) hq).2.2
      have hTu := (SignedPoint.coordinate_bounds (hn.sorted T)
        (hn.core T) (hn.contained T) hq).2.1
      have hDlower : -(C.point D).y<9/10 := (neg_le_abs _).trans_lt hDb
      have hd : 1/20<delta C.theta T :=
        td2_nonpositive_tangent_error_lower hDlower (hn.sorted T).1
          hTu hyneg.le (hn.spread D T) hf
      linarith [(hang T).1,pi_lt_22_over_7]
  fin_cases i
  · exact hHG
  · exact hquarter G (by decide)
  · exact hAB
  · exact hquarter B (by decide)
  · exact hTD
  · exact hquarter D (by decide)
  · exact hquarter E (by decide)

private theorem negative_angleGap_direction_distance (β : Vertex → ℝ) (i : Vertex)
    (hp : angleGap β i≤0) (hu : -angleGap β i≤Real.pi) :
    dist (β i : Direction) (β (next i) : Direction)= -angleGap β i := by
  have he : ((angleGap β i : ℝ) : Direction)=
      (β (next i) : Direction)-(β i : Direction) := by
    by_cases hi : i=6 <;>
      simp [angleGap,hi,Real.Angle.coe_add,Real.Angle.coe_sub,Real.Angle.coe_two_pi]
  have hn : ((-angleGap β i : ℝ) : Direction)=
      (β i : Direction)-(β (next i) : Direction) := by
    rw [Real.Angle.coe_neg,he,neg_sub]
  rw [direction_dist,← hn]
  exact Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨neg_nonneg.mpr hp,hu⟩

/-- No ordering hypothesis is used. The lower bound above and genuine
neighbor separation choose the correct lift of every polar direction. -/
theorem normal_necessary_gap_lower {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) (i : Vertex) :
    19/25<C.physicalGap i := by
  have hsep := necessary_direction_separation hn hq w i
  have hlo := normal_gap_above_negative_separation hn hq ha w hz i
  have hpos : 0<C.physicalGap i := by
    by_contra! hnonpos
    have hgap : angleGap C.polarAngle i≤0 := by
      rwa [polarAngle_gap]
    have hu : -angleGap C.polarAngle i≤Real.pi := by
      rw [polarAngle_gap]
      linarith [Real.pi_gt_three]
    rw [negative_angleGap_direction_distance C.polarAngle i hgap hu,
      polarAngle_gap] at hsep
    linarith
  by_contra! hsmall
  have hgap : 0≤angleGap C.polarAngle i := by
    rw [polarAngle_gap]; exact hpos.le
  have hu : angleGap C.polarAngle i≤Real.pi := by
    rw [polarAngle_gap]
    linarith [Real.pi_gt_three]
  rw [angleGap_direction_distance C.polarAngle i hgap hu,polarAngle_gap] at hsep
  linarith

/-- Physical order is recovered from the actual normal-owner geometry. This
supplies the missing order field for simultaneous G/T preprocessing, without
an assumed conclusion about the endpoint's gaps. -/
theorem normal_necessary_ordered {q : ℝ} {C : SignedCycle}
    (hn : C.Necessary q) (hq : q≤qCap) (ha : C.NormalAnchors)
    (w : C.Witnesses) (hz : C.ZeroSignImplications w) : C.Ordered := by
  have hlower := normal_necessary_gap_lower hn hq ha w hz
  have hupper : ∀ i,C.physicalGap i<3*Real.pi/4 := by
    have h := seven_gaps_three_quarters C.polarAngle (fun i => by
      rw [polarAngle_gap]; exact hlower i)
    simpa only [polarAngle_gap] using h
  constructor
  · intro i
    linarith [hlower i]
  · intro i
    linarith [hupper i,Real.pi_pos]

end SignedCycle
end SquaresInCircles.Eight.TableFree
