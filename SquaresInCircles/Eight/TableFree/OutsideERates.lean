module

public import SquaresInCircles.Eight.TableFree.OutsideEArc

/-!
# Strict simultaneous improvement directions for negative DE3 and positive EH1

Uncompiled source. The angular and radial rates are those of the original
physical projections. A small amount beyond the exact EH1-contact speed
makes both margins strictly improve, on either actual radial kind. These
directions supply compact endpoint attainment without an assumed path.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace OutsideE

def contactSpeed (a b v p : ℝ) : ℝ :=
  ((a-1/2)*Real.cos p+(b+1/2)*Real.sin p)/(Real.cos p+v*Real.sin p)

theorem contactSpeed_positive {a b v p : ℝ}
    (ha : 1/2<a) (hb : 0≤b) (hv : 0≤v)
    (hp : p∈Icc 0 (7/10 : ℝ)) :
    0<Real.cos p+v*Real.sin p ∧ 0<contactSpeed a b v p := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hp
  have hcpos : 0<Real.cos p := by linarith
  have hden : 0<Real.cos p+v*Real.sin p :=
    add_pos_of_pos_of_nonneg hcpos (mul_nonneg hv hs0)
  refine ⟨hden,div_pos ?_ hden⟩
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr ha) hcpos) (mul_nonneg (by linarith) hs0)

/-- The DE3 improvement is uniform in both angle orders. In particular,
no sign of the original H/D span occurs in this calculation. -/
theorem de3_contact_rate_positive {a b v p n : ℝ}
    (hb : 0≤b) (hv : 0≤v ∧ v≤1)
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ))
    (hr : (v=0 ∧ b≤1/2) ∨ b-v*a= -(1-v)/2) :
    0<(a+1/2-contactSpeed a b v p)*Real.cos n+
      (b-1/2-v*contactSpeed a b v p)*Real.sin n := by
  obtain ⟨hcp,hcp1,hsp0,hsp,hspcp⟩ := transport_trig hp
  obtain ⟨hcn,hcn1,hsn0,hsn,hsncn⟩ := transport_trig hn
  have hcp0 : 0<Real.cos p := by linarith
  have hcn0 : 0<Real.cos n := by linarith
  let den := Real.cos p+v*Real.sin p
  have hden : 0<den := add_pos_of_pos_of_nonneg hcp0 (mul_nonneg hv.1 hsp0)
  let W := (a+1/2-contactSpeed a b v p)*Real.cos n+
    (b-1/2-v*contactSpeed a b v p)*Real.sin n
  have hid : W*den=
      Real.cos n*Real.cos p-(1-v)/2*
        (Real.sin n*Real.cos p+Real.cos n*Real.sin p)+
      (b-v*a)*(Real.sin n*Real.cos p-Real.cos n*Real.sin p)-
      v*Real.sin n*Real.sin p := by
    dsimp [W,den,contactSpeed]
    field_simp [hden.ne']
    ring
  have hscaled : 0<W*den := by
    rcases hr with ⟨hvzero,hbhalf⟩ | hr
    · have heq : W*den=(1/2-b)*Real.cos p*(Real.cos n-Real.sin n)+
          (1/2+b)*Real.cos n*(Real.cos p-Real.sin p) := by
        rw [hid,hvzero]
        ring
      rw [heq]
      apply add_pos_of_nonneg_of_pos
      · exact mul_nonneg (mul_nonneg (by linarith) hcp0.le)
          (sub_nonneg.mpr hsncn.le)
      · exact mul_pos (mul_pos (by linarith) hcn0) (sub_pos.mpr hspcp)
    · have heq : W*den=Real.cos p*(Real.cos n-Real.sin n)+
          v*Real.sin n*(Real.cos p-Real.sin p) := by
        rw [hid,hr]
        ring
      rw [heq]
      exact add_pos_of_pos_of_nonneg (mul_pos hcp0 (sub_pos.mpr hsncn))
        (mul_nonneg (mul_nonneg hv.1 hsn0) (sub_nonneg.mpr hspcp.le))
  exact (mul_pos_iff_of_pos_right hden).1 hscaled

theorem ArcSource.de3_improving_speed {q b p n : ℝ} {E : SignedPoint} {kind : ArcKind}
    (I : ArcSource q E kind) (hq : qLow≤q) (hb : b∈Icc 0 (-E.y))
    (hp : p∈Icc 0 (7/10 : ℝ)) (hn : n∈Icc 0 (7/10 : ℝ)) :
    ∃ β, 0<β ∧
      0<β*(Real.cos p+kind.slope q b*Real.sin p)-
        ((kind.primary q b-1/2)*Real.cos p+(b+1/2)*Real.sin p) ∧
      0<(kind.primary q b+1/2-β)*Real.cos n+
        (b-1/2-kind.slope q b*β)*Real.sin n := by
  let a := kind.primary q b
  let v := kind.slope q b
  let β₀ := contactSpeed a b v p
  let c := Real.cos n+v*Real.sin n
  let W := (a+1/2-β₀)*Real.cos n+(b-1/2-v*β₀)*Real.sin n
  have hg := I.geometry hq hb
  have hd := I.derivative hq hb
  have hrad := I.radial_identity hq hb
  have hdenβ := contactSpeed_positive hg.2.2.2.2.2.1 hb.1 hd.2.1 hp
  have hW : 0<W := by
    apply de3_contact_rate_positive hb.1 hd.2 hp hn
    rcases hrad with ⟨hk,hv,hb⟩ | hr
    · exact Or.inl ⟨hv,hb⟩
    · exact Or.inr hr
  have hc : 0<c := by
    obtain ⟨hnc,hnc1,hns,hns1,hsc⟩ := transport_trig hn
    exact add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hd.2.1 hns)
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
      dsimp [β₀,contactSpeed]
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

theorem de3_fixed_tangent_rate_positive {a b n : ℝ}
    (ha : 1/2<a) (hb : 0≤b) (hn : n∈Icc 0 (7/10 : ℝ)) :
    0<(a+1/2)*Real.cos n+(b-1/2)*Real.sin n := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hn
  have haC := mul_pos (show 0<a by linarith) (show 0<Real.cos n by linarith)
  have hbS := mul_nonneg hb hs0
  nlinarith

theorem ArcSource.eh_direction_derivative {q b p β : ℝ} {E H : SignedPoint}
    {kind : ArcKind} (I : ArcSource q E kind)
    (hq : qLow≤q) (hb : b∈Icc 0 (-E.y)) :
    HasDerivAt (fun τ => ehSlack kind q H (p-τ) (b-β*τ))
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
  convert ((hasDerivAt_const (0:ℝ) (H.a-1/2)).add
    ((hader.sub_const (1/2)).mul hsder)).sub
      ((hbder.add_const (1/2)).mul hcder) using 1 <;>
    simp [ehSlack] <;> ring

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
  convert ((hasDerivAt_const (0:ℝ) (D.a-1/2)).sub
    ((hader.add_const (1/2)).mul hsder)).add
      ((hbder.sub_const (1/2)).mul hcder) using 1 <;>
    simp [de3Slack] <;> ring

theorem de2_direction_derivative (D : SignedPoint) (α b p β : ℝ) :
    HasDerivAt (fun τ => de2Slack D α (p-τ) (b-β*τ))
      ((D.a-1/2)*Real.sin (p-α)+(1/2-D.y)*Real.cos (p-α)-β) 0 := by
  have hbder : HasDerivAt (fun τ : ℝ => b-β*τ) (-β) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul β).const_sub b
  have hpder : HasDerivAt (fun τ : ℝ => (p-τ)-α) (-1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_sub p).sub_const α
  have hsder := (Real.hasDerivAt_sin ((p-0)-α)).comp 0 hpder
  have hcder := (Real.hasDerivAt_cos ((p-0)-α)).comp 0 hpder
  convert ((((hcder.const_mul (D.a-1/2)).add
    (hsder.const_mul (D.y-1/2))).add hbder).sub_const (1/2)) using 1 <;>
    simp [de2Slack] <;> ring

end OutsideE
end SquaresInCircles.Eight.TableFree
