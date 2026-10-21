module

public import SquaresInCircles.Eight.TableFree.FrameHighLowUpperCurvature

/-!
# The compact upper contact minimum lies on a proved boundary

Every interior contact admits the explicit line with second
derivative below `-.7`.  Compactness therefore reduces the whole
region to its four actual boundary pieces.  The diagonal boundary
uses the unique original circle contact, including its endpoints.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.FrameHighLowUpperMinimum
open FramePair FrameCircleArc FrameLowArc FrameMidArc FrameLowMidArc
open FrameHighArc FrameLowHighArc FrameLowHighAligned FramePairCalculus
open FrameHighLowPrimaryGeometry FrameHighLowUpperAligned FrameHighLowUpperSurface

theorem zero_angle_lower {B : ℝ} (hB : B∈Icc 0 b0) : (8833/10000:ℝ)<F 0 B := by
  simpa [F,height_at_zero] using negative_aligned
    (show B∈Icc 0 b1 from ⟨hB.1,hB.2.trans b0_low.2⟩)

theorem zero_target_lower {x : ℝ} (hx : x∈domain) : (8833/10000:ℝ)<F x 0 := by
  have hh := FrameHighLowAxialScalars.upper_lower
    (show x∈FrameHighLowAxialGeometry.upperDomain from ⟨hx.1,by linarith [hx.2]⟩)
  simpa [F,FrameHighLowContactSurface.height_zero,L_zero,FrameHighLowAxialCalculus.upperF]
    using hh

theorem final_angle_lower {B : ℝ} (hB : B∈Icc 0 b0)
    (hz : c0≤height (27/250) B) : (8833/10000:ℝ)<F (27/250) B := by
  have hx : (27/250:ℝ)∈domain := by constructor <;> norm_num [domain]
  have hBlow : B∈Icc 0 b1 := ⟨hB.1,hB.2.trans b0_low.2⟩
  have hc := (physical_contact_bounds hx hBlow hz).2
  have hh := negative_target_tail
    (show height (27/250) B∈sourceDomain from ⟨hc.1,by linarith [hc.2,a2_bounds.1]⟩)
    hBlow (le_refl (27/250:ℝ))
  dsimp [upperCost,sign] at hh
  rw [(first_width (FrameHighLowAxialGeometry.quadrant (domain_axial hx))).2] at hh
  simpa [F] using hh

theorem diagonal_lower {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b0)
    (hz : height x B=c0) : (8833/10000:ℝ)<F x B := by
  have hd := domain_diagonal hx
  have hBlow : B∈FrameHighLowContactSurface.lowDomain :=
    ⟨by linarith [hB.1],hB.2.trans b0_low.2⟩
  have hdiag := FrameHighLowContactSelection.diagonal_domain hd
  have heq : B=FrameHighLowDiagonalCurve.z x :=
    (FrameHighLowContactSelection.height_strict_antitone (domain_axial hx)).injOn
      hBlow hdiag (by rw [hz,FrameHighLowContactSurface.height_diagonal hd])
  have hh := FrameHighLowDiagonalScalar.lower hd
  rw [F,heq,FrameHighLowContactSurface.height_diagonal hd,G_c0]
  simpa [FrameHighLowDiagonalScalar.J] using hh

theorem contact_lower {x B : ℝ} (hx : x∈domain) (hB : B∈Icc 0 b1)
    (hz : c0≤height x B) : (8833/10000:ℝ)<F x B := by
  have hb0 := (physical_contact_bounds hx hB hz).1
  obtain ⟨p,hp,hp0,hmin⟩ := contact_region_minimum
    (contact := fun p : ℝ×ℝ => height p.1 p.2-c0)
    (height_continuous.sub_const c0) F_continuous
    (p₀ := (x,B)) ⟨hx,hb0,sub_nonneg.mpr hz⟩
  have hpz : c0≤height p.1 p.2 := by linarith [hp.2.2]
  have hbound : (8833/10000:ℝ)<F p.1 p.2 := by
    by_cases hx0 : p.1=0
    · simpa only [hx0] using zero_angle_lower hp.2.1
    by_cases hxf : p.1=27/250
    · rw [hxf] at hpz ⊢
      exact final_angle_lower hp.2.1 hpz
    by_cases hB0 : p.2=0
    · simpa only [hB0] using zero_target_lower hp.1
    by_cases hdiag : height p.1 p.2=c0
    · exact diagonal_lower hp.1 hp.2.1 hdiag
    have hxI : p.1∈Ioo (0:ℝ) (27/250) :=
      ⟨lt_of_le_of_ne hp.1.1 (Ne.symm hx0),lt_of_le_of_ne hp.1.2 hxf⟩
    have hBI : p.2∈Ioo (0:ℝ) b0 := by
      refine ⟨lt_of_le_of_ne hp.2.1.1 (Ne.symm hB0),?_⟩
      by_contra! hbad
      have heq : p.2=b0 := le_antisymm hp.2.1.2 hbad
      have hu := height_upper hp.1
        (show p.2∈Icc 0 b1 from ⟨hp.2.1.1,hp.2.1.2.trans b0_low.2⟩)
      rw [heq] at hu
      dsimp [b0] at hu
      exact hdiag (le_antisymm (by linarith) hpz)
    let O : Set ℝ := {t | p.1+t∈Ioo (0:ℝ) (27/250) ∧
      p.2-t∈Ioo (0:ℝ) b0 ∧ c0<height (p.1+t) (p.2-t)}
    have hline : Continuous (fun t : ℝ => height (p.1+t) (p.2-t)) :=
      height_continuous.comp ((continuous_const.add continuous_id).prodMk
        (continuous_const.sub continuous_id))
    have hO : IsOpen O :=
      (isOpen_Ioo.preimage (continuous_const.add continuous_id)).inter
        ((isOpen_Ioo.preimage (continuous_const.sub continuous_id)).inter
          (isOpen_lt continuous_const hline))
    have hzero : (0:ℝ)∈O := by
      dsimp [O]
      simpa using And.intro hxI (And.intro hBI (lt_of_le_of_ne hpz (Ne.symm hdiag)))
    have hdata (t : ℝ) (ht : t∈O) :
        p.1+t∈domain ∧ p.2-t∈Icc 0 b0 ∧ c0≤height (p.1+t) (p.2-t) :=
      ⟨Ioo_subset_Icc_self ht.1,Ioo_subset_Icc_self ht.2.1,ht.2.2.le⟩
    have hext (t : ℝ) (ht : t∈O) :
        p.2-t∈extendedDomain ∧ height (p.1+t) (p.2-t)∈extendedDomain := by
      have hd := hdata t ht
      have hlow : p.2-t∈Icc 0 b1 := ⟨hd.2.1.1,hd.2.1.2.trans b0_low.2⟩
      have hc := (physical_contact_bounds hd.1 hlow hd.2.2).2
      exact ⟨low_extended hlow,source_extended
        ⟨hc.1,by linarith [hc.2,a2_bounds.1]⟩⟩
    exfalso
    apply not_minimum_on_strictly_concave_curve
      (s := {q : ℝ×ℝ | q.1∈domain ∧ q.2∈Icc 0 b0 ∧ 0≤height q.1 q.2-c0})
      (cost := fun q : ℝ×ℝ => F q.1 q.2)
      (fun q hq => hmin q hq.1 hq.2.1 hq.2.2)
      (curve := fun t : ℝ => (p.1+t,p.2-t))
      (value := fun t => F (p.1+t) (p.2-t))
      (dvalue := fun t => lineD (p.1+t) (p.2-t))
      (ddvalue := fun t => lineDD (p.1+t) (p.2-t))
      hO hzero (show (0:ℝ)<7/10 by norm_num)
    · simp
    · intro t ht
      have hd := hdata t ht
      exact ⟨hd.1,hd.2.1,sub_nonneg.mpr hd.2.2⟩
    · intros
      rfl
    · intro t ht
      exact F_line_deriv (hext t ht).1 (hext t ht).2
    · intro t ht
      exact lineD_line_deriv (hext t ht).1 (hext t ht).2
    · intro t ht
      have hd := hdata t ht
      exact (FrameHighLowUpperCurvature.line_curvature hd.1 hd.2.1 hd.2.2).le
  exact hbound.trans_le hp0

end SquaresInCircles.Eight.TableFree.FrameHighLowUpperMinimum
