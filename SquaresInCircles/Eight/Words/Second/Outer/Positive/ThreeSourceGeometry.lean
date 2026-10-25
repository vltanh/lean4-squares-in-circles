module

public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeFirstContact
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeLowerFourth
public import SquaresInCircles.Eight.Words.Second.Outer.Positive.ThreeSourceCurve

/-!
# Eight squares: physical realization and uniqueness of the fixed-source contact

The rotation curve is identified with the original outer-circle chart
whenever its target is on that arc.  Conversely, every original contact
with the fixed source equals this curve.  The derivative quotient is
therefore the actual original cost derivative, with no contact witness
or minimizer premise.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve

open CommonQuarter CorePairGeometry Arithmetic
open ShortOuterOne.SameContact (arc ratio)

lemma rotation_z (k φ : ℝ) :
    u k φ*Real.sin φ-w k φ*Real.cos φ=z k φ := by
  dsimp [u,w]
  linear_combination z k φ*(Real.sin_sq_add_cos_sq φ)

lemma rotation_y (k φ : ℝ) :
    u k φ*Real.cos φ+w k φ*Real.sin φ=y k φ := by
  dsimp [u,w]
  linear_combination y k φ*(Real.sin_sq_add_cos_sq φ)

lemma target_W (k φ : ℝ) : W (target k φ)=w k φ := by
  dsimp [target,W]
  ring

lemma target_U {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) : U (target k φ)=u k φ := by
  have hc := UW_circle (outer_domain hb)
  rw [target_W] at hc
  have hp := U_positive (outer_domain hb)
  have hq := u_positive h
  nlinarith [circle h]

lemma target_ratio {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) : ratio (target k φ)=w k φ/u k φ := by
  change W (target k φ)/U (target k φ)=_
  rw [target_W,target_U h hb]

lemma contact {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.source (target k φ) φ=1/2-k := by
  have he := rotation_z k φ
  dsimp [FirstContact.source]
  rw [target_U h hb,target_W]
  dsimp [z] at he
  linarith

lemma contact_slope {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.sourceFirst (target k φ) φ=quotient k φ := by
  have hp := (u_positive h).ne'
  have he := rotation_y k φ
  dsimp [FirstContact.sourceFirst,quotient]
  rw [target_ratio h hb]
  field_simp [hp]
  linarith

lemma unique_target {k B φ : ℝ} (h : Domain k φ)
    (hB : B∈Icc 0 outerDiagonal)
    (he : FirstContact.source B φ=1/2-k) : B=target k φ := by
  have htr := lower_trig h.2
  have hproj : U B*Real.sin φ-W B*Real.cos φ=z k φ := by
    dsimp [FirstContact.source,z] at *
    linarith
  have hrot : (U B*Real.cos φ+W B*Real.sin φ)^2+
      (U B*Real.sin φ-W B*Real.cos φ)^2=Q0 := by
    linear_combination ((U B)^2+(W B)^2)*(Real.sin_sq_add_cos_sq φ)+
      UW_circle (outer_domain hB)
  rw [hproj] at hrot
  have hpos : 0<U B*Real.cos φ+W B*Real.sin φ := by
    have hp := mul_nonneg (U_positive (outer_domain hB)).le htr.2.2.1
    have hq := mul_pos (show 0<W B by dsimp [W]; linarith [hB.1])
      (by linarith [htr.1] : 0<Real.sin φ)
    linarith
  have hy : U B*Real.cos φ+W B*Real.sin φ=y k φ := by
    nlinarith [(y_data h).1,(y_data h).2]
  have hw : W B=w k φ := by
    dsimp [w]
    rw [←hy,←hproj]
    linear_combination -(W B)*(Real.sin_sq_add_cos_sq φ)
  dsimp [W] at hw
  dsimp [target]
  linarith

lemma contact_derivative {k φ : ℝ} (h : Domain k φ)
    (hb : target k φ∈Icc 0 outerDiagonal) :
    FirstContact.first (target k φ) φ=
      VLabel.d1 (1/2-k)*quotient k φ-LLabel.d1 (target k φ) := by
  rw [FirstContact.first,contact h hb,contact_slope h hb]

lemma fp_monotone {k : ℝ} (hk : k∈Icc 0 (1/2)) :
    MonotoneOn (fp k) (Icc lowerAngle (Real.pi/2)) := by
  intro φ hφ ψ hψ horder
  have hk' : k∈Icc (-2/5:ℝ) (1/2) := ⟨by linarith [hk.1],hk.2⟩
  have hs := lower_sin_monotone hφ hψ horder
  have hy := y_antitone hk' hφ hψ horder
  have hφtr := lower_trig hφ
  have hψtr := lower_trig hψ
  have hkprod := mul_nonneg hk.1 (sub_nonneg.mpr hk.2)
  have hk2 : k^2≤(1/4:ℝ) := by nlinarith
  have hsum : 0≤Real.sin ψ+Real.sin φ := by linarith [hφtr.1,hψtr.1]
  have hprod := mul_le_mul hk.2 (show Real.sin ψ+Real.sin φ≤2 by
      linarith [hφtr.2.1,hψtr.2.1]) hsum (by norm_num : (0:ℝ)≤1/2)
  have hfactor : 0≤Q0-1-k^2-k*(Real.sin ψ+Real.sin φ) := by
    norm_num [Q0]
    nlinarith
  have hN : Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2)≤
      Real.sin ψ*(Q0-1-k^2)-k*(1+(Real.sin ψ)^2) := by
    have hh := mul_nonneg (sub_nonneg.mpr hs) hfactor
    nlinarith
  have hyp : 0<y k φ := by linarith [(y_data ⟨hk',hφ⟩).1]
  have hyq : 0<y k ψ := by linarith [(y_data ⟨hk',hψ⟩).1]
  have hcube := pow_le_pow_left₀ hyq.le hy 3
  have hNpos : 0≤Real.sin φ*(Q0-1-k^2)-k*(1+(Real.sin φ)^2) := by
    have hh := fp_positive (show Domain k φ from ⟨hk',hφ⟩)
    dsimp [fp] at hh
    have hn := (lt_div_iff₀ (pow_pos hyp 3)).mp hh
    simpa only [zero_mul] using hn.le
  dsimp [fp]
  apply (div_le_div_iff₀ (pow_pos hyp 3) (pow_pos hyq 3)).2
  have hp := mul_nonneg hNpos (sub_nonneg.mpr hcube)
  have hq := mul_nonneg (sub_nonneg.mpr hN) (pow_nonneg hyp.le 3)
  nlinarith

end SquaresInCircles.Eight.SecondWord.PositiveThree.SourceCurve
