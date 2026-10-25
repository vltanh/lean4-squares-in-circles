module

public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks

/-!
# Eight squares: exact three-frame width minimum for the middle stress

The two angles are the original AB and BT
differences, with their original signs.  For every weight in `[.65,1]`,
their complete angular width is at least the width of the corresponding
single signed difference.  The proof uses the entire real frame interval;
no angle subdivision or moved middle square is involved.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleAngularPenalty
open PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open CorrelatedSameBlock

def endpointWidth (l s : ℝ) : ℝ :=
  if 0≤ s then l*(PositiveAngularEnvelope.phi s-1) else Real.cos s-1

theorem half_trig {u : ℝ} (hu : u∈Icc 0 (frameCap/2)) :
    (15/16 : ℝ)<Real.cos u ∧ 0≤Real.sin u ∧ Real.sin u<(343/1000 : ℝ) := by
  have hu2 : u≤7/20 := by have h := hu.2; norm_num [frameCap] at h; linarith
  have hu' : u∈Icc 0 frameCap := ⟨hu.1,by show u≤7/10; linarith⟩
  have hh : frameCap/2∈Icc 0 frameCap := by norm_num [frameCap]
  have hc := cos_lower_six (show (0:ℝ)≤frameCap/2 by norm_num [frameCap])
  have hs := sin_upper_five (show (0:ℝ)≤frameCap/2 by norm_num [frameCap])
  have hmC := cos_anti hu' hh hu.2
  have hmS := sin_mono hu' hh hu.2
  norm_num [frameCap] at hc hs hmC hmS
  exact ⟨by linarith,(transport_trig hu').2.2.1,by linarith⟩

theorem cosine_minus_sine_anti {x z : ℝ}
    (hx : x∈Icc 0 frameCap) (hz : z∈Icc 0 frameCap) (hxz : x≤z) :
    Real.cos z-Real.sin z≤Real.cos x-Real.sin x := by
  linarith [cos_anti hx hz hxz,sin_mono hx hz hxz]

/-- The half-angle bracket for a surviving positive signed difference.
The smallest permitted weight already has a strict rational reserve. -/
theorem positive_bracket {l a u : ℝ} (hl : (13/20 : ℝ)≤l)
    (ha : 0≤a) (hu : 0≤u) (hspan : a+2*u≤frameCap) :
    0≤l*(Real.cos (a+u)-Real.sin (a+u))-Real.sin u := by
  have hF : a+2*u≤7/10 := hspan
  have huHalf : u∈Icc 0 (frameCap/2) := ⟨hu,by show u≤7/10/2; linarith⟩
  have hdom : a+u∈Icc 0 frameCap := ⟨by linarith,by show a+u≤7/10; linarith⟩
  have htop : frameCap-u∈Icc 0 frameCap :=
    ⟨by show (0:ℝ)≤7/10-u; linarith,by show 7/10-u≤(7/10:ℝ); linarith⟩
  obtain ⟨hcu,hsu0,hsu⟩ := half_trig huHalf
  have hcmp := cosine_minus_sine_anti hdom htop (by show a+u≤7/10-u; linarith)
  have hexp : Real.cos (frameCap-u)-Real.sin (frameCap-u)=
      (Real.cos frameCap-Real.sin frameCap)*Real.cos u+
        (Real.cos frameCap+Real.sin frameCap)*Real.sin u := by
    rw [Real.cos_sub,Real.sin_sub]
    ring
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  obtain ⟨hch,_,_,hsh,_⟩ := transport_trig hcap
  have hφ := phi_cap_lower
  have hdiff : (241/2000 : ℝ)≤Real.cos frameCap-Real.sin frameCap := by
    linarith
  have hp₁ := mul_nonneg (sub_nonneg.mpr hdiff) (show 0≤Real.cos u by linarith)
  have hp₂ := mul_nonneg (show 0≤Real.cos frameCap+Real.sin frameCap-1409/1000 by
    dsimp [PositiveAngularEnvelope.phi] at hφ; linarith) hsu0
  have hd0 : 0≤Real.cos (a+u)-Real.sin (a+u) :=
    sub_nonneg.mpr (transport_trig hdom).2.2.2.2.le
  have hp₃ := mul_nonneg (sub_nonneg.mpr hl) hd0
  rw [hexp] at hcmp
  nlinarith

/-- The half-angle bracket for a surviving negative signed difference.
The sole ratio comparison is `sin(7/10)<13/20`. -/
theorem negative_bracket {l a u : ℝ} (hl : (13/20 : ℝ)≤l)
    (ha : 0≤a) (hu : 0≤u) (hspan : a+2*u≤frameCap) :
    0≤l*(Real.cos u-Real.sin u)-Real.sin (a+u) := by
  have hu' : u∈Icc 0 frameCap := ⟨hu,by dsimp [frameCap] at *; linarith⟩
  have hdom : a+u∈Icc 0 frameCap := ⟨by linarith,by linarith⟩
  have htop : frameCap-u∈Icc 0 frameCap := by
    constructor <;> dsimp [frameCap] at * <;> linarith
  have hs := sin_mono hdom htop (by linarith)
  have hcap : frameCap∈Icc 0 frameCap := by norm_num [frameCap]
  obtain ⟨_,_,_,hsh,hsch⟩ := transport_trig hcap
  have hsu := (transport_trig hu').2.2.1
  have hdiff := (transport_trig hu').2.2.2.2
  have hp₁ := mul_nonneg (sub_nonneg.mpr hsch.le) hsu
  have hp₂ := mul_nonneg (show 0≤l-Real.sin frameCap by linarith)
    (sub_nonneg.mpr hdiff.le)
  rw [Real.sin_sub] at hs
  nlinarith

theorem phi_difference (x u : ℝ) :
    PositiveAngularEnvelope.phi (x+u)-PositiveAngularEnvelope.phi (x-u)=2*Real.sin u*(Real.cos x-Real.sin x) := by
  simp only [PositiveAngularEnvelope.phi,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub]
  ring

theorem cosine_difference (x u : ℝ) :
    Real.cos (x+u)-Real.cos (x-u)= -2*Real.sin x*Real.sin u := by
  rw [Real.cos_add,Real.cos_sub]
  ring

theorem cosine_double_shift (u : ℝ) :
    Real.cos (2*u)-1= -2*(Real.sin u)^2 := by
  rw [show 2*u=u+u by ring,Real.cos_add]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem phi_double_shift (u : ℝ) :
    PositiveAngularEnvelope.phi (2*u)-1=2*Real.sin u*(Real.cos u-Real.sin u) := by
  simp only [show 2*u=u+u by ring,PositiveAngularEnvelope.phi,Real.cos_add,Real.sin_add]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem positive_surplus {l a b : ℝ} (hl : (13/20 : ℝ)≤l)
    (ha : 0≤a) (hb : 0≤b) (hspan : a+b≤frameCap) :
    0≤l*(PositiveAngularEnvelope.phi (a+b)-PositiveAngularEnvelope.phi a)+Real.cos b-1 := by
  have hF : a+b≤7/10 := hspan
  have hbr := positive_bracket hl ha (by linarith : 0≤b/2)
    (show a+2*(b/2)≤frameCap by show a+2*(b/2)≤7/10; linarith)
  have hsin : 0≤Real.sin (b/2) := (half_trig
    (show b/2∈Icc 0 (frameCap/2) from ⟨by linarith,by show b/2≤7/10/2; linarith⟩)).2.1
  have hp := mul_nonneg (show 0≤2*Real.sin (b/2) by linarith) hbr
  have hφ := phi_difference (a+b/2) (b/2)
  have hc := cosine_double_shift (b/2)
  have hφ' : PositiveAngularEnvelope.phi (a+b)-PositiveAngularEnvelope.phi a=
      2*Real.sin (b/2)*(Real.cos (a+b/2)-Real.sin (a+b/2)) := by
    simpa only [show a+b/2+b/2=a+b by ring,
      show a+b/2-b/2=a by ring] using hφ
  have hc' : Real.cos b-1= -2*(Real.sin (b/2))^2 := by
    simpa only [show 2*(b/2)=b by ring] using hc
  rw [hφ']
  nlinarith

theorem negative_surplus {l a b : ℝ} (hl : (13/20 : ℝ)≤l)
    (ha : 0≤a) (hb : 0≤b) (hspan : a+b≤frameCap) :
    0≤l*(PositiveAngularEnvelope.phi a-1)+Real.cos (a+b)-Real.cos b := by
  have hF : a+b≤7/10 := hspan
  have hbr := negative_bracket hl hb (by linarith : 0≤a/2)
    (show b+2*(a/2)≤frameCap by show b+2*(a/2)≤7/10; linarith)
  have hsin : 0≤Real.sin (a/2) := (half_trig
    (show a/2∈Icc 0 (frameCap/2) from ⟨by linarith,by show a/2≤7/10/2; linarith⟩)).2.1
  have hp := mul_nonneg (show 0≤2*Real.sin (a/2) by linarith) hbr
  have hφ := phi_double_shift (a/2)
  have hc := cosine_difference (b+a/2) (a/2)
  have hφ' : PositiveAngularEnvelope.phi a-1=2*Real.sin (a/2)*(Real.cos (a/2)-Real.sin (a/2)) := by
    simpa only [show 2*(a/2)=a by ring] using hφ
  have hc' : Real.cos (a+b)-Real.cos b=
      -2*Real.sin (b+a/2)*Real.sin (a/2) := by
    simpa only [show b+a/2+a/2=a+b by ring,
      show b+a/2-a/2=b by ring] using hc
  rw [hφ']
  nlinarith

/-- The complete signed width minimum.  Only the three pairwise frame
differences enter; the middle frame may lie outside the other two. -/
theorem signed_width {l d v : ℝ} (hl : l∈Icc (13/20 : ℝ) 1)
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hs : |d+v|≤frameCap) :
    endpointWidth l (d+v)≤l*psi d+psi v := by
  have hl0 : 0≤l := by linarith [hl.1]
  by_cases hd0 : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    rw [psi_positive hd']
    by_cases hv0 : 0≤v
    · have hv' : v∈Icc 0 frameCap := ⟨hv0,(le_abs_self v).trans hv⟩
      have hs0 : 0≤d+v := add_nonneg hd0 hv0
      have hsum : d+v≤frameCap := (le_abs_self _).trans hs
      have hconc := concave_zero_subadditive phi_increment_concave (by simp)
        hd0 hv0 hsum
      have hmul := mul_le_mul_of_nonneg_left hconc hl0
      have hmore := mul_nonneg (sub_nonneg.mpr hl.2)
        (sub_nonneg.mpr (one_le_phi hv'))
      rw [psi_positive hv']
      simp only [endpointWidth,hs0,↓reduceIte]
      nlinarith
    · have hn : -v∈Icc 0 frameCap := ⟨by linarith,
        by simpa [abs_of_neg (lt_of_not_ge hv0)] using hv⟩
      have hψ : psi v=Real.cos (-v)-1 := by
        simpa only [neg_neg] using psi_negative hn
      rw [hψ]
      by_cases hs0 : 0≤d+v
      · have hsur := positive_surplus hl.1 hs0 hn.1
          (show (d+v)+(-v)≤frameCap by linarith [hd'.2])
        rw [show d+v+-v=d by ring] at hsur
        simp only [endpointWidth,hs0,↓reduceIte]
        linarith
      · have hsur := negative_surplus hl.1 hd0
          (show 0≤-(d+v) by linarith)
          (show d+(-(d+v))≤frameCap by linarith [hn.2])
        rw [show d+-(d+v)= -v by ring] at hsur
        simp only [endpointWidth,hs0,↓reduceIte]
        simp only [Real.cos_neg] at hsur ⊢
        linarith
  · have hn : -d∈Icc 0 frameCap := ⟨by linarith,
      by simpa [abs_of_neg (lt_of_not_ge hd0)] using hd⟩
    have hψ : psi d=Real.cos (-d)-1 := by
      simpa only [neg_neg] using psi_negative hn
    rw [hψ]
    by_cases hv0 : 0≤v
    · have hv' : v∈Icc 0 frameCap := ⟨hv0,(le_abs_self v).trans hv⟩
      rw [psi_positive hv']
      by_cases hs0 : 0≤d+v
      · have hsur := positive_surplus (show (13/20 : ℝ)≤1 by norm_num) hs0 hn.1
          (show (d+v)+(-d)≤frameCap by linarith [hv'.2])
        rw [show d+v+-d=v by ring,one_mul] at hsur
        have hrem := mul_nonneg (sub_nonneg.mpr hl.2)
          (show 0≤1-Real.cos (-d) by linarith [Real.cos_le_one (-d)])
        have hs' : d+v∈Icc 0 frameCap := ⟨hs0,(le_abs_self _).trans hs⟩
        have hmore := mul_nonneg (sub_nonneg.mpr hl.2)
          (sub_nonneg.mpr (one_le_phi hs'))
        simp only [endpointWidth,hs0,↓reduceIte]
        nlinarith
      · have hsur := negative_surplus (show (13/20 : ℝ)≤1 by norm_num) hv0
          (show 0≤-(d+v) by linarith)
          (show v+(-(d+v))≤frameCap by linarith [hn.2])
        rw [show v+-(d+v)= -d by ring,one_mul] at hsur
        have hrem := mul_nonneg (sub_nonneg.mpr hl.2)
          (show 0≤1-Real.cos (-d) by linarith [Real.cos_le_one (-d)])
        simp only [endpointWidth,hs0,↓reduceIte]
        simp only [Real.cos_neg] at hsur hrem ⊢
        nlinarith
    · have hvn : -v∈Icc 0 frameCap := ⟨by linarith,
        by simpa [abs_of_neg (lt_of_not_ge hv0)] using hv⟩
      have hψv : psi v=Real.cos (-v)-1 := by
        simpa only [neg_neg] using psi_negative hvn
      have hsum : -d+-v≤frameCap := by
        have hsum0 : d+v<0 := by linarith
        rw [abs_of_neg hsum0] at hs
        linarith
      have hconc := concave_zero_subadditive cosine_increment_concave (by simp)
        hn.1 hvn.1 hsum
      have hrem := mul_nonneg (sub_nonneg.mpr hl.2)
        (show 0≤1-Real.cos (-d) by linarith [Real.cos_le_one (-d)])
      have hcos : Real.cos (-d+-v)=Real.cos (d+v) := by
        rw [show -d+-v= -(d+v) by ring,Real.cos_neg]
      rw [hcos] at hconc
      have hs0 : ¬0≤d+v := by linarith
      rw [hψv]
      simp only [endpointWidth,hs0,↓reduceIte]
      nlinarith

end SquaresInCircles.Eight.MiddleAngularPenalty
