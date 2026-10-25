module

public import SquaresInCircles.Eight.Boundary.ActualOrdinaryBlocks
public import SquaresInCircles.Eight.Frames.Ordinary.PositiveEnvelope
public import SquaresInCircles.Eight.Owners.Endpoint.BudgetScalars
public import SquaresInCircles.Eight.Owners.SpanNormBounds
public import SquaresInCircles.Eight.Words.Middle.PhysicalStress

/-!
# Eight squares: the common middle stress from either original AB owner

The conclusion (`middle_stress`) uses the signed T tangent, any lower bound for the original A
primary, and the original T--A frame difference. The B frame is eliminated by width and norm
comparisons on the whole interval (`B_eq_width`, `single_increment_lower`). No endpoint,
alignment, G/T sign, core or changed point enters.
-/

section
/-!
## Exact three-frame width minimum for the middle stress

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
end
end
end

section
/-!
## Signed middle-block compression, including cancellation

The two same-sign inequalities use the proved
whole-interval concavity. Opposite signs use the actual finite derivative
bounds and the ordinary chord bounds. Thus cancellation preserves the
original signed error and does not require the original errors to share
a sign.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleAngularStress
open PositiveAngularEnvelope OrdinaryAngleConcavity ActualOrdinaryBlocks
open OrdinaryNegativeEnvelope OrdinaryPositiveEnvelope

def B (lambda s : ℝ) : ℝ :=
  if 0≤ s then U (Real.sqrt qCap) lambda 1 s
  else V (Real.sqrt qCap) lambda 1 (-s)

theorem B_of_nonneg {lambda s : ℝ} (hs : 0≤ s) :
    B lambda s=U (Real.sqrt qCap) lambda 1 s := by simp [B,hs]

theorem B_of_nonpos {lambda s : ℝ} (hs : s≤0) :
    B lambda s=V (Real.sqrt qCap) lambda 1 (-s) := by
  by_cases hz : s=0
  · simp [B,hz]
  · have hnot : ¬0 ≤ s := not_le.mpr (lt_of_le_of_ne hs hz)
    simp [B,hnot]

@[simp] theorem B_zero (lambda : ℝ) : B lambda 0=0 := by simp [B]

theorem opposite_subadditive {lambda x s : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25))
    (hx : x∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    B lambda (x-s)≤U (Real.sqrt qCap) lambda 1 x+V (Real.sqrt qCap) lambda 1 s := by
  have hl0 : 0<lambda := by linarith [hl.1]
  have hl1 : lambda≤1 := by linarith [hl.2]
  have hl2 : (1:ℝ)≤2*lambda := by linarith [hl.1]
  by_cases hsx : s≤x
  · have hdiff : x-s∈Icc 0 frameCap := ⟨by linarith,by linarith [hx.2,hs.1]⟩
    rw [B_of_nonneg hdiff.1]
    have hg := SpanNormBounds.U_growth hl hdiff hx (by linarith [hs.1])
    have hV := V_chord_lower hl0 hl1 hl2 hs
    have hmul := mul_le_mul_of_nonneg_right hl.1 hs.1
    dsimp [SpanNormBounds.U,SpanNormBounds.R] at hg
    linarith [hs.1]
  · have hxs : x ≤ s := (lt_of_not_ge hsx).le
    have hdiff : s-x∈Icc 0 frameCap := ⟨by linarith,by linarith [hs.2,hx.1]⟩
    rw [B_of_nonpos (show x-s≤0 by linarith),show -(x-s)=s-x by ring]
    have hg := SpanNormBounds.V_growth hl hdiff hs (by linarith [hx.1])
    have hU := U_lower (Real.sqrt_nonneg qCap)
      (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le hl0 hl1 hl2 hx
    dsimp [SpanNormBounds.V,SpanNormBounds.R] at hg
    linarith [hx.1]

theorem subadditive {lambda d v : ℝ}
    (hl : lambda∈Icc (13/20 : ℝ) (23/25))
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hsum : |d+v|≤frameCap) :
    B lambda (d+v)≤B lambda d+B lambda v := by
  have hl0 : 0<lambda := by linarith [hl.1]
  have hl1 : lambda≤1 := by linarith [hl.2]
  have hl2 : (1:ℝ)≤2*lambda := by linarith [hl.1]
  have hR := Real.sqrt_nonneg qCap
  have hQ := (Real.sq_sqrt (show 0≤qCap by norm_num [qCap])).le
  by_cases hd0 : 0≤d
  · have hd' : d∈Icc 0 frameCap := ⟨hd0,(le_abs_self d).trans hd⟩
    by_cases hv0 : 0≤v
    · rw [B_of_nonneg (add_nonneg hd0 hv0),B_of_nonneg hd0,B_of_nonneg hv0]
      exact concave_zero_subadditive (U_concave hR hQ hl0 hl1 hl2) (by simp)
        hd0 hv0 ((le_abs_self (d+v)).trans hsum)
    · have hv0' : v≤0 := (lt_of_not_ge hv0).le
      have hv' : -v∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs v).trans hv⟩
      rw [B_of_nonneg hd0,B_of_nonpos hv0']
      simpa only [sub_neg_eq_add] using opposite_subadditive hl hd' hv'
  · have hd0' : d≤0 := (lt_of_not_ge hd0).le
    have hd' : -d∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs d).trans hd⟩
    by_cases hv0 : 0≤v
    · have hv' : v∈Icc 0 frameCap := ⟨hv0,(le_abs_self v).trans hv⟩
      rw [B_of_nonpos hd0',B_of_nonneg hv0]
      have h := opposite_subadditive hl hv' hd'
      simpa only [sub_neg_eq_add,add_comm] using h
    · have hv0' : v≤0 := (lt_of_not_ge hv0).le
      rw [B_of_nonpos (add_nonpos hd0' hv0'),B_of_nonpos hd0',B_of_nonpos hv0']
      have hn : -d+-v≤frameCap := by
        have h := (neg_le_abs (d+v)).trans hsum
        linarith
      simpa only [neg_add_rev,add_comm] using concave_zero_subadditive
        (V_concave hR hQ hl0 hl1 hl2) (by simp)
        (show 0≤-d by linarith) (show 0≤-v by linarith) hn

end SquaresInCircles.Eight.MiddleAngularStress
end
end
end

section
/-!
## The fixed signed middle stress before intermediate order

The weight `1 / sqrt (qCap - 1)` makes the
square-root tangent coefficient exactly one.  The resulting scalar bound
retains both signed G/T tangents and the actual A/B circles.  Its two
continuous sign sectors are proved on their full intervals.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.MiddleOrderScalar
open PositiveAngularEnvelope PairNormCalculus MiddleAngularPenalty
open EndpointRotationPenalty EndpointBudgetScalars CorrelatedSameBlock

def r1 : ℝ := Real.sqrt (qCap-1)
def weight : ℝ := 1/r1
def N (t : ℝ) : ℝ := pairNorm 1 weight t
def rateTerm (l t : ℝ) : ℝ := (1-l)*Real.sin t+l*(1-Real.cos t)

theorem r1_pos : 0<r1 := Real.sqrt_pos.mpr (by norm_num [qCap])

theorem r1_sq : r1^2=qCap-1 := Real.sq_sqrt (by norm_num [qCap])

theorem weight_bounds : (7/12 : ℝ)<weight ∧ weight<3/5 := by
  have hh := r1_sq
  have hp := r1_pos
  have hlo : (5/3 : ℝ)<r1 := by dsimp [qCap] at hh; nlinarith
  have hhi : r1<(12/7 : ℝ) := by dsimp [qCap] at hh; nlinarith
  dsimp [weight]
  constructor
  · apply (lt_div_iff₀ hp).2
    linarith
  · apply (div_lt_iff₀ hp).2
    linarith

theorem weight_pos : 0<weight := by linarith [weight_bounds.1]

theorem r1_weight : r1*weight=1 := by
  dsimp [weight]
  field_simp [r1_pos.ne']

theorem norm_zero_identities : R*weight=N 0 ∧ R*N 0=r1+weight := by
  have hN0 : 0≤N 0 := Real.sqrt_nonneg _
  have hN2 : (N 0)^2=1+weight^2 := by
    simpa [N,pairEnergy,pairProduct] using
      pairNorm_sq (show (0:ℝ)<1 by norm_num) weight_pos
        (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  have hR2 := congrArg (fun z : ℝ => z*weight^2) R_sq
  have hr2 := congrArg (fun z : ℝ => z*weight^2) r1_sq
  have hprod := congrArg (fun z : ℝ => z^2) r1_weight
  have hRlam0 := mul_nonneg R_nonneg weight_pos.le
  have hcoef : R*weight=N 0 := by nlinarith
  refine ⟨hcoef,?_⟩
  have hR := congrArg (fun z : ℝ => z*weight) R_sq
  have hr := congrArg (fun z : ℝ => z*weight) r1_sq
  have hp := congrArg (fun z : ℝ => r1*z) r1_weight
  rw [← hcoef]
  nlinarith

theorem baseline_identity : 2*R*N 0-2*weight-3=S0 := by
  have h := norm_zero_identities.2
  simp only [r1] at h
  simp only [S0]
  linear_combination 2*h

/-- The signed square-root tangent is valid on both sides of zero. -/
theorem norm_tangent {t : ℝ} (ht : |t|≤frameCap) :
    R*(N t-N 0)≤Real.sin t := by
  have hN0 : 0<N 0 := pairNorm_pos (show (0:ℝ)<1 by norm_num) weight_pos
    (by norm_num [frameCap])
  have hN2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) weight_pos ht
  have hZ2 := pairNorm_sq (show (0:ℝ)<1 by norm_num) weight_pos
    (show |(0:ℝ)|≤frameCap by norm_num [frameCap])
  change (N t)^2=pairEnergy 1 weight+2*pairProduct 1 weight*Real.sin t at hN2
  change (N 0)^2=pairEnergy 1 weight+2*pairProduct 1 weight*Real.sin 0 at hZ2
  simp only [pairEnergy,pairProduct,one_pow,one_mul,Real.sin_zero,mul_zero,add_zero] at hN2 hZ2
  have htan : N 0*(N t-N 0)≤weight*Real.sin t := by
    nlinarith [sq_nonneg (N t-N 0)]
  have hm := mul_le_mul_of_nonneg_left htan R_nonneg
  have hc := congrArg (fun z : ℝ => z*Real.sin t) norm_zero_identities.1
  refine le_of_mul_le_mul_left ?_ hN0
  linarith

theorem cosine_loss_linear {t : ℝ} (ht : t∈Icc 0 frameCap) :
    1-Real.cos t≤(7/20)*t := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  have htprod := mul_nonneg ht.1 (show 0≤7/10-t by dsimp [frameCap] at ht; linarith [ht.2])
  nlinarith

theorem short_half_charge {t : ℝ} (ht : t∈Icc 0 frameCap) :
    19*(1-Real.cos t)≤7*Real.sin t := by
  have h2 : t≤7/10 := ht.2
  have hh : t/2∈Icc 0 (frameCap/2) :=
    ⟨by linarith [ht.1],by show t/2≤7/10/2; linarith⟩
  obtain ⟨hc,hs0,hs⟩ := half_trig hh
  have hp := mul_nonneg (show 0≤2*Real.sin (t/2) by linarith)
    (show 0≤7*Real.cos (t/2)-19*Real.sin (t/2) by linarith)
  have hcos : Real.cos t-1= -2*(Real.sin (t/2))^2 := by
    simpa only [show 2*(t/2)=t by ring] using cosine_double_shift (t/2)
  have hsin : Real.sin t=2*Real.sin (t/2)*Real.cos (t/2) := by
    have h := Real.sin_two_mul (t/2)
    rwa [show 2*(t/2)=t by ring] at h
  nlinarith

theorem rate_derivative {l t : ℝ} :
    HasDerivAt (rateTerm l) ((1-l)*Real.cos t+l*Real.sin t) t := by
  have h : HasDerivAt (fun y => (1-l)*Real.sin y+l*(1-Real.cos y))
      ((1-l)*Real.cos t+l*(0- -Real.sin t)) t :=
    ((Real.hasDerivAt_sin t).const_mul (1-l)).add
      (((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).const_mul l)
  have e : (1-l)*Real.cos t+l*(0- -Real.sin t)=(1-l)*Real.cos t+l*Real.sin t := by ring
  rw [e] at h
  exact h

theorem rate_upper {l t : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5)) :
    (1-l)*Real.cos t+l*Real.sin t≤3/4 := by
  have hp : 0≤1-l := by linarith [hl.2]
  have hpu : 1-l≤5/12 := by linarith [hl.1]
  have hl0 : 0≤l := by linarith [hl.1]
  have hp2 := pow_le_pow_left₀ hp hpu 2
  have hl2 := pow_le_pow_left₀ hl0 hl.2 2
  have hid : ((1-l)*Real.cos t+l*Real.sin t)^2+
      ((1-l)*Real.sin t-l*Real.cos t)^2=(1-l)^2+l^2 := by
    nlinarith [Real.sin_sq_add_cos_sq t,
      congrArg (fun z : ℝ => (1-l)^2*z) (Real.sin_sq_add_cos_sq t),
      congrArg (fun z : ℝ => l^2*z) (Real.sin_sq_add_cos_sq t)]
  nlinarith [sq_nonneg ((1-l)*Real.sin t-l*Real.cos t)]

theorem rate_growth {l a b : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5))
    (ha : a∈Icc 0 frameCap) (hb : b∈Icc 0 frameCap) (hab : a≤b) :
    rateTerm l b-rateTerm l a≤(3/4)*(b-a) := by
  have hh := derivative_reserve
    (f := fun t => -rateTerm l t)
    (df := fun t => -((1-l)*Real.cos t+l*Real.sin t))
    (k := -(3/4 : ℝ))
    (fun t ht => (rate_derivative (l := l) (t := t)).neg.continuousAt.continuousWithinAt)
    (fun t ht => (rate_derivative (l := l) (t := t)).neg)
    (fun t ht => by linarith [rate_upper (t := t) hl]) ha hb hab
  linarith

theorem cosine_loss_growth {a b : ℝ}
    (ha : a∈Icc 0 frameCap) (hb : b∈Icc 0 frameCap) (hab : a≤b) :
    Real.cos a-Real.cos b≤(13/20)*(b-a) := by
  have hh := derivative_reserve (f := Real.cos) (df := fun t => -Real.sin t)
    (k := -(13/20 : ℝ)) Real.continuous_cos.continuousOn
    (fun t ht => Real.hasDerivAt_cos t)
    (fun t ht => by
      have hs := (transport_trig (Ioo_subset_Icc_self ht)).2.2.2.1
      linarith) ha hb hab
  linarith

/-- A is at or below T.  The signed A--G error may be negative. -/
theorem positive_sector {l x s : ℝ} (hl : l∈Icc (7/12 : ℝ) (3/5))
    (hx : |x|≤frameCap) (hs : s∈Icc 0 frameCap) (hr : 0≤x+s) :
    Real.sin x-psi x+Real.sin s-l*(PositiveAngularEnvelope.phi s-1)≤(3/4)*(x+s) := by
  have hl0 : 0≤l := by linarith [hl.1]
  have hl1 : 0≤1-l := by linarith [hl.2]
  by_cases hx0 : 0≤x
  · have hx' : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans hx⟩
    have hcx := cosine_loss_linear hx'
    have hcs := mul_le_mul_of_nonneg_left (cosine_loss_linear hs) hl0
    have hss := mul_le_mul_of_nonneg_left (Real.sin_le hs.1) hl1
    have hlam := mul_nonneg (show 0≤l-7/12 by linarith [hl.1]) hs.1
    rw [psi_positive hx']
    dsimp [PositiveAngularEnvelope.phi]
    nlinarith
  · have hv : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hratio := short_half_charge hv
    have hsin0 := (transport_trig hv).2.2.1
    have hC0 : 0≤1-Real.cos (-x) := by linarith [Real.cos_le_one (-x)]
    have hbase : (1+l)*(1-Real.cos (-x))-l*Real.sin (-x)≤0 := by
      have hratio' := mul_le_mul_of_nonneg_left hratio (show 0≤1+l by linarith [hl.1])
      have hmore := mul_nonneg (show 0≤12*l-7 by linarith [hl.1]) hsin0
      nlinarith
    have hgrowth := rate_growth hl hv hs (by linarith)
    have hpsi : psi x=Real.cos (-x)-1 := by
      simpa only [neg_neg] using psi_negative hv
    rw [hpsi]
    dsimp [rateTerm,PositiveAngularEnvelope.phi] at hgrowth ⊢
    simp only [Real.sin_neg,Real.cos_neg] at hbase hgrowth ⊢
    linarith

/-- A lies above T.  The remaining difference is exactly a cosine loss. -/
theorem negative_sector {x s : ℝ}
    (hx : |x|≤frameCap) (hs : -s∈Icc 0 frameCap) (hr : 0≤x+s) :
    Real.sin x-psi x+Real.sin s-(1-PositiveAngularEnvelope.phi (-s))≤(3/4)*(x+s) := by
  have hx0 : 0≤x := by linarith [hs.1]
  have hx' : x∈Icc 0 frameCap := ⟨hx0,(le_abs_self x).trans hx⟩
  have hgrowth := cosine_loss_growth hs hx' (by linarith)
  rw [psi_positive hx']
  dsimp [PositiveAngularEnvelope.phi]
  simp only [Real.sin_neg,Real.cos_neg] at hgrowth ⊢
  linarith

theorem raw_zero {G A B T : SignedPoint} {x d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap)
    (hyA : 0≤A.y) (hyB : B.y≤0)
    (hx : |x|≤frameCap) (hd : |d|≤frameCap) (hv : |v|≤frameCap)
    (hs : |d+v|≤frameCap)
    (hGA : quarterFeasible G A x 0) (hAB : zeroFeasible A B d 0)
    (hBT : quarterFeasible B T v 2) :
    -G.y+T.y≤S0+(Real.sin x-psi x)+Real.sin (d+v)-weight*psi d-psi v := by
  have hcA : A.Contained (R^2) := by
    show A.circle≤R^2
    rw [R_sq]; exact hA
  have hcB : B.Contained (R^2) := by
    show B.circle≤R^2
    rw [R_sq]; exact hB
  have hraw := MiddlePhysicalStress.signed_three_zero R_nonneg hcA hcB hyA hyB
    (by norm_num : (0:ℝ)≤1) weight_pos.le (by norm_num : (0:ℝ)≤1)
    hx hd hv hGA hAB hBT
  have hnx := norm_tangent hx
  have hns := norm_tangent hs
  change -1*G.y+1*T.y≤R*(N x+N (d+v))-
    (1+1)/2-weight-1*(1+psi x)-weight*(1+psi d)-1*(1+psi v) at hraw
  linarith [baseline_identity]

end SquaresInCircles.Eight.MiddleOrderScalar
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace MiddleStress
open Candidate PositiveAngularEnvelope OrdinaryAngleConcavity
open CorrelatedSameBlock MiddlePhysicalStress MiddleAngularPenalty

theorem B_eq_width (l s : ℝ) :
    MiddleAngularStress.B l s=endpointWidth l s-
      Real.sqrt qCap*(pairNorm l 1 s-pairNorm l 1 0) := by
  by_cases hs : 0≤ s
  · simp [MiddleAngularStress.B,endpointWidth,hs,U]
  · simp [MiddleAngularStress.B,endpointWidth,hs,V]

theorem single_increment_lower {l w s : ℝ} (hlw : l≤w) (hw : w≤1)
    (hs : |s|≤frameCap) :
    MiddleAngularStress.B l s≤w*psi s-
      Real.sqrt qCap*(pairNorm l 1 s-pairNorm l 1 0) := by
  rw [B_eq_width]
  by_cases hs0 : 0≤ s
  · have hs' : s∈Icc 0 frameCap := ⟨hs0,(le_abs_self s).trans hs⟩
    have hp := mul_nonneg (sub_nonneg.mpr hlw)
      (sub_nonneg.mpr (one_le_phi hs'))
    simp only [endpointWidth,hs0,↓reduceIte]
    rw [psi_positive hs']
    nlinarith
  · have hn : -s∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs s).trans hs⟩
    have hψ : psi s=Real.cos s-1 := by
      simpa only [neg_neg,Real.cos_neg] using psi_negative hn
    have hp := mul_nonneg (sub_nonneg.mpr hw)
      (show 0≤1-Real.cos s by linarith [Real.cos_le_one s])
    simp only [endpointWidth,hs0,↓reduceIte]
    rw [hψ]
    nlinarith

/-- Both weak AB owners give the same scalar bound, wherever B lies relative to A and T and
for either sign of T. -/
theorem actual_middle {A B T : SignedPoint} {l f d v : ℝ}
    (hA : A.circle≤qCap) (hB : B.circle≤qCap)
    (hyA : 0≤A.y) (hyB : B.y≤0) (hf : f≤A.a)
    (hl : l∈Icc (13/20 : ℝ) (23/25))
    (hd : |d|≤frameCap) (hv : |v|≤frameCap) (hs : |d+v|≤frameCap)
    (hAB : zeroFeasible A B d 0 ∨ zeroFeasible A B d 2)
    (hBT : quarterFeasible B T v 2) :
    f+2+2*l-2*Real.sqrt qCap*Real.sqrt (1+l^2)+
      MiddleAngularStress.B l (d+v)+T.y≤0 := by
  have hR := Real.sqrt_nonneg qCap
  have hq : (Real.sqrt qCap)^2=qCap :=
    Real.sq_sqrt (show 0≤qCap by norm_num [qCap])
  have hcA : A.Contained ((Real.sqrt qCap)^2) := by
    rw [hq]
    exact hA
  have hcB : B.Contained ((Real.sqrt qCap)^2) := by
    rw [hq]
    exact hB
  have hl0 : 0≤l := by linarith [hl.1]
  have hl1 : l≤1 := by linarith [hl.2]
  have hN0 : pairNorm l 1 0=Real.sqrt (1+l^2) := by
    simp [pairNorm_zero,add_comm]
  rcases hAB with hAB | hAB
  · have hraw := raw_zero hR hcA hcB hyA hyB hl0 hf hd hv hAB hBT
    have hwidth := signed_width ⟨hl.1,hl1⟩ hd hv hs
    rw [B_eq_width]
    rw [hN0] at hraw ⊢
    linarith
  · have hraw := raw_two hR hcA hcB hyA hyB hl0 hf hd hv hAB hBT
    have hd' := single_increment_lower (le_refl l) hl1 hd
    have hv' := single_increment_lower hl1 (le_refl (1:ℝ)) hv
    have hsum := MiddleAngularStress.subadditive hl hd hv hs
    rw [hN0] at hraw hd' hv'
    linarith

end MiddleStress

namespace SignedCycle
open Candidate

/-- The common middle stress on the original cycle. It uses only the retained AB owner and BT2,
so it applies also to a GA1 entry cycle. -/
theorem middle_stress {q l f : ℝ} {C : SignedCycle}
    (hq : q≤qCap) (hC : C.Necessary q) (hn : C.NormalAnchors)
    (w : C.Witnesses) (hBT : C.Feasible B 2) (hf : f≤(C.point A).a)
    (hl : l∈Icc (13/20 : ℝ) (23/25)) :
    f+2+2*l-2*Real.sqrt qCap*Real.sqrt (1+l^2)+
      MiddleAngularStress.B l (C.theta T-C.theta A)+(C.point T).y≤0 := by
  have howner : w.owner A=0 ∨ w.owner A=2 := by
    simpa [normalOwners,A] using w.allowed A
  simp only [A] at howner
  have hab : zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 0 ∨
      zeroFeasible (C.point A) (C.point B) (C.theta B-C.theta A) 2 := by
    have hw := w.feasible A
    rcases howner with ho | ho
    · left
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible,ho] using hw
    · right
      simpa [Feasible,slack,edge,delta,next,word,A,B,zeroFeasible,ho] using hw
  have hbt : quarterFeasible (C.point B) (C.point T) (C.theta T-C.theta B) 2 := by
    simpa [Feasible,slack,edge,delta,next,word,B,T,quarterFeasible] using hBT
  have hs : |(C.theta B-C.theta A)+(C.theta T-C.theta B)|≤frameCap := by
    rw [show (C.theta B-C.theta A)+(C.theta T-C.theta B)=C.theta T-C.theta A by ring]
    exact hC.spread T A
  have h := MiddleStress.actual_middle ((hC.contained A).trans hq)
    ((hC.contained B).trans hq) hn.A_nonneg hn.B_nonpos hf hl
    (hC.spread B A) (hC.spread T B) hs hab hbt
  simpa only [show (C.theta B-C.theta A)+(C.theta T-C.theta B)=
    C.theta T-C.theta A by ring] using h

end SignedCycle
end SquaresInCircles.Eight
end
end
end
