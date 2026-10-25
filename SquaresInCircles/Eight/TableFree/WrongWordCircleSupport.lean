module

public import SquaresInCircles.Eight.TableFree.CommonOneEnvelope

/-!
# Intrinsic circle-support transitions on a complete zero-quarter half

An affine functional on the actual outer arc is minimized at the axial
end, at the diagonal end, or at its full-circle support point. The two
changes occur at zeros of the actual endpoint derivatives. The norm
envelope is concave between those changes, so endpoint estimates extend
over the entire angle interval without selecting angular cells.

The derivative events are obtained by the intermediate value theorem;
their numerical locations are neither supplied nor used.
Uncompiled source draft.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.TableFree.WrongWordCircleSupport

open CommonQuarter

def X (p l x : ℝ) : ℝ := -p-l*Real.sin x
def Y (q l x : ℝ) : ℝ := q-l*Real.cos x
def mass (p q l : ℝ) : ℝ := p^2+q^2+l^2
def N (p q l x : ℝ) : ℝ :=
  CircularNorm.norm (mass p q l) (-2*l*q) (2*l*p) x

def base (c l x : ℝ) : ℝ := x+c+l*(1+Real.sin x+Real.cos x)/2
def axial (c p q l x : ℝ) : ℝ := base c l x+X p l x*outerAxial
def diagonal (c p q l x : ℝ) : ℝ :=
  base c l x+(X p l x+Y q l x)*outerDiagonal
def full (c p q l x : ℝ) : ℝ :=
  base c l x-(X p l x+Y q l x)/2-CommonQuarter.radius*N p q l x

/-- Endpoint derivatives, with the positive axial denominator cleared. -/
def axialSlope (p q l x : ℝ) : ℝ :=
  (outerAxial+1/2)*Y q l x-X p l x/2
def diagonalSlope (p q l x : ℝ) : ℝ := Y q l x-X p l x

lemma energy_eq (p q l x : ℝ) :
    CircularNorm.energy (mass p q l) (-2*l*q) (2*l*p) x=
      (X p l x)^2+(Y q l x)^2 := by
  dsimp [CircularNorm.energy,mass,X,Y]
  linear_combination -(l^2)*(Real.sin_sq_add_cos_sq x)

lemma coefficient_identity (p q l x : ℝ) :
    p^2+q^2=l^2+(X p l x)^2+(Y q l x)^2+
      2*l*(X p l x*Real.sin x+Y q l x*Real.cos x) := by
  dsimp [X,Y]
  linear_combination (l^2)*(Real.sin_sq_add_cos_sq x)

lemma energy_pos {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    0<CircularNorm.energy (mass p q l) (-2*l*q) (2*l*p) x := by
  rw [energy_eq]
  by_contra! hn
  have hx : X p l x=0 := by nlinarith [sq_nonneg (Y q l x)]
  have hy : Y q l x=0 := by nlinarith [sq_nonneg (X p l x)]
  have hh := coefficient_identity p q l x
  rw [hx,hy] at hh
  nlinarith

lemma N_sq {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    (N p q l x)^2=(X p l x)^2+(Y q l x)^2 := by
  exact (CircularNorm.norm_sq (energy_pos hl hpq).le).trans (energy_eq p q l x)

lemma N_pos {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    0<N p q l x := CircularNorm.norm_pos (energy_pos hl hpq)

lemma N_lt_twice {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    N p q l x<2*l := by
  let t := p*Real.sin x-q*Real.cos x
  have hproj : t^2≤p^2+q^2 := by
    have hid : t^2+(p*Real.cos x+q*Real.sin x)^2=p^2+q^2 := by
      dsimp [t]
      linear_combination (p^2+q^2)*(Real.sin_sq_add_cos_sq x)
    nlinarith [sq_nonneg (p*Real.cos x+q*Real.sin x)]
  have ht : t<l := by nlinarith
  have hn := N_sq (x := x) hl hpq
  have hpos := N_pos (x := x) hl hpq
  have he : (X p l x)^2+(Y q l x)^2=p^2+q^2+l^2+2*l*t := by
    dsimp [X,Y,t]
    linear_combination (l^2)*(Real.sin_sq_add_cos_sq x)
  have hm := mul_pos hl (sub_pos.mpr ht)
  nlinarith

lemma full_expression (c p q l x : ℝ) :
    full c p q l x=x+c+(l+p-q)/2+l*(Real.sin x+Real.cos x)-CommonQuarter.radius*N p q l x := by
  dsimp [full,base,X,Y]
  ring

def fullD (p q l x : ℝ) : ℝ := 1+l*(Real.cos x-Real.sin x)-
  CommonQuarter.radius*CircularNorm.d1 (mass p q l) (-2*l*q) (2*l*p) x
def fullDD (p q l x : ℝ) : ℝ := -l*(Real.sin x+Real.cos x)-
  CommonQuarter.radius*CircularNorm.d2 (mass p q l) (-2*l*q) (2*l*p) x

lemma full_hasDerivAt {c p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    HasDerivAt (full c p q l) (fullD p q l x) x := by
  have hn := CircularNorm.norm_hasDerivAt (energy_pos (x := x) hl hpq)
  have hf : full c p q l=fun z => z+c+(l+p-q)/2+l*(Real.sin z+Real.cos z)-CommonQuarter.radius*N p q l z := by
    funext z
    exact full_expression c p q l z
  rw [hf]
  have h := ((((hasDerivAt_id' x).add_const c).add_const ((l+p-q)/2)).fun_add
    (((Real.hasDerivAt_sin x).fun_add (Real.hasDerivAt_cos x)).const_mul l)).fun_sub
      (hn.const_mul CommonQuarter.radius)
  exact h.congr_deriv (by unfold fullD; ring)

lemma fullD_hasDerivAt {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    HasDerivAt (fullD p q l) (fullDD p q l x) x := by
  have hn := CircularNorm.d1_hasDerivAt (energy_pos (x := x) hl hpq)
  have h := ((((Real.hasDerivAt_cos x).fun_sub (Real.hasDerivAt_sin x)).const_mul l).const_add
    1).fun_sub (hn.const_mul CommonQuarter.radius)
  exact h.congr_deriv (by unfold fullDD; ring)

lemma full_concave {c p q l : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    ConcaveOn ℝ (Icc 0 (7/10)) (full c p q l) := by
  apply concave_of_deriv2 (fun x _ => full_hasDerivAt hl hpq)
    (fun x _ => fullD_hasDerivAt hl hpq)
  intro x hx
  have hcoef : (-2*l*q)^2+(2*l*p)^2≤(mass p q l)^2 := by
    dsimp [mass]
    nlinarith [sq_nonneg (p^2+q^2-l^2)]
  have hcurv := CircularNorm.curvature_lower (energy_pos (x := x) hl hpq) hcoef
  have hR : 0<CommonQuarter.radius := by linarith [radius_bounds.1]
  have hprod := mul_le_mul_of_nonneg_left hcurv hR.le
  have hnorm := mul_lt_mul_of_pos_left (N_lt_twice (x := x) hl hpq) hR
  have hRmass := mul_lt_mul_of_pos_right (show CommonQuarter.radius<2 by linarith [radius_bounds.2]) hl
  have hwidth := mul_le_mul_of_nonneg_left (positive_trig hx).2.2.2.2.2 hl.le
  change CommonQuarter.radius*(-N p q l x/4)≤CommonQuarter.radius*
    CircularNorm.d2 (mass p q l) (-2*l*q) (2*l*p) x at hprod
  dsimp [fullDD]
  nlinarith

/-- The circle support agrees with an endpoint whenever the force points
straight inward there. This is the exact Cauchy equality, not a bound. -/
lemma circle_support_eq {X Y a b : ℝ}
    (hc : (a+1/2)^2+(b+1/2)^2=Q0)
    (hcross : X*(b+1/2)-Y*(a+1/2)=0)
    (hdot : X*(a+1/2)+Y*(b+1/2)≤0) :
    -(X+Y)/2-CommonQuarter.radius*Real.sqrt (X^2+Y^2)=X*a+Y*b := by
  have hn := Real.sqrt_nonneg (X^2+Y^2)
  have hn2 := Real.sq_sqrt (show 0≤X^2+Y^2 by positivity)
  have hR : 0≤CommonQuarter.radius := by linarith [radius_bounds.1]
  have hprod := mul_nonneg hR hn
  have hsq : (CommonQuarter.radius*Real.sqrt (X^2+Y^2))^2=
      (X*(a+1/2)+Y*(b+1/2))^2 := by
    rw [mul_pow,radius_sq,hn2,← hc]
    have hid : ((a+1/2)^2+(b+1/2)^2)*(X^2+Y^2)-
        (X*(a+1/2)+Y*(b+1/2))^2=(X*(b+1/2)-Y*(a+1/2))^2 := by ring
    rw [hcross] at hid
    nlinarith only [hid]
  have he : CommonQuarter.radius*Real.sqrt (X^2+Y^2)=-(X*(a+1/2)+Y*(b+1/2)) := by
    nlinarith
  linarith

lemma N_eq_sqrt {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2) :
    N p q l x=Real.sqrt ((X p l x)^2+(Y q l x)^2) := by
  rw [N,CircularNorm.norm,energy_eq]

lemma coeff_not_both_nonneg {p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2)
    (hx : x∈Icc 0 (7/10)) : ¬(0≤X p l x ∧ 0≤Y q l x) := by
  rintro ⟨hX,hY⟩
  have ht := positive_trig hx
  have hm := mul_nonneg hl.le (add_nonneg
    (mul_nonneg hX ht.2.2.1) (mul_nonneg hY (show 0≤Real.cos x by linarith [ht.1])))
  nlinarith [coefficient_identity p q l x,sq_nonneg (X p l x),sq_nonneg (Y q l x)]

lemma full_at_diagonal_event {c p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2)
    (hx : x∈Icc 0 (7/10)) (he : diagonalSlope p q l x=0) :
    full c p q l x=diagonal c p q l x := by
  have hXY : Y q l x=X p l x := by simpa [diagonalSlope,sub_eq_zero] using he
  have hX : X p l x<0 := by
    by_contra! hn
    exact coeff_not_both_nonneg hl hpq hx ⟨hn,by rw [hXY]; exact hn⟩
  have hd : 0≤outerDiagonal+1/2 := by linarith [outer_endpoint_bounds.2.2.1]
  have hs := circle_support_eq (X := X p l x) (Y := Y q l x)
    (a := outerDiagonal) (b := outerDiagonal)
    (by nlinarith [diagonal_circle]) (by rw [hXY]; ring)
    (by rw [hXY]; nlinarith [mul_nonpos_of_nonpos_of_nonneg hX.le hd])
  rw [full,N_eq_sqrt hl hpq,diagonal]
  linarith

lemma full_at_axial_event {c p q l x : ℝ} (hl : 0<l) (hpq : p^2+q^2<l^2)
    (hx : x∈Icc 0 (7/10)) (he : axialSlope p q l x=0) :
    full c p q l x=axial c p q l x := by
  have hu : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
  have he' : (outerAxial+1/2)*Y q l x=X p l x/2 := by
    simpa [axialSlope,sub_eq_zero] using he
  have hX : X p l x<0 := by
    by_contra! hn
    have hY : 0≤Y q l x := by nlinarith
    exact coeff_not_both_nonneg hl hpq hx ⟨hn,hY⟩
  have hY : Y q l x<0 := by nlinarith
  have hs := circle_support_eq (X := X p l x) (Y := Y q l x)
    (a := outerAxial) (b := 0) (by simpa using axial_circle)
    (by nlinarith only [he'])
    (by nlinarith [mul_neg_of_neg_of_pos hX hu])
  rw [full,N_eq_sqrt hl hpq,axial]
  linarith

lemma outer_axial_lower {a b X Y : ℝ} (hc : OuterState a b)
    (hX : X≤0) (hder : 0≤(outerAxial+1/2)*Y-X/2) :
    X*outerAxial≤X*a+Y*b := by
  have hb := hc.1
  have hu : 0<outerAxial+1/2 := by linarith [outer_endpoint_bounds.1]
  have htangent : (outerAxial+1/2)*(a-outerAxial)+b/2≤0 := by
    nlinarith [hc.2.2,axial_circle,sq_nonneg (a-outerAxial),sq_nonneg b]
  have hp := mul_nonneg_of_nonpos_of_nonpos hX htangent
  have hd := mul_nonneg hder hb
  nlinarith

lemma outer_diagonal_lower {a b X Y : ℝ} (hc : OuterState a b)
    (hX : X≤0) (hder : Y-X≤0) : (X+Y)*outerDiagonal≤X*a+Y*b := by
  have hh := outer_bounds hc
  have hp := mul_le_mul_of_nonpos_left hh.2.2.2.2 hX
  have hq := mul_le_mul_of_nonpos_left hh.2.2.2.1 hder
  nlinarith

lemma outer_concave_lower {a b X Y m : ℝ} (hc : OuterState a b)
    (hX : 0≤X) (hA : m≤X*outerAxial) (hD : m≤(X+Y)*outerDiagonal) :
    m≤X*a+Y*b := by
  have hb := outer_bounds hc
  have hl : m≤X*Arithmetic.circleX (-1/2) CommonQuarter.radius 0+Y*0 := by
    rw [outer_branch_endpoints.1]
    linarith
  have hu : m≤X*Arithmetic.circleX (-1/2) CommonQuarter.radius outerDiagonal+Y*outerDiagonal := by
    rw [outer_branch_endpoints.2]
    linarith
  have hh := Arithmetic.circle_endpoints_lower (X := X) (Y := Y)
    hX (fun z hz => outer_radicand_pos hz) ⟨hc.1,hb.2.2.2.1⟩ hl hu
  rw [← outer_branch hc] at hh
  exact hh

/-- On the actual interior-support region, concavity joins the two
intrinsic derivative events. The left event may coincide with angle
zero when its full-circle value already has the required bound. -/
theorem interior_full_lower {c p q l m x : ℝ} (hl : 0<l)
    (hpq : p^2+q^2<l^2) (hx : x∈Icc 0 (7/10))
    (hA : ∀z∈Icc 0 (7/10),m<axial c p q l z)
    (hD : ∀z∈Icc 0 (7/10),m<diagonal c p q l z)
    (hleft : diagonalSlope p q l 0≤0 ∨ m<full c p q l 0)
    (hright : 0≤axialSlope p q l (7/10))
    (hd : 0<diagonalSlope p q l x) (ha : axialSlope p q l x<0) :
    m<full c p q l x := by
  have hAc : Continuous (axialSlope p q l) := by unfold axialSlope X Y; fun_prop
  have hDc : Continuous (diagonalSlope p q l) := by unfold diagonalSlope X Y; fun_prop
  obtain ⟨u,hu,heu⟩ := intermediate_value_Icc hx.2 hAc.continuousOn
    (show (0:ℝ)∈Icc (axialSlope p q l x) (axialSlope p q l (7/10)) from
      ⟨ha.le,hright⟩)
  have hu' : u∈Icc 0 (7/10) := ⟨hx.1.trans hu.1,hu.2⟩
  have hFu : m<full c p q l u := by
    rw [full_at_axial_event hl hpq hu' heu]
    exact hA u hu'
  obtain ⟨v,hv,hFv⟩ : ∃v,v∈Icc 0 x ∧ m<full c p q l v := by
    rcases hleft with hleft | hleft
    · obtain ⟨v,hv,hev⟩ := intermediate_value_Icc hx.1 hDc.continuousOn
        (show (0:ℝ)∈Icc (diagonalSlope p q l 0) (diagonalSlope p q l x) from
          ⟨hleft,hd.le⟩)
      have hv' : v∈Icc 0 (7/10) := ⟨hv.1,hv.2.trans hx.2⟩
      refine ⟨v,hv,?_⟩
      rw [full_at_diagonal_event hl hpq hv' hev]
      exact hD v hv'
    · exact ⟨0,⟨le_rfl,hx.1⟩,hleft⟩
  have hconc := (full_concave (c := c) hl hpq).subset
    (Icc_subset_Icc hv.1 hu.2) (convex_Icc v u)
  exact concave_gt_of_endpoints hconc ⟨hv.2,hu.1⟩ hFv hFu

/-- Complete actual-arc support from its two endpoint families and the
intrinsic norm transition. No angle event is a supplied parameter. -/
theorem actual_arc_lower {c p q l m a b x : ℝ} (hc : OuterState a b)
    (hl : 0<l) (hpq : p^2+q^2<l^2) (hx : x∈Icc 0 (7/10))
    (hA : ∀z∈Icc 0 (7/10),m<axial c p q l z)
    (hD : ∀z∈Icc 0 (7/10),m<diagonal c p q l z)
    (hleft : diagonalSlope p q l 0≤0 ∨ m<full c p q l 0)
    (hright : 0≤axialSlope p q l (7/10)) :
    m<base c l x+X p l x*a+Y q l x*b := by
  by_cases hX : 0≤X p l x
  · have hs := outer_concave_lower (Y := Y q l x)
      (m := min (X p l x*outerAxial) ((X p l x+Y q l x)*outerDiagonal)) hc hX
      (min_le_left _ _) (min_le_right _ _)
    have h1 := hA x hx
    have h2 := hD x hx
    dsimp only [axial] at h1
    dsimp only [diagonal] at h2
    have hmin : m-base c l x < min (X p l x*outerAxial) ((X p l x+Y q l x)*outerDiagonal) :=
      lt_min (by linarith) (by linarith)
    linarith
  have hX' : X p l x≤0 := (lt_of_not_ge hX).le
  by_cases hD' : diagonalSlope p q l x≤0
  · have hs := outer_diagonal_lower hc hX' hD'
    have hh := hD x hx
    dsimp [diagonal] at hh
    linarith
  by_cases hA' : 0≤axialSlope p q l x
  · have hs := outer_axial_lower hc hX' hA'
    have hh := hA x hx
    dsimp [axial] at hh
    linarith
  have hh := interior_full_lower hl hpq hx hA hD hleft hright
    (lt_of_not_ge hD') (lt_of_not_ge hA')
  have hs := outer_circle_lower (X := X p l x) (Y := Y q l x) hc
  rw [full,N_eq_sqrt hl hpq] at hh
  linarith

end SquaresInCircles.Eight.TableFree.WrongWordCircleSupport
