module

public import SquaresInCircles.Eight.TableFree.FlatCoreNegativePrimary

/-!
# A genuinely negative primary forces the actual flat-core branch

Uncompiled draft. The comparison uses the original weak GA1 separator and
the strict failure of GA0. Both shifted corners are evaluated at the same
input radius. The strict vector inequality excludes an outer G; it is not
an inference from a numerical state search.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree

/-- The primary and rotated projections bound two perpendicular coordinates
of the same A corner. The second bound is strict because GA0 is unavailable. -/
theorem negative_primary_contact_vector
    {a g A b z : ℝ} (ha : 0<a) (hg : 0≤g) (hga : g≤a)
    (hz : 0<z ∧ z≤7/10)
    (hprimary : edgeWidth (-z)≤A-a*Real.sin z-g*Real.cos z)
    (hsecondary : A*Real.cos z-b*Real.sin z-g<edgeWidth (-z)) :
    1+(a+1/2)^2+(g+1/2)^2+
        2*((g+1/2)*Real.cos z+(a+1/2)*Real.sin z) <
      (A+1/2)^2+(b+1/2)^2 ∧
    (a+1/2)^2+(g+3/2)^2 < (A+1/2)^2+(b+1/2)^2 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ⟨hz.1.le,hz.2⟩
  have hsp : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz.1
    (by linarith only [hz.2,Real.pi_gt_three])
  have hcp : 0<Real.cos z := by linarith only [hc]
  rw [edgeWidth_negative_formula ⟨hz.1.le,hz.2⟩] at hprimary hsecondary
  let K := a+1/2
  let D := g+1/2
  let X := A+1/2
  let Z := b+1/2
  have hK : 0<K := by dsimp [K]; linarith only [ha]
  have hD : 0<D := by dsimp [D]; linarith only [hg]
  have hKD : D≤K := by dsimp [D,K]; linarith only [hga]
  have hX : 1+K*Real.sin z+D*Real.cos z≤X := by
    dsimp [K,D,X]; linarith only [hprimary]
  have hZraw : (X-1)*Real.cos z-D<Z*Real.sin z := by
    dsimp [K,D,X,Z]; linarith only [hsecondary]
  have hrot : 0<K*Real.cos z-D*Real.sin z := by
    have hfirst := mul_pos hK (sub_pos.mpr hsc)
    have hsecond := mul_nonneg (sub_nonneg.mpr hKD) hs0
    linarith only [hfirst,hsecond]
  have hZ : K*Real.cos z-D*Real.sin z<Z := by
    have hmul := mul_le_mul_of_nonneg_right hX hcp.le
    have hu := Real.sin_sq_add_cos_sq z
    have hid :
        (K*Real.sin z+D*Real.cos z)*Real.cos z-D =
          (K*Real.cos z-D*Real.sin z)*Real.sin z := by
      linear_combination D*hu
    have hh : (K*Real.cos z-D*Real.sin z)*Real.sin z<Z*Real.sin z := by
      rw [← hid]
      linarith only [hmul,hZraw]
    exact lt_of_mul_lt_mul_right hh hsp.le
  have hXpos : 0<1+K*Real.sin z+D*Real.cos z := by
    have h1 := mul_nonneg hK.le hs0
    have h2 := mul_pos hD hcp
    linarith only [h1,h2]
  have hXs := pow_le_pow_left₀ hXpos.le hX 2
  have hZs := pow_lt_pow_left₀ hZ hrot.le (by decide : (2:ℕ)≠0)
  have hid : (1+K*Real.sin z+D*Real.cos z)^2+
      (K*Real.cos z-D*Real.sin z)^2 =
      1+K^2+D^2+2*(D*Real.cos z+K*Real.sin z) := by
    linear_combination (K^2+D^2)*Real.sin_sq_add_cos_sq z
  have hfirst : 1+K^2+D^2+2*(D*Real.cos z+K*Real.sin z)<X^2+Z^2 := by
    linarith only [hXs,hZs,hid]
  have hsum : 1≤Real.sin z+Real.cos z := by
    have h := one_le_abs_cos_add_abs_sin z
    rw [abs_of_nonneg hcp.le,abs_of_nonneg hs0] at h
    linarith only [h]
  have hsupp : D≤D*Real.cos z+K*Real.sin z := by
    have hm := mul_nonneg hD.le (sub_nonneg.mpr hsum)
    have hn := mul_nonneg (sub_nonneg.mpr hKD) hs0
    linarith only [hm,hn]
  dsimp [K,D,X,Z] at hfirst hsupp
  exact ⟨hfirst,by linarith only [hfirst,hsupp]⟩

/-- The comparison is attached to actual signed points and their actual
circle values. The original A tangent is not replaced by a convenient one. -/
theorem negative_primary_flat_entry {q z : ℝ} {G A : SignedPoint}
    (hGs : G.Sorted) (hAs : A.Sorted)
    (hGb : G.Boundary q) (hAc : A.Contained q) (hq : q≤qCap)
    (hGy : G.y≤0) (hAy : 0≤A.y)
    (hz : 0<z ∧ z≤7/10)
    (hGA1 : quarterFeasible G A (-z) 1)
    (hnotGA0 : ¬quarterFeasible G A (-z) 0) :
    G.a=7/12 ∧ |G.y|<1/2 ∧ G.Core ∧
      1+(G.a+1/2)^2+(|G.y|+1/2)^2+
          2*((|G.y|+1/2)*Real.cos z+(G.a+1/2)*Real.sin z) <q := by
  have habs : |G.y|= -G.y := abs_of_nonpos hGy
  have hfirst : edgeWidth (-z)≤A.a-G.a*Real.sin z-|G.y| * Real.cos z := by
    have h : edgeWidth (-z)≤A.a+G.a*Real.sin (-z)+G.y*Real.cos (-z) := hGA1
    rw [Real.sin_neg,Real.cos_neg] at h
    rw [habs]
    linarith only [h]
  have hsecond : A.a*Real.cos z-A.y*Real.sin z-|G.y|<edgeWidth (-z) := by
    have hh : ¬edgeWidth (-z)≤G.y+A.a*Real.cos (-z)+A.y*Real.sin (-z) := hnotGA0
    rw [Real.sin_neg,Real.cos_neg,not_le] at hh
    rw [habs]
    linarith only [hh]
  obtain ⟨hv,hstrict⟩ := negative_primary_contact_vector hGs.1
    (abs_nonneg G.y) hGs.2 hz hfirst hsecond
  have hAc' : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] using hAc
  have houter : ¬G.Outer q := by
    intro ho
    unfold SignedPoint.Outer SignedPoint.circle at ho
    obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig ⟨hz.1.le,hz.2⟩
    have h1 := mul_nonneg (by positivity : 0≤|G.y|+1/2) (by linarith only [hc] : 0≤Real.cos z)
    have h2 := mul_nonneg (by linarith only [hGs.1] : 0≤G.a+1/2) hs0
    linarith only [ho,hv,hAc',h1,h2]
  have hc := SignedPoint.core_of_not_outer hGb houter
  have hgsmall : |G.y|<1/2 := by
    by_contra! hbig
    have hK : 1≤G.a+1/2 := by linarith only [hGs.2,hbig]
    have hD : 2≤|G.y|+3/2 := by linarith only [hbig]
    have hq' : q≤9789/2500 := hq
    have hK2 := mul_le_mul hK hK zero_le_one (by linarith only [hK])
    have hD2 := mul_le_mul hD hD (by norm_num) (by linarith only [hD])
    linarith only [hstrict,hAc',hq',hK2,hD2]
  have hflat := (SignedPoint.flat_core_iff hGs hgsmall.le).1 hc
  exact ⟨hflat,hgsmall,hc,hv.trans_le hAc'⟩

/-- Exact half-angle bound on the exceptional quarter-interval. -/
theorem exceptional_half_tangent {z : ℝ} (hz : 0≤z ∧ z≤1/4) :
    0≤Real.tan (z/2) ∧ Real.tan (z/2)<63/500 := by
  have hx : z/2∈Icc 0 (1/8 : ℝ) := by constructor <;> linarith
  have ht := trig_bracket (l := 0) (u := (1/8 : ℝ))
    (by norm_num) (by linarith [Real.pi_gt_three]) hx
  have hc := transport_cos_pos (x := z/2) (by
    rw [abs_of_nonneg hx.1]; linarith [hx.2])
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hx.1
    (by linarith [hx.2,Real.pi_gt_three])
  rw [Real.tan_eq_sin_div_cos]
  refine ⟨div_nonneg hs hc.le,?_⟩
  rw [div_lt_iff₀ hc]
  have hr : (1/8 : ℝ)-(1/8 : ℝ)^3/6+(1/8 : ℝ)^5/120 <
      (63/500 : ℝ)*(1-(1/8 : ℝ)^2/2+(1/8 : ℝ)^4/24-(1/8 : ℝ)^6/720) := by norm_num
  nlinarith [ht.2.1,ht.2.2.1]

/-- A tangent-line disk estimate replaces the derivative computation of the
truncated A circle. It is valid on the whole interval 0≤b≤2/5. -/
theorem exceptional_A_linear_cap {a b : ℝ}
    (hb : 0≤b ∧ b≤2/5)
    (hc : (a+1/2)^2+(b+1/2)^2≤(9789/2500 : ℝ)) :
    b+(63/500)*a < (2/5 : ℝ)+(63/500)*(1263/1000) := by
  by_contra! h
  have hδ : 0≤(2/5 : ℝ)-b := by linarith
  have hy : 0≤a-(1263/1000 : ℝ) := by nlinarith
  have hr : (1763/1000 : ℝ)^2+(9/10 : ℝ)^2-(9789/2500)=2569/1000000 := by norm_num
  nlinarith [sq_nonneg (a-1263/1000),sq_nonneg (b-2/5)]

/-- Strong cuts for the unchanged original A and G in the canceling branch.
These cuts do not assert any transport or new separator. -/
theorem exceptional_negative_primary_cuts {q z : ℝ} {G A : SignedPoint}
    (hGs : G.Sorted) (hAs : A.Sorted)
    (hGb : G.Boundary q) (hAc : A.Contained q) (hq : q≤qCap)
    (hGy : G.y≤0) (hAy : 0≤A.y)
    (hz : 0<z ∧ z≤7/10)
    (hGA1 : quarterFeasible G A (-z) 1)
    (hnotGA0 : ¬quarterFeasible G A (-z) 0) :
    G.a=7/12 ∧ |G.y|<39/250 ∧ z<1/4 ∧
      2/5<A.y ∧ A.a-1/2<763/1000 := by
  obtain ⟨hflat,hgsmall,hcore,hvec⟩ := negative_primary_flat_entry
    hGs hAs hGb hAc hq hGy hAy hz hGA1 hnotGA0
  have habs : |G.y|= -G.y := abs_of_nonpos hGy
  have hp : edgeWidth (-z)≤A.a-G.a*Real.sin z-|G.y| * Real.cos z := by
    have h : edgeWidth (-z)≤A.a+G.a*Real.sin (-z)+G.y*Real.cos (-z) := hGA1
    rw [Real.sin_neg,Real.cos_neg] at h
    rw [habs]
    linarith only [h]
  have hn : A.a*Real.cos z-A.y*Real.sin z-|G.y|<edgeWidth (-z) := by
    have hh : ¬edgeWidth (-z)≤G.y+A.a*Real.cos (-z)+A.y*Real.sin (-z) := hnotGA0
    rw [Real.sin_neg,Real.cos_neg,not_le] at hh
    rw [habs]
    linarith only [hh]
  obtain ⟨hv,hstrict⟩ := negative_primary_contact_vector hGs.1
    (abs_nonneg G.y) hGs.2 hz hp hn
  have hAc' : (A.a+1/2)^2+(A.y+1/2)^2≤q := by
    simpa [SignedPoint.Contained,SignedPoint.circle,abs_of_nonneg hAy] using hAc
  have hq' : q≤(9789/2500 : ℝ) := hq
  have hg0 := abs_nonneg G.y
  have hgcut : |G.y|<39/250 := by
    rw [hflat] at hstrict
    by_contra! h
    have hm := mul_nonneg (sub_nonneg.mpr h) (by positivity : (0:ℝ)≤|G.y|+39/250+3)
    linarith only [hstrict,hm,hAc',hq']
  have hzcut : z<1/4 := by
    by_contra! h
    have hm := PrimaryCap.contactHeight_strictMono.monotoneOn
      (show (1/4 : ℝ)∈Icc 0 (7/10) by constructor <;> norm_num)
      ⟨hz.1.le,hz.2⟩ h
    have hc := Real.one_sub_sq_div_two_le_cos (x := (1/4 : ℝ))
    have hs := Real.sin_ge_sub_cube (show (0:ℝ)≤1/4 by norm_num)
    obtain ⟨hcz,hsz0,hsz⟩ := transport_trig_coarse ⟨hz.1.le,hz.2⟩
    have hprod := mul_nonneg hg0 (by linarith only [hcz] : 0≤Real.cos z)
    have hg2 : (1/2 : ℝ)^2≤(|G.y|+1/2)^2 := by linarith only [hg0,sq_nonneg |G.y|]
    rw [hflat] at hvec
    unfold PrimaryCap.contactHeight PrimaryCap.K at hm
    linarith only [hvec,hq',hm,hc,hs,hprod,hg2]
  have hhalf := exceptional_half_tangent ⟨hz.1.le,hzcut.le⟩
  have hsin : 0<Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz.1
    (by linarith only [hz.2,Real.pi_gt_three])
  have hcos := transport_cos_pos (by rw [abs_of_pos hz.1]; exact hz.2)
  have hhalfId : 1-Real.cos z=Real.sin z*Real.tan (z/2) := by
    have hc2 := transport_cos_pos (x := z/2)
      (by rw [abs_of_nonneg (by linarith only [hz.1] : 0≤z/2)]; linarith only [hz.2])
    have hs2 := Real.sin_two_mul (z/2)
    have hcc := Real.cos_two_mul (z/2)
    rw [show 2*(z/2)=z by ring] at hs2 hcc
    rw [Real.tan_eq_sin_div_cos,hs2,hcc]
    field_simp
    linear_combination (-2:ℝ)*Real.sin_sq_add_cos_sq (z/2)
  have hdiff : 7/12 < A.y+(A.a+|G.y|)*Real.tan (z/2) := by
    rw [hflat] at hp
    have hid :
        (A.a-(7/12)*Real.sin z-|G.y| * Real.cos z)-
          (A.a*Real.cos z-A.y*Real.sin z-|G.y|)=
          Real.sin z*(A.y+(A.a+|G.y|)*Real.tan (z/2)-7/12) := by
      linear_combination (A.a+|G.y|)*hhalfId
    have hpos : 0<Real.sin z*(A.y+(A.a+|G.y|)*Real.tan (z/2)-7/12) := by
      rw [← hid]
      linarith only [hp,hn]
    have htpos := (mul_pos_iff_of_pos_left hsin).1 hpos
    linarith only [htpos]
  have hAcut : 2/5<A.y := by
    by_contra! h
    have hlin := exceptional_A_linear_cap ⟨hAy,h⟩ (hAc'.trans hq')
    have hP0 : 0≤A.a+|G.y| := by linarith only [hAs.1,hg0]
    have hprod := mul_le_mul_of_nonneg_left hhalf.2.le hP0
    linarith only [hlin,hdiff,hprod,hgcut]
  have hPcut : A.a-1/2<763/1000 := by
    by_contra! h
    have h1 := mul_nonneg (show 0≤A.a-1/2-763/1000 by linarith only [h])
      (show 0≤A.a+1/2+1763/1000 by linarith only [hAs.1])
    have h2 := mul_pos (show 0<A.y-2/5 by linarith only [hAcut])
      (show 0<A.y+1/2+9/10 by linarith only [hAy])
    linarith only [h1,h2,hAc',hq']
  exact ⟨hflat,hgcut,hzcut,hAcut,hPcut⟩

end SquaresInCircles.Eight.TableFree