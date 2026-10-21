module

public import SquaresInCircles.Eight.TableFree.NonpositiveDE2ContactBounds

/-!
# Strict EH improvement along the original rotated DE2 contact

Uncompiled reconstruction.  The contact is the actual original D
projection and the radical belongs to E.circle.  Its derivative is
negative by a single cubic inequality on the whole frame interval.
The explicit 1/200 rate turns every positive angular movement into
strict actual EH slack at the endpoint.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.NonpositiveDE2Contact

def Jd (E D : SignedPoint) (α z : ℝ) : ℝ :=
  (U E D z-1)*Real.cos (α+z)+
    (Y D z*U E D z/X E D z)*Real.sin (α+z)

theorem J_derivative {E D H : SignedPoint} {α z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hb : b D z∈Icc 0 (-E.y)) :
    HasDerivAt (J E D H α) (Jd E D α z) z := by
  have hr := (OriginalECircle.root_bounds hEs hEy hb).1
  have hbder := b_derivative D z
  have hader := (OriginalECircle.derivative hEs hEy hb).1.comp z hbder
  have hpder : HasDerivAt (fun w : ℝ => α+w) 1 z := by
    simpa using (hasDerivAt_id z).const_add α
  convert ((hasDerivAt_const z (H.a-1/2)).add
    ((hader.sub_const (1/2)).mul hpder.sin)).sub
      ((hbder.add_const (1/2)).mul hpder.cos) using 1
  · rfl
  · dsimp [Jd,U,X,Y,OriginalECircle.primary,OriginalECircle.slope]
    field_simp [hr.ne']
    ring

/-- The quadratic chord dominates after the nonpositive cubic is
discarded.  Both intrinsic endpoint values leave a reserve beyond
1/150; no angular subdivision is involved. -/
theorem cubic_bound {z : ℝ} (hz : z∈Icc 0 (7/10:ℝ)) :
    (773/1000-(4/5)*z)*
      (1+(4/3)*(3/5+(11/10)*z)*(27/100+z))-1< -(1/150) := by
  have hquad := mul_nonneg hz.1 (show 0≤7/10-z by linarith [hz.2])
  have hcube : 0≤z^3 := pow_nonneg hz.1 3
  have hid : (773/1000-(4/5)*z)*
      (1+(4/3)*(3/5+(11/10)*z)*(27/100+z))-1=
      -(938/15625)-(12073/250000)*z+(1327/7500)*z^2-(88/75)*z^3 := by ring
  rw [hid]
  nlinarith

theorem J_rate {E D : SignedPoint} {α z : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 1<E.a) (hEc : E.circle≤qCap)
    (hDa : 353/500<D.a) (hDy : -D.y∈Ioo (353/500:ℝ) (9/10))
    (hα : α∈Icc 0 (27/100:ℝ)) (hz : z∈Icc 0 (7/10:ℝ)) (hsum : α+z≤7/10)
    (hb : b D z∈Icc 0 (-E.y)) : Jd E D α z< -(1/200) := by
  have hu := U_upper hEs hEy hEc hDy.1 hz hb
  have hr := ratio_upper hEs hEy hEa hDa hDy.2 hz hb
  have hX : 0<X E D z := (OriginalECircle.root_bounds hEs hEy hb).1
  have hY : 0<Y D z := by dsimp [Y]; linarith [hb.1]
  have hp : α+z∈Icc 0 (7/10:ℝ) := ⟨by linarith [hα.1,hz.1],hsum⟩
  have ht := transport_trig hp
  have hc : 0<Real.cos (α+z) := by linarith [ht.1]
  by_cases hU : U E D z≤0
  · have hfirst : (U E D z-1)*Real.cos (α+z)< -(3/4) := by
      have hm := mul_nonpos_of_nonpos_of_nonneg hU hc.le
      nlinarith [ht.1]
    have hratio : Y D z*U E D z/X E D z≤0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hY.le hU) hX.le
    have hsecond := mul_nonpos_of_nonpos_of_nonneg hratio ht.2.2.1
    dsimp [Jd]
    linarith
  have hUpos : 0<U E D z := lt_of_not_ge hU
  let u : ℝ := 773/1000-(4/5)*z
  let r : ℝ := 3/5+(11/10)*z
  have hu0 : 0<u := by dsimp [u]; linarith [hz.2]
  have hr0 : 0<r := by dsimp [r]; linarith [hz.1]
  have hUone : U E D z<1 := by dsimp [u] at *; linarith [hz.1]
  have hfirst : (U E D z-1)*Real.cos (α+z)<(3/4)*(u-1) := by
    have hm := mul_lt_mul_of_neg_left ht.1 (show U E D z-1<0 by linarith)
    linarith
  have hs : Real.sin (α+z)≤27/100+z :=
    (Real.sin_le hp.1).trans (by linarith [hα.2])
  have hproduct : (Y D z/X E D z)*U E D z≤r*u :=
    mul_le_mul hr.le hu.le hUpos.le hr0.le
  have hsecond : (Y D z*U E D z/X E D z)*Real.sin (α+z)≤r*u*(27/100+z) := by
    have hh := mul_le_mul hproduct hs ht.2.2.1 (mul_nonneg hr0.le hu0.le)
    convert hh using 1 <;> ring
  have hpoly := cubic_bound hz
  have hupper : (3/4)*(u-1)+r*u*(27/100+z)< -(1/200) := by
    dsimp [u,r]
    nlinarith
  dsimp [Jd]
  linarith

/-- The original circle contact has a quantified improvement between
any two of its actual nonnegative-tangent states.  The interval geometry
is derived from the two endpoint tangents by monotonicity of b. -/
theorem J_reverse_growth {E D H : SignedPoint} {α l r : ℝ}
    (hEs : E.Sorted) (hEy : E.y≤0) (hEa : 1<E.a) (hEc : E.circle≤qCap)
    (hDa : 353/500<D.a) (hDy : -D.y∈Ioo (353/500:ℝ) (9/10))
    (hα : α∈Icc 0 (27/100:ℝ))
    (hl : 0≤l) (hlr : l≤r) (hr : r≤7/10) (hsum : α+r≤7/10)
    (hbL : 0≤b D l) (hbR : b D r≤ -E.y) :
    (1/200)*(r-l)≤J E D H α l-J E D H α r := by
  have hlrange : l∈Icc 0 (7/10:ℝ) := ⟨hl,hlr.trans hr⟩
  have hrrange : r∈Icc 0 (7/10:ℝ) := ⟨hl.trans hlr,hr⟩
  have hm := b_monotone (show 1/2≤D.a by linarith) hDy.1
  have hgeometry (z : ℝ) (hz : z∈Icc l r) :
      z∈Icc 0 (7/10:ℝ) ∧ b D z∈Icc 0 (-E.y) := by
    have hzrange : z∈Icc 0 (7/10:ℝ) := ⟨hl.trans hz.1,hz.2.trans hr⟩
    exact ⟨hzrange,⟨hbL.trans (hm hlrange hzrange hz.1),
      (hm hzrange hrrange hz.2).trans hbR⟩⟩
  have hh := derivative_reserve
    (f := fun z => -J E D H α z) (df := fun z => -Jd E D α z) (k := (1/200:ℝ))
    (fun z hz => (J_derivative (H := H) (α := α) hEs hEy (hgeometry z hz).2).neg.continuousAt.continuousWithinAt)
    (fun z hz => (J_derivative (H := H) (α := α) hEs hEy
      (hgeometry z (Ioo_subset_Icc_self hz)).2).neg)
    (fun z hz => by
      have hz' := hgeometry z (Ioo_subset_Icc_self hz)
      have hs : α+z≤7/10 := by linarith [hz.2]
      linarith [J_rate hEs hEy hEa hEc hDa hDy hα hz'.1 hs hz'.2])
    (show l∈Icc l r from ⟨le_rfl,hlr⟩)
    (show r∈Icc l r from ⟨hlr,le_rfl⟩) hlr
  linarith

end SquaresInCircles.Eight.TableFree.NonpositiveDE2Contact
