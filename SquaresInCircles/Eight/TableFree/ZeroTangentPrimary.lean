module

public import SquaresInCircles.Eight.TableFree.PairedPrimaryGeometry

/-!
# The zero-tangent join is dominated at the same radius

Uncompiled draft of the zero-tangent argument in the uniform-radius paired
primary theorem. The comparison moves the intermediate to BT alignment on
its actual q-circle. The opposite TD witness becomes strict.

The half-angle variable is used only inside this polynomial proof. The
constructed square retains its actual real frame and signed center.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree
namespace PairedPrimary.ZeroTangent

def demand (d x : ℝ) : ℝ := 1/2+Real.cos x/2-d*Real.sin x

def derivative (d x : ℝ) : ℝ := -Real.sin x/2-d*Real.cos x

def allowance (d r : ℝ) : ℝ :=
  r*(1+4*r^2-r^4+4*d*r*(1-r^2))/(2*(1-r^4))

def loss (d r : ℝ) : ℝ := (2*d*r+r^2)/(1+r^2)

theorem demand_hasDeriv (d x : ℝ) :
    HasDerivAt (demand d) (derivative d x) x := by
  convert (((hasDerivAt_const x (1/2 : ℝ)).add
    ((Real.hasDerivAt_cos x).div_const 2)).sub
    ((Real.hasDerivAt_sin x).const_mul d)) using 1 <;>
    dsimp [demand,derivative] <;> ring

theorem demand_strictAnti {d : ℝ} (hd : 9/10≤d) :
    StrictAntiOn (demand d) (Icc 0 (7/10 : ℝ)) := by
  have hm : StrictMonoOn (fun x => -demand d x) (Icc 0 (7/10 : ℝ)) := by
    apply strict_increase_of_reserve (k := 3/5)
    · fun_prop
    · intro x hx
      exact (demand_hasDeriv d x).neg
    · norm_num
    · intro x hx
      obtain ⟨hc,hs0,hs⟩ := transport_trig_coarse (Ioo_subset_Icc_self hx)
      have hp := mul_nonneg (sub_nonneg.mpr hd) hc.le
      dsimp [derivative]
      nlinarith
  intro x hx y hy hxy
  have h := hm hx hy hxy
  linarith

theorem demand_eighth {d : ℝ} (hd : 9/10≤d) : demand d (1/8)<899/1000 := by
  have hc := cos_upper_four (x := (1/8 : ℝ)) (by norm_num)
  have hs := Real.sin_ge_sub_cube (x := (1/8 : ℝ)) (by norm_num)
  have hs0 : 0≤Real.sin (1/8 : ℝ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three])
  have hp := mul_nonneg (sub_nonneg.mpr hd) hs0
  dsimp [demand]
  norm_num at hc hs
  nlinarith

/-- All the nonlinear comparison is one rational identity on 0<r<1/15. -/
theorem allowance_bounds {d r : ℝ}
    (hd : 9/10<d ∧ d<183/200) (hr : 0<r ∧ r<1/15) :
    r/2+2*d*r^2<allowance d r ∧ allowance d r<2*r/3 ∧
      0<loss d r ∧ loss d r<2*r ∧ loss d r<2*d*r+r^2 := by
  have hd0 : 0<d := by linarith
  have hr0 : 0≤r := hr.1.le
  have hr2 : r^2<(1/15 : ℝ)^2 := pow_lt_pow_left₀ hr0 hr.2 (by norm_num)
  have hr4 : r^4<(1/15 : ℝ)^4 := pow_lt_pow_left₀ hr0 hr.2 (by norm_num)
  have hden : 0<1-r^4 := by nlinarith
  have hden' : 0<1+r^2 := by positivity
  have hprod : d*r<(183/200 : ℝ)*(1/15) :=
    mul_lt_mul hd.2 hr.2 hd0.le (by norm_num)
  have hbracket : 0<1-d*r+d*r^3 := by positivity
  have hid : allowance d r-(r/2+2*d*r^2)=
      2*r^3*(1-d*r+d*r^3)/(1-r^4) := by
    dsimp [allowance]
    field_simp [hden.ne']
    ring
  have hlow : r/2+2*d*r^2<allowance d r := by
    have hp : 0<2*r^3*(1-d*r+d*r^3)/(1-r^4) := by positivity
    rw [← hid] at hp
    linarith
  have hnum : 1+4*r^2-r^4+4*d*r*(1-r^2)<
      1+4/225+4*(183/200 : ℝ)/15 := by
    have hneg := mul_nonneg (mul_nonneg hd0.le hr0) (sq_nonneg r)
    nlinarith [pow_nonneg hr0 4]
  have hupper : allowance d r<2*r/3 := by
    unfold allowance
    apply (div_lt_iff₀ (by positivity : 0<2*(1-r^4))).2
    have hcoef : 1+4*r^2-r^4+4*d*r*(1-r^2)<(4/3)*(1-r^4) := by
      nlinarith
    have hmul := mul_lt_mul_of_pos_left hcoef hr.1
    nlinarith
  have hnumpos : 0<2*d*r+r^2 := by positivity
  have hlospos : 0<loss d r := div_pos hnumpos hden'
  have hlosnum : loss d r<2*d*r+r^2 := by
    unfold loss
    apply (div_lt_iff₀ hden').2
    nlinarith [mul_pos hnumpos (sq_pos_of_pos hr.1)]
  have hlosr : loss d r<2*r := by
    have hcoef : 2*d+r<2 := by linarith [hd.2,hr.2]
    have hmul := mul_lt_mul_of_pos_right hcoef hr.1
    linarith
  exact ⟨hlow,hupper,hlospos,hlosr,hlosnum⟩

theorem allowance_discriminant {A d r : ℝ}
    (hA : 19/10<A ∧ A<2) (hd : d=A-1)
    (hd' : 9/10<d ∧ d<183/200) (hr : 0<r ∧ r<1/15) :
    0<2*A*allowance d r-(allowance d r)^2-loss d r-(loss d r)^2 := by
  obtain ⟨hlo,hhi,hδ0,hδr,hδnum⟩ := allowance_bounds hd' hr
  have hA0 : 0<A := by linarith
  have hL0 : 0<allowance d r := by
    have hp : 0≤2*d*r^2 := by positivity
    linarith
  have hL2 : (allowance d r)^2<(2*r/3)^2 :=
    pow_lt_pow_left₀ hL0.le hhi (by norm_num)
  have hδ2 : (loss d r)^2<(2*r)^2 :=
    pow_lt_pow_left₀ hδ0.le hδr (by norm_num)
  have hmain := mul_lt_mul_of_pos_left hlo (show 0<2*A by positivity)
  have hAd : (171/100 : ℝ)<A*d := by
    have hp := mul_pos (show 0<A-19/10 by linarith) (show 0<d-9/10 by linarith [hd'.1])
    nlinarith [hA.1,hd'.1]
  have hcoef : 0<(2-A)*r+(314/225)*r^2 := by positivity
  have hcoef2 := mul_lt_mul_of_pos_right hAd (sq_pos_of_pos hr.1)
  nlinarith [hd]

/-- The allowance is greater than the actual primary loss on the same circle. -/
theorem allowance_dominates_circle_loss {A d r : ℝ}
    (hA : 19/10<A ∧ A<2) (hd : d=A-1)
    (hd' : 9/10<d ∧ d<183/200) (hr : 0<r ∧ r<1/15) :
    A-Real.sqrt (A^2-loss d r-(loss d r)^2)<allowance d r := by
  obtain ⟨hlo,hhi,hδ0,hδr,hδnum⟩ := allowance_bounds hd' hr
  have hδ2 : (loss d r)^2<(2/15 : ℝ)^2 := by
    exact pow_lt_pow_left₀ hδ0.le (hδr.trans (by linarith [hr.2])) (by norm_num)
  have hrad : 0<A^2-loss d r-(loss d r)^2 := by nlinarith [hA.1,hr.2]
  have hs := Real.sq_sqrt hrad.le
  have hn := Real.sqrt_nonneg (A^2-loss d r-(loss d r)^2)
  have hdis := allowance_discriminant hA hd hd' hr
  have hleft : 0<A-allowance d r := by linarith [hA.1,hr.2]
  nlinarith

/-- Algebraic half-angle identities with a positive denominator. -/
theorem half_angle_identities {u : ℝ} (hu : 0<u ∧ u<1/8) :
    let r := Real.sin u/(1+Real.cos u)
    0<r ∧ r<1/15 ∧
      Real.sin u=2*r/(1+r^2) ∧ Real.cos u=(1-r^2)/(1+r^2) := by
  have hsin : 0<Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu.1
    (by linarith [hu.2,Real.pi_gt_three])
  have hcos := Real.one_sub_sq_div_two_le_cos (x := u)
  have hsinupper := Real.sin_le u hu.1.le
  have hu2 : u^2<(1/8 : ℝ)^2 := pow_lt_pow_left₀ hu.1.le hu.2 (by norm_num)
  have hden : 0<1+Real.cos u := by nlinarith
  have hr0 : 0<Real.sin u/(1+Real.cos u) := div_pos hsin hden
  have hr15 : Real.sin u/(1+Real.cos u)<1/15 := by
    apply (div_lt_iff₀ hden).2
    nlinarith
  refine ⟨hr0,hr15,?_,?_⟩ <;>
    have hunit := Real.sin_sq_add_cos_sq u <;>
    field_simp [hden.ne',show (1+(Real.sin u/(1+Real.cos u))^2)≠0 by positivity] <;>
    nlinarith [hunit]

theorem allowance_trig_identity {d u r : ℝ}
    (hu : 0<u ∧ u<1/8)
    (hr : r=Real.sin u/(1+Real.cos u)) :
    allowance d r=d*(1-Real.cos u)+Real.sin u/2-
      (1-Real.cos u)*Real.cos (2*u)/Real.sin (2*u) := by
  obtain ⟨hr0,hr15,hs,hc⟩ := half_angle_identities hu
  rw [← hr] at hr0 hr15 hs hc
  have hr4 : r^4<1 := by
    have h := pow_lt_pow_left₀ hr0.le (show r<1 by linarith) (by norm_num : (4:ℕ)≠0)
    simpa using h
  have hsin2 : Real.sin (2*u)≠0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hu.2,Real.pi_gt_three]))
  unfold allowance
  rw [Real.sin_two_mul,Real.cos_two_mul,hs,hc]
  field_simp [show 1-r^4≠0 by linarith,show 1+r^2≠0 by positivity,
    show r≠0 by linarith,show 1-r^2≠0 by nlinarith [sq_nonneg r]]
  ring

end ZeroTangent

/-- The actual zero-tangent contact is replaced by a BT-aligned outer point.
The required TD coordinate is strictly reduced. -/
theorem zero_tangent_alignment {q B D u v : ℝ}
    (hqL : qLow≤q) (hqU : q≤qCap)
    (hB : diagonalCoordinate q≤B) (hD : D≤diagonalCoordinate q)
    (hu : 0<u) (hv : 0<v) (ht : u+v≤7/10)
    (hcontact : contact q B u 0=0)
    (hfeasible : required q (u+v) u 0≤D) :
    let p := arc q (B-1)
    p.Sorted ∧ p.Outer q ∧ p.AvoidsCore ∧ p.y<0 ∧
      B-p.y=1 ∧ edgeWidth (u+v)<p.a*Real.sin (u+v)+p.y*Real.cos (u+v)+D := by
  let A := Real.sqrt (q-1/4)
  let d := A-1
  obtain ⟨hcl,hcu,hAl,hAu⟩ := uniform_circle_reserves hqL hqU
  have hA : 19/10<A ∧ A<2 := ⟨hAl,by dsimp [A]; linarith⟩
  have hd : 9/10<d ∧ d<183/200 := by dsimp [d,A]; constructor <;> linarith
  have huI : u∈Icc 0 (7/10 : ℝ) := ⟨hu.le,by linarith⟩
  have hvI : v∈Icc 0 (7/10 : ℝ) := ⟨hv.le,by linarith⟩
  have hBf : B=ZeroTangent.demand d u := by
    rw [contact,edgeWidth_positive_formula huI] at hcontact
    simp [arc,SignedPoint.outerAt] at hcontact
    dsimp [ZeroTangent.demand,d,A]
    linarith
  have hDf : ZeroTangent.demand d v≤D := by
    rw [required,add_sub_cancel_left,edgeWidth_positive_formula hvI] at hfeasible
    simp [arc,SignedPoint.outerAt] at hfeasible
    dsimp [ZeroTangent.demand,d,A]
    linarith
  have huv : u≤v := by
    by_contra! h
    have hm := ZeroTangent.demand_strictAnti hd.1.le hvI huI h
    linarith [hBf,hDf,hB,hD]
  have hushort : u<1/8 := by
    by_contra! h
    have hm := (ZeroTangent.demand_strictAnti hd.1.le).antitoneOn
      (show (1/8:ℝ)∈Icc 0 (7/10 : ℝ) by norm_num) huI h
    have he := ZeroTangent.demand_eighth hd.1.le
    linarith [hBf,hB,hcl]
  have hB1 : B<1 := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [ht,hv,Real.pi_gt_three])
    have hc := Real.cos_le_one u
    have hp := mul_pos (show 0<d by linarith) hs
    rw [hBf]
    dsimp [ZeroTangent.demand]
    linarith
  let δ := 1-B
  let r := Real.sin u/(1+Real.cos u)
  have hδ : 0<δ ∧ δ<diagonalCoordinate q := by
    dsimp [δ]
    constructor <;> linarith
  have hy : |B-1|≤diagonalCoordinate q := by
    rw [abs_of_neg (by linarith : B-1<0)]
    linarith [hδ.2]
  obtain ⟨hps,hpo,hpc⟩ := SignedPoint.outerAt_spec hqL hy
  obtain ⟨hr0,hr15,hs,hc⟩ := ZeroTangent.half_angle_identities ⟨hu,hushort⟩
  have hδloss : δ=ZeroTangent.loss d r := by
    rw [hBf]
    dsimp [δ,ZeroTangent.demand,ZeroTangent.loss,r]
    rw [hs,hc]
    field_simp [show 1+(Real.sin u/(1+Real.cos u))^2≠0 by positivity]
    ring
  let ε := A-Real.sqrt (A^2-δ-δ^2)
  have hε : ε<ZeroTangent.allowance d r := by
    dsimp [ε]
    rw [hδloss]
    exact ZeroTangent.allowance_dominates_circle_loss hA rfl hd ⟨hr0,hr15⟩
  have hL := ZeroTangent.allowance_trig_identity (d := d) ⟨hu,hushort⟩ rfl
  have hA2 : A^2=q-1/4 :=
    Real.sq_sqrt (by dsimp [qLow] at hqL; linarith)
  have hpa : (arc q (B-1)).a=A-1/2-ε := by
    dsimp [arc,SignedPoint.outerAt,ε]
    rw [abs_of_neg (by linarith : B-1<0)]
    congr 2
    dsimp [δ]
    nlinarith [hA2]
  have hsinT : 0<Real.sin (u+v) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith [Real.pi_gt_three])
  have hsin2 : 0<Real.sin (2*u) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith [hushort,Real.pi_gt_three])
  have hangle : 0≤Real.sin ((u+v)-2*u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by linarith [ht,hu,Real.pi_gt_three])
  have hcot : 0≤Real.sin (u+v)*Real.cos (2*u)/Real.sin (2*u)-Real.cos (u+v) := by
    apply (sub_nonneg).2
    apply (le_div_iff₀ hsin2).2
    rw [Real.sin_sub] at hangle
    linarith
  have hones : 0≤1-Real.cos u := sub_nonneg.mpr (Real.cos_le_one u)
  have hbase := mul_nonneg hones hcot
  have hstrict := mul_lt_mul_of_pos_left hε hsinT
  rw [hL] at hstrict
  have hidentity :
      (A-1/2-ε)*Real.sin (u+v)-δ*Real.cos (u+v)+ZeroTangent.demand d v-
        edgeWidth (u+v)=
      Real.sin (u+v)*(d*(1-Real.cos u)+Real.sin u/2-ε)-
        (1-Real.cos u)*Real.cos (u+v) := by
    rw [edgeWidth_positive_formula ⟨by linarith,ht⟩,hBf]
    dsimp [δ,ZeroTangent.demand,d]
    simp only [Real.sin_add,Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hnew : edgeWidth (u+v)<
      (arc q (B-1)).a*Real.sin (u+v)+(B-1)*Real.cos (u+v)+D := by
    rw [hpa]
    dsimp [δ] at hidentity hbase hstrict
    nlinarith [hDf]
  exact ⟨hps,hpo,hpc,by dsimp [arc,SignedPoint.outerAt]; linarith,
    by dsimp [arc,SignedPoint.outerAt]; ring,hnew⟩

end PairedPrimary
end SquaresInCircles.Eight.TableFree