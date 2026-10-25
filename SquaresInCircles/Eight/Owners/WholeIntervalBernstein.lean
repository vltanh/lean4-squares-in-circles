module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic
public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity
public import SquaresInCircles.Eight.Owners.Positive.StressCoefficients

/-!
# Eight squares: A whole-interval Bernstein lower bound

A rational polynomial identity, nonnegative basis
functions, and their partition of unity imply a bound at every real
point. Concrete identities are proved in the application, not accepted
as external certificates or inferred from sampled values.
-/

section
/-!
## Correlated same-block saturation on the whole angular interval

The coefficient lower bound is the actual correlated ratio
`117/200+(51/200)d`, including its small-d values below `2/3`.
Both comparisons keep the original two-angle norm exactly: it cancels
because the signed angle difference is unchanged.

The negative-surplus estimate uses a quadratic lower bound for its
trigonometric bracket. The positive-surplus estimate uses concavity of
one explicit sinusoid. Neither argument subdivides the angle interval.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.CorrelatedSameBlock
open PositiveAngularEnvelope OrdinaryAngleConcavity
open PositiveStressCoefficients

theorem sin_mono {x y : ℝ} (hx : x∈Icc 0 frameCap)
    (hy : y∈Icc 0 frameCap) (hxy : x≤y) : Real.sin x≤Real.sin y :=
  Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [hx.1,Real.pi_pos])
    (by dsimp [frameCap] at hy; linarith [hy.2,Real.pi_gt_three]) hxy

theorem cos_anti {x y : ℝ} (hx : x∈Icc 0 frameCap)
    (hy : y∈Icc 0 frameCap) (hxy : x≤y) : Real.cos y≤Real.cos x :=
  Real.cos_le_cos_of_nonneg_of_le_pi hx.1
    (by dsimp [frameCap] at hy; linarith [hy.2,Real.pi_gt_three]) hxy

theorem phi_hasDerivAt (x : ℝ) :
    HasDerivAt PositiveAngularEnvelope.phi (Real.cos x-Real.sin x) x := by
  convert (Real.hasDerivAt_cos x).add (Real.hasDerivAt_sin x) using 1
  · rfl
  · ring

theorem phi_mono : MonotoneOn PositiveAngularEnvelope.phi (Icc 0 frameCap) := by
  apply monoOn_of_hasDeriv_nonneg
  · exact (by unfold PositiveAngularEnvelope.phi; fun_prop : Continuous PositiveAngularEnvelope.phi).continuousOn
  · intro x _
    exact phi_hasDerivAt x
  · intro x hx
    exact sub_nonneg.mpr (transport_trig (Ioo_subset_Icc_self hx)).2.2.2.2.le

theorem one_le_phi {x : ℝ} (hx : x∈Icc 0 frameCap) : 1≤PositiveAngularEnvelope.phi x := by
  simpa [PositiveAngularEnvelope.phi] using phi_mono
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hx hx.1

/-- The elementary half-angle lower estimate follows from the global
fourth- and fifth-order Taylor inequalities. -/
theorem half_angle_lower {a : ℝ} (ha : a∈Icc 0 frameCap) :
    (a/2)*Real.sin a≤1-Real.cos a := by
  have hc := cos_upper_four ha.1
  have hs := mul_le_mul_of_nonneg_left (sin_upper_five ha.1) ha.1
  have ha2 : a^2≤(7/10 : ℝ)^2 := pow_le_pow_left₀ ha.1 ha.2 2
  have hp : 0≤a^4*(10-a^2) := mul_nonneg (pow_nonneg ha.1 4) (by linarith)
  nlinarith

/-- A rational lower bound for the full correlated trigonometric
bracket. Its endpoint reserve is `363/100000`. -/
theorem correlated_bracket {d : ℝ} (hd : d∈Icc 0 frameCap) :
    (363/100000 : ℝ)≤ratio d-Real.sin frameCap+
      (Real.cos frameCap-ratio d)*(frameCap-d)/2 := by
  let a : ℝ := frameCap-d
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [hd.2],
    by dsimp [a]; linarith [hd.1]⟩
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).1
  have hs := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).2.2.2.1
  have hmul := mul_le_mul_of_nonneg_right hc.le ha.1
  have hp : 0≤(7/10-a)*((1651/10000 : ℝ)-(51/400 : ℝ)*a) := by
    apply mul_nonneg (by dsimp [frameCap] at ha; linarith [ha.2])
    dsimp [frameCap] at ha
    linarith [ha.2]
  have he : ratio d=1527/2000-(51/200)*a := by
    dsimp [ratio,a,frameCap]
    ring
  change (363/100000 : ℝ)≤ratio d-Real.sin frameCap+
    (Real.cos frameCap-ratio d)*a/2
  rw [he]
  nlinarith

theorem correlated_saturated_trig {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0≤ratio d*(PositiveAngularEnvelope.phi (frameCap-d)-1)+Real.cos frameCap-Real.cos d := by
  let a : ℝ := frameCap-d
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [hd.2],
    by dsimp [a]; linarith [hd.1]⟩
  have hsin := (transport_trig ha).2.2.1
  have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
    constructor; norm_num [frameCap]; rfl)).1
  have hd2 : d≤7/10 := hd.2
  have hr : ratio d≤1527/2000 := by dsimp [ratio]; linarith
  have hfactor : 0≤Real.cos frameCap-ratio d := by linarith
  have hhalf := mul_le_mul_of_nonneg_left (half_angle_lower ha) hfactor
  have hbracket := correlated_bracket hd
  have hbr0 : 0≤ratio d-Real.sin frameCap+
      (Real.cos frameCap-ratio d)*a/2 := by
    dsimp [a]
    linarith
  have hpositive := mul_nonneg hsin hbr0
  have hcos : Real.cos d=Real.cos frameCap*Real.cos a+
      Real.sin frameCap*Real.sin a := by
    rw [← Real.cos_sub]
    congr 1
    dsimp [a]
    ring
  change 0≤ratio d*(PositiveAngularEnvelope.phi a-1)+Real.cos frameCap-Real.cos d
  rw [hcos]
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith

/-- With the positive total fixed, the negative cosine increment is
smallest at the largest permitted negative surplus. -/
theorem cosine_increment_anti {a : ℝ} (ha : a∈Icc 0 frameCap) :
    AntitoneOn (fun w => Real.cos (a+w)-Real.cos w) (Icc 0 (frameCap-a)) := by
  apply antiOn_of_hasDeriv_nonpos (d := fun w => -Real.sin (a+w)*1+Real.sin w)
  · exact (by fun_prop : Continuous (fun w => Real.cos (a+w)-Real.cos w)).continuousOn
  · intro w _
    have h1 : HasDerivAt (fun w => Real.cos (a+w)) (-Real.sin (a+w)*1) w :=
      (Real.hasDerivAt_cos (a+w)).comp w ((hasDerivAt_id' w).const_add a)
    have h := h1.fun_sub (Real.hasDerivAt_cos w)
    convert h using 1
    ring
  · intro w hw
    have hw' : w∈Icc 0 frameCap := ⟨hw.1.le,by linarith [hw.2,ha.1]⟩
    have hsum : a+w∈Icc 0 frameCap := ⟨by linarith [ha.1,hw.1],by linarith [hw.2]⟩
    have hm := sin_mono hw' hsum (by linarith [ha.1])
    linarith

/-- The negative-surplus saturated block dominates its original single
negative block for the full correlated coefficient domain. -/
theorem negative_surplus {R p q d s : ℝ} (hq : 0≤q)
    (hratio : ratio d*q≤p) (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d) :
    V R p q (d-s)≤ mixedBlock R p q (frameCap-d) (frameCap-s) := by
  have ha : frameCap-d∈Icc 0 frameCap := ⟨by linarith [hd.2],by linarith [hd.1]⟩
  have hw : d-s∈Icc 0 (frameCap-(frameCap-d)) :=
    ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd' : d∈Icc 0 (frameCap-(frameCap-d)) := ⟨hd.1,by linarith⟩
  have hcos := cosine_increment_anti ha hw hd' (by linarith [hs.1])
  have hcos' : Real.cos frameCap-Real.cos d≤
      Real.cos (frameCap-s)-Real.cos (d-s) := by
    have e1 : frameCap-d+d=frameCap := by ring
    have e2 : frameCap-d+(d-s)=frameCap-s := by ring
    simp only [e1,e2] at hcos
    exact hcos
  have hphi := sub_nonneg.mpr (one_le_phi ha)
  have hp := mul_le_mul_of_nonneg_right hratio hphi
  have hqcos := mul_le_mul_of_nonneg_left hcos' hq
  have htrig := mul_nonneg hq (correlated_saturated_trig hd)
  have harg : frameCap-d-(frameCap-s)= -(d-s) := by ring
  dsimp [V,mixedBlock]
  rw [harg]
  nlinarith

/-- For fixed negative amount, translating both positive arguments to
the right decreases the increment of `phi`. -/
theorem phi_increment_anti {N : ℝ} (hN : N∈Icc 0 frameCap) :
    AntitoneOn (fun w => PositiveAngularEnvelope.phi (w+N)-PositiveAngularEnvelope.phi w) (Icc 0 (frameCap-N)) := by
  apply antiOn_of_hasDeriv_nonpos (d := fun w =>
    (Real.cos (w+N)-Real.sin (w+N))*1-(Real.cos w-Real.sin w))
  · exact (by unfold PositiveAngularEnvelope.phi; fun_prop : Continuous (fun w =>
      PositiveAngularEnvelope.phi (w+N)-PositiveAngularEnvelope.phi w)).continuousOn
  · intro w _
    have h0 := (phi_hasDerivAt (w+N)).comp w ((hasDerivAt_id' w).add_const N)
    have h1 : HasDerivAt (fun w => PositiveAngularEnvelope.phi (w+N))
        ((Real.cos (w+N)-Real.sin (w+N))*1) w := h0
    exact h1.fun_sub (phi_hasDerivAt w)
  · intro w hw
    have hw' : w∈Icc 0 frameCap := ⟨hw.1.le,by linarith [hw.2,hN.1]⟩
    have hsum : w+N∈Icc 0 frameCap := ⟨by linarith [hw.1,hN.1],by linarith [hw.2]⟩
    have hle : w≤w+N := by linarith [hN.1]
    have h1 := cos_anti hw' hsum hle
    have h2 := sin_mono hw' hsum hle
    linarith

private def surplusTrig (N : ℝ) : ℝ :=
  (117/200)*(PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N))+Real.cos N-1

private theorem surplusTrig_nonneg {N : ℝ} (hN : N∈Icc 0 frameCap) :
    0≤ surplusTrig N := by
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) surplusTrig := by
    apply concave_of_deriv2
      (f' := fun t => (117/200)*(0-(Real.cos (frameCap-t)-Real.sin (frameCap-t))*(-1))+
        -Real.sin t)
      (f'' := fun t => (117/200)*(-Real.sin (frameCap-t)*(-1)-Real.cos (frameCap-t)*(-1))-
        Real.cos t)
    · intro t _
      have ha : HasDerivAt (fun x => frameCap-x) (-1) t := (hasDerivAt_id' t).const_sub frameCap
      have h0 := (phi_hasDerivAt (frameCap-t)).comp t ha
      have h1 : HasDerivAt (fun x => PositiveAngularEnvelope.phi (frameCap-x))
          ((Real.cos (frameCap-t)-Real.sin (frameCap-t))*(-1)) t := h0
      exact ((((hasDerivAt_const t (PositiveAngularEnvelope.phi frameCap)).fun_sub h1).const_mul
        (117/200)).fun_add (Real.hasDerivAt_cos t)).sub_const 1
    · intro t _
      have ha : HasDerivAt (fun x => frameCap-x) (-1) t := (hasDerivAt_id' t).const_sub frameCap
      have hc : HasDerivAt (fun x => Real.cos (frameCap-x)) (-Real.sin (frameCap-t)*(-1)) t :=
        (Real.hasDerivAt_cos _).comp t ha
      have hs : HasDerivAt (fun x => Real.sin (frameCap-x)) (Real.cos (frameCap-t)*(-1)) t :=
        (Real.hasDerivAt_sin _).comp t ha
      have h := (((hasDerivAt_const t (0:ℝ)).fun_sub ((hc.fun_sub hs).mul_const (-1))).const_mul
        (117/200)).fun_add (Real.hasDerivAt_sin t).neg
      convert h using 1
      ring
    · intro t ht
      obtain ⟨hc,_,hs0,hs,hsc⟩ := transport_trig
        (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl)
      have hct : 0≤Real.cos t := by have h := (transport_trig ht).1; linarith
      have hst : 0≤Real.sin t := (transport_trig ht).2.2.1
      have hfirst : 0≤(1-(117/200)*PositiveAngularEnvelope.phi frameCap)*Real.cos t := by
        apply mul_nonneg _ hct
        dsimp [PositiveAngularEnvelope.phi]
        linarith [Real.cos_le_one frameCap]
      have hsecond := mul_nonneg (show 0≤(117/200)*(Real.cos frameCap-Real.sin frameCap) by
        linarith) hst
      have he : Real.cos (frameCap-t)+Real.sin (frameCap-t)=
          PositiveAngularEnvelope.phi frameCap*Real.cos t+
            (Real.sin frameCap-Real.cos frameCap)*Real.sin t := by
        simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
        ring
      have he' : (117/200)*(-Real.sin (frameCap-t)*(-1)-Real.cos (frameCap-t)*(-1))-Real.cos t=
          (117/200)*(Real.cos (frameCap-t)+Real.sin (frameCap-t))-Real.cos t := by ring
      show (117/200)*(-Real.sin (frameCap-t)*(-1)-Real.cos (frameCap-t)*(-1))-Real.cos t≤0
      rw [he',he]
      nlinarith
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) hN
  have hz : surplusTrig 0=0 := by simp [surplusTrig]
  have hh : 0≤surplusTrig frameCap := by
    have hphi := phi_cap_lower
    have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
      constructor; norm_num [frameCap]; rfl)).1
    simp only [surplusTrig,sub_self,PositiveAngularEnvelope.phi,Real.cos_zero,Real.sin_zero,
      add_zero]
    dsimp [PositiveAngularEnvelope.phi] at hphi
    linarith
  rw [hz,min_eq_left hh] at hmin
  exact hmin

/-- Every ordinary block with ratio at least `.585` dominates the pure
positive surplus when its two nonnegative amounts fit in the frame. -/
theorem positive_surplus {R p q P N : ℝ} (hq : 0≤q)
    (hratio : (117/200)*q≤p) (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 P) :
    U R p q (P-N)≤ mixedBlock R p q P N := by
  have hN' : N∈Icc 0 frameCap := ⟨hN.1,hN.2.trans hP.2⟩
  have hw : P-N∈Icc 0 frameCap := ⟨by linarith [hN.2],by linarith [hP.2,hN.1]⟩
  have hincrement : 0≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) :=
    sub_nonneg.mpr (phi_mono hw hP (by linarith [hN.1]))
  have hi := phi_increment_anti hN'
    (show P-N∈Icc 0 (frameCap-N) from ⟨hw.1,by linarith [hP.2]⟩)
    (show frameCap-N∈Icc 0 (frameCap-N) from ⟨by linarith [hN'.2],le_rfl⟩)
    (by linarith [hP.2])
  have hi' : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) := by
    convert hi using 1 <;> congr 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hratio hincrement
  have hmin := mul_le_mul_of_nonneg_left hi' (show 0≤(117/200 : ℝ)*q by positivity)
  have hbase := mul_nonneg hq (surplusTrig_nonneg hN')
  dsimp [surplusTrig] at hbase
  dsimp [U,mixedBlock]
  nlinarith

end SquaresInCircles.Eight.CorrelatedSameBlock
end
end
end

section
/-!
## A finite positive-mass radical transfer with inactive summands

Each positive auxiliary multiplies its
own square comparison. Multiplication by the product of the other
positive auxiliaries removes every denominator. An inactive term has
zero actual norm; it is absent from the numerator as well. This single
lemma treats three- and four-norm endpoint expressions without adding
a spurious norm to the sorted-D baseline.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.FiniteActiveRadicalTransfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A purely real, division-free version of the rational auxiliary estimate. -/
theorem positive (active : ι→Prop) [DecidablePred active]
    (mass norm upper : ι→ℝ) {R Rbar A B : ℝ}
    (hmass : ∀i,0< mass i) (hnorm : ∀i,0≤norm i)
    (hupper : ∀i,(norm i)^2≤upper i)
    (hinactive : ∀i,¬active i→norm i=0)
    (hR : R≤Rbar) (hRbar : 0≤Rbar) (hA : A≤B)
    (hnum : 0<2*A*(∏i,mass i)-Rbar*
      ∑i,if active i then (upper i+(mass i)^2)*∏j∈Finset.univ.erase i,mass j else 0) :
    0<B-R*∑i,norm i := by
  let total : ℝ := ∏i,mass i
  let others (i : ι) : ℝ := ∏j∈Finset.univ.erase i,mass j
  have htotal : 0<total := Finset.prod_pos (fun i _ => hmass i)
  have hothers (i : ι) : 0≤others i :=
    (Finset.prod_pos (fun j _ => hmass j)).le
  have hfactor (i : ι) : total=mass i*others i := by
    have hi : insert i (Finset.univ.erase i)=(Finset.univ : Finset ι) :=
      Finset.insert_erase (Finset.mem_univ i)
    calc
      total=∏j∈insert i (Finset.univ.erase i),mass j :=
        congrArg (fun s : Finset ι => ∏j∈s,mass j) hi.symm
      _=mass i*others i := by
        rw [Finset.prod_insert (by simp)]
  have hterm (i : ι) :
      2*total*R*norm i≤Rbar*(if active i then (upper i+(mass i)^2)*others i else 0) := by
    by_cases hi : active i
    · have hsquare : 2*mass i*norm i≤upper i+(mass i)^2 := by
        nlinarith only [hupper i,sq_nonneg (norm i-mass i)]
      have hscaled := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare hRbar) (hothers i)
      have hrad := mul_le_mul_of_nonneg_left hR
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) htotal.le) (hnorm i))
      simp only [hi,↓reduceIte]
      rw [hfactor i] at hrad ⊢
      linarith only [hscaled,hrad]
    · rw [hinactive i hi]
      simp [hi]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hterm i)
  simp only [←Finset.mul_sum] at hsum
  have hA' := mul_le_mul_of_nonneg_right hA (show 0≤2*total by positivity)
  have hnum' : 0<2*A*total-Rbar*
      ∑i,if active i then (upper i+(mass i)^2)*others i else 0 := hnum
  have hpositive : 0<2*total*(B-R*∑i,norm i) := by
    linarith only [hsum,hA',hnum']
  exact (mul_pos_iff_of_pos_left (show 0<2*total by positivity)).mp hpositive

end SquaresInCircles.Eight.FiniteActiveRadicalTransfer
end
end
end

section
/-!
## Same-block comparisons after the short BT secant enlargement

The negative comparison retains `31/10000` of
slack in the correlated ratio; the positive comparison only needs ratio
`29/50`. These reserves cover the actual factor `cos s`, `s ≤ .09`.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.RelaxedSameBlock
open PositiveAngularEnvelope OrdinaryAngleConcavity CorrelatedSameBlock
open PositiveStressCoefficients

theorem relaxed_saturated_trig {d : ℝ} (hd : d∈Icc 0 frameCap) :
    0≤(ratio d-31/10000)*(PositiveAngularEnvelope.phi (frameCap-d)-1)+Real.cos frameCap-Real.cos d := by
  let a : ℝ := frameCap-d
  have ha : a∈Icc 0 frameCap := ⟨by dsimp [a]; linarith [hd.2],
    by dsimp [a]; linarith [hd.1]⟩
  have hsin := (transport_trig ha).2.2.1
  have hh : frameCap∈Icc 0 frameCap := ⟨by norm_num [frameCap],le_rfl⟩
  have hr : ratio d≤1527/2000 := (coefficient_bounds hd).2.2.2.2.2.2.2.2.2
  have hfactor : 0≤Real.cos frameCap-(ratio d-31/10000) := by
    linarith [(transport_trig hh).1]
  have hhalf := mul_le_mul_of_nonneg_left (half_angle_lower ha) hfactor
  have hbracket := correlated_bracket hd
  have hbr0 : 0≤ratio d-31/10000-Real.sin frameCap+
      (Real.cos frameCap-(ratio d-31/10000))*a/2 := by
    have ha0 : 0≤a := ha.1
    have hb := hbracket
    dsimp only [a] at ha0 ⊢
    simp only [frameCap] at hb ha0 ⊢
    linarith
  have hpositive := mul_nonneg hsin hbr0
  have hcos : Real.cos d=Real.cos frameCap*Real.cos a+
      Real.sin frameCap*Real.sin a := by
    rw [← Real.cos_sub]
    congr 1
    dsimp [a]
    ring
  change 0≤(ratio d-31/10000)*(PositiveAngularEnvelope.phi a-1)+Real.cos frameCap-Real.cos d
  rw [hcos]
  dsimp [PositiveAngularEnvelope.phi]
  nlinarith

theorem negative_surplus {R p q d s : ℝ} (hq : 0≤q)
    (hratio : (ratio d-31/10000)*q≤p)
    (hd : d∈Icc 0 frameCap) (hs : s∈Icc 0 d) :
    V R p q (d-s)≤ mixedBlock R p q (frameCap-d) (frameCap-s) := by
  have ha : frameCap-d∈Icc 0 frameCap := ⟨by linarith [hd.2],by linarith [hd.1]⟩
  have hw : d-s∈Icc 0 (frameCap-(frameCap-d)) :=
    ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hd' : d∈Icc 0 (frameCap-(frameCap-d)) := ⟨hd.1,by linarith⟩
  have hcos := cosine_increment_anti ha hw hd' (by linarith [hs.1])
  have hcos' : Real.cos frameCap-Real.cos d≤
      Real.cos (frameCap-s)-Real.cos (d-s) := by
    convert hcos using 1 <;> congr 1 <;> ring
  have hp := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr (one_le_phi ha))
  have hqcos := mul_le_mul_of_nonneg_left hcos' hq
  have htrig := mul_nonneg hq (relaxed_saturated_trig hd)
  have harg : frameCap-d-(frameCap-s)= -(d-s) := by ring
  dsimp [V,mixedBlock]
  rw [harg]
  nlinarith

private def surplusTrig (N : ℝ) : ℝ :=
  (29/50)*(PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N))+Real.cos N-1

private theorem surplusTrig_nonneg {N : ℝ} (hN : N∈Icc 0 frameCap) :
    0≤ surplusTrig N := by
  have hconc : ConcaveOn ℝ (Icc 0 frameCap) surplusTrig := by
    apply concave_of_deriv2
      (f' := fun t => (29/50)*(Real.cos (frameCap-t)-Real.sin (frameCap-t))-Real.sin t)
      (f'' := fun t => (29/50)*PositiveAngularEnvelope.phi (frameCap-t)-Real.cos t)
    · intro t _
      have ha := (hasDerivAt_id t).const_sub frameCap
      have hraw := ((((hasDerivAt_const t (PositiveAngularEnvelope.phi frameCap)).sub
        ((phi_hasDerivAt (frameCap-t)).comp t ha)).const_mul (29/50)).add
          (Real.hasDerivAt_cos t)).sub_const 1
      convert hraw using 1
      · rfl
      · ring
    · intro t _
      have ha := (hasDerivAt_id t).const_sub frameCap
      exact (((ha.cos.fun_sub ha.sin).const_mul (29/50)).fun_sub
        (Real.hasDerivAt_sin t)).congr_deriv (by simp only [PositiveAngularEnvelope.phi,id]; ring)
    · intro t ht
      obtain ⟨hc,_,hs0,hs,hsc⟩ := transport_trig
        (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl)
      have hct : 0≤Real.cos t := by linarith [(transport_trig ht).1]
      have hst := (transport_trig ht).2.2.1
      have hfirst : 0≤(1-(29/50)*PositiveAngularEnvelope.phi frameCap)*Real.cos t := by
        apply mul_nonneg _ hct
        dsimp [PositiveAngularEnvelope.phi]
        linarith [Real.cos_le_one frameCap]
      have hsecond := mul_nonneg
        (show 0≤(29/50)*(Real.cos frameCap-Real.sin frameCap) by linarith) hst
      have he : PositiveAngularEnvelope.phi (frameCap-t)=PositiveAngularEnvelope.phi frameCap*Real.cos t+
          (Real.sin frameCap-Real.cos frameCap)*Real.sin t := by
        simp only [PositiveAngularEnvelope.phi,Real.cos_sub,Real.sin_sub]
        ring
      rw [he]
      nlinarith
  have hmin := hconc.min_le_of_mem_Icc
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap])
    (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl) hN
  have hz : surplusTrig 0=0 := by simp [surplusTrig]
  have hh : 0≤surplusTrig frameCap := by
    have hphi := phi_cap_lower
    have hc := (transport_trig (show frameCap∈Icc 0 frameCap by
      constructor; norm_num [frameCap]; rfl)).1
    simp only [surplusTrig,sub_self,PositiveAngularEnvelope.phi,Real.cos_zero,Real.sin_zero,add_zero]
    dsimp [PositiveAngularEnvelope.phi] at hphi
    linarith
  rw [hz,min_eq_left hh] at hmin
  exact hmin

theorem positive_surplus {R p q P N : ℝ} (hq : 0≤q)
    (hratio : (29/50)*q≤p) (hP : P∈Icc 0 frameCap) (hN : N∈Icc 0 P) :
    U R p q (P-N)≤ mixedBlock R p q P N := by
  have hN' : N∈Icc 0 frameCap := ⟨hN.1,hN.2.trans hP.2⟩
  have hw : P-N∈Icc 0 frameCap := ⟨by linarith [hN.2],by linarith [hP.2,hN.1]⟩
  have hincrement := sub_nonneg.mpr (phi_mono hw hP (by linarith [hN.1]))
  have hi := phi_increment_anti hN'
    (show P-N∈Icc 0 (frameCap-N) from ⟨hw.1,by linarith [hP.2]⟩)
    (show frameCap-N∈Icc 0 (frameCap-N) from ⟨by linarith [hN'.2],le_rfl⟩)
    (by linarith [hP.2])
  have hi' : PositiveAngularEnvelope.phi frameCap-PositiveAngularEnvelope.phi (frameCap-N)≤PositiveAngularEnvelope.phi P-PositiveAngularEnvelope.phi (P-N) := by
    convert hi using 1 <;> congr 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hratio hincrement
  have hmin := mul_le_mul_of_nonneg_left hi' (show 0≤(29/50 : ℝ)*q by positivity)
  have hbase := mul_nonneg hq (surplusTrig_nonneg hN')
  dsimp [surplusTrig] at hbase
  dsimp [U,mixedBlock]
  nlinarith

end SquaresInCircles.Eight.RelaxedSameBlock
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.WholeIntervalBernstein
open Polynomial

def basis (D : ℕ) (b : ℚ) (i : Fin (D+1)) : ℚ[X] :=
  C ((Nat.choose D i.val : ℚ)/b^D)*X^i.val*(C b-X)^(D-i.val)

def coefficient (D : ℕ) (b : ℚ) (p : ℚ[X]) (i : Fin (D+1)) : ℚ :=
  ∑ j∈Finset.range (i.val+1),p.coeff j*b^j*(Nat.choose i.val j : ℚ)/(Nat.choose D j : ℚ)

def expansion (D : ℕ) (b : ℚ) (p : ℚ[X]) : ℚ[X] :=
  ∑ i : Fin (D+1),C (coefficient D b p i)*basis D b i

theorem basis_nonneg {D : ℕ} {b : ℚ} (hb : 0<b) (i : Fin (D+1))
    {x : ℝ} (hx : x∈Set.Icc 0 (b:ℝ)) : 0≤aeval x (basis D b i) := by
  have hb' : (0:ℝ)<(b:ℝ) := by exact_mod_cast hb
  simp only [basis,map_mul,aeval_C,eq_ratCast,map_pow,aeval_X,map_sub]
  push_cast
  exact mul_nonneg
    (mul_nonneg (div_nonneg (by positivity) (pow_nonneg hb'.le _)) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.mpr hx.2) _)

theorem lower_on_interval {D : ℕ} {b r : ℚ} {p : ℚ[X]}
    (hb : 0<b) (hid : p=expansion D b p)
    (hone : (∑ i : Fin (D+1),basis D b i)=1)
    (hcoef : ∀i,r≤coefficient D b p i) {x : ℝ}
    (hx : x∈Set.Icc 0 (b:ℝ)) : (r:ℝ)≤aeval x p := by
  have hsum : (∑ i : Fin (D+1),aeval x (basis D b i))=1 := by
    simpa only [map_sum,map_one] using congrArg (aeval x) hone
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right
      (show (r:ℝ)≤(coefficient D b p i:ℝ) by exact_mod_cast hcoef i)
      (basis_nonneg hb i hx))
  rw [hid]
  simp only [expansion,map_sum,map_mul,aeval_C,eq_ratCast]
  rw [← Finset.mul_sum,hsum,mul_one] at hbound
  exact hbound

end SquaresInCircles.Eight.WholeIntervalBernstein
end
end
end
