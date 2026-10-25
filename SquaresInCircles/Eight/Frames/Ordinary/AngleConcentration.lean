module

public import SquaresInCircles.Eight.Frames.Ordinary.AngleConcavity

/-!
# Eight squares: concentrating the two signed angle budgets

A concave finite sum at a fixed total has a
minimizer with all of that total at one coordinate. Applying this first
to the negative variables and then to the positive variables is justified
by the whole-square curvature proved in `OrdinaryAngleConcavity`.

The final common positive-variation parameter has only its two intrinsic
endpoints. No original geometric angle is asserted to be concentrated;
the result is an exact lower bound on its original analytic stress.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.OrdinaryAngleConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity

def massAt {ι : Type*} [DecidableEq ι] (j : ι) (s : ℝ) (i : ι) : ℝ :=
  if i=j then s else 0

theorem massAt_mem {ι : Type*} [DecidableEq ι] {j i : ι} {s h : ℝ}
    (hs : s∈Icc 0 h) : massAt j s i∈Icc 0 h := by
  by_cases hi : i=j
  · simpa [massAt,hi] using hs
  · simp [massAt,hi]
    linarith [hs.1,hs.2]

/-- The finite simplex step uses only concavity and the original total. -/
theorem concave_sum_concentrates {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (x : ι → ℝ) {T h : ℝ}
    (hx : ∀ i,0≤x i) (hsum : (∑ i,x i)=T) (hT : T≤h)
    (hf : ∀ i,ConcaveOn ℝ (Icc 0 h) (f i)) :
    ∃ j, (∑ i,f i (massAt j T i))≤∑ i,f i (x i) := by
  classical
  have hT0 : 0≤T := by rw [← hsum]; exact Finset.sum_nonneg fun i _ => hx i
  have hxT (i : ι) : x i≤T := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => hx k) (Finset.mem_univ i)
  by_cases hzero : T=0
  · obtain ⟨j⟩ := ‹Nonempty ι›
    have hxzero (i : ι) : x i=0 := by have h := hxT i; rw [hzero] at h; linarith [hx i]
    refine ⟨j,?_⟩
    simp [massAt,hzero,hxzero]
  have hTp : 0<T := lt_of_le_of_ne hT0 (Ne.symm hzero)
  let a (i : ι) : ℝ := f i T-f i 0
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  have hcoeff (i : ι) : 0≤x i/T ∧ x i/T≤1 :=
    ⟨div_nonneg (hx i) hT0,(div_le_one hTp).2 (hxT i)⟩
  have hchord (i : ι) : f i 0+(x i/T)*a i≤f i (x i) := by
    have h := (hf i).2
      (show (0:ℝ)∈Icc 0 h from ⟨le_rfl,hT0.trans hT⟩)
      (show T∈Icc 0 h from ⟨hT0,hT⟩)
      (sub_nonneg.mpr (hcoeff i).2) (hcoeff i).1 (by ring)
    have he : (1-x i/T)*0+(x i/T)*T=x i := by field_simp [hzero]; ring
    simp only [smul_eq_mul,he] at h
    dsimp [a]
    nlinarith only [h]
  have hterm (i : ι) : f i 0+(x i/T)*a j≤f i (x i) := by
    have hm := mul_le_mul_of_nonneg_left (hj i (Finset.mem_univ i)) (hcoeff i).1
    linarith [hchord i]
  have hcoeffsum : (∑ i,x i/T)=1 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul,hsum]
    field_simp [hzero]
  have hsumleft : (∑ i,(f i 0+(x i/T)*a j))=(∑ i,f i 0)+a j := by
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hcoeffsum,one_mul]
  have hsumright : (∑ i,f i (massAt j T i))=(∑ i,f i 0)+a j := by
    have he (i : ι) : f i (massAt j T i)=f i 0+if i=j then a j else 0 := by
      by_cases hi : i=j
      · subst i
        simp [massAt,a]
      · simp [massAt,hi]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp
  refine ⟨j,?_⟩
  rw [hsumright,← hsumleft]
  exact Finset.sum_le_sum fun i _ => hterm i

theorem concentrated_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ℝ) (p q : ι → ℝ) (i j : ι) (P N : ℝ) :
    (∑ k,mixedBlock R (p k) (q k) (massAt i P k) (massAt j N k))=
      if i=j then mixedBlock R (p i) (q i) P N
      else U R (p i) (q i) P+V R (p j) (q j) N := by
  by_cases hij : i=j
  · subst j
    have he (k : ι) : mixedBlock R (p k) (q k) (massAt i P k) (massAt i N k)=
        if k=i then mixedBlock R (p i) (q i) P N else 0 := by
      by_cases hki : k=i
      · subst k
        simp [massAt]
      · simp [massAt,hki]
    simp_rw [he]
    simp
  · have he (k : ι) : mixedBlock R (p k) (q k) (massAt i P k) (massAt j N k)=
        (if k=i then U R (p i) (q i) P else 0)+
        (if k=j then V R (p j) (q j) N else 0) := by
      by_cases hki : k=i
      · subst k
        simp [massAt,hij]
      · by_cases hkj : k=j
        · subst k
          simp [massAt,hki]
        · simp [massAt,hki,hkj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

/-- The two applications preserve both totals. Neither application asserts
that the original angles were concentrated. -/
theorem both_signs_concentrate {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (R : ℝ) (p q P N : ι → ℝ)
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap) :
    ∃ i j, (if i=j then mixedBlock R (p i) (q i) (∑ k,P k) (∑ k,N k)
      else U R (p i) (q i) (∑ k,P k)+V R (p j) (q j) (∑ k,N k))≤
        ∑ k,mixedBlock R (p k) (q k) (P k) (N k) := by
  classical
  have hPi (i : ι) : P i∈Icc 0 frameCap := by
    refine ⟨hP i,?_⟩
    exact (Finset.single_le_sum (fun k _ => hP k) (Finset.mem_univ i)).trans hPt
  obtain ⟨j,hj⟩ := concave_sum_concentrates
    (fun i => mixedBlock R (p i) (q i) (P i)) N hN rfl hNt
      (fun i => mixedBlock_concave_negative hR hQ (hp i) (hpq i) (hqp i) (hPi i))
  have hNmass (k : ι) : massAt j (∑ i,N i) k∈Icc 0 frameCap :=
    massAt_mem ⟨Finset.sum_nonneg (fun i _ => hN i),hNt⟩
  obtain ⟨i,hi⟩ := concave_sum_concentrates
    (fun k x => mixedBlock R (p k) (q k) x (massAt j (∑ i,N i) k)) P hP rfl hPt
      (fun k => mixedBlock_concave_positive hR hQ (hp k) (hpq k) (hqp k) (hNmass k))
  refine ⟨i,j,?_⟩
  rw [← concentrated_sum]
  exact hi.trans hj

def M (R p q z : ℝ) : ℝ :=
  p*(PositiveAngularEnvelope.phi (frameCap-z)-1)+q*(Real.cos frameCap-1)-
    R*(pairNorm p q (-z)-pairNorm p q 0)

theorem mixedBlock_saturated (R p q z : ℝ) :
    mixedBlock R p q (frameCap-z) (z+(frameCap-z))=M R p q z := by
  rw [show z+(frameCap-z)=frameCap by ring]
  unfold mixedBlock M
  rw [show frameCap-z-frameCap= -z by ring]

theorem separatedLine_concave {R p q p' q' z : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p')
    (hz : z∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-z))
      (fun P => U R p q P+V R p' q' (z+P)) := by
  have hU := (U_concave hR hQ hp hpq hqp).subset
    (Icc_subset_Icc le_rfl (show frameCap-z≤frameCap by linarith [hz.1]))
    (convex_Icc 0 (frameCap-z))
  have hV := concave_affine_argument (V_concave hR hQ hp' hpq' hqp')
    (a := 1) (b := z) (l := 0) (u := frameCap-z)
    (fun P hP => ⟨by linarith [hP.1,hz.1],by linarith [hP.2]⟩)
  refine (hU.add hV).congr ?_
  intro P _
  simp only [Pi.add_apply,one_mul,add_comm P z]

/-- The only remaining scalar cases are a single negative angle, a
saturated same block, or a saturated pair of distinct blocks. -/
theorem ordinary_concentration {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (R : ℝ) (p q P N : ι → ℝ) {z : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hz : z∈Icc 0 frameCap)
    (hbudget : (∑ i,P i)≤frameCap-z)
    (hbalance : (∑ i,N i)=z+∑ i,P i) :
    ∃ i j, min (V R (p j) (q j) z)
      (if i=j then M R (p i) (q i) z
       else U R (p i) (q i) (frameCap-z)+V R (p j) (q j) frameCap)≤
        ∑ k,mixedBlock R (p k) (q k) (P k) (N k) := by
  classical
  have hPt : (∑ i,P i)≤frameCap := by linarith [hz.1]
  have hNt : (∑ i,N i)≤frameCap := by rw [hbalance]; linarith
  obtain ⟨i,j,hij⟩ := both_signs_concentrate R p q P N hR hQ hp hpq hqp hP hN hPt hNt
  have htotal : (∑ i,P i)∈Icc 0 (frameCap-z) :=
    ⟨Finset.sum_nonneg (fun i _ => hP i),hbudget⟩
  have hspan : 0≤frameCap-z := by linarith [hz.2]
  refine ⟨i,j,?_⟩
  by_cases he : i=j
  · subst j
    simp only [] at hij ⊢
    rw [hbalance] at hij
    have hconc := sameBlockLine_concave (R := R) (hp i).le ((hp i).trans_le (hpq i)).le hz
    have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    rw [add_zero,mixedBlock_zero_left,mixedBlock_saturated] at hmin
    exact hmin.trans hij
  · simp only [ite_eq_right he] at hij ⊢
    rw [hbalance] at hij
    have hconc := separatedLine_concave hR hQ
      (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) hz
    have hmin := hconc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
    have hzero : U R (p i) (q i) 0+V R (p j) (q j) (z+0)=V R (p j) (q j) z := by simp
    have hsat : U R (p i) (q i) (frameCap-z)+
        V R (p j) (q j) (z+(frameCap-z))=
          U R (p i) (q i) (frameCap-z)+V R (p j) (q j) frameCap := by
      rw [show z+(frameCap-z)=frameCap by ring]
    rw [hzero,hsat] at hmin
    exact hmin.trans hij

/-- The balanced-coefficient same-block comparison keeps the full original
norm and needs no lower bound on the radius. -/
theorem M_ge_V {R p q z : ℝ} (hp : 0≤p) (_hq : 0≤q) (hqp : q≤(3/2)*p)
    (hz : z∈Icc 0 frameCap) : V R p q z≤M R p q z := by
  have ha : frameCap-z∈Icc 0 frameCap := ⟨by linarith [hz.2],by linarith [hz.1]⟩
  obtain ⟨hch,_,hsh0,hsh,_⟩ := transport_trig
    (show frameCap∈Icc 0 frameCap by constructor; norm_num [frameCap]; rfl)
  have hsa := (transport_trig ha).2.2.1
  have hca := Real.cos_le_one (frameCap-z)
  have hcz : Real.cos frameCap≤Real.cos z :=
    Real.cos_le_cos_of_nonneg_of_le_pi hz.1
      (by dsimp [frameCap]; linarith [Real.pi_gt_three]) hz.2
  have hqmul := mul_le_mul_of_nonneg_right hqp (sub_nonneg.mpr hcz)
  have hfirst : 0≤(1-(3/2)*Real.cos frameCap)*(Real.cos (frameCap-z)-1) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hsecond : 0≤(1-(3/2)*Real.sin frameCap)*Real.sin (frameCap-z) :=
    mul_nonneg (by linarith) hsa
  have hid : PositiveAngularEnvelope.phi (frameCap-z)-1-(3/2)*(Real.cos z-Real.cos frameCap)=
      (1-(3/2)*Real.cos frameCap)*(Real.cos (frameCap-z)-1)+
        (1-(3/2)*Real.sin frameCap)*Real.sin (frameCap-z) := by
    have he : Real.cos z=Real.cos frameCap*Real.cos (frameCap-z)+
        Real.sin frameCap*Real.sin (frameCap-z) := by
      rw [← Real.cos_sub,show frameCap-(frameCap-z)=z by ring]
    rw [he]
    dsimp [PositiveAngularEnvelope.phi]
    ring
  have hpos := mul_nonneg hp (show 0≤PositiveAngularEnvelope.phi (frameCap-z)-1-
      (3/2)*(Real.cos z-Real.cos frameCap) by rw [hid]; linarith)
  dsimp [M,V]
  nlinarith

end SquaresInCircles.Eight.OrdinaryAngleConcentration
