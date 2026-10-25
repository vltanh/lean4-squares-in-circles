module

public import SquaresInCircles.Eight.TableFree.SingleAngleConcavity

/-!
# Concentration respecting which anchors have one ordinary angle

Uncompiled source. A positive total can be concentrated at an index
where the original mass was positive. Applying this to each sign prevents
a one-angle anchor from receiving both signs. Thus only actual two-angle
anchors need the same-block endpoint comparison. Zero total is included.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.TableFree.SingleAngleConcentration
open PositiveAngularEnvelope OrdinaryAngleConcavity OrdinaryAngleConcentration
open SingleAngleConcavity

/-- A nonzero simplex total is concentrated at a member of its original
support. The proof is the finite chord inequality on that support. -/
theorem support_concentrates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (x : ι → ℝ) {h : ℝ}
    (hx : ∀ i,0≤x i) (hpos : 0<∑ i,x i) (hbound : (∑ i,x i)≤h)
    (hf : ∀ i,ConcaveOn ℝ (Icc 0 h) (f i)) :
    ∃ j,0<x j ∧ (∑ i,f i (massAt j (∑ a,x a) i))≤∑ i,f i (x i) := by
  classical
  let T := ∑ i,x i
  let S : Finset ι := Finset.univ.filter (fun i => 0<x i)
  let a (i : ι) := f i T-f i 0
  have hT : 0<T := hpos
  have hxT (i : ι) : x i≤T := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  have hex : ∃ i,0<x i := by
    by_contra hn
    push Not at hn
    have hs : (∑ i,x i)≤0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,by simp [S,hi]⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S a hS
  have hjpos : 0<x j := (Finset.mem_filter.mp hj).2
  have hc (i : ι) : 0≤x i/T ∧ x i/T≤1 :=
    ⟨div_nonneg (hx i) hT.le,(div_le_one hT).2 (hxT i)⟩
  have hchord (i : ι) : f i 0+(x i/T)*a i≤f i (x i) := by
    have hh := (hf i).2
      (show (0:ℝ)∈Icc 0 h from ⟨le_rfl,hT.le.trans hbound⟩)
      (show T∈Icc 0 h from ⟨hT.le,hbound⟩)
      (sub_nonneg.mpr (hc i).2) (hc i).1 (by ring)
    have he : (1-x i/T)*0+(x i/T)*T=x i := by field_simp [hT.ne']; ring
    simp only [smul_eq_mul,he] at hh
    dsimp [a]
    nlinarith only [hh]
  have hterm (i : ι) : f i 0+(x i/T)*a j≤f i (x i) := by
    by_cases hi : 0<x i
    · have hm := mul_le_mul_of_nonneg_left (hmin i (by simp [S,hi])) (hc i).1
      linarith [hchord i]
    · have hz : x i=0 := by linarith [hx i]
      simp [hz]
  have hsumcoeff : (∑ i,x i/T)=1 := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change T*T⁻¹=1
    exact mul_inv_cancel₀ hT.ne'
  have hsumleft : (∑ i,(f i 0+(x i/T)*a j))=(∑ i,f i 0)+a j := by
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hsumcoeff,one_mul]
  have hsumright : (∑ i,f i (massAt j T i))=(∑ i,f i 0)+a j := by
    have he (i : ι) : f i (massAt j T i)=f i 0+if i=j then a j else 0 := by
      by_cases hi : i=j
      · subst i; simp [massAt,a]
      · simp [massAt,hi]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp
  refine ⟨j,hjpos,?_⟩
  rw [hsumright,← hsumleft]
  exact Finset.sum_le_sum (fun i _ => hterm i)

theorem concentrated_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu : ι → ℝ) (i j : ι) (P N : ℝ) :
    (∑ a,F (m a) R (p a) (q a) (nu a) (massAt i P a) (massAt j N a))=
      if i=j then F (m i) R (p i) (q i) (nu i) P N
      else U R (p i) (q i) P+pure (m j) R (p j) (q j) (nu j) N := by
  by_cases hij : i=j
  · subst j
    have he (a : ι) : F (m a) R (p a) (q a) (nu a) (massAt i P a) (massAt i N a)=
        if a=i then F (m i) R (p i) (q i) (nu i) P N else 0 := by
      by_cases hai : a=i
      · subst a; simp [massAt]
      · simp [massAt,hai]
    simp_rw [he]
    simp
  · have he (a : ι) : F (m a) R (p a) (q a) (nu a) (massAt i P a) (massAt j N a)=
        (if a=i then U R (p i) (q i) P else 0)+
        (if a=j then pure (m j) R (p j) (q j) (nu j) N else 0) := by
      by_cases hai : a=i
      · subst a; simp [massAt,hij]
      · by_cases haj : a=j
        · subst a; simp [massAt,hai]
        · simp [massAt,hai,haj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

/-- If both totals are positive, concentration cannot put them together
at a single-angle anchor: both original support memberships are retained. -/
theorem both_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu P N : ι → ℝ)
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hnu : ∀ i,p i≤nu i) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPpos : 0<∑ i,P i) (hNpos : 0<∑ i,N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap)
    (hsingle : ∀ i,m i=true → P i=0 ∨ N i=0) :
    ∃ i j,(i=j → m i=false) ∧
      (if i=j then F (m i) R (p i) (q i) (nu i) (∑ a,P a) (∑ a,N a)
       else U R (p i) (q i) (∑ a,P a)+pure (m j) R (p j) (q j) (nu j) (∑ a,N a))≤
        ∑ a,F (m a) R (p a) (q a) (nu a) (P a) (N a) := by
  have hPi (i : ι) : P i∈Icc 0 frameCap :=
    ⟨hP i,(Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)).trans hPt⟩
  obtain ⟨j,hjpos,hj⟩ := support_concentrates
    (fun a n => F (m a) R (p a) (q a) (nu a) (P a) n) N hN hNpos hNt
    (fun a => F_concave_N hR hQ (hp a) (hpq a) (hqp a) (hnu a) (hPi a))
  have hNm (a : ι) : massAt j (∑ b,N b) a∈Icc 0 frameCap := massAt_mem ⟨hNpos.le,hNt⟩
  obtain ⟨i,hipos,hi⟩ := support_concentrates
    (fun a p' => F (m a) R (p a) (q a) (nu a) p' (massAt j (∑ b,N b) a))
    P hP hPpos hPt (fun a => F_concave_P hR hQ (hp a) (hpq a) (hqp a) (hNm a))
  refine ⟨i,j,?_,?_⟩
  · intro hij
    subst j
    cases hm : m i
    · rfl
    · rcases hsingle i hm with hz | hz
      · linarith
      · linarith
  · rw [concentrated_sum] at hi
    exact hi.trans hj

theorem separated_concave {single : Bool} {R p q p' q' nu t : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p)
    (hp' : 0<p') (hpq' : p'≤q') (hqp' : q'≤2*p') (hnu : p'≤nu)
    (ht : t∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc 0 (frameCap-t))
      (fun P => U R p q P+pure single R p' q' nu (t+P)) := by
  have hU := (U_concave hR hQ hp hpq hqp).subset
    (Icc_subset_Icc le_rfl (by linarith [ht.1])) (convex_Icc 0 (frameCap-t))
  have hV := concave_affine_argument (pure_concave (single := single) hR hQ hp' hpq' hqp' hnu)
    (a := 1) (b := t) (l := 0) (u := frameCap-t)
    (fun x hx => ⟨by linarith [ht.1,hx.1],by linarith [hx.2]⟩)
  convert hU.add hV using 1
  funext P
  simp only [Pi.add_apply,one_mul,add_comm t]

/-- The analytic endpoint comparisons imply a lower bound for every
original allocation. The same-block premise is needed only for anchors
which actually have two ordinary arguments. -/
theorem lower_from_endpoints {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (m : ι → Bool) (R : ℝ) (p q nu P N : ι → ℝ) {t L : ℝ}
    (hR : 0≤R) (hQ : R^2≤qCap)
    (hp : ∀ i,0<p i) (hpq : ∀ i,p i≤q i) (hqp : ∀ i,q i≤2*p i)
    (hnu : ∀ i,p i≤nu i) (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (ht : t∈Icc 0 frameCap) (hbudget : (∑ i,P i)≤frameCap-t)
    (hbalance : (∑ i,N i)=t+∑ i,P i)
    (hsingle : ∀ i,m i=true → P i=0 ∨ N i=0)
    (hpure : ∀ i,L≤pure (m i) R (p i) (q i) (nu i) t)
    (hmixed : ∀ i,m i=false → L≤M R (p i) (q i) t)
    (hseparated : ∀ i j,i≠j → L≤U R (p i) (q i) (frameCap-t)+
      pure (m j) R (p j) (q j) (nu j) frameCap) :
    L≤∑ i,F (m i) R (p i) (q i) (nu i) (P i) (N i) := by
  have hP0 : 0≤∑ i,P i := Finset.sum_nonneg (fun i _ => hP i)
  have hPt : (∑ i,P i)≤frameCap := by linarith [ht.1]
  have hNt : (∑ i,N i)≤frameCap := by linarith
  by_cases hz : (∑ i,P i)=0
  · have hPi (i : ι) : P i=0 := by
      have hh := Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)
      linarith [hP i]
    have hNeq : (∑ i,N i)=t := by linarith
    obtain ⟨j,hj⟩ := concave_sum_concentrates
      (fun i n => pure (m i) R (p i) (q i) (nu i) n) N hN hNeq ht.2
      (fun i => pure_concave hR hQ (hp i) (hpq i) (hqp i) (hnu i))
    have hsum : (∑ i,pure (m i) R (p i) (q i) (nu i) (massAt j t i))=
        pure (m j) R (p j) (q j) (nu j) t := by
      simp only [massAt,apply_ite,pure_zero]
      simp
    rw [hsum] at hj
    have heq : (∑ i,F (m i) R (p i) (q i) (nu i) (P i) (N i))=
        ∑ i,pure (m i) R (p i) (q i) (nu i) (N i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hPi i,F_zero_left]
    rw [heq]
    exact (hpure j).trans hj
  · have hPpos : 0<∑ i,P i := lt_of_le_of_ne hP0 (Ne.symm hz)
    have hNpos : 0<∑ i,N i := by linarith [ht.1]
    obtain ⟨i,j,htwo,hij⟩ := both_signs m R p q nu P N hR hQ hp hpq hqp hnu
      hP hN hPpos hNpos hPt hNt hsingle
    have htotal : (∑ i,P i)∈Icc 0 (frameCap-t) := ⟨hP0,hbudget⟩
    have hspan : 0≤frameCap-t := by linarith [ht.2]
    by_cases he : i=j
    · subst j
      have hm : m i=false := htwo rfl
      simp only [↓reduceIte] at hij
      rw [show F (m i) R (p i) (q i) (nu i) (∑ a,P a) (∑ a,N a)=
        mixedBlock R (p i) (q i) (∑ a,P a) (∑ a,N a) by simp [F,hm],hbalance] at hij
      have hc := sameBlockLine_concave (R := R) (hp i).le ((hp i).trans_le (hpq i)).le ht
      have hmin := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      rw [add_zero,mixedBlock_zero_left,mixedBlock_saturated] at hmin
      have hpure' : L≤V R (p i) (q i) t := by simpa [SingleAngleConcavity.pure,hm] using hpure i
      exact (le_min hpure' (hmixed i hm)).trans (hmin.trans hij)
    · simp only [he,↓reduceIte] at hij
      rw [hbalance] at hij
      have hc := separated_concave (single := m j) hR hQ
        (hp i) (hpq i) (hqp i) (hp j) (hpq j) (hqp j) (hnu j) ht
      have hmin := hc.min_le_of_mem_Icc ⟨le_rfl,hspan⟩ ⟨hspan,le_rfl⟩ htotal
      simp only [U_zero,zero_add,add_zero,show t+(frameCap-t)=frameCap by ring] at hmin
      exact (le_min (hpure j) (hseparated i j he)).trans (hmin.trans hij)

end SquaresInCircles.Eight.TableFree.SingleAngleConcentration
