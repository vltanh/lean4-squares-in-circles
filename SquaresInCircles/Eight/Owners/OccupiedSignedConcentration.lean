module

public import SquaresInCircles.Eight.Owners.SingleAngleConcentration

/-!
# Eight squares: signed concentration after both primary signs are removed

The scalar block functions of `Data` may include a clipped support minorant or a minimum of two
negative charges. Both sign totals are concentrated at indices that were occupied
(`concentrated_sum`, `occupied_both_signs`). The remaining one-dimensional interval has the caps
`h - t` and `h - s`, and includes the junction `t = s` without a strict sign hypothesis
(`line_domain`, `lower_from_endpoints`).
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace SquaresInCircles.Eight.OccupiedSignedConcentration
open OrdinaryAngleConcavity OrdinaryAngleConcentration

structure Data (ι : Type*) where
  U : ι → ℝ → ℝ
  V : ι → ℝ → ℝ
  F : ι → ℝ → ℝ → ℝ
  single : ι → Bool
  U_zero : ∀ i,U i 0=0
  V_zero : ∀ i,V i 0=0
  F_left : ∀ i N,F i 0 N=V i N
  F_right : ∀ i P,F i P 0=U i P
  U_concave : ∀ i,ConcaveOn ℝ (Icc 0 frameCap) (U i)
  V_concave : ∀ i,ConcaveOn ℝ (Icc 0 frameCap) (V i)
  F_concave_P : ∀ i N,N∈Icc 0 frameCap →
    ConcaveOn ℝ (Icc 0 frameCap) (fun P => F i P N)
  F_concave_N : ∀ i P,P∈Icc 0 frameCap →
    ConcaveOn ℝ (Icc 0 frameCap) (F i P)

namespace Data

@[simp] theorem F_zero {ι : Type*} (D : Data ι) (i : ι) : D.F i 0 0=0 := by
  rw [D.F_left,D.V_zero]

theorem concentrated_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (i j : ι) (P N : ℝ) :
    (∑ a,D.F a (massAt i P a) (massAt j N a))=
      if i=j then D.F i P N else D.U i P+D.V j N := by
  by_cases hij : i=j
  · subst j
    have he (a : ι) : D.F a (massAt i P a) (massAt i N a)=
        if a=i then D.F i P N else 0 := by
      by_cases hai : a=i
      · subst a; simp [massAt]
      · simp [massAt,hai]
    simp_rw [he]
    simp
  · have he (a : ι) : D.F a (massAt i P a) (massAt j N a)=
        (if a=i then D.U i P else 0)+(if a=j then D.V j N else 0) := by
      by_cases hai : a=i
      · subst a; simp [massAt,hij,D.F_right]
      · by_cases haj : a=j
        · subst a; simp [massAt,hai,D.F_left]
        · simp [massAt,hai,haj]
    simp_rw [he]
    rw [Finset.sum_add_distrib]
    simp [hij]

theorem occupied_both_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data ι) (P N : ι → ℝ)
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (hPpos : 0<∑ i,P i) (hNpos : 0<∑ i,N i)
    (hPt : (∑ i,P i)≤frameCap) (hNt : (∑ i,N i)≤frameCap)
    (hsingle : ∀ i,D.single i=true → P i=0 ∨ N i=0) :
    ∃ i j,(i=j → D.single i=false) ∧
      (if i=j then D.F i (∑ a,P a) (∑ a,N a)
       else D.U i (∑ a,P a)+D.V j (∑ a,N a))≤∑ a,D.F a (P a) (N a) := by
  have hPi (i : ι) : P i∈Icc 0 frameCap :=
    ⟨hP i,(Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)).trans hPt⟩
  obtain ⟨j,hjpos,hj⟩ := SingleAngleConcentration.support_concentrates
    (fun a n => D.F a (P a) n) N hN hNpos hNt
    (fun a => D.F_concave_N a (P a) (hPi a))
  have hNm (a : ι) : massAt j (∑ b,N b) a∈Icc 0 frameCap :=
    massAt_mem ⟨hNpos.le,hNt⟩
  obtain ⟨i,hipos,hi⟩ := SingleAngleConcentration.support_concentrates
    (fun a p => D.F a p (massAt j (∑ b,N b) a)) P hP hPpos hPt
    (fun a => D.F_concave_P a _ (hNm a))
  refine ⟨i,j,?_,?_⟩
  · intro hij
    subst j
    cases hm : D.single i
    · rfl
    · rcases hsingle i hm with hz | hz <;> linarith
  · rw [D.concentrated_sum] at hi
    exact hi.trans hj

theorem line_domain {t s : ℝ} (ht : t∈Icc 0 frameCap)
    (hs : s∈Icc 0 frameCap) :
    max 0 (s-t)≤frameCap-t ∧
      ∀ P∈Icc (max 0 (s-t)) (frameCap-t),
        P∈Icc 0 frameCap ∧ t-s+P∈Icc 0 frameCap := by
  refine ⟨max_le (by linarith [ht.2]) (by linarith [hs.2]),?_⟩
  intro P hP
  have hP0 := (le_max_left (0:ℝ) (s-t)).trans hP.1
  have hdiff := (le_max_right (0:ℝ) (s-t)).trans hP.1
  exact ⟨⟨hP0,by linarith [hP.2,ht.1]⟩,
    ⟨by linarith,by linarith [hP.2,hs.1]⟩⟩

theorem separated_line {ι : Type*} (D : Data ι) (i j : ι) {t s : ℝ}
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap) :
    ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
      (fun P => D.U i P+D.V j (t-s+P)) := by
  have hdom := line_domain ht hs
  have hU := (D.U_concave i).subset
    (fun P hP => (hdom.2 P hP).1) (convex_Icc _ _)
  have hV := concave_affine_argument (D.V_concave j)
    (a:=1) (b:=t-s) (l:=max 0 (s-t)) (u:=frameCap-t)
    (fun P hP => by simpa only [one_mul,add_comm P] using (hdom.2 P hP).2)
  have hfun : (fun P => D.U i P+D.V j (t-s+P))=
      D.U i+(fun x => D.V j (1*x+(t-s))) := by
    funext P
    simp only [Pi.add_apply,one_mul,add_comm P]
  rw [hfun]
  exact hU.add hV

/-- Every allocation is bounded below through the pure-sign junction or one of the two saturated
alternatives; the concavity along the mixed line is used only at an index that carried both
signs. -/
theorem lower_from_endpoints {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (D : Data ι) (P N : ι → ℝ) {t s L : ℝ}
    (hP : ∀ i,0≤P i) (hN : ∀ i,0≤N i)
    (ht : t∈Icc 0 frameCap) (hs : s∈Icc 0 frameCap)
    (hbudget : (∑ i,P i)≤frameCap-t) (hbalance : (∑ i,N i)=t-s+∑ i,P i)
    (hsingle : ∀ i,D.single i=true → P i=0 ∨ N i=0)
    (hline : ∀ i,D.single i=false →
      ConcaveOn ℝ (Icc (max 0 (s-t)) (frameCap-t))
        (fun P => D.F i P (t-s+P)))
    (hnegative : s≤t → ∀ i,L≤D.V i (t-s))
    (hpositive : t≤ s → ∀ i,L≤D.U i (s-t))
    (hmixed : ∀ i,D.single i=false → L≤D.F i (frameCap-t) (frameCap-s))
    (hseparated : ∀ i j,i≠j → L≤D.U i (frameCap-t)+D.V j (frameCap-s)) :
    L≤∑ i,D.F i (P i) (N i) := by
  have hP0 : 0≤∑ i,P i := Finset.sum_nonneg (fun i _ => hP i)
  have hN0 : 0≤∑ i,N i := Finset.sum_nonneg (fun i _ => hN i)
  have hPt : (∑ i,P i)≤frameCap := by linarith [ht.1]
  have hNt : (∑ i,N i)≤frameCap := by linarith [hs.1]
  by_cases hzP : (∑ i,P i)=0
  · have hPi (i : ι) : P i=0 := by
      have hh := Finset.single_le_sum (fun a _ => hP a) (Finset.mem_univ i)
      linarith [hP i]
    have hNeq : (∑ i,N i)=t-s := by linarith
    have hst : s≤t := by linarith
    obtain ⟨j,hj⟩ := concave_sum_concentrates D.V N hN hNeq
      (by linarith [ht.2,hs.1] : t-s≤frameCap) D.V_concave
    have hsum : (∑ i,D.V i (massAt j (t-s) i))=D.V j (t-s) := by
      simp only [massAt,apply_ite,D.V_zero]
      simp
    rw [hsum] at hj
    calc
      L≤D.V j (t-s) := hnegative hst j
      _≤∑ i,D.V i (N i) := hj
      _=∑ i,D.F i (P i) (N i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hPi i,D.F_left]
  by_cases hzN : (∑ i,N i)=0
  · have hNi (i : ι) : N i=0 := by
      have hh := Finset.single_le_sum (fun a _ => hN a) (Finset.mem_univ i)
      linarith [hN i]
    have hPeq : (∑ i,P i)=s-t := by linarith
    have hts : t≤ s := by linarith
    obtain ⟨i,hi⟩ := concave_sum_concentrates D.U P hP hPeq
      (by linarith [hs.2,ht.1] : s-t≤frameCap) D.U_concave
    have hsum : (∑ j,D.U j (massAt i (s-t) j))=D.U i (s-t) := by
      simp only [massAt,apply_ite,D.U_zero]
      simp
    rw [hsum] at hi
    calc
      L≤D.U i (s-t) := hpositive hts i
      _≤∑ j,D.U j (P j) := hi
      _=∑ j,D.F j (P j) (N j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hNi j,D.F_right]
  have hPpos : 0<∑ i,P i := lt_of_le_of_ne hP0 (Ne.symm hzP)
  have hNpos : 0<∑ i,N i := lt_of_le_of_ne hN0 (Ne.symm hzN)
  obtain ⟨i,j,htwo,hij⟩ := D.occupied_both_signs P N hP hN
    hPpos hNpos hPt hNt hsingle
  have hspan := (line_domain ht hs).1
  have htotal : (∑ i,P i)∈Icc (max 0 (s-t)) (frameCap-t) :=
    ⟨max_le hP0 (by linarith),hbudget⟩
  have hleft : max 0 (s-t)∈Icc (max 0 (s-t)) (frameCap-t) := ⟨le_rfl,hspan⟩
  have hright : frameCap-t∈Icc (max 0 (s-t)) (frameCap-t) := ⟨hspan,le_rfl⟩
  by_cases he : i=j
  · subst j
    have hm : D.single i=false := htwo rfl
    simp only at hij
    rw [hbalance] at hij
    have hpure : L≤D.F i (max 0 (s-t)) (t-s+max 0 (s-t)) := by
      by_cases hst : s≤t
      · rw [max_eq_left (by linarith : s-t≤0),add_zero,D.F_left]
        exact hnegative hst i
      · have hts : t≤ s := (lt_of_not_ge hst).le
        rw [max_eq_right (by linarith : 0≤ s-t),
          show t-s+(s-t)=0 by ring,D.F_right]
        exact hpositive hts i
    have hfar := hmixed i hm
    have hmin := (hline i hm).min_le_of_mem_Icc hleft hright htotal
    rw [show t-s+(frameCap-t)=frameCap-s by ring] at hmin
    exact (le_min hpure hfar).trans (hmin.trans hij)
  · simp only [he,↓reduceIte] at hij
    rw [hbalance] at hij
    have hpure : L≤D.U i (max 0 (s-t))+D.V j (t-s+max 0 (s-t)) := by
      by_cases hst : s≤t
      · rw [max_eq_left (by linarith : s-t≤0),add_zero,D.U_zero,zero_add]
        exact hnegative hst j
      · have hts : t≤ s := (lt_of_not_ge hst).le
        rw [max_eq_right (by linarith : 0≤ s-t),
          show t-s+(s-t)=0 by ring,D.V_zero,add_zero]
        exact hpositive hts i
    have hmin := (D.separated_line i j ht hs).min_le_of_mem_Icc hleft hright htotal
    rw [show t-s+(frameCap-t)=frameCap-s by ring] at hmin
    exact (le_min hpure (hseparated i j he)).trans (hmin.trans hij)

end Data

end SquaresInCircles.Eight.OccupiedSignedConcentration
