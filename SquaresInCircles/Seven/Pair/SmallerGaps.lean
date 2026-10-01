import SquaresInCircles.Seven.Pair.Frame
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import SquaresInCircles.Seven.Pair.CriticalGap

/-!
# Seven squares: the gaps below `π/3`

The support sums of a pair of admissible states are positive for every gap in
`[0, π/3)`. For gaps below 1 the two marker arcs share an arc of the unit
circle, which a weakly separating line would contain. For larger gaps a
nonpositive value, with the sum positive at `1/2` and nonnegative at `π/3`,
forces a leftmost minimum inside `(1/2, π/3)`, at a gap of at least 1 by the
small gaps; there the relative phase lies in `(-π/2, π)`. At `0` the squares
are parallel, and side by side across the axis their labels would add up to at
least `π/3`; at `π/2` they are quarter-turned, and a separating side would bring
their labels within `π/6`. Otherwise the support of the second square is a
sinusoid near the minimum: Fermat's theorem and one comparison to the left make
it stationary with a negative value, pointing away from the corner of the
second square nearest the disk centre, and the support of the first square
exceeds the distance of that corner.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Seven

lemma cardinal_range (k : Fin 4) : 0≤cardinalAngle k ∧ cardinalAngle k≤3*Real.pi/2 := by
  fin_cases k <;> norm_num [cardinalAngle] <;> (try constructor) <;> linarith [Real.pi_pos]

/-- Shifting a phase by a cardinal angle and `π` exchanges `cos` and `sin` up to
sign, so it keeps both nonzero. -/
lemma cardinal_shift_ne (k : Fin 4) {d : ℝ} (hc : Real.cos d ≠ 0) (hs : Real.sin d ≠ 0) :
    Real.cos (cardinalAngle k+Real.pi-d) ≠ 0 ∧ Real.sin (cardinalAngle k+Real.pi-d) ≠ 0 := by
  obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by fin_cases k <;> simp
  · simp [cardinalAngle,Real.cos_pi_sub,Real.sin_pi_sub,hc,hs]
  · rw [show cardinalAngle 1+Real.pi-d = (Real.pi/2-d)+Real.pi by norm_num [cardinalAngle]; ring]
    simp [Real.cos_add_pi,Real.sin_add_pi,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,hc,hs]
  · rw [show cardinalAngle 2+Real.pi-d = 2*Real.pi-d by norm_num [cardinalAngle]; ring]
    simp [Real.cos_two_pi_sub,Real.sin_two_pi_sub,hc,hs]
  · rw [show cardinalAngle 3+Real.pi-d = (Real.pi/2-d)+2*Real.pi by norm_num [cardinalAngle]; ring]
    simp [Real.cos_add_two_pi,Real.sin_add_two_pi,Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub,hc,hs]

lemma corner_label_gt {A v : ℝ} (h : Admissible A v) (hv : 1/2<v) :
    Real.pi/6<label A v := by
  have hax : Real.pi/6<axial v := by dsimp [axial]; linarith [pi_lt_22_over_7]
  have hside : Real.pi/6<side A v := by
    rw [side_identity_transverse]
    linarith [h.remainder_nonneg]
  unfold label
  exact lt_min (lt_min hax hside) (by linarith [Real.pi_pos])

/-- Algebraic characterization of a smooth negative support minimum. -/
lemma stationary_nearest_corner {A v z X Y H : ℝ} (t : TransverseSign)
    (h : Admissible A v) (hC : Real.cos z≠0) (hS : Real.sin z≠0)
    (hX : X=A+(if 0<Real.cos z then (1:ℝ) else -1)/2)
    (hY : Y=t.coe*v+(if 0<Real.sin z then (1:ℝ) else -1)/2)
    (hstat : X*Real.sin z-Y*Real.cos z=0)
    (hH : H=X*Real.cos z+Y*Real.sin z) (hneg : H<0) :
    ∃ d b : ℝ, 0<d ∧ d<1/2 ∧ 0<b ∧ b≤Real.pi/4 ∧
      A=1/2+d*Real.cos b ∧ v=1/2+d*Real.sin b ∧ H=-d ∧
      Real.cos z= -Real.cos b ∧ Real.sin z= -t.coe*Real.sin b := by
  have hu := Real.cos_sq_add_sin_sq z
  have hXC : X=H*Real.cos z := by
    calc
      X=X*(Real.cos z^2+Real.sin z^2) := by rw [hu]; ring
      _=H*Real.cos z+Real.sin z*(X*Real.sin z-Y*Real.cos z) := by rw [hH]; ring
      _=H*Real.cos z := by rw [hstat]; ring
  have hYS : Y=H*Real.sin z := by
    calc
      Y=Y*(Real.cos z^2+Real.sin z^2) := by rw [hu]; ring
      _=H*Real.sin z-Real.cos z*(X*Real.sin z-Y*Real.cos z) := by rw [hH]; ring
      _=H*Real.sin z := by rw [hstat]; ring
  have hCneg : Real.cos z<0 := by
    by_contra hn
    have hCp : 0<Real.cos z := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hC)
    rw [ite_eq_left hCp] at hX
    have hm := mul_neg_of_neg_of_pos hneg hCp
    linarith [h.half_le]
  have hXX : X=A-1/2 := by
    rw [ite_eq_right (not_lt_of_ge hCneg.le)] at hX
    linarith
  have hA : 1/2<A := by
    have hm := mul_pos_of_neg_of_neg hneg hCneg
    linarith
  have hYY : Y=t.coe*(v-1/2) ∧ 1/2<v := by
    cases t
    · simp only [TransverseSign.coe,one_mul] at hY ⊢
      have hSn : Real.sin z<0 := by
        by_contra hn
        have hSp : 0<Real.sin z := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hS)
        rw [ite_eq_left hSp] at hY
        have hm := mul_neg_of_neg_of_pos hneg hSp
        linarith [h.u_nonneg]
      rw [ite_eq_right (not_lt_of_ge hSn.le)] at hY
      have hm := mul_pos_of_neg_of_neg hneg hSn
      exact ⟨by linarith,by linarith⟩
    · simp only [TransverseSign.coe,neg_one_mul] at hY ⊢
      have hSp : 0<Real.sin z := by
        by_contra hn
        have hSn : Real.sin z<0 := lt_of_le_of_ne (le_of_not_gt hn) hS
        rw [ite_eq_right (not_lt_of_ge hSn.le)] at hY
        have hm := mul_pos_of_neg_of_neg hneg hSn
        linarith [h.u_nonneg]
      rw [ite_eq_left hSp] at hY
      have hm := mul_neg_of_neg_of_pos hneg hSp
      exact ⟨by linarith,by linarith⟩
  obtain ⟨d,b,hd,hb,hbq,hd2,hdc,hds⟩ := first_octant_polar
    (x := A-1/2) (y := v-1/2) (by linarith) (by linarith [hYY.2]) (by linarith [h.u_le])
  have hnorm : X^2+Y^2=H^2 := by
    rw [hXC,hYS]
    linear_combination H^2*hu
  have hH' : H=-d := by
    rw [hXX,hYY.1] at hnorm
    have ht : t.coe^2=1 := by cases t <;> norm_num [TransverseSign.coe]
    have hsq : (H+d)*(H-d)=0 := by linear_combination -hnorm-hd2+(v-1/2)^2*ht
    rcases mul_eq_zero.mp hsq with he | he <;> linarith
  have hcos : Real.cos z= -Real.cos b := by
    rw [hXX,hH'] at hXC
    have hm : d*(Real.cos z+Real.cos b)=0 := by linear_combination hXC+hdc
    have hh := (mul_eq_zero.mp hm).resolve_left (ne_of_gt hd)
    linarith
  have hsin : Real.sin z= -t.coe*Real.sin b := by
    rw [hYY.1,hH'] at hYS
    have hm : d*(Real.sin z+t.coe*Real.sin b)=0 := by linear_combination hYS+t.coe*hds
    have hh := (mul_eq_zero.mp hm).resolve_left (ne_of_gt hd)
    linarith
  have hsum : d<A+v-1 := by
    have hprod := mul_pos (show 0<A-1/2 by linarith) (show 0<v-1/2 by linarith [hYY.2])
    nlinarith only [hprod,hd2,hd,hA,hYY.2]
  have hp := h.phi_le
  have hdhalf : d<1/2 := by
    dsimp [phi,targetSq] at hp
    nlinarith only [hp,hd2,hsum,hd]
  exact ⟨d,b,hd,hdhalf,hb,hbq,by linarith,by linarith,hH',hcos,hsin⟩

lemma corner_source_margin {a u A v g d b : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (hg : 1≤g ∧ g≤gap)
    (hd : 0<d ∧ d<1/2) (hb : 0<b ∧ b≤Real.pi/4)
    (hA : A=1/2+d*Real.cos b) (hv : v=1/2+d*Real.sin b)
    (hC : Real.cos (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v)= -Real.cos b)
    (hS : Real.sin (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v)= -t.coe*Real.sin b) :
    d<support a (s.coe*u) (cardinalAngle k) := by
  have hsb : 0<Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [hb.2,Real.pi_pos])
  have hvh : 1/2<v := by rw [hv]; linarith [mul_pos hd.1 hsb]
  have hsmin := corner_label_gt h' hvh
  let p := label a u
  let r := label A v
  let N := cardinalAngle k-s.coe*p
  let C := g+t.coe*(b-r)
  have hp0 : 0≤p := h.label_nonneg
  have hp1 : p≤Real.pi/4 := h.label_le_quarter
  have hr0 : Real.pi/6<r := hsmin
  have hr1 : r≤Real.pi/4 := h'.label_le_quarter
  have hCrange : 0<C ∧ C<7*Real.pi/12 := by
    cases t <;> dsimp [C,TransverseSign.coe,gap] at * <;>
      constructor <;> linarith [pi_lt_22_over_7,Real.pi_pos]
  have hNrange : -Real.pi/4≤N ∧ N≤7*Real.pi/4 := by
    have hk := cardinal_range k
    cases s <;> dsimp [N,TransverseSign.coe] <;> constructor <;> linarith
  have he : N=C := by
    have hangle : N-C=(cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v)-(Real.pi+t.coe*b) := by
      dsimp [N,C,p,r]; ring
    have hcos : Real.cos (N-C)=1 := by
      rw [hangle,Real.cos_sub,hC,hS]
      cases t <;> simp only [TransverseSign.coe,one_mul,Real.cos_add,Real.sin_add,
        Real.cos_pi,Real.sin_pi,Real.cos_neg,Real.sin_neg,zero_mul,one_mul,neg_mul,
        neg_neg,zero_add,mul_neg] <;>
        linear_combination Real.sin_sq_add_cos_sq b
    have hh := cos_one_between
      ⟨by linarith [hNrange.1,hCrange.2,Real.pi_pos],
       by linarith [hNrange.2,hCrange.1,Real.pi_pos]⟩ hcos
    linarith
  fin_cases k
  · norm_num [cardinalAngle,support]
    linarith [h.half_le]
  · cases s
    · norm_num [cardinalAngle,support,TransverseSign.coe]
      linarith [h.u_nonneg]
    · have he' : Real.pi/2+p=g+t.coe*(b-r) := by
        simpa only [N,C,cardinalAngle,Fin.val_one,Nat.cast_one,one_mul,
          TransverseSign.coe,neg_one_mul,sub_neg_eq_add] using he
      cases t
      · simp only [TransverseSign.coe,one_mul] at he'
        dsimp [gap] at hg
        linarith [hb.2]
      · simp only [TransverseSign.coe,neg_one_mul] at he'
        have hcredit : Real.pi/6+p≤r-b := by dsimp [gap] at hg; linarith [hg.2]
        have hp12 : p<Real.pi/12 := by linarith [hb.1]
        have hax : label a u=axial u := by
          rcases h.selected with hA' | hT' | hcap
          · exact hA'
          · linarith [side_selected_label_gt h hT',Real.pi_lt_d2]
          · change p=Real.pi/4 at hcap
            linarith [Real.pi_pos]
        have hup : u=(4/5)*p := by dsimp [p]; rw [hax]; dsimp [axial]; ring
        let K := (3/4)*Real.cos b-(1/3)*Real.sin b
        have hcospos : 0<Real.cos b := Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hb.1,Real.pi_pos],by linarith [hb.2,Real.pi_pos]⟩
        have hsc := sin_le_cos_of_small ⟨hb.1.le,hb.2⟩
        have hK : 0<K := by dsimp [K]; linarith
        have hbound : d*K≤3/8-p-b := by
          have hh := h'.label_le_side
          change r ≤ side A v at hh
          rw [hA,hv] at hh
          dsimp [side,K] at hh ⊢
          linarith
        have hcosL : 1-b≤Real.cos b := by
          have hh := Real.one_sub_sq_div_two_le_cos (x := b)
          have hb1 : b<1 := by linarith [hb.2,pi_lt_22_over_7]
          linarith [mul_pos hb.1 (sub_pos.mpr hb1)]
        have hsinU := Real.sin_le hb.1.le
        have hKL : 3/4-(13/12)*b≤K := by dsimp [K]; linarith
        have hhpos : 0<1/2-(4/5)*p := by linarith [hp12,pi_lt_22_over_7]
        have hmult := mul_le_mul_of_nonneg_left hKL hhpos.le
        have hcross := mul_nonneg hp0 hb.1.le
        have hstrict : 3/8-p-b < (1/2-(4/5)*p)*K := by linarith
        have hd' : d<1/2-(4/5)*p := lt_of_mul_lt_mul_right (hbound.trans_lt hstrict) hK.le
        norm_num [cardinalAngle,support,TransverseSign.coe]
        rw [hup]
        linarith
  all_goals
    cases s <;> norm_num [N,C,cardinalAngle,TransverseSign.coe] at he <;>
      change _ = C at he <;> linarith [hCrange.2,hp1,Real.pi_pos]

/-- A smooth leftmost support minimum in the intermediate interval is strictly
positive. Degenerate constant pieces are already excluded by leftmostness. -/
theorem smooth_leftmost_support_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (hg : g∈Ioo (1/2) gap) (hg1 : 1≤g)
    (hmin : ∀y∈Icc (1/2) gap,pairSupport a u A v s t k g≤pairSupport a u A v s t k y)
    (hleft : ∀y∈Icc (1/2) gap,y<g → pairSupport a u A v s t k g<pairSupport a u A v s t k y)
    (hc : Real.cos (relativePhase a u A v g s t)≠0) (hs : Real.sin (relativePhase a u A v g s t)≠0) :
    0<pairSupport a u A v s t k g := by
  obtain ⟨hC,hS⟩ := cardinal_shift_ne k hc hs
  rw [show cardinalAngle k+Real.pi-relativePhase a u A v g s t =
    cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v by simp only [relativePhase]; ring]
    at hC hS
  let Z := cardinalAngle k+Real.pi-s.coe*label a u+t.coe*label A v
  let z := Z-g
  let X := A+(if 0<Real.cos z then (1:ℝ) else -1)/2
  let Y := t.coe*v+(if 0<Real.sin z then (1:ℝ) else -1)/2
  let H := X*Real.cos z+Y*Real.sin z
  have hphase : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v=z := by dsimp [z,Z]; ring
  have hCe : Real.cos z≠0 := by rwa [← hphase]
  have hSe : Real.sin z≠0 := by rwa [← hphase]
  have hcEv := absolute_sign_eventually
    (f := fun y => Real.cos (Z-y)) (by fun_prop) hCe
  have hsEv := absolute_sign_eventually
    (f := fun y => Real.sin (Z-y)) (by fun_prop) hSe
  have hevent : (fun y => pairSupport a u A v s t k y) =ᶠ[𝓝 g]
      (fun y => support a (s.coe*u) (cardinalAngle k)+X*Real.cos (Z-y)+Y*Real.sin (Z-y)) := by
    filter_upwards [hcEv,hsEv] with y hyc hys
    have hang : cardinalAngle k+Real.pi-y-s.coe*label a u+t.coe*label A v=Z-y := by dsimp [Z]; ring
    dsimp [pairSupport]
    rw [hang]
    dsimp [support,X,Y,z]
    rw [hyc,hys]
    ring
  obtain ⟨hstat,hneg⟩ := sinusoid_leftmost_minimum hg hmin hleft hevent
  change X*Real.sin z-Y*Real.cos z=0 at hstat
  change H<0 at hneg
  obtain ⟨d,b,hd,hdhalf,hb,hbq,hA,hv,hH,hcos,hsin⟩ :=
    stationary_nearest_corner t h' hCe hSe rfl rfl hstat rfl hneg
  have hsource := corner_source_margin s t k h h' ⟨hg1,hg.2.le⟩
    ⟨hd,hdhalf⟩ ⟨hb,hbq⟩ hA hv (by rw [hphase]; exact hcos) (by rw [hphase]; exact hsin)
  have heq := hevent.eq_of_nhds
  change pairSupport a u A v s t k g=
    support a (s.coe*u) (cardinalAngle k)+X*Real.cos z+Y*Real.sin z at heq
  have hH' : X*Real.cos z+Y*Real.sin z=-d := hH
  rw [heq]
  linarith

/-- Small gaps: the marker arcs share an arc of the unit circle. -/
lemma small_gap_support_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0≤g ∧ g<1) :
    0<pairSupport a u A v s t k g := by
  let p := s.coe*label a u
  let r := t.coe*label A v
  let z := cardinalAngle k-p-g/2
  let ε := (1-g)/2
  let h1 := support a (s.coe*u) (cardinalAngle k)
  let h2 := support A (t.coe*v) (cardinalAngle k+Real.pi-g-p+r)
  have hε : 0<ε := by dsimp [ε]; linarith [hg.2]
  have hb (e : ℝ) (he : |e|≤ε) : Real.cos (z-e)≤h1 ∧ -Real.cos (z-e)≤h2 := by
    have he' := abs_le.mp he
    dsimp only [ε] at he'
    have hfirst := marker_arc_support h s (x := p+g/2+e)
      (abs_le.mpr ⟨by dsimp only [p]; linarith [hg.1,he'.1],
        by dsimp only [p]; linarith [hg.1,he'.2]⟩) (cardinalAngle k)
    have hsecond := marker_arc_support h' t (x := r-g/2+e)
      (abs_le.mpr ⟨by dsimp only [r]; linarith [hg.1,he'.1],
        by dsimp only [r]; linarith [hg.1,he'.2]⟩)
      (cardinalAngle k+Real.pi-g-p+r)
    rw [show cardinalAngle k-(p+g/2+e) = z-e by dsimp [z]; ring] at hfirst
    rw [show cardinalAngle k+Real.pi-g-p+r-(r-g/2+e) = (z-e)+Real.pi by dsimp [z]; ring,
      Real.cos_add_pi] at hsecond
    exact ⟨hfirst,hsecond⟩
  by_contra hn
  have hsum : h1+h2≤0 := le_of_not_gt hn
  have heq (e : ℝ) (he : |e|≤ε) : Real.cos (z-e)=h1 := by
    have hh := hb e he
    linarith
  have h0 := heq 0 (by rw [abs_zero]; exact hε.le)
  have hp := heq ε (abs_of_pos hε).le
  have hm := heq (-ε) (by rw [abs_neg,abs_of_pos hε])
  rw [sub_zero] at h0
  rw [sub_neg_eq_add,Real.cos_add] at hm
  rw [Real.cos_sub] at hp
  have hsin0 : 0<Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε
    (by dsimp [ε]; linarith [hg.1,Real.pi_gt_three])
  have hcos1 : Real.cos ε < 1 := by
    have hu := Real.sin_sq_add_cos_sq ε
    nlinarith [Real.cos_le_one ε]
  have hsz : Real.sin z = 0 := (mul_eq_zero.mp (show Real.sin z*Real.sin ε = 0 by
    linear_combination (hp-hm)/2)).resolve_right hsin0.ne'
  have hcz : Real.cos z = 0 := (mul_eq_zero.mp (show Real.cos z*(Real.cos ε-1) = 0 by
    linear_combination (hp+hm)/2-h0)).resolve_right (by linarith)
  have hu := Real.sin_sq_add_cos_sq z
  rw [hsz,hcz] at hu
  norm_num at hu

/-- Two labels on opposite sides of parallel squares add up to at least
`π/3`. -/
theorem opposite_labels_ge {a x A y : ℝ}
    (h : Admissible a x) (h' : Admissible A y) (hs : 1 ≤ x+y) :
    gap ≤ label a x+label A y := by
  have := h.tangent
  have := h'.tangent
  have := h.sum_lt
  have := h'.sum_lt
  have := h.u_lt
  have := h'.u_lt
  rcases h.selected with hx | hx | hx <;> rcases h'.selected with hy | hy | hy <;>
    rw [hx,hy] <;> dsimp [axial,side,gap] <;> linarith [h.u_le,h'.u_le,pi_lt_22_over_7,Real.pi_gt_d2]

/-- At the relative phase `0` below the gap `π/3` every support sum is positive:
parallel squares side by side across the axis would have labels adding up to at
least `π/3`. -/
lemma parallel_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 < g ∧ g < gap)
    (hd : relativePhase a u A v g s t = 0) :
    0 < pairSupport a u A v s t k g := by
  obtain ⟨e0,e1,e2,e3⟩ := pair_support_axis_values a u A v g s t
  simp only [angularWidth,centerDX,centerDY,hd,Real.cos_zero,Real.sin_zero,
    abs_zero,abs_one,mul_zero,mul_one] at e0 e1 e2 e3
  have := h.a_lt_five_fourths
  have := h'.a_lt_five_fourths
  have := h.u_lt
  have := h'.u_lt
  have hl := h.label_nonneg
  have hL := h'.label_nonneg
  have hside (hs : s = .negative) (ht : t = .positive) : u+v < 1 := by
    by_contra hn
    have := opposite_labels_ge h h' (le_of_not_gt hn)
    subst hs ht
    simp only [relativePhase,TransverseSign.coe] at hd
    linarith
  obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by fin_cases k <;> simp
  · rw [e0]; linarith [h.half_le]
  · rw [e1]
    cases s <;> cases t <;> simp only [relativePhase,TransverseSign.coe] at hd ⊢ <;>
      first | linarith [h.u_nonneg,h'.u_nonneg] | linarith [hside rfl rfl]
  · rw [e2]; linarith [h'.half_le]
  · rw [e3]
    cases s <;> cases t <;> simp only [relativePhase,TransverseSign.coe] at hd ⊢ <;>
      linarith [h.u_nonneg,h'.u_nonneg]

/-- A quarter-turned pair with the first square beyond a whole side of the second
along the first axis: the signed labels differ by at most `π/6`. -/
lemma quarter_difference_horizontal {a u A v : ℝ} (h : Admissible a u) (h' : Admissible A v)
    (s t : TransverseSign) (hsep : 1 ≤ a+t.coe*v) :
    s.coe*label a u-t.coe*label A v ≤ Real.pi/6 := by
  have := h.tangent
  have := h.a_lt_five_fourths
  have hS := h.label_le_side
  have hA := h'.label_le_axial
  obtain ⟨h0,h1⟩ := h.label_mem
  obtain ⟨h2,h3⟩ := h'.label_mem
  dsimp [side,axial] at hS hA
  cases s <;> cases t <;> simp only [TransverseSign.coe] at hsep ⊢
  · rcases h'.selected with hL | hL | hL
    · rw [hL]
      dsimp [axial]
      linarith
    · linarith [side_selected_label_gt h' hL,Real.pi_lt_d2]
    · linarith
  · linarith
  · linarith
  · linarith [h'.u_nonneg,Real.pi_gt_d2]

/-- A quarter-turned pair separated along an axis of either square has signed
labels at most `π/6` apart. -/
theorem quarter_difference_le {a u A v : ℝ} (h : Admissible a u) (h' : Admissible A v)
    (s t : TransverseSign) (hsep : 1 ≤ a+t.coe*v ∨ 1 ≤ A-s.coe*u) :
    s.coe*label a u-t.coe*label A v ≤ Real.pi/6 := by
  rcases hsep with hh | hh
  · exact quarter_difference_horizontal h h' s t hh
  · have hq := quarter_difference_horizontal h' h t.flip s.flip
      (by rw [TransverseSign.coe_flip]; linarith)
    rw [TransverseSign.coe_flip,TransverseSign.coe_flip] at hq
    linarith

/-- At the relative phase `π/2` below the gap `π/3` every support sum is
positive: a separating side would bring the labels within `π/6`. -/
lemma quarter_turn_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : g < gap)
    (hd : relativePhase a u A v g s t = Real.pi/2) :
    0 < pairSupport a u A v s t k g := by
  obtain ⟨e0,e1,e2,e3⟩ := pair_support_axis_values a u A v g s t
  simp only [angularWidth,centerDX,centerDY,hd,Real.cos_pi_div_two,Real.sin_pi_div_two,
    abs_zero,abs_one,mul_zero,mul_one] at e0 e1 e2 e3
  have hsep (hh : 1 ≤ a+t.coe*v ∨ 1 ≤ A-s.coe*u) : False := by
    have hq := quarter_difference_le h h' s t hh
    simp only [relativePhase,gap] at hd hg
    linarith
  have hu : |s.coe*u| < 31/40 := by
    cases s <;> simpa [TransverseSign.coe,abs_of_nonneg h.u_nonneg] using h.u_lt
  have hv : |t.coe*v| < 31/40 := by
    cases t <;> simpa [TransverseSign.coe,abs_of_nonneg h'.u_nonneg] using h'.u_lt
  have hu' := abs_lt.mp hu
  have hv' := abs_lt.mp hv
  obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by fin_cases k <;> simp
  · rw [e0]; linarith [h.half_le]
  · rw [e1]; by_contra hn; exact hsep (Or.inr (by linarith))
  · rw [e2]; by_contra hn; exact hsep (Or.inl (by linarith))
  · rw [e3]; linarith [h'.half_le]

lemma pairSupport_continuous (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) :
    Continuous (fun g => pairSupport a u A v s t k g) := by
  unfold pairSupport support
  fun_prop

/-- Admissible states: the support sums are positive below the gap `π/3`. -/
theorem all_gap_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 ≤ g ∧ g < gap) :
    0 < pairSupport a u A v s t k g := by
  by_cases hg1 : g<1
  · exact small_gap_support_pos s t k h h' ⟨hg.1,hg1⟩
  by_contra hn
  obtain ⟨x,hx,hxnon,hmin,hbefore⟩ := leftmost_nonpositive_minimum
    (pairSupport_continuous a u A v s t k) ⟨by linarith,hg.2⟩ (le_of_not_gt hn)
    (small_gap_support_pos s t k h h' (g := 1/2) ⟨by norm_num,by norm_num⟩)
    (fixed_gap_nonneg s t k h h')
  have hx1 : 1 ≤ x := le_of_not_gt fun hlt =>
    (small_gap_support_pos s t k h h' ⟨by linarith [hx.1],hlt⟩).not_ge hxnon
  have hd : -Real.pi/2 < relativePhase a u A v x s t ∧ relativePhase a u A v x s t < Real.pi := by
    obtain ⟨h0,h1⟩ := h.label_mem
    obtain ⟨h2,h3⟩ := h'.label_mem
    have := hx.2
    simp only [relativePhase,gap] at *
    cases s <;> cases t <;> simp only [TransverseSign.coe] <;> constructor <;>
      linarith [Real.pi_gt_d2,Real.pi_lt_d2]
  by_cases hs : Real.sin (relativePhase a u A v x s t) = 0
  · have hp := parallel_pos s t k h h' ⟨by linarith [hx.1],hx.2⟩
      (sin_zero_between ⟨by linarith [Real.pi_pos],hd.2⟩ hs)
    linarith
  by_cases hc : Real.cos (relativePhase a u A v x s t) = 0
  · have hq := quarter_turn_pos s t k h h' hx.2 (cos_zero_between hd hc)
    linarith
  · have hp := smooth_leftmost_support_pos s t k h h' hx hx1 hmin hbefore hc hs
    linarith

end SquaresInCircles.Seven
