import SquaresInCircles.Seven.PairModel
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Smooth minima of a support sum

A nonpositive value after a positive left endpoint and before a nonnegative
right endpoint gives an interior leftmost minimum, so a stretch where a support
sum is constant cannot hide a new case. At a smooth leftmost minimum the target
support is a sinusoid; Fermat's theorem and one comparison to the left make it
stationary with a negative value, pointing away from the target's corner nearest
the disk centre. The source support then exceeds the distance of that corner.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Seven

lemma sin_zero_between {x : ℝ} (hx : -Real.pi<x ∧ x<Real.pi)
    (hs : Real.sin x=0) : x=0 := by
  rcases lt_trichotomy x 0 with h | h | h
  · have hp := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith) (by linarith [hx.1])
    rw [Real.sin_neg,hs] at hp
    linarith
  · exact h
  · have hp := Real.sin_pos_of_pos_of_lt_pi h hx.2
    rw [hs] at hp
    linarith

lemma cos_one_between {x : ℝ} (hx : -2*Real.pi<x ∧ x<2*Real.pi)
    (hc : Real.cos x=1) : x=0 := by
  have hhalf : Real.sin (x/2)=0 := by
    have he := Real.cos_two_mul (x/2)
    rw [show 2*(x/2)=x by ring,hc] at he
    have hu := Real.sin_sq_add_cos_sq (x/2)
    nlinarith
  have hh := sin_zero_between (x := x/2)
    ⟨by linarith [hx.1],by linarith [hx.2]⟩ hhalf
  linarith

lemma cos_zero_between {x : ℝ} (hx : -Real.pi/2<x ∧ x<Real.pi)
    (hc : Real.cos x=0) : x=Real.pi/2 := by
  have hs : Real.sin (x-Real.pi/2)=0 := by
    rw [Real.sin_sub]
    simpa using congrArg Neg.neg hc
  have h := sin_zero_between
    (x := x-Real.pi/2) ⟨by linarith [hx.1],by linarith [hx.2,Real.pi_pos]⟩ hs
  linarith

lemma cardinal_range (k : Fin 4) : 0≤cardinalAngle k ∧ cardinalAngle k≤3*Real.pi/2 := by
  fin_cases k <;> norm_num [cardinalAngle] <;> (try constructor) <;> linarith [Real.pi_pos]

/-- A nonpositive value after a positive left endpoint and before a nonnegative
right endpoint has an interior leftmost minimizer. Every earlier point has
strictly larger value. -/
lemma leftmost_nonpositive_minimum {f : ℝ → ℝ} {l u y : ℝ}
    (hf : Continuous f) (hy : y∈Ico l u) (hbad : f y≤0)
    (hl : 0<f l) (hu : 0≤f u) :
    ∃ x, x∈Ioo l u ∧ f x≤0 ∧
      (∀z∈Icc l u,f x≤f z) ∧
      (∀z∈Icc l u,z<x → f x<f z) := by
  have hy' : y∈Icc l u := Ico_subset_Icc_self hy
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨y,hy'⟩ hf.continuousOn
  let K : Set ℝ := Icc l u ∩ {x | f x=f m}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_eq hf continuous_const)
  have hn : K.Nonempty := ⟨m,hm,rfl⟩
  obtain ⟨x,hx,hleft⟩ := hK.exists_isMinOn hn continuous_id.continuousOn
  have hxval : f x=f m := hx.2
  have hym : f m≤f y := hmin hy'
  have hxnon : f x≤0 := hxval.le.trans (hym.trans hbad)
  have hxl : l<x := by
    have hle := hx.1.1
    by_contra hn
    have he : x=l := le_antisymm (le_of_not_gt hn) hle
    rw [he] at hxnon
    linarith
  have hxu : x<u := by
    refine lt_of_le_of_ne hx.1.2 fun he => ?_
    rw [he] at hxval
    have hyK : y∈K := ⟨hy',le_antisymm (by linarith) hym⟩
    have hxy : x≤y := hleft hyK
    linarith [hy.2]
  refine ⟨x,⟨hxl,hxu⟩,hxnon,?_,?_⟩
  · intro z hz
    rw [hxval]
    exact hmin hz
  · intro z hz hzx
    have hle : f x≤f z := hxval.le.trans (hmin hz)
    by_contra hn
    have he : f z=f m := by linarith
    have hk : z∈K := ⟨hz,he⟩
    have hh : x≤z := hleft hk
    linarith

lemma sinusoid_leftmost_minimum {f : ℝ → ℝ} {l u x c A B Z : ℝ}
    (hx : x∈Ioo l u)
    (hmin : ∀y∈Icc l u,f x≤f y)
    (hleft : ∀y∈Icc l u,y<x → f x<f y)
    (hevent : f =ᶠ[𝓝 x] (fun y => c+A*Real.cos (Z-y)+B*Real.sin (Z-y))) :
    A*Real.sin (Z-x)-B*Real.cos (Z-x)=0 ∧
      A*Real.cos (Z-x)+B*Real.sin (Z-x)<0 := by
  let g : ℝ → ℝ := fun y => c+A*Real.cos (Z-y)+B*Real.sin (Z-y)
  have he0 : f x=g x := hevent.eq_of_nhds
  have hlocal : IsLocalMin f x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hmin y ⟨hy.1.le,hy.2.le⟩
  have harg : HasDerivAt (fun y : ℝ => Z-y) (-1) x := (hasDerivAt_id' x).const_sub Z
  have hg : HasDerivAt g (A*Real.sin (Z-x)-B*Real.cos (Z-x)) x := by
    convert (((harg.cos.const_mul A).const_add c).add (harg.sin.const_mul B)) using 1
    ring
  have hf := hg.congr_of_eventuallyEq hevent
  have hstationary : A*Real.sin (Z-x)-B*Real.cos (Z-x)=0 :=
    hlocal.hasDerivAt_eq_zero hf
  refine ⟨hstationary,?_⟩
  by_contra hn
  have hnon : 0≤A*Real.cos (Z-x)+B*Real.sin (Z-x) := le_of_not_gt hn
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hevent
  let e := min (r/2) ((x-l)/2)
  have hepos : 0<e := lt_min (by positivity) (by linarith [hx.1])
  have her : e<r := (min_le_left _ _).trans_lt (by linarith)
  have hex : e≤(x-l)/2 := min_le_right _ _
  have hy : x-e∈Icc l u := ⟨by linarith,by linarith [hx.2]⟩
  have hyl : x-e<x := by linarith
  have hye : f (x-e)=g (x-e) := hball
    (by rw [Metric.mem_ball,Real.dist_eq,show (x-e)-x=-e by ring,abs_neg,abs_of_pos hepos]; exact her)
  have hstrict := hleft (x-e) hy hyl
  rw [he0,hye] at hstrict
  have hid : g (x-e)-g x=
      (A*Real.cos (Z-x)+B*Real.sin (Z-x))*(Real.cos e-1) := by
    have he : Z-(x-e)=(Z-x)+e := by ring
    dsimp [g]
    rw [he,Real.cos_add,Real.sin_add]
    linear_combination (-Real.sin e)*hstationary
  have hprod := mul_nonpos_of_nonneg_of_nonpos hnon
    (sub_nonpos.mpr (Real.cos_le_one e))
  linarith

lemma absolute_sign_eventually {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : f x≠0) :
    ∀ᶠ y in 𝓝 x, |f y|=(if 0<f x then (1:ℝ) else -1)*f y := by
  by_cases hpos : 0<f x
  · filter_upwards [(hf.tendsto x).eventually (lt_mem_nhds hpos)] with y hy
    simp only [ite_eq_left hpos,one_mul,abs_of_pos hy]
  · have hneg : f x<0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    filter_upwards [(hf.tendsto x).eventually (gt_mem_nhds hneg)] with y hy
    simp only [ite_eq_right hpos,neg_one_mul,abs_of_neg hy]

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

lemma first_octant_polar {x y : ℝ} (hx : 0<x) (hy : 0<y) (hxy : y≤x) :
    ∃ d b : ℝ, 0<d ∧ 0<b ∧ b≤Real.pi/4 ∧ d^2=x^2+y^2 ∧
      d*Real.cos b=x ∧ d*Real.sin b=y := by
  let d := Real.sqrt (x^2+y^2)
  have hd : 0<d := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x,sq_nonneg y])
  have hd2 : d^2=x^2+y^2 := Real.sq_sqrt (by positivity)
  have hxd : 0<x/d := div_pos hx hd
  have hxd1 : x/d<1 := (div_lt_one hd).mpr (by nlinarith)
  let b := Real.arccos (x/d)
  have hc : Real.cos b=x/d := Real.cos_arccos (by linarith) hxd1.le
  have hb0 : 0≤b := Real.arccos_nonneg _
  have hbpi : b≤Real.pi := Real.arccos_le_pi _
  have hbhalf : b<Real.pi/2 := by
    have hs := Real.arcsin_pos.mpr hxd
    dsimp [b,Real.arccos]
    linarith
  have hbp : 0<b := by
    by_contra hn
    have he : b=0 := le_antisymm (le_of_not_gt hn) hb0
    rw [he,Real.cos_zero] at hc
    linarith
  have hdc : d*Real.cos b=x := by rw [hc]; field_simp
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hb0 hbpi
  have hds : d*Real.sin b=y := by
    have hu := congrArg (fun z : ℝ => d^2*z) (Real.sin_sq_add_cos_sq b)
    have hc2 := congrArg (fun z : ℝ => z^2) hdc
    have hn := mul_nonneg hd.le hs0
    nlinarith
  have hbq : b≤Real.pi/4 := by
    by_contra hn
    have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hbhalf.le
      (show Real.pi/2-b<b by linarith)
    rw [Real.sin_pi_div_two_sub] at hsin
    have hm := mul_lt_mul_of_pos_left hsin hd
    rw [hdc,hds] at hm
    linarith
  exact ⟨d,b,hd,hbp,hbq,hd2,hdc,hds⟩

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
    (hg : 1<g ∧ g<gap)
    (hmin : ∀y∈Icc 1 gap,pairSupport a u A v s t k g≤pairSupport a u A v s t k y)
    (hleft : ∀y∈Icc 1 gap,y<g → pairSupport a u A v s t k g<pairSupport a u A v s t k y)
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
  have hsource := corner_source_margin s t k h h' ⟨hg.1.le,hg.2.le⟩
    ⟨hd,hdhalf⟩ ⟨hb,hbq⟩ hA hv (by rw [hphase]; exact hcos) (by rw [hphase]; exact hsin)
  have heq := hevent.eq_of_nhds
  change pairSupport a u A v s t k g=
    support a (s.coe*u) (cardinalAngle k)+X*Real.cos z+Y*Real.sin z at heq
  have hH' : X*Real.cos z+Y*Real.sin z=-d := hH
  rw [heq]
  linarith

end SquaresInCircles.Seven
