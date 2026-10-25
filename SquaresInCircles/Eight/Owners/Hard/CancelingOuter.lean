module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Contact.Continuation
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: a negative canceling outer error has an aligned descendant

After the middle is aligned, the frame of G lies at or above that of A. In the sector `G ≤ H` the
HG2 and GA0 inequalities cancel the same signed coordinate of G (`rate_identity`), and their
composite has a positive derivative wherever it is feasible (`rate_on_feasible`), so the
first-contact continuation reaches H with a linear reserve (`feasible_right_reserve`,
`actual_aligned_reserve`).

The reserve is spent on a decrease of the primary coordinate of A (`alignment_of_reserve`). G is
replaced by a point of the flat core at the frame of H, while the point of H and the tangent and
frame of A stay, and a nonzero HG error gives a strict loss on the original circle of A
(`GAlignment`, `actual_G_alignment`). The equality argument uses no circle loss at the free
intermediate. Reflection gives the same on the side of T (`TAlignment`, `actual_T_alignment`).
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
namespace HardCancelingOuter

/-- Feasible-contact continuation to the right: if `k ≤ f'` wherever `b ≤ f`, and `b ≤ f l`, then
`b ≤ f` on `[l, u]`, with the linear gain `k (x - l)`; feasibility along the motion follows from
the sign of the derivative. -/
theorem feasible_right_reserve {f df : ℝ → ℝ} {l u b k : ℝ}
    (hlu : l≤u) (hk : 0<k)
    (hd : ∀x∈Icc l u, HasDerivAt f (df x) x)
    (hpos : ∀x∈Icc l u, b≤f x → k≤df x) (hl : b≤f l) :
    ∀x∈Icc l u, b≤f x ∧ k*(x-l)≤f x-f l := by
  let g : ℝ → ℝ := fun x => f (-x)
  let dg : ℝ → ℝ := fun x => -df (-x)
  have hmem (x : ℝ) (hx : x∈Icc (-u) (-l)) : -x∈Icc l u := by
    constructor <;> linarith [hx.1,hx.2]
  have hderiv (x : ℝ) (hx : x∈Icc (-u) (-l)) : HasDerivAt g (dg x) x := by
    convert (hd (-x) (hmem x hx)).comp x (hasDerivAt_id x).neg using 1
    · rfl
    · dsimp [dg]
      ring
  have hh := feasible_left_reserve (f := g) (df := dg)
    (l := -u) (u := -l) (b := b) (k := k)
    (by linarith) hk
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
    hderiv
    (by
      intro x hx hfx
      have hp := hpos (-x) (hmem x hx) hfx
      dsimp [dg]
      linarith)
    (by simpa [g] using hl)
  intro x hx
  have h := hh (-x) (by constructor <;> linarith [hx.1,hx.2])
  simpa [g,show -l- -x=x-l by ring] using h

def value (H A : SignedPoint) (Θ x : ℝ) : ℝ :=
  (A.a-1/2)*Real.cos x-(A.y+1/2)*Real.sin x+
    (H.y-1/2)*Real.cos (Θ-x)-(H.a+1/2)*Real.sin (Θ-x)

def rate (H A : SignedPoint) (Θ x : ℝ) : ℝ :=
  -(A.a-1/2)*Real.sin x-(A.y+1/2)*Real.cos x+
    (H.y-1/2)*Real.sin (Θ-x)+(H.a+1/2)*Real.cos (Θ-x)

theorem value_hasDerivAt (H A : SignedPoint) (Θ x : ℝ) :
    HasDerivAt (value H A Θ) (rate H A Θ x) x := by
  have hs := (Real.hasDerivAt_sin (Θ-x)).comp x
    ((hasDerivAt_const x Θ).sub (hasDerivAt_id x))
  have hc := (Real.hasDerivAt_cos (Θ-x)).comp x
    ((hasDerivAt_const x Θ).sub (hasDerivAt_id x))
  convert ((((Real.hasDerivAt_cos x).const_mul (A.a-1/2)).sub
    ((Real.hasDerivAt_sin x).const_mul (A.y+1/2))).add
    (hc.const_mul (H.y-1/2))).sub (hs.const_mul (H.a+1/2)) using 1
  · rfl
  · simp only [rate]
    ring

theorem circle_sum_bound {A : SignedPoint} (hAy : 0≤A.y)
    (hAa : 0<A.a) (hAc : A.circle≤qCap) : A.a+A.y<9/5 := by
  rw [SignedPoint.circle,abs_of_nonneg hAy] at hAc
  dsimp [qCap] at hAc
  nlinarith [sq_nonneg (A.a-A.y)]

/-- The exact cancellation behind the feasible derivative estimate. -/
theorem rate_identity (H A : SignedPoint) (Θ x : ℝ) :
    rate H A Θ x*(Real.cos (Θ-x)-Real.sin (Θ-x))=
      value H A Θ x*(Real.cos (Θ-x)+Real.sin (Θ-x))+1+(H.a-H.y)-
        (A.a+A.y)*Real.cos Θ-(A.a-A.y-1)*Real.sin Θ := by
  have hc : Real.cos Θ=Real.cos x*Real.cos (Θ-x)-Real.sin x*Real.sin (Θ-x) := by
    rw [←Real.cos_add]
    congr 1
    ring
  have hs : Real.sin Θ=Real.sin x*Real.cos (Θ-x)+Real.cos x*Real.sin (Θ-x) := by
    rw [←Real.sin_add]
    congr 1
    ring
  rw [hc,hs]
  unfold value rate
  linear_combination (H.a-H.y+1)*(Real.sin_sq_add_cos_sq (Θ-x))

theorem coefficient_bound {A : SignedPoint} {Θ : ℝ}
    (hAy : 0≤A.y) (hAa : 0<A.a) (hAc : A.circle≤qCap)
    (hAu : A.a<283/200) (hΘ : Θ∈Icc 0 (7/10 : ℝ)) :
    (A.a+A.y)*Real.cos Θ+(A.a-A.y-1)*Real.sin Θ<37/20 := by
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hΘ
  have hsum := circle_sum_bound hAy hAa hAc
  have hfirst := mul_le_mul_of_nonneg_right hsum.le (by linarith : 0≤Real.cos Θ)
  have hsecond := mul_le_mul_of_nonneg_right
    (show A.a-A.y-1≤83/200 by linarith) hs0
  have hnorm : (9/5*Real.cos Θ+83/200*Real.sin Θ)^2+
      (9/5*Real.sin Θ-83/200*Real.cos Θ)^2=(9/5 : ℝ)^2+(83/200 : ℝ)^2 := by
    linear_combination (((9/5 : ℝ)^2+(83/200 : ℝ)^2)*
      Real.sin_sq_add_cos_sq Θ)
  have hbound : 9/5*Real.cos Θ+83/200*Real.sin Θ<37/20 := by
    nlinarith [sq_nonneg (9/5*Real.sin Θ-83/200*Real.cos Θ)]
  linarith

/-- Where the composite is feasible, `1 ≤ value H A Θ x`, its rate exceeds `3/20`. -/
theorem rate_on_feasible {H A : SignedPoint} {Θ x : ℝ}
    (hHs : H.Sorted) (hHy : 0≤H.y) (hAy : 0≤A.y) (hAa : 0<A.a)
    (hAc : A.circle≤qCap) (hAu : A.a<283/200)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (hx : x∈Icc 0 Θ)
    (hf : 1≤value H A Θ x) : 3/20<rate H A Θ x := by
  have he : Θ-x∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [hx.2],by linarith [hx.1,hΘ.2]⟩
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig he
  have hden : 0<Real.cos (Θ-x)-Real.sin (Θ-x) := sub_pos.mpr hsc
  have hdenu : Real.cos (Θ-x)-Real.sin (Θ-x)≤1 := by linarith
  have hsum : 1≤Real.cos (Θ-x)+Real.sin (Θ-x) := by
    have hw := edgeWidth_ge_one (Θ-x)
    rw [edgeWidth_positive_formula he] at hw
    linarith
  have hmul := mul_le_mul_of_nonneg_right hf (by linarith :
    0≤Real.cos (Θ-x)+Real.sin (Θ-x))
  have hsort : 0≤H.a-H.y := by
    have hh := hHs.2
    rw [abs_of_nonneg hHy] at hh
    linarith
  have hcoef := coefficient_bound hAy hAa hAc hAu hΘ
  have hid := rate_identity H A Θ x
  have hproduct : 3/20<rate H A Θ x*
      (Real.cos (Θ-x)-Real.sin (Θ-x)) := by linarith
  have hrate : 0<rate H A Θ x := by nlinarith
  have hu := mul_le_mul_of_nonneg_left hdenu hrate.le
  linarith

theorem original_composite {H G A : SignedPoint} {Θ t : ℝ}
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hHG : zeroFeasible H G (t-Θ) 2)
    (hGA : quarterFeasible G A (-t) 0) : 1≤value H A Θ t := by
  have htwide : t∈Icc 0 (7/10 : ℝ) := ⟨ht.1,ht.2.trans hΘ.2⟩
  have he : Θ-t∈Icc 0 (7/10 : ℝ) :=
    ⟨by linarith [ht.2],by linarith [ht.1,hΘ.2]⟩
  have hh := hHG
  have hg := hGA
  rw [show t-Θ= -(Θ-t) by ring,zeroFeasible,edgeWidth_negative_formula he] at hh
  rw [quarterFeasible,edgeWidth_negative_formula htwide] at hg
  simp [zeroProjection,quarterProjection,Real.sin_neg,Real.cos_neg] at hh hg
  have h1 : Real.sin (t-Θ)= -Real.sin (Θ-t) := by rw [← Real.sin_neg,neg_sub]
  have h2 : Real.cos (t-Θ)=Real.cos (Θ-t) := by rw [← Real.cos_neg,neg_sub]
  rw [h1,h2] at hh
  unfold value
  linarith

/-- At the same H and A, the aligned hard contact improves by `(3/20)(Θ - t)`, an amount given by
the negative HG error. -/
theorem actual_aligned_reserve {q Θ t : ℝ} {H G A : SignedPoint}
    (hq : q≤qCap) (hHs : H.Sorted) (hAs : A.Sorted)
    (hAcore : A.AvoidsCore) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : 0≤A.y)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hHG : zeroFeasible H G (t-Θ) 2)
    (hGA : quarterFeasible G A (-t) 0) :
    (3/20)*(Θ-t)≤
      quarterProjection (SignedPoint.flat (H.y-1)) A (-Θ) 0-edgeWidth (-Θ) := by
  have hAu := (A.coordinate_bounds hAs hAcore hAc hq).2.1
  have hf := original_composite hΘ ht hHG hGA
  have hr := feasible_right_reserve (f := value H A Θ) (df := rate H A Θ)
    ht.2 (by norm_num : (0:ℝ)<3/20)
    (fun x _ => value_hasDerivAt H A Θ x)
    (by
      intro x hx hfx
      exact (rate_on_feasible hHs hHy hAy hAs.1 (hAc.trans hq) hAu hΘ
        ⟨ht.1.trans hx.1,hx.2⟩ hfx).le)
    hf Θ ⟨ht.2,le_rfl⟩
  have hend : 1+(3/20)*(Θ-t)≤value H A Θ Θ := by linarith [hr.2]
  rw [edgeWidth_negative_formula hΘ]
  simp [quarterProjection,SignedPoint.flat,Real.sin_neg,Real.cos_neg,value] at hend ⊢
  linarith

def alignedG (H : SignedPoint) : SignedPoint := SignedPoint.flat (H.y-1)

def reducedA (A : SignedPoint) (Θ t : ℝ) : SignedPoint :=
  ⟨A.a-(3/40)*(Θ-t),A.y⟩

/-- The output of the G alignment: G on the flat core at the frame of H, and A with a smaller
primary coordinate, whose circle is compared with that of the input A. The circle of the free G
matters only for containment and the core. -/
structure GAlignment (q : ℝ) (H A : SignedPoint) (Θ t : ℝ) where
  pointG : SignedPoint
  pointA : SignedPoint
  G_eq : pointG=alignedG H
  A_eq : pointA=reducedA A Θ t
  G_sorted : pointG.Sorted
  G_core : pointG.Core
  G_contained : pointG.Contained q
  G_normal : pointG.y< -(1/10 : ℝ)
  A_sorted : pointA.Sorted
  A_avoids : pointA.AvoidsCore
  A_primary : 1<pointA.a
  A_tangent : pointA.y=A.y
  A_tangent_upper : pointA.y<133/200
  A_circle : pointA.circle≤A.circle
  A_strict : t<Θ → pointA.circle<A.circle
  HG_zero : zeroFeasible H pointG 0 0
  HG_two : zeroFeasible H pointG 0 2
  GA_hard : quarterFeasible pointG pointA (-Θ) 0
  GA_reserve : (3/40)*(Θ-t)≤quarterProjection pointG pointA (-Θ) 0-edgeWidth (-Θ)

private theorem r8_quarterProjection_zero (p r : SignedPoint) (d : ℝ) :
    quarterProjection p r d 0=p.y+r.a*Real.cos d+r.y*Real.sin d := rfl

/-- Half of an aligned contact reserve is spent on a decrease of the primary coordinate of A; the
construction works for any such reserve. -/
theorem alignment_of_reserve {q Θ t : ℝ} {H A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : 0≤A.y)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (he : 0≤Θ-t ∧ Θ-t≤7/10)
    (hres : (3/20)*(Θ-t)≤
      quarterProjection (SignedPoint.flat (H.y-1)) A (-Θ) 0-edgeWidth (-Θ)) :
    Nonempty (GAlignment q H A Θ t) := by
  have hHu := (H.coordinate_bounds hHs hHcore hHc hq).2.2
  have hAu := (A.coordinate_bounds hAs hAcore hAc hq).2.1
  have hAyu := (A.coordinate_bounds hAs hAcore hAc hq).2.2
  rw [abs_of_nonneg hHy] at hHu
  rw [abs_of_nonneg hAy] at hAyu
  obtain ⟨hc,hc1,hs0,hs,hsc⟩ := transport_trig hΘ
  have hreserve0 : 0≤(3/20 : ℝ)*(Θ-t) := mul_nonneg (by norm_num) he.1
  have hqp : quarterProjection (SignedPoint.flat (H.y-1)) A (-Θ) 0=
      H.y-1+A.a*Real.cos Θ-A.y*Real.sin Θ := by
    rw [r8_quarterProjection_zero,Real.cos_neg,Real.sin_neg]
    simp only [SignedPoint.flat]
    ring
  have hproject : edgeWidth (-Θ)≤H.y-1+A.a*Real.cos Θ-A.y*Real.sin Θ := by
    rw [← hqp]
    linarith
  have hsin := mul_nonneg hAy hs0
  have hcos := mul_le_mul_of_nonneg_left hc1 hAs.1.le
  have hw := edgeWidth_ge_one (-Θ)
  have hAgt : 11/10<A.a := by linarith
  have hAyu' : A.y<133/200 := by
    have hh := hAc.trans hq
    rw [SignedPoint.circle,abs_of_nonneg hAy] at hh
    dsimp [qCap] at hh
    have h1 : (8/5:ℝ)^2<(A.a+1/2)^2 := by nlinarith only [hAgt]
    by_contra! hbad
    have h2 : (233/200:ℝ)^2≤(A.y+1/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    linarith
  have hHlow : 117/200<H.y := by linarith
  have hflat : |H.y-1|≤1/2 := by
    rw [abs_of_neg (by linarith : H.y-1<0)]
    linarith
  let ε : ℝ := (3/40)*(Θ-t)
  have hε : 0≤ε := mul_nonneg (by norm_num) he.1
  have hεu : ε≤1/10 := by dsimp [ε]; linarith [he.2]
  have hAa : 1<(reducedA A Θ t).a := by
    dsimp [reducedA]
    dsimp [ε] at hεu
    linarith
  have hAsorted : (reducedA A Θ t).Sorted := by
    refine ⟨by linarith,?_⟩
    change |A.y|≤(reducedA A Θ t).a
    rw [abs_of_nonneg hAy]
    linarith
  have hAavoid : (reducedA A Θ t).AvoidsCore := by
    unfold SignedPoint.AvoidsCore SignedPoint.coreDistance
    rw [max_eq_left (by linarith : 0≤(reducedA A Θ t).a-1/2)]
    have h1 : (1/12:ℝ)^2≤((reducedA A Θ t).a-1/2)^2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    linarith [sq_nonneg (max (|(reducedA A Θ t).y|-1/2) 0)]
  have hid : A.circle-(reducedA A Θ t).circle=ε*(2*A.a+1-ε) := by
    dsimp [SignedPoint.circle,reducedA,ε]
    ring
  have hfactor : 0<2*A.a+1-ε := by linarith
  have hcircle : (reducedA A Θ t).circle≤A.circle := by
    have hp := mul_nonneg hε hfactor.le
    linarith
  have hstrict : t<Θ → (reducedA A Θ t).circle<A.circle := by
    intro htlt
    have hp := mul_pos (show 0<ε by dsimp [ε]; positivity) hfactor
    linarith
  have hcosloss := mul_le_mul_of_nonneg_left hc1 hε
  have hreserve : (3/40)*(Θ-t)≤
      quarterProjection (alignedG H) (reducedA A Θ t) (-Θ) 0-edgeWidth (-Θ) := by
    have hqp' : quarterProjection (alignedG H) (reducedA A Θ t) (-Θ) 0=
        H.y-1+(A.a-(3/40)*(Θ-t))*Real.cos Θ-A.y*Real.sin Θ := by
      rw [r8_quarterProjection_zero,Real.cos_neg,Real.sin_neg]
      simp only [alignedG,SignedPoint.flat,reducedA]
      ring
    rw [hqp']
    rw [hqp] at hres
    dsimp [ε] at hcosloss
    linarith
  refine ⟨{
    pointG := alignedG H
    pointA := reducedA A Θ t
    G_eq := rfl
    A_eq := rfl
    G_sorted := SignedPoint.flat_sorted hflat
    G_core := SignedPoint.flat_on_core hflat
    G_contained := SignedPoint.flat_contained hqL hflat
    G_normal := by dsimp [alignedG,SignedPoint.flat]; linarith
    A_sorted := hAsorted
    A_avoids := hAavoid
    A_primary := hAa
    A_tangent := rfl
    A_tangent_upper := hAyu'
    A_circle := hcircle
    A_strict := hstrict
    HG_zero := by simp [zeroFeasible,zeroProjection,alignedG,SignedPoint.flat]
    HG_two := by simp [zeroFeasible,zeroProjection,alignedG,SignedPoint.flat]
    GA_hard := by unfold quarterFeasible; linarith
    GA_reserve := hreserve }⟩

theorem actual_G_alignment {q Θ t : ℝ} {H G A : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hHs : H.Sorted) (hAs : A.Sorted)
    (hHcore : H.AvoidsCore) (hAcore : A.AvoidsCore)
    (hHc : H.Contained q) (hAc : A.Contained q)
    (hHy : 0≤H.y) (hAy : 0≤A.y)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hHG : zeroFeasible H G (t-Θ) 2)
    (hGA : quarterFeasible G A (-t) 0) :
    Nonempty (GAlignment q H A Θ t) := by
  exact alignment_of_reserve hqL hq hHs hAs hHcore hAcore hHc hAc hHy hAy hΘ
    ⟨by linarith [ht.2],by linarith [ht.1,hΘ.2]⟩
    (actual_aligned_reserve hq hHs hAs hAcore hAc hHy hAy hΘ ht hHG hGA)

/-- The reflected construction on the side of T, compared with the circle of the input B; it does
not reflect E or move any outer anchor. -/
structure TAlignment (q : ℝ) (B D : SignedPoint) (Θ t : ℝ) where
  pointT : SignedPoint
  pointB : SignedPoint
  T_eq : pointT=(alignedG D.reflect).reflect
  B_eq : pointB=(reducedA B.reflect Θ t).reflect
  T_sorted : pointT.Sorted
  T_core : pointT.Core
  T_contained : pointT.Contained q
  T_normal : (1/10 : ℝ)<pointT.y
  B_sorted : pointB.Sorted
  B_avoids : pointB.AvoidsCore
  B_primary : 1<pointB.a
  B_tangent : pointB.y=B.y
  B_tangent_lower : -(133/200 : ℝ)<pointB.y
  B_circle : pointB.circle≤B.circle
  B_strict : t<Θ → pointB.circle<B.circle
  TD_zero : zeroFeasible pointT D 0 0
  TD_two : zeroFeasible pointT D 0 2
  BT_hard : quarterFeasible pointB pointT (-Θ) 2
  BT_reserve : (3/40)*(Θ-t)≤quarterProjection pointB pointT (-Θ) 2-edgeWidth (-Θ)

theorem actual_T_alignment {q Θ t : ℝ} {B T D : SignedPoint}
    (hqL : qLow≤q) (hq : q≤qCap)
    (hBs : B.Sorted) (hDs : D.Sorted)
    (hBcore : B.AvoidsCore) (hDcore : D.AvoidsCore)
    (hBc : B.Contained q) (hDc : D.Contained q)
    (hBy : B.y≤0) (hDy : D.y≤0)
    (hΘ : Θ∈Icc 0 (7/10 : ℝ)) (ht : t∈Icc 0 Θ)
    (hBT : quarterFeasible B T (-t) 2)
    (hTD : zeroFeasible T D (t-Θ) 0) :
    Nonempty (TAlignment q B D Θ t) := by
  have hHG : zeroFeasible D.reflect T.reflect (t-Θ) 2 := by
    simpa [reflectedOwner] using (zeroFeasible_reflect T D (t-Θ) 0).2 hTD
  have hGA : quarterFeasible T.reflect B.reflect (-t) 0 := by
    simpa [reflectedOwner] using (quarterFeasible_reflect B T (-t) 2).2 hBT
  obtain ⟨O⟩ := actual_G_alignment hqL hq
    (by simpa using hDs) (by simpa using hBs)
    (by simpa using hDcore) (by simpa using hBcore)
    (by simpa using hDc) (by simpa using hBc)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hDy)
    (by simpa [SignedPoint.reflect] using neg_nonneg.mpr hBy)
    hΘ ht hHG hGA
  refine ⟨{
    pointT := O.pointG.reflect
    pointB := O.pointA.reflect
    T_eq := by rw [O.G_eq]
    B_eq := by rw [O.A_eq]
    T_sorted := by simpa using O.G_sorted
    T_core := by simpa using O.G_core
    T_contained := by simpa using O.G_contained
    T_normal := by dsimp [SignedPoint.reflect]; linarith [O.G_normal]
    B_sorted := by simpa using O.A_sorted
    B_avoids := by simpa using O.A_avoids
    B_primary := O.A_primary
    B_tangent := by
      have hy := O.A_tangent
      change O.pointA.y= -B.y at hy
      change -O.pointA.y=B.y
      linarith
    B_tangent_lower := by dsimp [SignedPoint.reflect]; linarith [O.A_tangent_upper]
    B_circle := by simpa using O.A_circle
    B_strict := fun h => by simpa using O.A_strict h
    TD_zero := ?_
    TD_two := ?_
    BT_hard := ?_
    BT_reserve := ?_ }⟩
  · simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG 0 2).2 O.HG_two
  · simpa [reflectedOwner] using
      (zeroFeasible_reflect D.reflect O.pointG 0 0).2 O.HG_zero
  · simpa [reflectedOwner] using
      (quarterFeasible_reflect O.pointG O.pointA (-Θ) 0).2 O.GA_hard
  · have hid := quarterProjection_reflect O.pointG O.pointA (-Θ) 0
    have hh := O.GA_reserve
    rw [←hid] at hh
    simpa [reflectedOwner] using hh

end HardCancelingOuter
end SquaresInCircles.Eight
