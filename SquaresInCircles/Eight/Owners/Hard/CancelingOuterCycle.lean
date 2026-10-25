module

public import SquaresInCircles.Eight.Owners.CircleGeometry
public import SquaresInCircles.Eight.Owners.Contact.MinimumDerivatives
public import SquaresInCircles.Eight.Owners.NecessaryCycle
public import SquaresInCircles.Eight.Owners.TrigonometricReserves

/-!
# Eight squares: the two canceling outer alignments on a hard cycle

The alignment of G (`alignGACycle`, `HardInput.fromCancelingHG`) and that of T (`alignBTCycle`,
`HardInput.fromCancelingTD`) use the HG2 or TD0 axis and keep the selected AB0 or AB2 axis at the
common middle frame, with every other selected witness. Only the free intermediate and its
adjacent middle anchor change, and a strict loss is recorded on the original circle of that
anchor (`HardInput.align_nonpositive_HG2`, `HardInput.align_nonpositive_TD0`).
-/

section
/-!
## A negative canceling outer error has an aligned descendant

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
end
end
end

section
@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight
open Candidate HardCancelingOuter
namespace SignedCycle

def alignGACycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,P,Q,C.point B,C.point T,C.point D,C.point E]
  theta := ![C.theta H,C.theta H,C.theta A,C.theta B,C.theta T,C.theta D,C.theta E]

theorem alignGACycle_unchanged (C : SignedCycle) (P Q : SignedPoint)
    (i : Vertex) (hiG : i≠G) (hiA : i≠A) :
    (alignGACycle C P Q).point i=C.point i ∧
      (alignGACycle C P Q).theta i=C.theta i := by
  fin_cases i <;> simp [alignGACycle,H,G,A,B,T,D,E] at hiG hiA ⊢

theorem alignGACycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (alignGACycle C P Q).theta i=if i=G then C.theta H else C.theta i := by
  fin_cases i <;> simp [alignGACycle,H,G,A,B,T,D,E]

theorem alignGACycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (alignGACycle C P Q).Spread := by
  intro i j
  rw [alignGACycle_theta,alignGACycle_theta]
  by_cases hi : i=G <;> by_cases hj : j=G
  · simpa [hi,hj] using h H H
  · simpa [hi,hj] using h H j
  · simpa [hi,hj] using h i H
  · simpa [hi,hj] using h i j

def Witnesses.alignGA {q t : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : GAlignment q (C.point H) (C.point A)
      (C.theta H-C.theta A) t) :
    (alignGACycle C O.pointG O.pointA).Witnesses where
  owner i := if i=G then 0 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · have hj : w.owner H=0 ∨ w.owner H=2 := by
        simpa [normalOwners,H] using w.allowed H
      simp only [H] at hj
      rcases hj with hj | hj
      · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
          hj,zeroFeasible,sub_nonneg] using O.HG_zero
      · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
          hj,zeroFeasible,sub_nonneg] using O.HG_two
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
        quarterFeasible,sub_nonneg,neg_sub] using O.GA_hard
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      simp only [A,B] at hj hAB
      rcases hj with hj | hj <;>
        simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,A,B,
          hAB,hj,zeroProjection,O.A_tangent] using w.feasible A
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,B,T] using w.feasible B
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,T,D] using w.feasible T
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,D,E] using w.feasible D
    · simpa [alignGACycle,Feasible,slack,edge,word,delta,next,G,E,H] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=G
    · subst i; norm_num [normalOwners,G]
    · simpa [hi] using w.allowed i

def HardInput.fromCancelingHG {q t : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A) t) :
    HardInput q where
  cycle := alignGACycle I.cycle O.pointG O.pointA
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact O.G_sorted
      · exact O.A_sorted
      · exact I.necessary.sorted B
      · exact I.necessary.sorted T
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact O.G_contained
      · exact O.A_circle.trans (I.necessary.contained A)
      · exact I.necessary.contained B
      · exact I.necessary.contained T
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact O.G_core.ge
      · exact O.A_avoids
      · exact I.necessary.core B
      · exact I.necessary.core T
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := alignGACycle_spread I.necessary.spread O.pointG O.pointA }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := by simpa [alignGACycle,A,O.A_tangent] using I.anchors_normal.A_nonneg
    B_nonpos := I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.alignGA hAB O
  GA_hard := by
    simpa [alignGACycle,Feasible,slack,edge,word,delta,next,H,G,A,
      quarterFeasible,sub_nonneg,neg_sub] using O.GA_hard
  BT_hard := by
    simpa [alignGACycle,Feasible,slack,edge,word,delta,next,B,T] using I.BT_hard
  zero_signs := {
    HG_canceling := by
      intro _
      change O.pointG.y<0
      linarith [O.G_normal]
    TD_canceling := by
      intro hh
      have hj : I.witnesses.owner T=0 := by simpa [Witnesses.alignGA,T,G] using hh
      exact I.zero_signs.TD_canceling hj }
  E_radial := I.E_radial

theorem HardInput.canceling_HG_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hHG : I.cycle.Feasible H 2) :
    Nonempty (GAlignment q (I.cycle.point H) (I.cycle.point A)
      (I.cycle.theta H-I.cycle.theta A) (I.cycle.theta G-I.cycle.theta A)) := by
  have hΘ : I.cycle.theta H-I.cycle.theta A∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread H A
    refine ⟨by linarith,?_⟩
    dsimp [frameCap] at hh
    linarith [le_abs_self (I.cycle.theta H-I.cycle.theta A)]
  have ht : I.cycle.theta G-I.cycle.theta A∈
      Icc 0 (I.cycle.theta H-I.cycle.theta A) := by constructor <;> linarith
  have hHG' : zeroFeasible (I.cycle.point H) (I.cycle.point G)
      ((I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)) 2 := by
    rw [show (I.cycle.theta G-I.cycle.theta A)-(I.cycle.theta H-I.cycle.theta A)=
      I.cycle.theta G-I.cycle.theta H by ring]
    simpa [Feasible,slack,edge,word,delta,next,H,G,zeroFeasible,sub_nonneg] using hHG
  have hGA' : quarterFeasible (I.cycle.point G) (I.cycle.point A)
      (-(I.cycle.theta G-I.cycle.theta A)) 0 := by
    simpa [Feasible,slack,edge,word,delta,next,G,A,quarterFeasible,sub_nonneg,neg_sub]
      using I.GA_hard
  exact actual_G_alignment hqL hq (I.necessary.sorted H) (I.necessary.sorted A)
    (I.necessary.core H) (I.necessary.core A) (I.necessary.contained H)
    (I.necessary.contained A) I.anchors_normal.H_nonneg I.anchors_normal.A_nonneg
    hΘ ht hHG' hGA'

/-- A nonpositive canceling HG error is removed within the hard inputs; the construction spends
half its contact reserve on the original circle of A. -/
theorem HardInput.align_nonpositive_HG2 {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hAG : I.cycle.theta A≤I.cycle.theta G)
    (hGH : I.cycle.theta G≤I.cycle.theta H)
    (hHG : I.cycle.Feasible H 2) :
    ∃ J : HardInput q,
      J.cycle.theta G=J.cycle.theta H ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point A).y=(I.cycle.point A).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta G<I.cycle.theta H → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠G → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠G → i≠A → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.canceling_HG_output hqL hq hAG hGH hHG
  refine ⟨I.fromCancelingHG hAB O,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · exact hAB
  · exact O.A_tangent
  · intro i hi
    by_cases hiA : i=A
    · subst i; exact O.A_circle
    by_cases hiG : i=G
    · subst i; simp [anchorVertices,H,G,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1).le
  · intro hstrict
    refine ⟨A,by simp [anchorVertices],?_⟩
    exact O.A_strict (by linarith)
  · intro i hi
    change (alignGACycle I.cycle O.pointG O.pointA).theta i=I.cycle.theta i
    simp [alignGACycle_theta,hi]
  · intro i hiG hiA
    exact (alignGACycle_unchanged I.cycle O.pointG O.pointA i hiG hiA).1

def alignBTCycle (C : SignedCycle) (P Q : SignedPoint) : SignedCycle where
  point := ![C.point H,C.point G,C.point A,Q,P,C.point D,C.point E]
  theta := ![C.theta H,C.theta G,C.theta A,C.theta B,C.theta D,C.theta D,C.theta E]

theorem alignBTCycle_unchanged (C : SignedCycle) (P Q : SignedPoint)
    (i : Vertex) (hiT : i≠T) (hiB : i≠B) :
    (alignBTCycle C P Q).point i=C.point i ∧
      (alignBTCycle C P Q).theta i=C.theta i := by
  fin_cases i <;> simp [alignBTCycle,H,G,A,B,T,D,E] at hiT hiB ⊢

theorem alignBTCycle_theta (C : SignedCycle) (P Q : SignedPoint) (i : Vertex) :
    (alignBTCycle C P Q).theta i=if i=T then C.theta D else C.theta i := by
  fin_cases i <;> simp [alignBTCycle,H,G,A,B,T,D,E]

theorem alignBTCycle_spread {C : SignedCycle} (h : C.Spread) (P Q : SignedPoint) :
    (alignBTCycle C P Q).Spread := by
  intro i j
  rw [alignBTCycle_theta,alignBTCycle_theta]
  by_cases hi : i=T <;> by_cases hj : j=T
  · simpa [hi,hj] using h D D
  · simpa [hi,hj] using h D j
  · simpa [hi,hj] using h i D
  · simpa [hi,hj] using h i j

def Witnesses.alignBT {q t : ℝ} {C : SignedCycle} (w : C.Witnesses)
    (hAB : C.theta A=C.theta B)
    (O : TAlignment q (C.point B) (C.point D)
      (C.theta B-C.theta D) t) :
    (alignBTCycle C O.pointT O.pointB).Witnesses where
  owner i := if i=B then 2 else w.owner i
  feasible := by
    intro i
    fin_cases i
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,H,G] using w.feasible H
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,G,A] using w.feasible G
    · have hj : w.owner A=0 ∨ w.owner A=2 := by
        simpa [normalOwners,A] using w.allowed A
      simp only [A,B] at hj hAB
      rcases hj with hj | hj <;>
        simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,A,B,
          hAB,hj,zeroProjection,O.B_tangent] using w.feasible A
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
        quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
    · have hj : w.owner T=0 ∨ w.owner T=2 := by
        simpa [normalOwners,T] using w.allowed T
      simp only [T] at hj
      rcases hj with hj | hj
      · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
          hj,zeroFeasible,sub_nonneg] using O.TD_zero
      · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
          hj,zeroFeasible,sub_nonneg] using O.TD_two
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,D,E] using w.feasible D
    · simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,E,H] using w.feasible E
  allowed := by
    intro i
    by_cases hi : i=B
    · subst i; norm_num [normalOwners,B]
    · simpa [hi] using w.allowed i

def HardInput.fromCancelingTD {q t : ℝ} (I : HardInput q)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (O : TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D) t) :
    HardInput q where
  cycle := alignBTCycle I.cycle O.pointT O.pointB
  necessary := {
    sorted := by
      intro i
      fin_cases i
      · exact I.necessary.sorted H
      · exact I.necessary.sorted G
      · exact I.necessary.sorted A
      · exact O.B_sorted
      · exact O.T_sorted
      · exact I.necessary.sorted D
      · exact I.necessary.sorted E
    contained := by
      intro i
      fin_cases i
      · exact I.necessary.contained H
      · exact I.necessary.contained G
      · exact I.necessary.contained A
      · exact O.B_circle.trans (I.necessary.contained B)
      · exact O.T_contained
      · exact I.necessary.contained D
      · exact I.necessary.contained E
    core := by
      intro i
      fin_cases i
      · exact I.necessary.core H
      · exact I.necessary.core G
      · exact I.necessary.core A
      · exact O.B_avoids
      · exact O.T_core.ge
      · exact I.necessary.core D
      · exact I.necessary.core E
    spread := alignBTCycle_spread I.necessary.spread O.pointT O.pointB }
  anchors_normal := {
    H_nonneg := I.anchors_normal.H_nonneg
    A_nonneg := I.anchors_normal.A_nonneg
    B_nonpos := by simpa [alignBTCycle,B,O.B_tangent] using I.anchors_normal.B_nonpos
    D_nonpos := I.anchors_normal.D_nonpos }
  E_nonpos := I.E_nonpos
  witnesses := I.witnesses.alignBT hAB O
  GA_hard := by
    simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,G,A] using I.GA_hard
  BT_hard := by
    simpa [alignBTCycle,Feasible,slack,edge,word,delta,next,B,T,D,
      quarterFeasible,sub_nonneg,neg_sub] using O.BT_hard
  zero_signs := {
    HG_canceling := by
      intro hh
      have hj : I.witnesses.owner H=2 := by simpa [Witnesses.alignBT,H,B] using hh
      exact I.zero_signs.HG_canceling hj
    TD_canceling := by
      intro _
      change 0<O.pointT.y
      linarith [O.T_normal] }
  E_radial := I.E_radial

theorem HardInput.canceling_TD_output {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 0) :
    Nonempty (TAlignment q (I.cycle.point B) (I.cycle.point D)
      (I.cycle.theta B-I.cycle.theta D) (I.cycle.theta B-I.cycle.theta T)) := by
  have hΘ : I.cycle.theta B-I.cycle.theta D∈Icc 0 (7/10 : ℝ) := by
    have hh := I.necessary.spread B D
    refine ⟨by linarith,?_⟩
    dsimp [frameCap] at hh
    linarith [le_abs_self (I.cycle.theta B-I.cycle.theta D)]
  have ht : I.cycle.theta B-I.cycle.theta T∈
      Icc 0 (I.cycle.theta B-I.cycle.theta D) := by constructor <;> linarith
  have hTD' : zeroFeasible (I.cycle.point T) (I.cycle.point D)
      ((I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)) 0 := by
    rw [show (I.cycle.theta B-I.cycle.theta T)-(I.cycle.theta B-I.cycle.theta D)=
      I.cycle.theta D-I.cycle.theta T by ring]
    simpa [Feasible,slack,edge,word,delta,next,T,D,zeroFeasible,sub_nonneg] using hTD
  have hBT' : quarterFeasible (I.cycle.point B) (I.cycle.point T)
      (-(I.cycle.theta B-I.cycle.theta T)) 2 := by
    simpa [Feasible,slack,edge,word,delta,next,B,T,quarterFeasible,sub_nonneg,neg_sub]
      using I.BT_hard
  exact actual_T_alignment hqL hq (I.necessary.sorted B) (I.necessary.sorted D)
    (I.necessary.core B) (I.necessary.core D) (I.necessary.contained B)
    (I.necessary.contained D) I.anchors_normal.B_nonpos I.anchors_normal.D_nonpos
    hΘ ht hBT' hTD'

/-- The mirror statement for TD0: a nonpositive canceling TD error is removed, leaving H, G, A, D
and E unchanged. -/
theorem HardInput.align_nonpositive_TD0 {q : ℝ} (I : HardInput q)
    (hqL : qLow≤q) (hq : q≤qCap)
    (hAB : I.cycle.theta A=I.cycle.theta B)
    (hDT : I.cycle.theta D≤I.cycle.theta T)
    (hTB : I.cycle.theta T≤I.cycle.theta B)
    (hTD : I.cycle.Feasible T 0) :
    ∃ J : HardInput q,
      J.cycle.theta T=J.cycle.theta D ∧
      J.cycle.theta A=J.cycle.theta B ∧
      (J.cycle.point B).y=(I.cycle.point B).y ∧
      AnchorNonincrease I.cycle J.cycle ∧
      (I.cycle.theta D<I.cycle.theta T → StrictAnchorLoss I.cycle J.cycle) ∧
      (∀ i,i≠T → J.cycle.theta i=I.cycle.theta i) ∧
      (∀ i,i≠T → i≠B → J.cycle.point i=I.cycle.point i) := by
  obtain ⟨O⟩ := I.canceling_TD_output hqL hq hDT hTB hTD
  refine ⟨I.fromCancelingTD hAB O,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · exact hAB
  · exact O.B_tangent
  · intro i hi
    by_cases hiB : i=B
    · subst i; exact O.B_circle
    by_cases hiT : i=T
    · subst i; simp [anchorVertices,H,T,A,B,D,E] at hi
    · exact (congrArg SignedPoint.circle
        (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1).le
  · intro hstrict
    refine ⟨B,by simp [anchorVertices],?_⟩
    exact O.B_strict (by linarith)
  · intro i hi
    change (alignBTCycle I.cycle O.pointT O.pointB).theta i=I.cycle.theta i
    simp [alignBTCycle_theta,hi]
  · intro i hiT hiB
    exact (alignBTCycle_unchanged I.cycle O.pointT O.pointB i hiT hiB).1

end SignedCycle
end SquaresInCircles.Eight
end
end
end
