module

public import SquaresInCircles.Eight.TableFree.CriticalERadicals

/-!
# Positive substitution into the actual cleared position equation

Uncompiled source. Bounds are attached to the actual trigonometric
and radical expressions. Their products have the displayed polynomial
endpoints, so the full-interval signs apply to the real position
gradient after clearing only its proved positive denominator.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.CriticalESubstitution
open Polynomial CriticalEPolynomials CriticalERadicals WholeIntervalPolynomial
open ExactFamily.FiveCornerGeometry HighOrderTaylor

theorem trig_evaluations (t : ℝ) :
    ev t sineLo=S15 t ∧ ev t sineHi=S13 t ∧
    ev t cosineLo=C14 t ∧ ev t cosineHi=C16 t := by
  have hp : aeval (t-1/10) parameter=t := by
    simp only [parameter,map_add,aeval_C,aeval_X,eq_ratCast]
    push_cast
    ring
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp only [ev,sineLo,sineHi,cosineLo,cosineHi,aeval_comp,hp,map_add,map_sub,map_mul,
      map_pow,aeval_C,aeval_X,eq_ratCast,PositiveScalarPolynomials.sine_eval,
      PositiveScalarPolynomials.cosine_eval]
  · simp only [S15]
    push_cast
    ring
  · simp only [C16]
    push_cast
    ring

theorem trig_bounds {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    Real.sin t∈Icc (ev t sineLo) (ev t sineHi) ∧
    Real.cos t∈Icc (ev t cosineLo) (ev t cosineHi) ∧
    0≤ev t sineLo ∧ 0<ev t cosineLo := by
  have ht0 : 0≤t := by linarith [ht.1]
  have ht' : t∈Icc 0 frameCap := ⟨ht0,by dsimp [frameCap]; linarith [ht.2]⟩
  obtain ⟨hs,hs',hc,hc'⟩ := trig_evaluations t
  rw [hs,hs',hc,hc']
  exact ⟨⟨S15_le_sin ht0,sin_le_S13 ht0⟩,⟨C14_le_cos ht0,cos_le_C16 ht0⟩,
    S15_nonneg ht',C14_pos ht'⟩

theorem auxiliary_bounds (s : Chain) {t : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25)) :
    1<ev t (rLo s) ∧ 1<ev t (wLo s) ∧
    1<ev t (firstLo s) ∧ 1<ev t (secondLo s) := by
  have hz : t-1/10∈Icc ((0:ℚ):ℝ) (length:ℝ) := by
    rw [Rat.cast_zero]
    exact local_parameter ht
  have h0 := positive_on_interval (by norm_num [length]) (coordinate_identities s 0).1
    (auxiliary_reserves s).1 hz
  have h1 := positive_on_interval (by norm_num [length]) (coordinate_identities s 5).1
    (auxiliary_reserves s).2.1 hz
  have h2 := positive_on_interval (by norm_num [length]) (auxiliary_identities s).1
    (auxiliary_reserves s).2.2.1 hz
  have h3 := positive_on_interval (by norm_num [length]) (auxiliary_identities s).2
    (auxiliary_reserves s).2.2.2 hz
  rw [Rat.cast_one] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

theorem component_bounds {s : Chain} {q t u : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hu : u∈Icc (ev t (a s)) (ev t (b s)))
    (h : RadicalBounds s q t u) :
    firstComponent q (Real.cos t) (Real.sin t) u∈Icc (ev t (firstLo s)) (ev t (firstHi s)) ∧
    secondComponent q (Real.cos t) (Real.sin t) u∈Icc (ev t (secondLo s)) (ev t (secondHi s)) := by
  obtain ⟨hs,hc,hs0,hc0⟩ := trig_bounds ht
  obtain ⟨hr,hw,_,_⟩ := auxiliary_bounds s ht
  have hv4 : 1/2<ev t (vLo s) := (polynomial_coordinates s 4 ht).1
  have hcr := StationaryPrimitives.product_bounds hc
    (show lowerRight q u-1∈Icc (ev t (rLo s)-1) (ev t (rHi s)-1) by
      constructor <;> linarith [h.r.1,h.r.2]) hc0.le (by linarith)
  have hsu := StationaryPrimitives.product_bounds hs hu hs0
    (by have h' := (endpoints ht s).1; linarith)
  have hcv := StationaryPrimitives.product_bounds hc h.v hc0.le (by linarith)
  have hsw := StationaryPrimitives.product_bounds hs
    (show lowerLeft q u-1∈Icc (ev t (wLo s)-1) (ev t (wHi s)-1) by
      constructor <;> linarith [h.w.1,h.w.2]) hs0 (by linarith)
  have e1 : ev t (1:ℚ[X])=1 := by simp [ev]
  have e2 : ev t (2:ℚ[X])=2 := by rw [ev]; exact map_ofNat _ 2
  simp only [firstComponent,secondComponent,firstLo,firstHi,secondLo,secondHi,
    ev_sub,ev_add,ev_mul,e1,e2]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> linarith [hcr.1,hcr.2,hsu.1,hsu.2,hcv.1,hcv.2,hsw.1,hsw.2]

/-- Elementary positive interval multiplication, without a state grid. -/
structure PositiveInterval (x : ℝ) where
  lo : ℝ
  hi : ℝ
  mem : x∈Icc lo hi
  lo_nonneg : 0≤lo

namespace PositiveInterval

def of_bounds {x a b : ℝ} (h : x∈Icc a b) (ha : 0≤a) : PositiveInterval x := ⟨a,b,h,ha⟩
def add {x y : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y) : PositiveInterval (x+y) :=
  ⟨X.lo+Y.lo,X.hi+Y.hi,⟨add_le_add X.mem.1 Y.mem.1,add_le_add X.mem.2 Y.mem.2⟩,
    add_nonneg X.lo_nonneg Y.lo_nonneg⟩
def mul {x y : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y) : PositiveInterval (x*y) :=
  ⟨X.lo*Y.lo,X.hi*Y.hi,StationaryPrimitives.product_bounds X.mem Y.mem X.lo_nonneg Y.lo_nonneg,
    mul_nonneg X.lo_nonneg Y.lo_nonneg⟩

theorem lower_ratio {x y r : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y)
    (hy : 0<Y.lo) (hr : 0≤r) (h : r*Y.hi<X.lo) : r<x/y := by
  have hyp : 0<y := hy.trans_le Y.mem.1
  apply (lt_div_iff₀ hyp).2
  have hm := mul_le_mul_of_nonneg_left Y.mem.2 hr
  linarith [X.mem.1]

theorem upper_ratio {x y r : ℝ} (X : PositiveInterval x) (Y : PositiveInterval y)
    (hy : 0<Y.lo) (hr : 0≤r) (h : X.hi<r*Y.lo) : x/y<r := by
  have hyp : 0<y := hy.trans_le Y.mem.1
  apply (div_lt_iff₀ hyp).2
  have hm := mul_le_mul_of_nonneg_left Y.mem.1 hr
  linarith [X.mem.2]

end PositiveInterval

structure Boxes (s : Chain) (q t u : ℝ) where
  height : PositiveInterval u
  height_lo : height.lo=ev t (a s)
  height_hi : height.hi=ev t (b s)
  other : PositiveInterval (2-u)
  other_lo : other.lo=2-ev t (b s)
  other_hi : other.hi=2-ev t (a s)
  r : PositiveInterval (lowerRight q u)
  r_lo : r.lo=ev t (rLo s)
  r_hi : r.hi=ev t (rHi s)
  U : PositiveInterval (topRight q u)
  U_lo : U.lo=ev t (ULo s)
  U_hi : U.hi=ev t (UHi s)
  V : PositiveInterval (topLeft q u)
  V_lo : V.lo=ev t (VLo s)
  V_hi : V.hi=ev t (VHi s)
  Y : PositiveInterval (topHeight q u)
  Y_lo : Y.lo=ev t (YLo s)
  Y_hi : Y.hi=ev t (YHi s)
  v : PositiveInterval (lowerHeight q u)
  v_lo : v.lo=ev t (vLo s)
  v_hi : v.hi=ev t (vHi s)
  w : PositiveInterval (lowerLeft q u)
  w_lo : w.lo=ev t (wLo s)
  w_hi : w.hi=ev t (wHi s)
  sine : PositiveInterval (Real.sin t)
  sine_lo : sine.lo=ev t sineLo
  sine_hi : sine.hi=ev t sineHi
  cosine : PositiveInterval (Real.cos t)
  cosine_lo : cosine.lo=ev t cosineLo
  cosine_hi : cosine.hi=ev t cosineHi
  first : PositiveInterval (firstComponent q (Real.cos t) (Real.sin t) u)
  first_lo : first.lo=ev t (firstLo s)
  first_hi : first.hi=ev t (firstHi s)
  second : PositiveInterval (secondComponent q (Real.cos t) (Real.sin t) u)
  second_lo : second.lo=ev t (secondLo s)
  second_hi : second.hi=ev t (secondHi s)

def boxes {s : Chain} {q t u : ℝ} (ht : t∈Icc (1/10:ℝ) (4/25))
    (hu : u∈Icc (ev t (a s)) (ev t (b s))) (h : RadicalBounds s q t u) : Boxes s q t u := by
  have hp (i : Fin 6) : 0≤ev t (coordinateLower s i) := by linarith [(polynomial_coordinates s i ht).1]
  have hb := endpoints ht s
  have ht' := trig_bounds ht
  have hf := component_bounds ht hu h
  have ha := auxiliary_bounds s ht
  refine ⟨PositiveInterval.of_bounds hu (by linarith [hb.1]),rfl,rfl,
    PositiveInterval.of_bounds ⟨by linarith [hu.2],by linarith [hu.1]⟩ (by linarith [hb.2.2]),rfl,rfl,
    PositiveInterval.of_bounds h.r (hp 0),rfl,rfl,
    PositiveInterval.of_bounds h.U (hp 1),rfl,rfl,
    PositiveInterval.of_bounds h.V (hp 2),rfl,rfl,
    PositiveInterval.of_bounds h.Y (hp 3),rfl,rfl,
    PositiveInterval.of_bounds h.v (hp 4),rfl,rfl,
    PositiveInterval.of_bounds h.w (hp 5),rfl,rfl,
    PositiveInterval.of_bounds ht'.1 ht'.2.2.1,rfl,rfl,
    PositiveInterval.of_bounds ht'.2.1 ht'.2.2.2.le,rfl,rfl,
    PositiveInterval.of_bounds hf.1 (by linarith [ha.2.2.1]),rfl,rfl,
    PositiveInterval.of_bounds hf.2 (by linarith [ha.2.2.2]),rfl,rfl⟩

def clearedPosition (q t u : ℝ) : ℝ :=
  firstComponent q (Real.cos t) (Real.sin t) u*(Real.cos t*u+Real.sin t*lowerRight q u)*
    topRight q u*topHeight q u*lowerLeft q u-
  secondComponent q (Real.cos t) (Real.sin t) u*(2-u)*topLeft q u*
    (Real.cos t*lowerLeft q u+Real.sin t*lowerHeight q u)*lowerRight q u

theorem clearedPosition_identity {q t u : ℝ} (h : SmoothDomain q u) :
    clearedPosition q t u=positionHalf q (Real.cos t) (Real.sin t) u*
      (lowerRight q u*topRight q u*topHeight q u*lowerLeft q u) := by
  dsimp [clearedPosition,positionHalf,slopeRatio]
  field_simp [h.r_pos.ne',h.U_pos.ne',h.Y_pos.ne',h.w_pos.ne']
  ring

theorem position_bounds {s : Chain} {q t u : ℝ}
    (ht : t∈Icc (1/10:ℝ) (4/25)) (hu : u∈Icc (ev t (a s)) (ev t (b s)))
    (h : RadicalBounds s q t u) :
    clearedPosition q t u∈Icc (ev t (positionLowerAt s)) (ev t (positionUpperAt s)) := by
  let B := boxes ht hu h
  let X := (((B.first.mul ((B.cosine.mul B.height).add (B.sine.mul B.r))).mul B.U).mul B.Y).mul
    B.w
  let Y := (((B.second.mul B.other).mul B.V).mul ((B.cosine.mul B.w).add (B.sine.mul B.v))).mul
    B.r
  have e2 : ev t (2:ℚ[X])=2 := by rw [ev]; exact map_ofNat _ 2
  have hlo : ev t (positionLowerAt s)=X.lo-Y.hi := by
    show _=B.first.lo*(B.cosine.lo*B.height.lo+B.sine.lo*B.r.lo)*B.U.lo*B.Y.lo*B.w.lo-
      B.second.hi*B.other.hi*B.V.hi*(B.cosine.hi*B.w.hi+B.sine.hi*B.v.hi)*B.r.hi
    rw [B.first_lo,B.cosine_lo,B.height_lo,B.sine_lo,B.r_lo,B.U_lo,B.Y_lo,B.w_lo,
      B.second_hi,B.other_hi,B.V_hi,B.cosine_hi,B.w_hi,B.sine_hi,B.v_hi,B.r_hi]
    simp only [positionLowerAt,ev_sub,ev_mul,ev_add,e2]
  have hhi : ev t (positionUpperAt s)=X.hi-Y.lo := by
    show _=B.first.hi*(B.cosine.hi*B.height.hi+B.sine.hi*B.r.hi)*B.U.hi*B.Y.hi*B.w.hi-
      B.second.lo*B.other.lo*B.V.lo*(B.cosine.lo*B.w.lo+B.sine.lo*B.v.lo)*B.r.lo
    rw [B.first_hi,B.cosine_hi,B.height_hi,B.sine_hi,B.r_hi,B.U_hi,B.Y_hi,B.w_hi,
      B.second_lo,B.other_lo,B.V_lo,B.cosine_lo,B.w_lo,B.sine_lo,B.v_lo,B.r_lo]
    simp only [positionUpperAt,ev_sub,ev_mul,ev_add,e2]
  rw [hlo,hhi]
  exact ⟨sub_le_sub X.mem.1 Y.mem.2,sub_le_sub X.mem.2 Y.mem.1⟩

end SquaresInCircles.Eight.TableFree.CriticalESubstitution
