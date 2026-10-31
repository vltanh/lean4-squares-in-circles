module

public import SquaresInCircles.Eight.ExactFamily.Stationary
public import SquaresInCircles.Eight.Boundary.Model
public import SquaresInCircles.Common.SeparatingAxes

/-!
# Eight squares: the admissible models are packings

For admissible parameters the model is a packing in the closed disk of squared radius `qStar`
about the origin (`model_sqPacking`). The seven exterior squares lie in the disk
(`exterior_contained`) and are pairwise disjoint (`exterior_disjoint`) on the whole closed ranges
of the two sliders, contacts and endpoint ties included; each pair is separated along an explicit
normal (`exterior_separator`). The central square lies in the disk, and its seven separation
conditions are the separating-axis conditions on its four axes and the four axes of the other
square, written as `W₀ ≤ M₀` and `Wₜ ≤ Mₜ` (`sat_max_iff`, `central_axis_sat`,
`central_tilted_sat`), so they hold exactly when the central square is disjoint from the others.
The bounds on the coordinates of `sharpData` used here are `sharp_exterior_bounds`,
proved directly from `sharp_coordinates` by signs and products of short rational bounds.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily
open Coordinates EqualityParameters

def sampleParameters : EqualityParameters := ⟨7/50,0,1/10,27/20,-8/25⟩
theorem sampleParameters_inBox : sampleParameters.InBox := by
  norm_num [sampleParameters,EqualityParameters.InBox]

theorem sharp_exterior_bounds :
    0<sharpData.x₁-sharpData.x₂ ∧ sharpData.x₁-sharpData.x₂<1 ∧
    0<sharpData.x₂-3/2 ∧ sharpData.x₂-3/2<1/2 ∧
    0<sharpData.h₁+3/2 ∧ sharpData.h₁+3/2<1/2 ∧
    sharpData.x₄-sharpData.x₃<0 ∧
    0<sharpData.y+1 ∧ 0<sharpData.y₃-1 ∧
    sharpData.s*(sharpData.h₁+1)+sharpData.c*(sharpData.h₂+1)<0 ∧
    sharpData.s*(sharpData.h₁+2)-sharpData.c/12<0 ∧
    -(355/1000)<sharpData.c*(sharpData.h₁+1)+sharpData.s/12 := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hy := sharp_y
  have hc0 : 0 < sharpData.c := by linarith only [hc]
  have hs0 : 0 < sharpData.s := by linarith only [hs]
  have hH : sharpData.s*(sharpData.h₁+1)+sharpData.c*(sharpData.h₂+1) < 0 :=
    add_neg (mul_neg_of_pos_of_neg hs0 (by linarith only [hh₁u]))
      (mul_neg_of_pos_of_neg hc0 (by linarith only [hh₂u]))
  have hG : sharpData.s*(sharpData.h₁+2)-sharpData.c/12 < 0 := by
    have hprod : sharpData.s*(sharpData.h₁+2) ≤ (0.124:ℝ)*0.633 :=
      mul_le_mul (by linarith only [hsu]) (by linarith only [hh₁u])
        (by linarith only [hh₁]) (by norm_num)
    linarith only [hprod,hc]
  have hL : -(355/1000) < sharpData.c*(sharpData.h₁+1)+sharpData.s/12 := by
    have hprod : (0.9925:ℝ)*(-0.368) ≤ sharpData.c*(sharpData.h₁+1) := calc
      _ ≤ sharpData.c*(-0.368) :=
        mul_le_mul_of_nonpos_right (by linarith only [hcu]) (by norm_num)
      _ ≤ sharpData.c*(sharpData.h₁+1) :=
        mul_le_mul_of_nonneg_left (by linarith only [hh₁]) hc0.le
    linarith only [hprod,hs]
  dsimp only [x₃]
  exact ⟨by linarith only [hx₁, hx₂u],by linarith only [hx₁u, hx₂],by linarith only [hx₂],
    by linarith only [hx₂u],by linarith only [hh₁],by linarith only [hh₁u],
    by linarith only [hx₂, hx₄u],by linarith only [hy.1],by linarith only [hy₃],
    hH,hG,hL⟩

theorem separated_by_normal {K L : UnitSquare} {n : Point} (hn : n≠(0,0))
    (hsep : width K n+width L n≤dot n (sub L.center K.center)) :
    ∀ p, ¬(openSquare K p ∧ openSquare L p) := by
  intro p hp
  have hK := (abs_lt.mp (dot_open_bound_of_ne K hn hp.1)).2
  have hL := (abs_lt.mp (dot_open_bound_of_ne L hn hp.2)).1
  have hid : dot n (sub L.center K.center)=dot n (sub p K.center)-dot n (sub p L.center) := by
    dsimp [dot,sub]; ring
  linarith

theorem separated_by_unsigned {K L : UnitSquare} {n : Point} (hn : n≠(0,0))
    (hsep : width K n+width L n≤|dot n (sub L.center K.center)|) :
    ∀ p, ¬(openSquare K p ∧ openSquare L p) := by
  rcases le_total 0 (dot n (sub L.center K.center)) with h | h
  · rw [abs_of_nonneg h] at hsep
    exact separated_by_normal hn hsep
  · apply separated_by_normal (n:=scale (-1) n)
    · intro hh
      apply hn
      have h₁ := congrArg Prod.fst hh
      have h₂ := congrArg Prod.snd hh
      dsimp [scale] at h₁ h₂
      ext <;> simp <;> linarith
    · have hds : dot (scale (-1) n) (sub L.center K.center)=
          -dot n (sub L.center K.center) := by
        simp only [dot,scale]; ring
      rw [width_neg,width_neg,hds]
      rwa [abs_of_nonpos h] at hsep

theorem sat_max_iff (K L : UnitSquare) :
    (∀ p, ¬(openSquare K p ∧ openSquare L p)) ↔
      SAT.threshold K L≤ max
        (max |frameX K (sub L.center K.center)| |frameY K (sub L.center K.center)|)
        (max |frameX L (sub L.center K.center)| |frameY L (sub L.center K.center)|) := by
  constructor
  · intro hd
    have h := SAT.separating_axes K L hd
    simp only [le_max_iff]
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro hh
    simp only [le_max_iff] at hh
    have hKu := K.unit
    have hLu := L.unit
    have hne (a b : ℝ) (hab : a^2+b^2=1) : ((a,b) : Point)≠(0,0) := by
      intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      rw [h1,h2] at hab
      norm_num at hab
    have hw (S : UnitSquare) (a b : ℝ) :
        width S (a,b)=(|S.cosine*a+S.sine*b|+|-S.sine*a+S.cosine*b|)/2 := rfl
    have hthr : SAT.threshold K L=(1+|relativeC K L|+|relativeS K L|)/2 := rfl
    have hC : relativeC K L=K.cosine*L.cosine+K.sine*L.sine := rfl
    have hS : relativeS K L=-K.sine*L.cosine+K.cosine*L.sine := rfl
    rcases hh with (h | h) | (h | h)
    · refine separated_by_unsigned (n:=(K.cosine,K.sine)) (hne _ _ hKu) ?_
      rw [hw,hw,show K.cosine*K.cosine+K.sine*K.sine=1 by linear_combination hKu,
        show -K.sine*K.cosine+K.cosine*K.sine=0 by ring,
        show L.cosine*K.cosine+L.sine*K.sine=relativeC K L by rw [hC]; ring,
        show -L.sine*K.cosine+L.cosine*K.sine=-relativeS K L by rw [hS]; ring,abs_neg]
      rw [hthr] at h
      change _≤|frameX K (sub L.center K.center)|
      norm_num
      linarith
    · refine separated_by_unsigned (n:=(-K.sine,K.cosine))
        (hne _ _ (by linear_combination hKu)) ?_
      rw [hw,hw,show K.cosine*-K.sine+K.sine*K.cosine=0 by ring,
        show -K.sine*-K.sine+K.cosine*K.cosine=1 by linear_combination hKu,
        show L.cosine*-K.sine+L.sine*K.cosine=relativeS K L by rw [hS]; ring,
        show -L.sine*-K.sine+L.cosine*K.cosine=relativeC K L by rw [hC]; ring]
      rw [hthr] at h
      change _≤|frameY K (sub L.center K.center)|
      norm_num
      linarith
    · refine separated_by_unsigned (n:=(L.cosine,L.sine)) (hne _ _ hLu) ?_
      rw [hw,hw,show L.cosine*L.cosine+L.sine*L.sine=1 by linear_combination hLu,
        show -L.sine*L.cosine+L.cosine*L.sine=0 by ring,
        show K.cosine*L.cosine+K.sine*L.sine=relativeC K L by rw [hC],
        show -K.sine*L.cosine+K.cosine*L.sine=relativeS K L by rw [hS]]
      rw [hthr] at h
      change _≤|frameX L (sub L.center K.center)|
      norm_num
      linarith
    · refine separated_by_unsigned (n:=(-L.sine,L.cosine))
        (hne _ _ (by linear_combination hLu)) ?_
      rw [hw,hw,show L.cosine*-L.sine+L.sine*L.cosine=0 by ring,
        show -L.sine*-L.sine+L.cosine*L.cosine=1 by linear_combination hLu,
        show K.cosine*-L.sine+K.sine*L.cosine=-relativeS K L by rw [hS]; ring,
        show -K.sine*-L.sine+K.cosine*L.cosine=relativeC K L by rw [hC]; ring,abs_neg]
      rw [hthr] at h
      change _≤|frameY L (sub L.center K.center)|
      norm_num
      linarith

theorem frame_parameter_bounds {p : EqualityParameters}
    (hl : 1-Real.sqrt 2≤p.w) (hu : p.w<Real.sqrt 2-1) :
    7/10<p.C ∧ |p.S|<18/25 ∧
      0<sharpData.c*p.C+sharpData.s*p.S := by
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hw : |p.w|<21/50 := by rw [abs_lt]; constructor <;> nlinarith only [hl, hs2, hu]
  have hpden := halfAngle_den_pos p.w
  have hC : 7/10<p.C := by
    dsimp [C,halfAngleCos]
    rw [lt_div_iff₀ hpden]
    have hb := abs_lt.mp hw
    nlinarith only [hs2, hb, hl, hu]
  have hU := halfAngle_unit p.w
  have hS : |p.S|<18/25 := by
    dsimp [C] at hC
    dsimp [S]
    rw [abs_lt]
    constructor <;> nlinarith only [hC, hU]
  have hb := sharp_coordinates
  have hsp := abs_lt.mp hS
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  have hcc := mul_lt_mul_of_pos_left hC hc
  have hss := mul_lt_mul_of_pos_left hsp.1 hs
  refine ⟨hC,hS,?_⟩
  linarith only [hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2.1, hs, hcc, hss]

theorem central_axis_sat {p : EqualityParameters}
    (hframe : 1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1) (v : Point) :
    (∀ x, ¬(openSquare p.centralSquare x ∧ openSquare (axisSquare v) x)) ↔
      p.W₀≤p.M₀ (sub v p.center) := by
  have hc := (frame_parameter_bounds hframe.1 hframe.2).1
  rw [sat_max_iff]
  simp [SAT.threshold,relativeC,relativeS,centralSquare,axisSquare,frameX,frameY,
    W₀,M₀,abs_of_pos (by linarith : 0<p.C),abs_neg,max_comm,max_left_comm,max_assoc]

theorem central_tilted_sat {p : EqualityParameters}
    (hframe : 1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1) (v : Point) :
    (∀ x, ¬(openSquare p.centralSquare x ∧ openSquare (sharpData.tiltedSquare v) x)) ↔
      p.Wₜ sharpData≤p.Mₜ sharpData (sub v p.center) := by
  have hc := (frame_parameter_bounds hframe.1 hframe.2).2.2
  have hthr : SAT.threshold p.centralSquare (sharpData.tiltedSquare v)=p.Wₜ sharpData := by
    simp only [SAT.threshold,relativeC,relativeS,centralSquare,tiltedSquare,Wₜ]
    rw [show p.C*sharpData.c+p.S*sharpData.s=sharpData.c*p.C+sharpData.s*p.S by ring,
      abs_of_pos hc,
      show -p.S*sharpData.c+p.C*sharpData.s=-(sharpData.c*p.S-sharpData.s*p.C) by ring,
      abs_neg]
    ring
  rw [sat_max_iff,hthr,max_comm]
  rfl

theorem axis_containment (q : ℝ) (v : Point) : SqContained q (axisSquare v) ↔
    (|v.1|+1/2)^2+(|v.2|+1/2)^2≤q := by
  simp [SqContained,phi,alpha,beta,localX,localY,axisSquare,abs_neg]

theorem tilted_containment (d : Coordinates) (q a b : ℝ) :
    SqContained q (d.tiltedSquare (d.inFrame a b)) ↔
      (|a|+1/2)^2+(|b|+1/2)^2≤q := by
  have hx : localX (d.tiltedSquare (d.inFrame a b)) (0,0)= -a := by
    dsimp [localX,tiltedSquare,inFrame]
    linear_combination -a*d.unit
  have hy : localY (d.tiltedSquare (d.inFrame a b)) (0,0)= -b := by
    dsimp [localY,tiltedSquare,inFrame]
    linear_combination -b*d.unit
  simp [SqContained,phi,alpha,beta,hx,hy,abs_neg]

theorem exterior_contained {p : EqualityParameters} (hp : p.Admissible sharpData)
    (i : Fin 7) : SqContained qStar (sharpData.exteriorSquares p.z p.eta i) := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hy := sharp_y
  have hchain := sharpData_stationary
  have hq := qStar_limits.1
  have hqd : sharpData.q=qStar := rfl
  have htopRad : 0≤ sharpData.q-(sharpData.x₂-1)^2 := by
    change 0≤ qStar-(sharpData.x₂-1)^2
    nlinarith only [hx₂u, hq, hx₂]
  have hGRad : 0≤ sharpData.q-(sharpData.h₁+2)^2 := by
    change 0≤ qStar-(sharpData.h₁+2)^2
    nlinarith only [hh₁u, hq, hh₁]
  have htop : p.z+1/2≤ Real.sqrt (sharpData.q-(sharpData.x₂-1)^2) := by
    have h := hp.top_upper
    dsimp [zMax] at h
    linarith only [h]
  have hG : -Real.sqrt (sharpData.q-(sharpData.h₁+2)^2)≤ sharpData.h₂+p.eta := by
    have h := hp.tilted_lower
    dsimp [etaMin] at h
    linarith only [h]
  have hGupper : sharpData.h₂+p.eta≤ -13/12 := by
    have h := hp.tilted_upper
    dsimp [etaMax] at h
    linarith only [h]
  have h0 : SqContained qStar (sharpData.tiltedSquare sharpData.pH) := by
    rw [pH,tilted_containment]
    rw [abs_of_neg (by linarith only [hh₁u] : sharpData.h₁+1/2<0),
      abs_of_neg (by linarith only [hh₂u] : sharpData.h₂+1/2<0)]
    have hz := hchain.zero_defect
    dsimp [Coordinates.defect] at hz
    rw [hqd] at hz
    linarith only [hz]
  have h1 : SqContained qStar (sharpData.tiltedSquare (sharpData.pG p.eta)) := by
    rw [pG,tilted_containment]
    rw [abs_of_pos (by linarith only [hh₁] : 0< sharpData.h₁+3/2),
      abs_of_neg (by linarith only [hGupper] : sharpData.h₂+1/2+p.eta<0)]
    rw [hqd] at hGRad hG
    nlinarith only [Real.sq_sqrt hGRad, Real.sqrt_nonneg (qStar-(sharpData.h₁+2)^2), hG, hGRad,
      hGupper]
  have h2 : SqContained qStar (axisSquare sharpData.pA) := by
    rw [axis_containment]
    simp only [pA]
    rw [abs_of_pos (by linarith only [hx₁] : 0< sharpData.x₁-1/2),
      abs_of_neg (by linarith only [hy.2] : sharpData.y+1/2<0)]
    have hcirc := hchain.first_circle
    rw [hqd] at hcirc
    linarith only [hcirc]
  have h3 : SqContained qStar (axisSquare sharpData.pB) := by
    rw [axis_containment]
    simp only [pB]
    rw [abs_of_pos (by linarith only [hx₂] : 0< sharpData.x₂-1/2),
      abs_of_pos (by linarith only [hy.1] : 0< sharpData.y+3/2)]
    have hcirc := hchain.second_circle
    rw [hqd] at hcirc
    linarith only [hcirc]
  have h4 : SqContained qStar (axisSquare (sharpData.pT p.z)) := by
    rw [axis_containment]
    simp only [pT]
    rw [abs_of_pos (by linarith only [hx₂] : 0< sharpData.x₂-3/2),
      abs_of_pos (by linarith only [hp.top_lower] : 0< p.z)]
    rw [hqd] at htopRad htop
    have hz0 : 0 ≤ p.z+1/2 := by linarith only [hp.top_lower]
    have hsq := mul_le_mul htop htop hz0 (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt htopRad] at hsq
    linarith only [hsq]
  have h5 : SqContained qStar (axisSquare sharpData.pD) := by
    rw [axis_containment]
    simp only [pD,x₃]
    rw [abs_of_neg (by linarith only [hx₂u] : sharpData.x₂-3+1/2<0),
      abs_of_pos (by linarith only [hy₃] : 0< sharpData.y₃-1/2)]
    have hcirc := hchain.third_circle
    simp only [x₃] at hcirc
    rw [hqd] at hcirc
    linarith only [hcirc]
  have h6 : SqContained qStar (axisSquare sharpData.pE) := by
    rw [axis_containment]
    simp only [pE,y₄]
    rw [abs_of_neg (by linarith only [hx₄u] : sharpData.x₄+1/2<0),
      abs_of_neg (by linarith only [hy₃u] : sharpData.y₃-2+1/2<0)]
    have hcirc := hchain.fourth_circle
    simp only [y₄] at hcirc
    rw [hqd] at hcirc
    linarith only [hcirc]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

def exteriorNormal (d : Coordinates) (i j : Fin 7) : Point :=
  if (i=0 ∧ j=1) ∨ (i=0 ∧ j=2) ∨ (i=1 ∧ j=2) then d.e
  else if i=0 ∧ j=6 then d.f
  else if (i=0 ∨ i=1) ∧ (j=3 ∨ j=4 ∨ j=5) then (0,1)
  else if (i=2 ∧ j=3) then (0,1)
  else if i=5 ∧ j=6 then (0,-1)
  else (-1,0)

private theorem width_tilted_e (p : Point) :
    width (sharpData.tiltedSquare p) sharpData.e=1/2 := by
  have hx : frameX (sharpData.tiltedSquare p) sharpData.e=1 := by
    dsimp [frameX,Coordinates.tiltedSquare,Coordinates.e]
    linear_combination sharpData.unit
  have hy : frameY (sharpData.tiltedSquare p) sharpData.e=0 := by
    dsimp [frameY,Coordinates.tiltedSquare,Coordinates.e]
    ring
  simp [width,hx,hy]

private theorem width_tilted_f (p : Point) :
    width (sharpData.tiltedSquare p) sharpData.f=1/2 := by
  have hx : frameX (sharpData.tiltedSquare p) sharpData.f=0 := by
    dsimp [frameX,Coordinates.tiltedSquare,Coordinates.f]
    ring
  have hy : frameY (sharpData.tiltedSquare p) sharpData.f=1 := by
    dsimp [frameY,Coordinates.tiltedSquare,Coordinates.f]
    nlinarith [sharpData.unit]
  simp [width,hx,hy]

private theorem width_axis_e (p : Point) :
    width (axisSquare p) sharpData.e=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,axisSquare,Coordinates.e,abs_of_pos hc,abs_of_pos hs]

private theorem width_axis_f (p : Point) :
    width (axisSquare p) sharpData.f=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,axisSquare,Coordinates.f,abs_of_pos hc,abs_of_pos hs,
    abs_neg,add_comm]

private theorem width_tilted_horizontal (p : Point) :
    width (sharpData.tiltedSquare p) (-1,0)=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,Coordinates.tiltedSquare,abs_of_pos hc,abs_of_pos hs,abs_neg]

private theorem width_tilted_vertical (p : Point) :
    width (sharpData.tiltedSquare p) (0,1)=(sharpData.c+sharpData.s)/2 := by
  have hc := sharpData_stationary.weightDomain.c_pos
  have hs := sharpData_stationary.weightDomain.s_pos
  simp [width,frameX,frameY,Coordinates.tiltedSquare,abs_of_pos hc,abs_of_pos hs,add_comm]

/- The twenty-one pairs of exterior squares are separated for `z ≥ 1/2` and G below the axis:
the ten pairs of axis-parallel squares; H–G, H–A, G–A and H–E; G–E; and the six pairs joining H
or G to B, T or D. The bounds `7/12 ≤ z` and `η ≤ etaMax` of the core are not needed. -/
set_option linter.unusedSimpArgs false in
theorem exterior_separator_wide {z η : ℝ} (hz : 1/2≤z)
    (hGtop : sharpData.s*(sharpData.h₁+2)+
      sharpData.c*(sharpData.h₂+1+η)≤0)
    (i j : Fin 7) (hij : i<j) :
    exteriorNormal sharpData i j≠(0,0) ∧
      width (sharpData.exteriorSquares z η i) (exteriorNormal sharpData i j)+
        width (sharpData.exteriorSquares z η j) (exteriorNormal sharpData i j)≤
      dot (exteriorNormal sharpData i j)
        (sub (sharpData.exteriorCenters z η j) (sharpData.exteriorCenters z η i)) := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,
    hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  obtain ⟨hAB,hABu,hTx,hTxu,hGx,hGxu,hED,hBbot,hDbot,hHtop,hGcore,hGleftCore⟩ :=
    sharp_exterior_bounds
  have hneg : sharpData.h₂+1+η≤0 := by
    by_contra! h
    have hp := mul_pos (show 0<sharpData.c by linarith only [hc]) h
    have hp' := mul_pos (show 0<sharpData.s by linarith only [hs])
      (show 0<sharpData.h₁+2 by linarith only [hh₁])
    linarith only [hp,hp',hGtop]
  have hGleft : -1/2<sharpData.c*(sharpData.h₁+1)-
      sharpData.s*(sharpData.h₂+1+η) := by
    have h₁ := mul_nonneg (show 0≤1-sharpData.c by linarith only [hcu])
      (show 0≤-(sharpData.h₁+1) by linarith only [hh₁u])
    have h₂ := mul_nonpos_of_nonneg_of_nonpos (show 0≤ sharpData.s by linarith only [hs]) hneg
    linarith only [h₁,h₂,hh₁]
  have hHG := sharpData.HG_contact η
  have hHA := sharpData.HA_contact
  have hGA := sharpData.GA_contact η
  have hHE := sharpData.HE_contact
  have he : sharpData.e≠(0,0) := by
    intro h
    have hc₀ := congrArg Prod.fst h
    dsimp [Coordinates.e] at hc₀
    linarith only [hc₀,hc]
  have hf : sharpData.f≠(0,0) := by
    intro h
    have hc₀ := congrArg Prod.snd h
    dsimp [Coordinates.f] at hc₀
    linarith only [hc₀,hc]
  have hy : ((0,1):Point)≠(0,0) := by simp
  have hmy : ((0,-1):Point)≠(0,0) := by simp
  have hmx : ((-1,0):Point)≠(0,0) := by simp
  have wAy (v : Point) : width (axisSquare v) ((0,1):Point)=1/2 := by
    simp [width,frameX,frameY,axisSquare]
  have wAmy (v : Point) : width (axisSquare v) ((0,-1):Point)=1/2 := by
    simp [width,frameX,frameY,axisSquare]
  have wAmx (v : Point) : width (axisSquare v) ((-1,0):Point)=1/2 := by
    simp [width,frameX,frameY,axisSquare]
  have hnormal (k l : Fin 7) : exteriorNormal sharpData k l ≠ (0,0) := by
    unfold exteriorNormal
    split_ifs <;> first | exact he | exact hf | exact hy | exact hmy | exact hmx
  refine ⟨hnormal i j, ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    simp [Coordinates.exteriorSquares, Coordinates.exteriorCenters, exteriorNormal,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk,
      width_tilted_e, width_tilted_f, width_tilted_vertical, width_tilted_horizontal,
      width_axis_e, width_axis_f, wAy, wAmy, wAmx]
    simp only [dot, sub, Coordinates.pA, Coordinates.pB, Coordinates.pD, Coordinates.pE,
      Coordinates.pT, Coordinates.pH, Coordinates.pG, Coordinates.x₃, Coordinates.y₄,
      Coordinates.inFrame] at *
    linarith

theorem exterior_separator {p : EqualityParameters} (hp : p.Admissible sharpData)
    (i j : Fin 7) (hij : i<j) :
    exteriorNormal sharpData i j≠(0,0) ∧
      width (sharpData.exteriorSquares p.z p.eta i) (exteriorNormal sharpData i j)+
      width (sharpData.exteriorSquares p.z p.eta j) (exteriorNormal sharpData i j)≤
        dot (exteriorNormal sharpData i j)
          (sub (sharpData.exteriorCenters p.z p.eta j) (sharpData.exteriorCenters p.z p.eta i)) := by
  have hz : 1/2 ≤ p.z := le_trans (by norm_num) hp.top_lower
  have hη : sharpData.h₂ + p.eta ≤ -13/12 := by
    have h := hp.tilted_upper
    dsimp [etaMax] at h
    linarith
  have hc := sharpData_stationary.weightDomain.c_pos.le
  have hηc := mul_le_mul_of_nonneg_left hη hc
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hGcore,_⟩ := sharp_exterior_bounds
  apply exterior_separator_wide hz (i := i) (j := j) ?_ hij
  linarith

theorem exterior_disjoint {p : EqualityParameters} (hp : p.Admissible sharpData) :
    InteriorDisjoint (sharpData.exteriorSquares p.z p.eta) := by
  have hcen (k : Fin 7) : sharpData.exteriorCenters p.z p.eta k =
      (sharpData.exteriorSquares p.z p.eta k).center := by
    fin_cases k <;> rfl
  intro i j hij x hx
  rcases lt_or_gt_of_ne hij with hij | hji
  · obtain ⟨hn,hs⟩ := exterior_separator hp i j hij
    rw [hcen,hcen] at hs
    exact separated_by_normal hn hs x hx
  · obtain ⟨hn,hs⟩ := exterior_separator hp j i hji
    rw [hcen,hcen] at hs
    exact separated_by_normal hn hs x ⟨hx.2,hx.1⟩

theorem model_sqPacking {p : EqualityParameters} (hp : p.Admissible sharpData) :
    SqPacking (p.model sharpData) (0,0) qStar := by
  have hq0 : 0 ≤ qStar := by linarith [qStar_limits.1]
  have hmodel (k : Fin 7) : p.model sharpData k.succ = sharpData.exteriorSquares p.z p.eta k := by
    fin_cases k <;> rfl
  have hmodel0 : p.model sharpData 0 = p.centralSquare := rfl
  refine ⟨hq0,?_,?_⟩
  · intro i x hx
    have key : SqContained qStar (p.model sharpData i) := by
      induction i using Fin.cases with
      | zero =>
        have hq : 121/72 < sharpData.q := by change 121/72 < qStar; linarith [qStar_limits.1]
        rw [hmodel0]
        exact (central_containment hp hq).le
      | succ k =>
        rw [hmodel]
        exact exterior_contained hp k
    have h := ((SqContained.iff_points hq0 _).mp key) x hx
    simpa [sub] using h
  · have hax := central_axis_sat ⟨hp.frame_lower,hp.frame_upper⟩
    have hti := central_tilted_sat ⟨hp.frame_lower,hp.frame_upper⟩
    have hA := (hax sharpData.pA).2 hp.A_sep
    have hB := (hax sharpData.pB).2 hp.B_sep
    have hD := (hax sharpData.pD).2 hp.D_sep
    have hE := (hax sharpData.pE).2 hp.E_sep
    have hT := (hax (sharpData.pT p.z)).2 hp.T_sep
    have hH := (hti sharpData.pH).2 hp.H_sep
    have hG := (hti (sharpData.pG p.eta)).2 hp.G_sep
    have hext := exterior_disjoint hp
    have hcent (k : Fin 7) : ∀ y, ¬(openSquare p.centralSquare y ∧
        openSquare (sharpData.exteriorSquares p.z p.eta k) y) := by
      fin_cases k
      · exact hH
      · exact hG
      · exact hA
      · exact hB
      · exact hT
      · exact hD
      · exact hE
    intro i j hij x hx
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact hij rfl
      | succ l =>
        rw [hmodel0,hmodel] at hx
        exact hcent l x hx
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [hmodel0,hmodel] at hx
        exact hcent k x ⟨hx.2,hx.1⟩
      | succ l =>
        rw [hmodel,hmodel] at hx
        exact hext k l (fun h => hij (by rw [h])) x hx

end SquaresInCircles.Eight.ExactFamily
