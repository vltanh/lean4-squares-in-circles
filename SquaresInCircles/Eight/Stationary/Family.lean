module

public import SquaresInCircles.Common.Frames
public import SquaresInCircles.Eight.Model
public import SquaresInCircles.Eight.Stationary.Generated.LocalStationaryBounds
public import SquaresInCircles.Eight.Stationary.System
public import SquaresInCircles.Eight.Stationary.FixedEval

/-!
# Eight squares: the five-parameter family

The models of the admissible parameters `(x, y, w, z, eta)` of the stationary chart and their
mirror images in the diagonal (`stationaryReflectedModel`) form the set `stationaryModels`: each
is a packing in the closed disk of radius `stationaryRadius = √qStar` about the origin
(`model_packing`) that reaches the circle (`model_reaches`). The admissible set contains its weak
contact boundaries, and every point of the rational box `InBox`, of side `0.002` in each
parameter, is admissible (`box_admissible`); the sample parameters give a model
(`models_nonempty`). Conversely, the admissibility conditions are necessary for a packing at the
radius `√qStar` whose exterior squares are those of a model (`admissible_of_original_geometry`).

The mirror image is a separate branch, chosen by a Boolean, because `Congruent` uses positively
oriented frames.
-/

section
/-!
## The admissible models are packings

For admissible parameters the model is a packing in the closed disk of squared radius `qStar`
about the origin (`model_sqPacking`). The seven exterior squares lie in the disk
(`exterior_contained`) and are pairwise disjoint (`exterior_disjoint`) on the whole closed ranges
of the two sliders, contacts and endpoint ties included; each pair is separated along an explicit
normal (`exterior_separator`). The central square lies in the disk, and its seven separation
conditions are the separating-axis conditions on its four axes and the four axes of the other
square, written as `W₀ ≤ M₀` and `Wₜ ≤ Mₜ` (`sat_max_iff`, `central_axis_sat`,
`central_tilted_sat`), so they hold exactly when the central square is disjoint from the others.
The bounds on the coordinates of `sharpData` used here are `sharp_exterior_bounds`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.Stationary
open Coordinates EqualityParameters Arithmetic

def boxEnv (p : EqualityParameters) : Fin 8 → ℝ :=
  ![qStar,sharpPose.1,sharpPose.2,p.x,p.y,p.w,p.z,p.eta]

theorem boxEnv_mem {p : EqualityParameters} (hp : p.InBox) : EqualityGenerated.box.Mem (boxEnv p) := by
  have hs := sharpBox_mem
  intro i; fin_cases i
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · simp only [EqualityGenerated.box,boxEnv,QInterval.Mem]; push_cast; exact hp.1
  · simp only [EqualityGenerated.box,boxEnv,QInterval.Mem]; push_cast
    exact ⟨by linarith [hp.2.1.1],by linarith [hp.2.1.2]⟩
  · simp only [EqualityGenerated.box,boxEnv,QInterval.Mem]; push_cast; exact hp.2.2.1
  · simp only [EqualityGenerated.box,boxEnv,QInterval.Mem]; push_cast; exact hp.2.2.2.1
  · simp only [EqualityGenerated.box,boxEnv,QInterval.Mem]; push_cast
    exact ⟨by linarith [hp.2.2.2.2.1],by linarith [hp.2.2.2.2.2]⟩

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
  have henv := boxEnv_mem sampleParameters_inBox
  have hH := (EqualityGenerated.topH_bound _ henv).2
  have hG := (EqualityGenerated.topG_bound _ henv).2
  have hL := (EqualityGenerated.leftG_bound _ henv).1
  have eH : EqualityGenerated.topHExpression.eval (boxEnv sampleParameters)=
      sharpData.s*(sharpData.h₁+1)+sharpData.c*(sharpData.h₂+1) := by
    norm_num [EqualityGenerated.topHExpression,ScalarExpr.eval,boxEnv,sharpData,
      radicalCoordinates,c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv]
    ring_nf
  have eG : EqualityGenerated.topGExpression.eval (boxEnv sampleParameters)=
      sharpData.s*(sharpData.h₁+2)-sharpData.c/12 := by
    norm_num [EqualityGenerated.topGExpression,ScalarExpr.eval,boxEnv,sharpData,
      radicalCoordinates,c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv]
    ring_nf
  have eL : EqualityGenerated.leftGExpression.eval (boxEnv sampleParameters)=
      sharpData.c*(sharpData.h₁+1)+sharpData.s/12 := by
    norm_num [EqualityGenerated.leftGExpression,ScalarExpr.eval,boxEnv,sharpData,
      radicalCoordinates,c,s,h₁,h₂,y₄,halfAngleCos,halfAngleSin,div_eq_mul_inv]
    ring_nf
  rw [eH] at hH; rw [eG] at hG; rw [eL] at hL
  have hcu' : sharpData.c ≤ 99242/100000 := hcu
  have hL' : -(355/1000) < sharpData.c*(sharpData.h₁+1)+sharpData.s/12 := by
    have h₁ := mul_nonneg (sub_nonneg.2 hcu') (by linarith only [hh₁u] : 0 ≤ -(sharpData.h₁+1))
    have h₂ := mul_le_mul_of_nonneg_left (by linarith only [hh₁] : -36797/100000 ≤ sharpData.h₁+1)
      (by norm_num : (0:ℝ) ≤ 99242/100000)
    linarith only [hs, hh₁, h₁]
  dsimp only [x₃]
  exact ⟨by linarith only [hx₁, hx₂u],by linarith only [hx₁u, hx₂],by linarith only [hx₂],
    by linarith only [hx₂u],by linarith only [hh₁],by linarith only [hh₁u],
    by linarith only [hx₂, hx₄u],by linarith only [hy.1],by linarith only [hy₃],
    by linarith only [hH],by linarith only [hG],hL'⟩

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

theorem exterior_separator {p : EqualityParameters} (hp : p.Admissible sharpData)
    (i j : Fin 7) (hij : i<j) :
    exteriorNormal sharpData i j≠(0,0) ∧
      width (sharpData.exteriorSquares p.z p.eta i) (exteriorNormal sharpData i j)+
      width (sharpData.exteriorSquares p.z p.eta j) (exteriorNormal sharpData i j)≤
        dot (exteriorNormal sharpData i j)
          (sub (sharpData.exteriorCenters p.z p.eta j) (sharpData.exteriorCenters p.z p.eta i)) := by
  obtain ⟨hY0,hY1,hTx,hTxu,hGx,hGxu,hED,hyB,hyD,hHtop,hGtop,hGleft⟩ := sharp_exterior_bounds
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  have hη : sharpData.h₂+p.eta ≤ -13/12 := by
    have h := hp.tilted_upper
    dsimp [etaMax] at h
    linarith only [h]
  have hz := hp.top_lower
  have hηc := mul_le_mul_of_nonneg_left hη (by linarith only [hY0, hx₁u, hx₂, hc] : 0 ≤ sharpData.c)
  have hηs := mul_le_mul_of_nonneg_left hη (by linarith only [hY0, hx₁u, hx₂, hs] : 0 ≤ sharpData.s)
  have hunit := sharpData.unit
  have hHG := sharpData.HG_contact p.eta
  have hHA := sharpData.HA_contact
  have hGA := sharpData.GA_contact p.eta
  have hHE := sharpData.HE_contact
  have hcp : 0 < sharpData.c := by linarith only [hY0, hx₁u, hx₂, hc]
  have hsp : 0 < sharpData.s := by linarith only [hY0, hx₁u, hx₂, hs]
  have hw (S : UnitSquare) (a b : ℝ) :
      width S (a,b) = (|S.cosine*a+S.sine*b|+|-S.sine*a+S.cosine*b|)/2 := rfl
  have he : sharpData.e = (sharpData.c,sharpData.s) := rfl
  have hf : sharpData.f = (-sharpData.s,sharpData.c) := rfl
  have wTe (v : Point) : width (sharpData.tiltedSquare v) sharpData.e = 1/2 := by
    rw [he,hw]
    change (|sharpData.c*sharpData.c+sharpData.s*sharpData.s|+
      |-sharpData.s*sharpData.c+sharpData.c*sharpData.s|)/2 = 1/2
    rw [show sharpData.c*sharpData.c+sharpData.s*sharpData.s = 1 by linear_combination hunit,
      show -sharpData.s*sharpData.c+sharpData.c*sharpData.s = 0 by ring]
    norm_num
  have wAe (v : Point) : width (axisSquare v) sharpData.e = (sharpData.c+sharpData.s)/2 := by
    rw [he,hw]
    change (|1*sharpData.c+0*sharpData.s|+|-0*sharpData.c+1*sharpData.s|)/2 = _
    rw [show 1*sharpData.c+0*sharpData.s = sharpData.c by ring,
      show -0*sharpData.c+1*sharpData.s = sharpData.s by ring,abs_of_pos hcp,abs_of_pos hsp]
  have wTf (v : Point) : width (sharpData.tiltedSquare v) sharpData.f = 1/2 := by
    rw [hf,hw]
    change (|sharpData.c*(-sharpData.s)+sharpData.s*sharpData.c|+
      |-sharpData.s*(-sharpData.s)+sharpData.c*sharpData.c|)/2 = 1/2
    rw [show sharpData.c*(-sharpData.s)+sharpData.s*sharpData.c = 0 by ring,
      show -sharpData.s*(-sharpData.s)+sharpData.c*sharpData.c = 1 by linear_combination hunit]
    norm_num
  have wAf (v : Point) : width (axisSquare v) sharpData.f = (sharpData.c+sharpData.s)/2 := by
    rw [hf,hw]
    change (|1*(-sharpData.s)+0*sharpData.c|+|-0*(-sharpData.s)+1*sharpData.c|)/2 = _
    rw [show 1*(-sharpData.s)+0*sharpData.c = -sharpData.s by ring,
      show -0*(-sharpData.s)+1*sharpData.c = sharpData.c by ring,abs_neg,abs_of_pos hcp,
      abs_of_pos hsp]
    ring
  have wTy (v : Point) : width (sharpData.tiltedSquare v) ((0,1):Point) =
      (sharpData.c+sharpData.s)/2 := by
    rw [hw]
    change (|sharpData.c*0+sharpData.s*1|+|-sharpData.s*0+sharpData.c*1|)/2 = _
    rw [show sharpData.c*0+sharpData.s*1 = sharpData.s by ring,
      show -sharpData.s*0+sharpData.c*1 = sharpData.c by ring,abs_of_pos hcp,abs_of_pos hsp]
    ring
  have wAy (v : Point) : width (axisSquare v) ((0,1):Point) = 1/2 := by
    rw [hw]; change (|1*0+0*1|+|-0*0+1*1|)/2 = (1/2:ℝ); norm_num
  have wAmy (v : Point) : width (axisSquare v) ((0,-1):Point) = 1/2 := by
    rw [hw]; change (|1*0+0*(-1)|+|-0*0+1*(-1)|)/2 = (1/2:ℝ); norm_num
  have wTmx (v : Point) : width (sharpData.tiltedSquare v) ((-1,0):Point) =
      (sharpData.c+sharpData.s)/2 := by
    rw [hw]
    change (|sharpData.c*(-1)+sharpData.s*0|+|-sharpData.s*(-1)+sharpData.c*0|)/2 = _
    rw [show sharpData.c*(-1)+sharpData.s*0 = -sharpData.c by ring,
      show -sharpData.s*(-1)+sharpData.c*0 = sharpData.s by ring,abs_neg,abs_of_pos hcp,
      abs_of_pos hsp]
  have wAmx (v : Point) : width (axisSquare v) ((-1,0):Point) = 1/2 := by
    rw [hw]; change (|1*(-1)+0*0|+|-0*(-1)+1*0|)/2 = (1/2:ℝ); norm_num
  have ne_e : sharpData.e ≠ (0,0) := by
    rw [he]; intro h; have := congrArg Prod.fst h; simp only at this; linarith only [hY0, hx₁u,
      hx₂, hc, this]
  have ne_f : sharpData.f ≠ (0,0) := by
    rw [hf]; intro h; have := congrArg Prod.snd h; simp only at this; linarith only [hY0, hx₁u,
      hx₂, hc, this]
  have ne_y : ((0,1):Point) ≠ (0,0) := by simp
  have ne_my : ((0,-1):Point) ≠ (0,0) := by simp
  have ne_mx : ((-1,0):Point) ≠ (0,0) := by simp
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · refine ⟨ne_e,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) sharpData.e+width (sharpData.tiltedSquare (sharpData.pG p.eta)) sharpData.e ≤ dot sharpData.e (sub (sharpData.pG p.eta) (sharpData.pH))
    rw [wTe,wTe]
    rw [hHG]; norm_num
  · refine ⟨ne_e,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) sharpData.e+width (axisSquare sharpData.pA) sharpData.e ≤ dot sharpData.e (sub (sharpData.pA) (sharpData.pH))
    rw [wTe,wAe]
    rw [hHA]; linarith only [hY0, hx₁u, hx₂]
  · refine ⟨ne_y,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) ((0,1):Point) + width (axisSquare sharpData.pB) ((0,1):Point) ≤ dot ((0,1):Point) (sub (sharpData.pB) (sharpData.pH))
    rw [wTy,wAy]
    simp only [dot,sub,pB,pH,inFrame]
    linarith only [hyB, hHtop]
  · refine ⟨ne_y,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) ((0,1):Point) + width (axisSquare (sharpData.pT p.z)) ((0,1):Point) ≤ dot ((0,1):Point) (sub (sharpData.pT p.z) (sharpData.pH))
    rw [wTy,wAy]
    simp only [dot,sub,pH,pT,inFrame]
    linarith only [hY0, hHtop, hx₁u, hx₂, hz]
  · refine ⟨ne_y,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) ((0,1):Point) + width (axisSquare sharpData.pD) ((0,1):Point) ≤ dot ((0,1):Point) (sub (sharpData.pD) (sharpData.pH))
    rw [wTy,wAy]
    simp only [dot,sub,pD,pH,inFrame,x₃]
    linarith only [hY0, hHtop, hx₁u, hx₂, hy₃]
  · refine ⟨ne_f,?_⟩
    show width (sharpData.tiltedSquare sharpData.pH) sharpData.f+width (axisSquare sharpData.pE) sharpData.f ≤ dot sharpData.f (sub (sharpData.pE) (sharpData.pH))
    rw [wTf,wAf]
    rw [hHE]; linarith only []
  · refine ⟨ne_e,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG p.eta)) sharpData.e+width (axisSquare sharpData.pA) sharpData.e ≤ dot sharpData.e (sub (sharpData.pA) (sharpData.pG p.eta))
    rw [wTe,wAe]
    rw [hGA]; linarith only []
  · refine ⟨ne_y,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG p.eta)) ((0,1):Point) + width (axisSquare sharpData.pB) ((0,1):Point) ≤ dot ((0,1):Point) (sub (sharpData.pB) (sharpData.pG p.eta))
    rw [wTy,wAy]
    simp only [dot,sub,pB,pG,inFrame]
    linarith only [hyB, hGtop, hηc]
  · refine ⟨ne_y,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG p.eta)) ((0,1):Point) + width (axisSquare (sharpData.pT p.z)) ((0,1):Point) ≤ dot ((0,1):Point) (sub (sharpData.pT p.z) (sharpData.pG p.eta))
    rw [wTy,wAy]
    simp only [dot,sub,pT,pG,inFrame]
    linarith only [hY0, hGtop, hx₁u, hx₂, hz, hηc]
  · refine ⟨ne_y,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG p.eta)) ((0,1):Point) + width (axisSquare sharpData.pD) ((0,1):Point) ≤ dot ((0,1):Point) (sub (sharpData.pD) (sharpData.pG p.eta))
    rw [wTy,wAy]
    simp only [dot,sub,pD,pG,inFrame,x₃]
    linarith only [hY0, hGtop, hx₁u, hx₂, hy₃, hηc]
  · refine ⟨ne_mx,?_⟩
    show width (sharpData.tiltedSquare (sharpData.pG p.eta)) ((-1,0):Point)+width (axisSquare sharpData.pE) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pE) (sharpData.pG p.eta))
    rw [wTmx,wAmx]
    simp only [dot,sub,pE,pG,inFrame,y₄]
    linarith only [hY0, hGleft, hx₁u, hx₂, hx₄u, hηs]
  · refine ⟨ne_y,?_⟩
    show width (axisSquare sharpData.pA) ((0,1):Point) + width (axisSquare sharpData.pB) ((0,1):Point) ≤ dot ((0,1):Point) (sub (sharpData.pB) (sharpData.pA))
    rw [wAy,wAy]
    simp only [dot,sub,pA,pB]
    linarith only []
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare sharpData.pA) ((-1,0):Point)+width (axisSquare (sharpData.pT p.z)) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pT p.z) (sharpData.pA))
    rw [wAmx,wAmx]
    simp only [dot,sub,pA,pT]
    linarith only [hY0]
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare sharpData.pA) ((-1,0):Point)+width (axisSquare sharpData.pD) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pD) (sharpData.pA))
    rw [wAmx,wAmx]
    simp only [dot,sub,pA,pD,x₃]
    linarith only [hY0, hx₁u, hx₂]
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare sharpData.pA) ((-1,0):Point)+width (axisSquare sharpData.pE) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pE) (sharpData.pA))
    rw [wAmx,wAmx]
    simp only [dot,sub,pA,pE,y₄]
    linarith only [hY0, hx₁u, hx₂, hx₄u]
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare sharpData.pB) ((-1,0):Point)+width (axisSquare (sharpData.pT p.z)) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pT p.z) (sharpData.pB))
    rw [wAmx,wAmx]
    simp only [dot,sub,pB,pT]
    linarith only []
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare sharpData.pB) ((-1,0):Point)+width (axisSquare sharpData.pD) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pD) (sharpData.pB))
    rw [wAmx,wAmx]
    simp only [dot,sub,pB,pD,x₃]
    linarith only [hY0, hx₁u, hx₂]
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare sharpData.pB) ((-1,0):Point)+width (axisSquare sharpData.pE) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pE) (sharpData.pB))
    rw [wAmx,wAmx]
    simp only [dot,sub,pB,pE,y₄]
    linarith only [hY0, hx₁u, hx₂, hx₄u]
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare (sharpData.pT p.z)) ((-1,0):Point)+width (axisSquare sharpData.pD) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pD) (sharpData.pT p.z))
    rw [wAmx,wAmx]
    simp only [dot,sub,pD,pT,x₃]
    linarith only []
  · refine ⟨ne_mx,?_⟩
    show width (axisSquare (sharpData.pT p.z)) ((-1,0):Point)+width (axisSquare sharpData.pE) ((-1,0):Point) ≤ dot ((-1,0):Point) (sub (sharpData.pE) (sharpData.pT p.z))
    rw [wAmx,wAmx]
    simp only [dot,sub,pE,pT,y₄]
    linarith only [hY0, hx₁u, hx₂, hx₄u]
  · refine ⟨ne_my,?_⟩
    show width (axisSquare sharpData.pD) ((0,-1):Point)+width (axisSquare sharpData.pE) ((0,-1):Point) ≤ dot ((0,-1):Point) (sub (sharpData.pE) (sharpData.pD))
    rw [wAmy,wAmy]
    simp only [dot,sub,pD,pE,x₃,y₄]
    linarith only []

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

end SquaresInCircles.Eight.Stationary
end
end
end

section
/-!
## Bounds on the box of parameters

Eighteen quantities of the model, as functions of the parameters (`boxData`): the cosine and sine
of the central frame and of its angle to the frame of `H` and `G`, the coordinates of the centre in
the frame of the central square, the seven separation margins of the central square, the room
left in the containment of `T` and `G`, the height of the highest point of `H`, and the height of
the highest point and the abscissa of the leftmost point of `G` when `eta = etaMax`. They are the
interval expressions of `Generated/EqualityBox.lean` (`box_interpretation`), so on the box `InBox`
each lies between the rational bounds `boxLower` and `boxUpper` (`box_data_bounds`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.Stationary
open Coordinates EqualityParameters Arithmetic

def rawTiltWidth (p : EqualityParameters) : ℝ :=
  (1+sharpData.c*p.C+sharpData.s*p.S+sharpData.c*p.S-sharpData.s*p.C)/2

def boxData (p : EqualityParameters) : Fin 18 → ℝ :=
  ![p.C,
    p.S,
    sharpData.c*p.C+sharpData.s*p.S,
    sharpData.c*p.S-sharpData.s*p.C,
    p.C*p.x+p.S*p.y,
    -p.S*p.x+p.C*p.y,
    (sharpData.pA).1-p.x-(1+p.C+p.S)/2,
    p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y)-(1+p.C+p.S)/2,
    -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y)-(1+p.C+p.S)/2,
    -((sharpData.pE).1-p.x)-(1+p.C+p.S)/2,
    -p.C*((sharpData.pH).1-p.x)-p.S*((sharpData.pH).2-p.y)-rawTiltWidth p,
    sharpData.s*((sharpData.pG p.eta).1-p.x)-sharpData.c*((sharpData.pG p.eta).2-p.y)-rawTiltWidth p,
    p.z-p.y-(1+p.C+p.S)/2,
    qStar-((sharpData.x₂-1)^2+(p.z+1/2)^2),
    qStar-((sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2),
    sharpData.s*(sharpData.h₁+1)+sharpData.c*(sharpData.h₂+1),
    sharpData.s*(sharpData.h₁+2)-sharpData.c/12,
    sharpData.c*(sharpData.h₁+1)+sharpData.s/12]
def boxLower : Fin 18 → ℝ := ![(979/1000),(39/200),(99/100),(9/125),(-139/1000),(-3/100),(1/100),(1/100),(1/100),(1/100),(1/100),(1/100),(1/100),(11/200),(56/125),-1,(-1/100),(-71/200)]
def boxUpper : Fin 18 → ℝ := ![(981/1000),(201/1000),1,(2/25),(139/1000),(3/100),1,1,1,1,1,1,1,(2/25),(12/25),(-3/10),(-1/250),(-7/20)]
def boxExpressions : Fin 18 → ScalarExpr 8 := ![EqualityGenerated.centralCosineExpression, EqualityGenerated.centralSineExpression, EqualityGenerated.relativeCosineExpression, EqualityGenerated.relativeSineExpression, EqualityGenerated.coreFirstExpression, EqualityGenerated.coreSecondExpression, EqualityGenerated.AMarginExpression, EqualityGenerated.BMarginExpression, EqualityGenerated.DMarginExpression, EqualityGenerated.EMarginExpression, EqualityGenerated.HMarginExpression, EqualityGenerated.GMarginExpression, EqualityGenerated.TMarginExpression, EqualityGenerated.topDiskReserveExpression, EqualityGenerated.tiltedDiskReserveExpression, EqualityGenerated.topHExpression, EqualityGenerated.topGExpression, EqualityGenerated.leftGExpression]

private theorem box_interpretation_0 (p : EqualityParameters) :
    (boxExpressions 0).eval (boxEnv p)=boxData p 0 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.centralCosineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero]
  push_cast
  ring_nf

private theorem box_interpretation_1 (p : EqualityParameters) :
    (boxExpressions 1).eval (boxEnv p)=boxData p 1 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.centralSineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_2 (p : EqualityParameters) :
    (boxExpressions 2).eval (boxEnv p)=boxData p 2 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.relativeCosineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_3 (p : EqualityParameters) :
    (boxExpressions 3).eval (boxEnv p)=boxData p 3 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.relativeSineExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_4 (p : EqualityParameters) :
    (boxExpressions 4).eval (boxEnv p)=boxData p 4 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.coreFirstExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_5 (p : EqualityParameters) :
    (boxExpressions 5).eval (boxEnv p)=boxData p 5 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.coreSecondExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_6 (p : EqualityParameters) :
    (boxExpressions 6).eval (boxEnv p)=boxData p 6 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.AMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_7 (p : EqualityParameters) :
    (boxExpressions 7).eval (boxEnv p)=boxData p 7 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.BMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_8 (p : EqualityParameters) :
    (boxExpressions 8).eval (boxEnv p)=boxData p 8 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.DMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_9 (p : EqualityParameters) :
    (boxExpressions 9).eval (boxEnv p)=boxData p 9 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.EMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_10 (p : EqualityParameters) :
    (boxExpressions 10).eval (boxEnv p)=boxData p 10 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.HMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_11 (p : EqualityParameters) :
    (boxExpressions 11).eval (boxEnv p)=boxData p 11 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.GMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_12 (p : EqualityParameters) :
    (boxExpressions 12).eval (boxEnv p)=boxData p 12 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.TMarginExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val]
  push_cast
  ring_nf

private theorem box_interpretation_13 (p : EqualityParameters) :
    (boxExpressions 13).eval (boxEnv p)=boxData p 13 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.topDiskReserveExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_14 (p : EqualityParameters) :
    (boxExpressions 14).eval (boxEnv p)=boxData p 14 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.tiltedDiskReserveExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_15 (p : EqualityParameters) :
    (boxExpressions 15).eval (boxEnv p)=boxData p 15 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.topHExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_16 (p : EqualityParameters) :
    (boxExpressions 16).eval (boxEnv p)=boxData p 16 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.topGExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

private theorem box_interpretation_17 (p : EqualityParameters) :
    (boxExpressions 17).eval (boxEnv p)=boxData p 17 := by
  simp only [boxExpressions,boxData,rawTiltWidth,EqualityGenerated.leftGExpression,
    ScalarExpr.eval,boxEnv,sharpData,radicalCoordinates,EqualityParameters.C,EqualityParameters.S,
    c,s,h₁,h₂,y₄,pA,pB,pD,pE,pH,pG,inFrame,x₃,halfAngleCos,halfAngleSin,div_eq_mul_inv,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring_nf

theorem box_interpretation (p : EqualityParameters) (i : Fin 18) :
    (boxExpressions i).eval (boxEnv p)=boxData p i := by
  fin_cases i
  · exact box_interpretation_0 p
  · exact box_interpretation_1 p
  · exact box_interpretation_2 p
  · exact box_interpretation_3 p
  · exact box_interpretation_4 p
  · exact box_interpretation_5 p
  · exact box_interpretation_6 p
  · exact box_interpretation_7 p
  · exact box_interpretation_8 p
  · exact box_interpretation_9 p
  · exact box_interpretation_10 p
  · exact box_interpretation_11 p
  · exact box_interpretation_12 p
  · exact box_interpretation_13 p
  · exact box_interpretation_14 p
  · exact box_interpretation_15 p
  · exact box_interpretation_16 p
  · exact box_interpretation_17 p

theorem box_data_bounds {p : EqualityParameters} (hp : p.InBox) (i : Fin 18) :
    boxLower i≤boxData p i ∧ boxData p i≤boxUpper i := by
  have he := boxEnv_mem hp
  rw [← box_interpretation p i]
  fin_cases i
  · exact EqualityGenerated.centralCosine_bound _ he
  · exact EqualityGenerated.centralSine_bound _ he
  · exact EqualityGenerated.relativeCosine_bound _ he
  · exact EqualityGenerated.relativeSine_bound _ he
  · exact EqualityGenerated.coreFirst_bound _ he
  · exact EqualityGenerated.coreSecond_bound _ he
  · exact EqualityGenerated.AMargin_bound _ he
  · exact EqualityGenerated.BMargin_bound _ he
  · exact EqualityGenerated.DMargin_bound _ he
  · exact EqualityGenerated.EMargin_bound _ he
  · exact EqualityGenerated.HMargin_bound _ he
  · exact EqualityGenerated.GMargin_bound _ he
  · exact EqualityGenerated.TMargin_bound _ he
  · exact EqualityGenerated.topDiskReserve_bound _ he
  · exact EqualityGenerated.tiltedDiskReserve_bound _ he
  · exact EqualityGenerated.topH_bound _ he
  · exact EqualityGenerated.topG_bound _ he
  · exact EqualityGenerated.leftG_bound _ he

end SquaresInCircles.Eight.Stationary
end
end
end

section
@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight
open Stationary Coordinates EqualityParameters

theorem box_admissible {p : EqualityParameters} (hp : p.InBox) : p.Admissible sharpData := by
  have b0 : (979/1000:ℝ) ≤ p.C ∧ p.C ≤ 981/1000 := box_data_bounds hp 0
  have b1 : (39/200:ℝ) ≤ p.S ∧ p.S ≤ 201/1000 := box_data_bounds hp 1
  have b2 : (99/100:ℝ) ≤ sharpData.c*p.C+sharpData.s*p.S ∧
      sharpData.c*p.C+sharpData.s*p.S ≤ 1 := box_data_bounds hp 2
  have b3 : (9/125:ℝ) ≤ sharpData.c*p.S-sharpData.s*p.C ∧
      sharpData.c*p.S-sharpData.s*p.C ≤ 2/25 := box_data_bounds hp 3
  have b4 : (-139/1000:ℝ) ≤ p.C*p.x+p.S*p.y ∧ p.C*p.x+p.S*p.y ≤ 139/1000 :=
    box_data_bounds hp 4
  have b5 : (-3/100:ℝ) ≤ -p.S*p.x+p.C*p.y ∧ -p.S*p.x+p.C*p.y ≤ 3/100 :=
    box_data_bounds hp 5
  have b6 : (1/100:ℝ) ≤ (sharpData.pA).1-p.x-(1+p.C+p.S)/2 ∧
      (sharpData.pA).1-p.x-(1+p.C+p.S)/2 ≤ 1 := box_data_bounds hp 6
  have b7 : (1/100:ℝ) ≤ p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y)-(1+p.C+p.S)/2 ∧
      p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y)-(1+p.C+p.S)/2 ≤ 1 :=
    box_data_bounds hp 7
  have b8 : (1/100:ℝ) ≤ -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y)-(1+p.C+p.S)/2 ∧
      -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y)-(1+p.C+p.S)/2 ≤ 1 :=
    box_data_bounds hp 8
  have b9 : (1/100:ℝ) ≤ -((sharpData.pE).1-p.x)-(1+p.C+p.S)/2 ∧
      -((sharpData.pE).1-p.x)-(1+p.C+p.S)/2 ≤ 1 := box_data_bounds hp 9
  have b10 : (1/100:ℝ) ≤ -p.C*((sharpData.pH).1-p.x)-p.S*((sharpData.pH).2-p.y)-rawTiltWidth p ∧
      -p.C*((sharpData.pH).1-p.x)-p.S*((sharpData.pH).2-p.y)-rawTiltWidth p ≤ 1 :=
    box_data_bounds hp 10
  have b11 : (1/100:ℝ) ≤ sharpData.s*((sharpData.pG p.eta).1-p.x)-
        sharpData.c*((sharpData.pG p.eta).2-p.y)-rawTiltWidth p ∧
      sharpData.s*((sharpData.pG p.eta).1-p.x)-
        sharpData.c*((sharpData.pG p.eta).2-p.y)-rawTiltWidth p ≤ 1 :=
    box_data_bounds hp 11
  have b12 : (1/100:ℝ) ≤ p.z-p.y-(1+p.C+p.S)/2 ∧ p.z-p.y-(1+p.C+p.S)/2 ≤ 1 :=
    box_data_bounds hp 12
  have b13 : (11/200:ℝ) ≤ qStar-((sharpData.x₂-1)^2+(p.z+1/2)^2) ∧
      qStar-((sharpData.x₂-1)^2+(p.z+1/2)^2) ≤ 2/25 := box_data_bounds hp 13
  have b14 : (56/125:ℝ) ≤ qStar-((sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2) ∧
      qStar-((sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2) ≤ 12/25 := box_data_bounds hp 14
  have hW0 : p.W₀=(1+p.C+p.S)/2 := by rw [W₀,abs_of_pos (by linarith : 0< p.S)]
  have hWt : p.Wₜ sharpData=rawTiltWidth p := by
    rw [Wₜ,abs_of_pos (by linarith : 0< sharpData.c*p.S-sharpData.s*p.C)]
    dsimp [rawTiltWidth]; ring
  have hsqrt := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hsqrt0 := Real.sqrt_nonneg (2:ℝ)
  have hh := sharp_coordinates
  have htopRad : 0≤ qStar-(sharpData.x₂-1)^2 := by
    nlinarith only [b13.1,sq_nonneg (p.z+1/2)]
  have htiltRad : 0≤ qStar-(sharpData.h₁+2)^2 := by
    nlinarith only [b14.1,sq_nonneg (sharpData.h₂+p.eta)]
  refine {
    frame_lower := by nlinarith only [hp.2.2.1.1,hsqrt,hsqrt0]
    frame_upper := by nlinarith only [hp.2.2.1.2,hsqrt,hsqrt0]
    top_lower := by linarith [hp.2.2.2.1.1]
    top_upper := ?_
    tilted_lower := ?_
    tilted_upper := ?_
    core_first := by rw [abs_lt]; exact ⟨by linarith,by linarith⟩
    core_second := by rw [abs_lt]; exact ⟨by linarith,by linarith⟩
    A_sep := ?_
    B_sep := ?_
    D_sep := ?_
    E_sep := ?_
    T_sep := ?_
    H_sep := ?_
    G_sep := ?_ }
  · dsimp [zMax]
    change p.z≤ Real.sqrt (qStar-(sharpData.x₂-1)^2)-1/2
    have hz0 : 0 ≤ p.z+1/2 := by linarith [hp.2.2.2.1.1]
    have hle : p.z+1/2 ≤ Real.sqrt (qStar-(sharpData.x₂-1)^2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [b13.1])
    linarith
  · dsimp [etaMin]
    change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤ p.eta
    have hle : -(sharpData.h₂+p.eta) ≤ Real.sqrt (qStar-(sharpData.h₁+2)^2) :=
      Real.le_sqrt_of_sq_le (by nlinarith only [b14.1])
    linarith
  · dsimp [etaMax]
    linarith [hp.2.2.2.2.2,hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤ (sharpData.pA).1-p.x)
    exact (le_abs_self _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤
      p.C*((sharpData.pB).1-p.x)+p.S*((sharpData.pB).2-p.y))
    exact (le_abs_self _).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤
      -p.S*((sharpData.pD).1-p.x)+p.C*((sharpData.pD).2-p.y))
    exact (le_abs_self _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤ -((sharpData.pE).1-p.x))
    exact (neg_le_abs _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hW0]
    apply le_trans (by linarith : (1+p.C+p.S)/2≤ p.z-p.y)
    exact (le_abs_self _).trans ((le_max_right _ _).trans (le_max_left _ _))
  · rw [hWt]
    apply le_trans (by linarith : rawTiltWidth p≤
      -(p.C*((sharpData.pH).1-p.x)+p.S*((sharpData.pH).2-p.y)))
    exact (neg_le_abs _).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [hWt]
    apply le_trans (by linarith : rawTiltWidth p≤
      -(-sharpData.s*((sharpData.pG p.eta).1-p.x)+sharpData.c*((sharpData.pG p.eta).2-p.y)))
    exact (neg_le_abs _).trans ((le_max_right _ _).trans (le_max_left _ _))

theorem sample_admissible : sampleParameters.Admissible sharpData :=
  box_admissible sampleParameters_inBox

theorem containsCore_center_bounds {K : UnitSquare} (hc : ContainsCore K) :
    alpha K (0,0)<5/12 ∧ beta K (0,0)<5/12 := by
  have hunit := K.unit
  have hnorm (a b : ℝ) (h : a^2+b^2≤(1/12:ℝ)^2) :
      normSq (rotate K (a,b))≤coreRadius^2 := by
    dsimp [normSq,rotate,coreRadius]
    nlinarith [hunit]
  have hXp := hc (rotate K (1/12,0)) (hnorm _ _ (by norm_num))
  have hXm := hc (rotate K (-1/12,0)) (hnorm _ _ (by norm_num))
  have hYp := hc (rotate K (0,1/12)) (hnorm _ _ (by norm_num))
  have hYm := hc (rotate K (0,-1/12)) (hnorm _ _ (by norm_num))
  have hloc (a b : ℝ) :
      localX K (rotate K (a,b))=a+localX K (0,0) ∧
      localY K (rotate K (a,b))=b+localY K (0,0) := by
    constructor <;> dsimp [localX,localY,rotate] <;>
      first | linear_combination a*K.unit | linear_combination b*K.unit
  rw [openSquare,(hloc _ _).1] at hXp hXm
  rw [openSquare,(hloc _ _).2] at hYp hYm
  have hxp := abs_lt.mp hXp.1
  have hxm := abs_lt.mp hXm.1
  have hyp := abs_lt.mp hYp.2
  have hym := abs_lt.mp hYm.2
  constructor
  · change |localX K (0,0)|<5/12
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · change |localY K (0,0)|<5/12
    exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- The admissibility conditions are necessary: if the model of `p` is a packing at the squared
radius `qStar`, its central square contains the core disk, its frame parameter `w` lies in
`[1 - √2, √2 - 1)`, and the sliders have `7/12 ≤ z` and `eta ≤ etaMax`, then `p` is admissible. It
is applied once the stationary identity on the original centres and the cyclic order have placed
the two sliders. -/
theorem admissible_of_original_geometry {p : EqualityParameters}
    (hp : SqPacking (p.model sharpData) (0,0) qStar)
    (hcore : ContainsCore p.centralSquare)
    (hframe : 1-Real.sqrt 2≤p.w ∧ p.w<Real.sqrt 2-1)
    (hT : 7/12≤p.z) (hG : p.eta≤ sharpData.etaMax) : p.Admissible sharpData := by
  have hcont (i : Fin 8) : SqContained qStar (p.model sharpData i) := by
    apply (SqContained.iff_points hp.1 _).mpr
    intro x hx
    simpa [sub] using hp.2.1 i x hx
  have hTcont := hcont 5
  have hGcont := hcont 2
  have hbounds := sharp_exterior_bounds
  have hcore' := containsCore_center_bounds hcore
  obtain ⟨hcx,hcy⟩ := p.central_core_coordinates
  rw [hcx,hcy] at hcore'
  have hTpoly : (sharpData.x₂-1)^2+(p.z+1/2)^2≤ qStar := by
    change SqContained qStar (axisSquare (sharpData.pT p.z)) at hTcont
    rw [axis_containment] at hTcont
    simp only [pT] at hTcont
    rw [abs_of_pos (by linarith [hbounds.2.2.1] : 0< sharpData.x₂-3/2),
      abs_of_pos (by linarith : 0< p.z),
      show sharpData.x₂-3/2+1/2=sharpData.x₂-1 by ring] at hTcont
    exact hTcont
  have hGneg : sharpData.h₂+1/2+p.eta<0 := by
    dsimp [etaMax] at hG
    linarith
  have hGpoly : (sharpData.h₁+2)^2+(sharpData.h₂+p.eta)^2≤ qStar := by
    change SqContained qStar (sharpData.tiltedSquare (sharpData.pG p.eta)) at hGcont
    rw [pG,tilted_containment] at hGcont
    rw [abs_of_pos hbounds.2.2.2.2.1,abs_of_neg hGneg] at hGcont
    nlinarith
  have hTrad : 0≤ qStar-(sharpData.x₂-1)^2 := by nlinarith [sq_nonneg (p.z+1/2)]
  have hGrad : 0≤ qStar-(sharpData.h₁+2)^2 := by nlinarith [sq_nonneg (sharpData.h₂+p.eta)]
  refine {
    frame_lower := hframe.1
    frame_upper := hframe.2
    top_lower := hT
    top_upper := ?_
    tilted_lower := ?_
    tilted_upper := hG
    core_first := hcore'.1
    core_second := hcore'.2
    A_sep := (central_axis_sat hframe sharpData.pA).1 ?_
    B_sep := (central_axis_sat hframe sharpData.pB).1 ?_
    D_sep := (central_axis_sat hframe sharpData.pD).1 ?_
    E_sep := (central_axis_sat hframe sharpData.pE).1 ?_
    T_sep := (central_axis_sat hframe (sharpData.pT p.z)).1 ?_
    H_sep := (central_tilted_sat hframe sharpData.pH).1 ?_
    G_sep := (central_tilted_sat hframe (sharpData.pG p.eta)).1 ?_ }
  · dsimp [zMax]
    change p.z≤ Real.sqrt (qStar-(sharpData.x₂-1)^2)-1/2
    nlinarith [Real.sq_sqrt hTrad,Real.sqrt_nonneg (qStar-(sharpData.x₂-1)^2)]
  · dsimp [etaMin]
    change -sharpData.h₂-Real.sqrt (qStar-(sharpData.h₁+2)^2)≤ p.eta
    nlinarith [Real.sq_sqrt hGrad,Real.sqrt_nonneg (qStar-(sharpData.h₁+2)^2)]
  · simpa [EqualityParameters.model] using hp.2.2 0 3 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 4 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 6 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 7 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 5 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 1 (by decide)
  · simpa [EqualityParameters.model] using hp.2.2 0 2 (by decide)

def stationaryRadius : ℝ := Real.sqrt qStar
def stationaryReflectedModel (reflected : Bool) (p : EqualityParameters) : Fin 8 → UnitSquare :=
  if reflected then fun i=>reflectDiagonalSquare (p.model sharpData i) else p.model sharpData
def stationaryModels : Set (Fin 8 → UnitSquare) :=
  {M | ∃ reflected : Bool, ∃ p : EqualityParameters,
    p.Admissible sharpData ∧ M=stationaryReflectedModel reflected p}
def attainingModel : Fin 8 → UnitSquare := sampleParameters.model sharpData

theorem models_nonempty : stationaryModels.Nonempty :=
  ⟨attainingModel,false,sampleParameters,sample_admissible,rfl⟩

theorem model_packing (M : Fin 8 → UnitSquare) (hM : M∈stationaryModels) :
    Packing M (0,0) stationaryRadius := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  have h := (sqPacking_iff_packing _ _ (by linarith [qStar_limits.1])).mp (model_sqPacking hp)
  cases b
  · exact h
  · exact packing_reflectDiagonal h

theorem unreflected_model_reaches (p : EqualityParameters) :
    ∃ i x, closedSquare (p.model sharpData i) x ∧ stationaryRadius^2≤normSq x := by
  refine ⟨3,(sharpData.x₁,sharpData.y),?_,?_⟩
  · norm_num [EqualityParameters.model,axisSquare,closedSquare,localX,localY,pA]
  · rw [stationaryRadius,Real.sq_sqrt (by linarith [qStar_limits.1])]
    change qStar≤ sharpData.x₁^2+sharpData.y^2
    exact sharpData_stationary.first_circle.ge

theorem model_reaches (M : Fin 8 → UnitSquare) (hM : M∈stationaryModels) :
    ∃ i x, closedSquare (M i) x ∧ stationaryRadius^2≤normSq x := by
  obtain ⟨b,p,hp,rfl⟩ := hM
  obtain ⟨i,x,hx,hr⟩ := unreflected_model_reaches p
  cases b
  · exact ⟨i,x,hx,hr⟩
  · refine ⟨i,diagonalPoint x,?_,?_⟩
    · simpa [stationaryReflectedModel,reflectDiagonal_closed] using hx
    · simpa [normSq,diagonalPoint,add_comm] using hr

end SquaresInCircles.Eight
end
end
end
