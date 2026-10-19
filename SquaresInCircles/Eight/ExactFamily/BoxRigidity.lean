module

public import SquaresInCircles.Eight.Equality
public import SquaresInCircles.Common.DiskSupport

/-!
# Eight squares: distinct points of the box give non-congruent packings

If two points of the closed box `InBox` give models that are congruent by a distance-preserving
bijection of the plane, which may translate, rotate and reflect, together with a relabelling of
the squares, then the two points are equal (`box_rigid_parameters`, `box_rigidlyCongruent_iff`). The
positive circle weights of the stationary chain first recover the disk centre: the origin is the
only centre of a disk of radius `√qStar` that holds a model (`enclosing_center_unique`), so the
isometry fixes it. The squared distances of the eight centres from the origin lie in rational
bands (`center_band`), and the bands of `A` and `E` are disjoint from all others, so the isometry
fixes the centres of `A` and `E`. These are linearly independent, so by polarization the isometry is
the identity (`fixed_independent_points`). The remaining centres and the frame of the central
square, through its support widths, then give all five parameters.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Eight.ExactFamily.BoxRigidity
open Coordinates EqualityParameters

def midpoint (p r : Point) : Point := ((p.1+r.1)/2,(p.2+r.2)/2)

theorem midpoint_identity (p r c : Point) :
    normSq (sub p c)+normSq (sub r c)=
      normSq (sub p r)/2+2*normSq (sub (midpoint p r) c) := by
  dsimp [normSq,sub,midpoint]
  ring

theorem isometry_midpoint (e : Point ≃ Point)
    (he : ∀ p r, normSq (sub (e p) (e r))=normSq (sub p r)) (p r : Point) :
    e (midpoint p r)=midpoint (e p) (e r) := by
  have h₁ := he p (midpoint p r)
  have h₂ := he r (midpoint p r)
  have h₃ := he p r
  have hm := midpoint_identity (e p) (e r) (e (midpoint p r))
  have hpm : normSq (sub p (midpoint p r))=normSq (sub p r)/4 := by
    dsimp [normSq,sub,midpoint]; ring
  have hrm : normSq (sub r (midpoint p r))=normSq (sub p r)/4 := by
    dsimp [normSq,sub,midpoint]; ring
  have hn : normSq (sub (midpoint (e p) (e r)) (e (midpoint p r)))=0 := by
    rw [h₁,h₂,h₃,hpm,hrm] at hm
    linarith
  have hz := (zero_normSq_iff _).mp hn
  have hx := congrArg Prod.fst hz
  have hy := congrArg Prod.snd hz
  dsimp [sub] at hx hy
  exact Prod.ext (by linarith) (by linarith)

theorem closed_center_distance (K : UnitSquare) {p : Point} (hp : closedSquare K p) :
    normSq (sub p K.center)≤1/2 := by
  have hx : (localX K p)^2≤(1/2:ℝ)^2 := by
    have h := abs_le.mp hp.1
    linarith [mul_nonneg (by linarith only [h] : 0≤localX K p+1/2)
      (by linarith only [h] : 0≤1/2-localX K p)]
  have hy : (localY K p)^2≤(1/2:ℝ)^2 := by
    have h := abs_le.mp hp.2
    linarith [mul_nonneg (by linarith only [h] : 0≤localY K p+1/2)
      (by linarith only [h] : 0≤1/2-localY K p)]
  have hid : normSq (sub p K.center)=(localX K p)^2+(localY K p)^2 := by
    dsimp [normSq,sub,localX,localY]
    linear_combination -((p.1-K.center.1)^2+(p.2-K.center.2)^2)*K.unit
  rw [hid]
  linarith only [hx, hy]

/-- The centre is recovered from one pair of opposite vertices. This avoids
any choice of quarter-turn representative for the frame of the square. -/
theorem isometry_square_center (e : Point ≃ Point)
    (he : ∀ p r, normSq (sub (e p) (e r))=normSq (sub p r))
    (K L : UnitSquare) (himage : ∀ p, closedSquare K p→ closedSquare L (e p)) :
    e K.center=L.center := by
  let p := add K.center (rotate K (1/2,1/2))
  let r := add K.center (rotate K (-1/2,-1/2))
  have hp : closedSquare K p := by
    dsimp [p]
    rw [closedSquare,localX_rotated,localY_rotated]
    norm_num
  have hr : closedSquare K r := by
    dsimp [r]
    rw [closedSquare,localX_rotated,localY_rotated]
    norm_num
  have hmid : midpoint p r=K.center := by
    ext <;> dsimp [p,r,midpoint,add,rotate] <;> ring
  have hdist : normSq (sub p r)=2 := by
    dsimp [p,r,normSq,sub,add,rotate]
    linear_combination 2*K.unit
  have h₁ := closed_center_distance L (himage p hp)
  have h₂ := closed_center_distance L (himage r hr)
  have hm := midpoint_identity (e p) (e r) L.center
  rw [he p r,hdist,← isometry_midpoint e he p r,hmid] at hm
  have hz : normSq (sub (e K.center) L.center)=0 := by
    linarith [normSq_nonneg (sub (e K.center) L.center)]
  have hzero := (zero_normSq_iff _).mp hz
  apply Prod.ext <;>
    have hx := congrArg Prod.fst hzero <;> have hy := congrArg Prod.snd hzero <;>
    dsimp [sub] at hx hy <;> linarith

theorem same_closed_width {K L : UnitSquare}
    (hc : K.center=L.center) (hs : ∀ p,closedSquare K p↔closedSquare L p)
    (n : Point) : width K n=width L n := by
  have one_way (K L : UnitSquare) (hc : K.center=L.center)
      (h : ∀ p,closedSquare K p→ closedSquare L p) : width K n≤width L n := by
    obtain ⟨p,hp,he⟩ := exists_support_vertex K n
    have hb := closed_dot_bound L n (h p hp)
    have hb' := (abs_le.mp hb).2
    dsimp [dot,sub] at he hb'
    rw [hc] at he
    linarith
  exact le_antisymm (one_way K L hc (fun p=>(hs p).mp))
    (one_way L K hc.symm (fun p=>(hs p).mpr))

def anchorIndex : Fin 5 → Fin 8 := ![3,4,6,7,1]

theorem anchor_closed (p : EqualityParameters) (i : Fin 5) :
    closedSquare (p.model sharpData (anchorIndex i)) (sharpData.anchorPoints i) := by
  fin_cases i
  · norm_num [anchorIndex,model,anchorPoints,pA,axisSquare,closedSquare,localX,localY]
  · norm_num [anchorIndex,model,anchorPoints,pB,axisSquare,closedSquare,localX,localY]
  · norm_num [anchorIndex,model,anchorPoints,pD,axisSquare,closedSquare,localX,localY]
  · norm_num [anchorIndex,model,anchorPoints,pE,axisSquare,closedSquare,localX,localY]
  · change closedSquare (sharpData.tiltedSquare sharpData.pH)
      (sharpData.inFrame sharpData.h₁ sharpData.h₂)
    have hx : localX (sharpData.tiltedSquare sharpData.pH)
        (sharpData.inFrame sharpData.h₁ sharpData.h₂)= -1/2 := by
      dsimp [localX,tiltedSquare,pH,inFrame]
      linear_combination -(1/2:ℝ)*sharpData.unit
    have hy : localY (sharpData.tiltedSquare sharpData.pH)
        (sharpData.inFrame sharpData.h₁ sharpData.h₂)= -1/2 := by
      dsimp [localY,tiltedSquare,pH,inFrame]
      linear_combination -(1/2:ℝ)*sharpData.unit
    norm_num [closedSquare,hx,hy]

theorem anchor_barycenter :
    (∑ i : Fin 5,sharpData.mu i*(sharpData.anchorPoints i).1)=0 ∧
    (∑ i : Fin 5,sharpData.mu i*(sharpData.anchorPoints i).2)=0 := by
  have hw := sharpData_stationary.weightDomain
  have hs := sharpData_stationary.position_stationary
  have hx : (∑ i : Fin 5,(sharpData.forces i.castSucc.castSucc).1)=0 := by
    norm_num [Fin.sum_univ_succ,forces,rawForces,scale]
    ring
  have hy : (∑ i : Fin 5,(sharpData.forces i.castSucc.castSucc).2)=0 := by
    norm_num [Fin.sum_univ_succ,forces,rawForces,scale]
    ring
  simp only [force_balance hw hs,scale] at hx hy
  have ex : (∑ i : Fin 5,(-2*sharpData.mu i)*(sharpData.anchorPoints i).1)=
      -2*(∑ i : Fin 5,sharpData.mu i*(sharpData.anchorPoints i).1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have ey : (∑ i : Fin 5,(-2*sharpData.mu i)*(sharpData.anchorPoints i).2)=
      -2*(∑ i : Fin 5,sharpData.mu i*(sharpData.anchorPoints i).2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [ex] at hx
  rw [ey] at hy
  exact ⟨by linarith,by linarith⟩

theorem anchor_second_moment (o : Point) :
    (∑ i : Fin 5,sharpData.mu i*normSq (sub (sharpData.anchorPoints i) o))=
      qStar+normSq o := by
  have hmass := sharpData_stationary.weightDomain.mu_sum
  have hb := anchor_barycenter
  have hid : (∑ i : Fin 5,sharpData.mu i*normSq (sub (sharpData.anchorPoints i) o))=
      (∑ i : Fin 5,sharpData.mu i*normSq (sharpData.anchorPoints i))-
      2*o.1*(∑ i : Fin 5,sharpData.mu i*(sharpData.anchorPoints i).1)-
      2*o.2*(∑ i : Fin 5,sharpData.mu i*(sharpData.anchorPoints i).2)+
      normSq o*(∑ i : Fin 5,sharpData.mu i) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [normSq,sub]
    ring
  rw [hid,hb.1,hb.2,hmass]
  have hq : sharpData.q=qStar := rfl
  simp only [anchor_circle sharpData_stationary.toIsChain sharpData_stationary.zero_defect,
    hq,mul_zero,sub_zero,mul_one]
  rw [← Finset.sum_mul,hmass]
  ring

/-- The origin is the only centre of a disk of squared radius `qStar` that holds a model. The
corners on the circle have their weighted barycentre at the origin, so a disk about any other point
would miss one of them; this needs no lower bound for the radius. -/
theorem enclosing_center_unique (p : EqualityParameters) (o : Point)
    (h : ∀ i x,closedSquare (p.model sharpData i) x→ normSq (sub x o)≤qStar) :
    o=(0,0) := by
  have hsum : (∑ i : Fin 5,sharpData.mu i*normSq (sub (sharpData.anchorPoints i) o))≤
      ∑ i : Fin 5,sharpData.mu i*qStar := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (h (anchorIndex i) _ (anchor_closed p i))
      (sharpData_stationary.weightDomain.mu_pos i).le
  rw [anchor_second_moment,← Finset.sum_mul,sharpData_stationary.weightDomain.mu_sum] at hsum
  have hz : normSq o=0 := by linarith [normSq_nonneg o]
  exact (zero_normSq_iff _).mp hz

private theorem positive_square_interval {l u x : ℝ} (hl : 0≤l)
    (hx : l≤x ∧ x≤u) : l^2≤x^2 ∧ x^2≤u^2 := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hx.1) (show 0≤x+l by linarith)
  have h₂ := mul_nonneg (sub_nonneg.mpr hx.2) (show 0≤u+x by linarith)
  constructor <;> linarith

def centerBand : Fin 8 → ℝ × ℝ :=
  ![(1/100,3/100),(161/100,163/100),(157/100,159/100),
    (173/100,175/100),(167/100,169/100),(184/100,186/100),
    (161/100,163/100),(196/100,198/100)]

/-- Only D and H share a band.  A, E, the central square and both sliders
are distinguished using the squared radii of their centres alone. -/
theorem center_band {p : EqualityParameters} (hp : p.InBox) (i : Fin 8) :
    (centerBand i).1<normSq (p.model sharpData i).center ∧
      normSq (p.model sharpData i).center<(centerBand i).2 := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  obtain ⟨hy,huy⟩ := sharp_y
  obtain ⟨hpx,hpy,hpw,hpz,hpη⟩ := hp
  have hAx := positive_square_interval (l:=12515/10000) (u:=12516/10000)
    (x:=sharpData.x₁-1/2) (by norm_num) ⟨by linarith only [hx₁],by linarith only [hx₁u]⟩
  have hAy := positive_square_interval (l:=4205/10000) (u:=4208/10000)
    (x:=-(sharpData.y+1/2)) (by norm_num) ⟨by linarith only [huy],by linarith only [hy]⟩
  have hBx := positive_square_interval (l:=11584/10000) (u:=11586/10000)
    (x:=sharpData.x₂-1/2) (by norm_num) ⟨by linarith only [hx₂],by linarith only [hx₂u]⟩
  have hBy := positive_square_interval (l:=5792/10000) (u:=5795/10000)
    (x:=sharpData.y+3/2) (by norm_num) ⟨by linarith only [hy],by linarith only [huy]⟩
  have hDx := positive_square_interval (l:=8414/10000) (u:=8416/10000)
    (x:=-(sharpData.x₂-5/2)) (by norm_num) ⟨by linarith only [hx₂u],by linarith only [hx₂]⟩
  have hDy := positive_square_interval (l:=9545/10000) (u:=9547/10000)
    (x:=sharpData.y₃-1/2) (by norm_num) ⟨by linarith only [hy₃],by linarith only [hy₃u]⟩
  have hEx := positive_square_interval (l:=14021/10000) (u:=14022/10000)
    (x:=-(sharpData.x₄+1/2)) (by norm_num) ⟨by linarith only [hx₄u],by linarith only [hx₄]⟩
  have hEy := positive_square_interval (l:=453/10000) (u:=455/10000)
    (x:=-(sharpData.y₃-3/2)) (by norm_num) ⟨by linarith only [hy₃u],by linarith only [hy₃]⟩
  have hHx := positive_square_interval (l:=8674/10000) (u:=8680/10000)
    (x:=-(sharpData.h₁+1/2)) (by norm_num) ⟨by linarith only [hh₁u],by linarith only [hh₁]⟩
  have hHy := positive_square_interval (l:=9297/10000) (u:=9303/10000)
    (x:=-(sharpData.h₂+1/2)) (by norm_num) ⟨by linarith only [hh₂u],by linarith only [hh₂]⟩
  have hGx := positive_square_interval (l:=1320/10000) (u:=1326/10000)
    (x:=sharpData.h₁+3/2) (by norm_num) ⟨by linarith only [hh₁],by linarith only [hh₁u]⟩
  have hGy := positive_square_interval (l:=12487/10000) (u:=12513/10000)
    (x:=-(sharpData.h₂+1/2+p.eta)) (by norm_num)
    ⟨by linarith only [hh₂u,hpη.2],by linarith only [hh₂,hpη.1]⟩
  have hTx := positive_square_interval (l:=1584/10000) (u:=1586/10000)
    (x:=sharpData.x₂-3/2) (by norm_num) ⟨by linarith only [hx₂],by linarith only [hx₂u]⟩
  have hTy := positive_square_interval (l:=1349/1000) (u:=1351/1000)
    (x:=p.z) (by norm_num) hpz
  have hCx := positive_square_interval (l:=139/1000) (u:=141/1000)
    (x:=p.x) (by norm_num) hpx
  have hCy : p.y^2≤(1/1000:ℝ)^2 := by
    have h := mul_nonneg (by linarith only [hpy.1] : 0≤ p.y+1/1000)
      (by linarith only [hpy.2] : 0≤ 1/1000-p.y)
    linarith only [h]
  have c0 : (1/100:ℝ) < normSq (p.x,p.y) ∧ normSq (p.x,p.y) < 3/100 := by
    simp only [normSq]
    constructor <;> linarith only [hCx.1,hCx.2,hCy,sq_nonneg p.y]
  have c1 : (161/100:ℝ) < normSq sharpData.pH ∧ normSq sharpData.pH < 163/100 := by
    rw [pH,sharpData.normSq_inFrame]
    constructor <;> linarith only [hHx.1,hHx.2,hHy.1,hHy.2]
  have c2 : (157/100:ℝ) < normSq (sharpData.pG p.eta) ∧
      normSq (sharpData.pG p.eta) < 159/100 := by
    rw [pG,sharpData.normSq_inFrame]
    constructor <;> linarith only [hGx.1,hGx.2,hGy.1,hGy.2]
  have c3 : (173/100:ℝ) < normSq sharpData.pA ∧ normSq sharpData.pA < 175/100 := by
    simp only [pA,normSq]
    constructor <;> linarith only [hAx.1,hAx.2,hAy.1,hAy.2]
  have c4 : (167/100:ℝ) < normSq sharpData.pB ∧ normSq sharpData.pB < 169/100 := by
    simp only [pB,normSq]
    constructor <;> linarith only [hBx.1,hBx.2,hBy.1,hBy.2]
  have c5 : (184/100:ℝ) < normSq (sharpData.pT p.z) ∧ normSq (sharpData.pT p.z) < 186/100 := by
    simp only [pT,normSq]
    constructor <;> linarith only [hTx.1,hTx.2,hTy.1,hTy.2]
  have c6 : (161/100:ℝ) < normSq sharpData.pD ∧ normSq sharpData.pD < 163/100 := by
    simp only [pD,normSq,x₃]
    constructor <;> linarith only [hDx.1,hDx.2,hDy.1,hDy.2]
  have c7 : (196/100:ℝ) < normSq sharpData.pE ∧ normSq sharpData.pE < 198/100 := by
    simp only [pE,normSq,y₄]
    constructor <;> linarith only [hEx.1,hEx.2,hEy.1,hEy.2]
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7

theorem distinguished_band {p r : EqualityParameters} (hp : p.InBox) (hr : r.InBox)
    (i j : Fin 8) (hi : i=0 ∨ i=2 ∨ i=3 ∨ i=5 ∨ i=7)
    (h : normSq (p.model sharpData j).center=normSq (r.model sharpData i).center) : j=i := by
  have hpj := center_band hp j
  have hri := center_band hr i
  rw [h] at hpj
  generalize normSq (r.model sharpData i).center = v at hpj hri
  obtain ⟨a1,a2⟩ := hpj
  obtain ⟨b1,b2⟩ := hri
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       simp only [centerBand,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val] at a1 a2 b1 b2
       linarith)

theorem anchors_independent :
    sharpData.pA.1*sharpData.pE.2-sharpData.pA.2*sharpData.pE.1≠0 := by
  obtain ⟨hx₁,hx₁u,hx₂,hx₂u,hy₃,hy₃u,hx₄,hx₄u,hc,hcu,hs,hsu,hh₁,hh₁u,hh₂,hh₂u⟩ := sharp_coordinates
  obtain ⟨hy,huy⟩ := sharp_y
  have hpos : 0<(sharpData.y+1/2)*(sharpData.x₄+1/2) :=
    mul_pos_of_neg_of_neg (by linarith only [huy]) (by linarith only [hx₄u])
  have hneg : (sharpData.x₁-1/2)*(sharpData.y₃-3/2)<0 :=
    mul_neg_of_pos_of_neg (by linarith only [hx₁]) (by linarith only [hy₃u])
  dsimp [pA,pE,y₄]
  linarith only [hpos, hneg]

theorem fixed_independent_points (e : Point ≃ Point)
    (he : ∀ p r, normSq (sub (e p) (e r))=normSq (sub p r))
    (hzero : e (0,0)=(0,0)) (hA : e sharpData.pA=sharpData.pA)
    (hE : e sharpData.pE=sharpData.pE) : ∀ p,e p=p := by
  intro p
  have hn := he p (0,0)
  have h₁ := he p sharpData.pA
  have h₂ := he p sharpData.pE
  rw [hzero] at hn
  rw [hA] at h₁
  rw [hE] at h₂
  have hdA : sharpData.pA.1*((e p).1-p.1)+sharpData.pA.2*((e p).2-p.2)=0 := by
    dsimp [normSq,sub] at hn h₁
    linarith
  have hdE : sharpData.pE.1*((e p).1-p.1)+sharpData.pE.2*((e p).2-p.2)=0 := by
    dsimp [normSq,sub] at hn h₂
    linarith
  let det := sharpData.pA.1*sharpData.pE.2-sharpData.pA.2*sharpData.pE.1
  have hx : det*((e p).1-p.1)=0 := by
    dsimp [det]
    linear_combination sharpData.pE.2*hdA-sharpData.pA.2*hdE
  have hy : det*((e p).2-p.2)=0 := by
    dsimp [det]
    linear_combination sharpData.pA.1*hdE-sharpData.pE.1*hdA
  have hx0 := (mul_eq_zero.mp hx).resolve_left anchors_independent
  have hy0 := (mul_eq_zero.mp hy).resolve_left anchors_independent
  exact Prod.ext (by linarith) (by linarith)

theorem central_frame_from_sets {p r : EqualityParameters} (hp : p.InBox) (hr : r.InBox)
    (hc : p.centralSquare.center=r.centralSquare.center)
    (hs : ∀ x,closedSquare p.centralSquare x↔closedSquare r.centralSquare x) : p.w=r.w := by
  have hpC : (979/1000:ℝ) ≤ p.C ∧ p.C ≤ 981/1000 := box_data_bounds hp 0
  have hpS : (39/200:ℝ) ≤ p.S ∧ p.S ≤ 201/1000 := box_data_bounds hp 1
  have hrC : (979/1000:ℝ) ≤ r.C ∧ r.C ≤ 981/1000 := box_data_bounds hr 0
  have hrS : (39/200:ℝ) ≤ r.S ∧ r.S ≤ 201/1000 := box_data_bounds hr 1
  have hx := same_closed_width hc hs (1,0)
  have hd := same_closed_width hc hs (1,1)
  change (|p.C*1+p.S*0|+|-p.S*1+p.C*0|)/2=(|r.C*1+r.S*0|+|-r.S*1+r.C*0|)/2 at hx
  change (|p.C*1+p.S*1|+|-p.S*1+p.C*1|)/2=(|r.C*1+r.S*1|+|-r.S*1+r.C*1|)/2 at hd
  rw [abs_of_pos (by linarith only [hpC] : (0:ℝ) < p.C*1+p.S*0),
    abs_of_neg (by linarith only [hpS] : -p.S*1+p.C*0 < 0),
    abs_of_pos (by linarith only [hrC] : (0:ℝ) < r.C*1+r.S*0),
    abs_of_neg (by linarith only [hrS] : -r.S*1+r.C*0 < 0)] at hx
  rw [abs_of_pos (by linarith only [hpC, hpS] : (0:ℝ) < p.C*1+p.S*1),
    abs_of_pos (by linarith only [hpC, hpS] : (0:ℝ) < -p.S*1+p.C*1),
    abs_of_pos (by linarith only [hrC, hrS] : (0:ℝ) < r.C*1+r.S*1),
    abs_of_pos (by linarith only [hrC, hrS] : (0:ℝ) < -r.S*1+r.C*1)] at hd
  have hC : p.C=r.C := by linarith only [hd]
  have hS : p.S=r.S := by linarith only [hx, hd]
  have recover (w : ℝ) : halfAngleSin w/(1+halfAngleCos w)=w := by
    dsimp [halfAngleCos,halfAngleSin]
    field_simp [ne_of_gt (halfAngle_den_pos w)]
    ring
  rw [← recover p.w,← recover r.w]
  exact congrArg₂ (fun s c : ℝ=>s/(1+c)) hS hC

/-- A formulation in terms of all squared distances includes arbitrary
translations and both orientations of ambient Euclidean isometries. -/
def RigidlyCongruent (S T : Fin 8 → UnitSquare) : Prop :=
  ∃ e : Point ≃ Point, ∃ σ : Equiv.Perm (Fin 8),
    (∀ x y,normSq (sub (e x) (e y))=normSq (sub x y)) ∧
    ∀ i x,(openSquare (S (σ i)) (e x)↔openSquare (T i) x) ∧
      (closedSquare (S (σ i)) (e x)↔closedSquare (T i) x)

theorem box_rigid_parameters {p r : EqualityParameters} (hp : p.InBox) (hr : r.InBox)
    (h : RigidlyCongruent (p.model sharpData) (r.model sharpData)) : p=r := by
  obtain ⟨e,σ,he,hsets⟩ := h
  have hcenter (i : Fin 8) : e (r.model sharpData i).center=(p.model sharpData (σ i)).center :=
    isometry_square_center e he _ _ (fun x hx=>(hsets i x).2.mpr hx)
  have hzero : e (0,0)=(0,0) := by
    apply enclosing_center_unique p (e (0,0))
    intro j y hy
    obtain ⟨i,rfl⟩ := σ.surjective j
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [he x (0,0)]
    have hc := (whole_box_packing hr).2.1 i x ((hsets i x).2.mp hy)
    simpa [inDisk,sub,radius,Real.sq_sqrt (by linarith [qStar_limits.1] : 0≤qStar)] using hc
  have hnorm (i : Fin 8) :
      normSq (p.model sharpData (σ i)).center=normSq (r.model sharpData i).center := by
    have hn := he (r.model sharpData i).center (0,0)
    simpa [hcenter i,hzero,sub] using hn
  have hσ (i : Fin 8) (hi : i=0 ∨ i=2 ∨ i=3 ∨ i=5 ∨ i=7) : σ i=i :=
    distinguished_band hp hr i (σ i) hi (hnorm i)
  have hA : e sharpData.pA=sharpData.pA := by
    simpa [model,hσ 3 (by simp),axisSquare] using hcenter 3
  have hE : e sharpData.pE=sharpData.pE := by
    simpa [model,hσ 7 (by simp),axisSquare] using hcenter 7
  have hid := fixed_independent_points e he hzero hA hE
  have hcentral : p.centralSquare.center=r.centralSquare.center := by
    simpa [hid,model,hσ 0 (by simp)] using (hcenter 0).symm
  have hclosed : ∀ x,closedSquare p.centralSquare x↔closedSquare r.centralSquare x := by
    intro x
    simpa [hid,model,hσ 0 (by simp)] using (hsets 0 x).2
  have hw := central_frame_from_sets hp hr hcentral hclosed
  have hT : sharpData.pT p.z=sharpData.pT r.z := by
    simpa [hid,model,hσ 5 (by simp),axisSquare] using (hcenter 5).symm
  have hG : sharpData.pG p.eta=sharpData.pG r.eta := by
    simpa [hid,model,hσ 2 (by simp),tiltedSquare] using (hcenter 2).symm
  have hz : p.z=r.z := congrArg Prod.snd hT
  have hη : p.eta=r.eta := by
    have hh := congrArg (dot sharpData.f) hG
    rw [pG,pG,sharpData.dot_f_inFrame,sharpData.dot_f_inFrame] at hh
    linarith
  have hx : p.x=r.x := congrArg Prod.fst hcentral
  have hy : p.y=r.y := congrArg Prod.snd hcentral
  cases p
  cases r
  simp_all [centralSquare,center]

theorem box_rigidlyCongruent_iff {p r : EqualityParameters} (hp : p.InBox) (hr : r.InBox) :
    RigidlyCongruent (p.model sharpData) (r.model sharpData)↔p=r := by
  refine ⟨box_rigid_parameters hp hr,?_⟩
  rintro rfl
  exact ⟨Equiv.refl _,Equiv.refl _,by simp,by simp⟩

end SquaresInCircles.Eight.ExactFamily.BoxRigidity
