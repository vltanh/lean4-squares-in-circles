module

public import SquaresInCircles.Eight.Owners.All.HighBridgeData

/-!
# Eight squares: the exact six-edge residual bonus from the four original G1 types

Alternating the two scalar residual potentials pays the difference
between the endpoint type potentials.  A path from middle to middle
either stays middle or pays two exits.  Only the established four-type
G1 constants are used.
-/

@[expose] public section
noncomputable section

namespace SquaresInCircles.Eight.GlobalAllHigh.Bridge

def sixTypeCost (a b c d e f g : Fin 4) : ℝ :=
  handGamma a b+handGamma b c+handGamma c d+handGamma d e+handGamma e f+handGamma f g
def middlePotential (i : Fin 4) : ℝ := if i=2 then 93/10000 else 0

theorem bonus_symm (i j : Fin 4) : bonus i j=bonus j i := by
  simp only [bonus,abs_sub_comm,show (i=2 ∧ j=2)↔(j=2 ∧ i=2) from and_comm]

theorem residual_steps (i j : Fin 4) :
    8833/10000+tau i+tau j-53/2000≤handGamma i j ∧
    8833/10000-tau i-tau j+53/2000≤handGamma i j := by
  fin_cases i <;> fin_cases j <;> norm_num [handGamma,handGammaNumerator,tau]

theorem middle_steps (i j : Fin 4) :
    8833/10000+middlePotential i-middlePotential j≤handGamma i j ∧
    8833/10000-middlePotential i+middlePotential j≤handGamma i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [handGamma,handGammaNumerator,middlePotential]

theorem six_type_absolute (a b c d e f g : Fin 4) :
    |tau a-tau g|≤ sixTypeCost a b c d e f g-6*(8833/10000) := by
  have h0 := residual_steps a b
  have h1 := residual_steps b c
  have h2 := residual_steps c d
  have h3 := residual_steps d e
  have h4 := residual_steps e f
  have h5 := residual_steps f g
  apply abs_le.mpr
  dsimp [sixTypeCost]
  constructor
  · linarith [h0.2,h1.1,h2.2,h3.1,h4.2,h5.1]
  · linarith [h0.1,h1.2,h2.1,h3.2,h4.1,h5.2]

theorem six_type_middle (a b c d e : Fin 4) :
    (93/5000:ℝ)≤ sixTypeCost 2 a b c d e 2-6*(8833/10000) := by
  have h0 := middle_steps 2 a
  have h1 := middle_steps a b
  have h2 := middle_steps b c
  have h3 := middle_steps c d
  have h4 := middle_steps d e
  have h5 := middle_steps e 2
  have hM : middlePotential 2=(93/10000:ℝ) := by norm_num [middlePotential]
  by_cases ha : a=2
  · by_cases hb : b=2
    · by_cases hc : c=2
      · by_cases hd : d=2
        · by_cases he : e=2
          · norm_num [sixTypeCost,ha,hb,hc,hd,he,handGamma,handGammaNumerator]
          · have hz : middlePotential e=0 := by simp [middlePotential,he]
            dsimp [sixTypeCost]
            linarith [h0.1,h1.1,h2.1,h3.1,h4.1,h5.2]
        · have hz : middlePotential d=0 := by simp [middlePotential,hd]
          dsimp [sixTypeCost]
          linarith [h0.1,h1.1,h2.1,h3.1,h4.2,h5.2]
      · have hz : middlePotential c=0 := by simp [middlePotential,hc]
        dsimp [sixTypeCost]
        linarith [h0.1,h1.1,h2.1,h3.2,h4.2,h5.2]
    · have hz : middlePotential b=0 := by simp [middlePotential,hb]
      dsimp [sixTypeCost]
      linarith [h0.1,h1.1,h2.2,h3.2,h4.2,h5.2]
  · have hz : middlePotential a=0 := by simp [middlePotential,ha]
    dsimp [sixTypeCost]
    linarith [h0.1,h1.2,h2.2,h3.2,h4.2,h5.2]

theorem six_type_bonus (a b c d e f g : Fin 4) :
    6*(8833/10000)+bonus a g≤ sixTypeCost a b c d e f g := by
  have hAbs := six_type_absolute a b c d e f g
  have hM : (if a=2 ∧ g=2 then (93/5000:ℝ) else 0)≤
      sixTypeCost a b c d e f g-6*(8833/10000) := by
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩
      exact six_type_middle b c d e f
    · exact (abs_nonneg _).trans hAbs
  have hh := max_le hAbs hM
  dsimp [bonus]
  linarith

end SquaresInCircles.Eight.GlobalAllHigh.Bridge
