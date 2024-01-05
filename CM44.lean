import Mathlib.Data.Real.Basic
import Esisar.CM43

open chap3

namespace chap4


lemma P_4_1_0_2 {E F : Type} (f:E →F ):  ∀ x:E, ∃!y:F , y=f x :=
  λ x:E ↦
    Exists.intro (f x)
    (
      And.intro
      (
        rfl : f x  = f x
      )
      (
        λ (y:F)  (hy:y=f x) ↦
          hy 
      )
    )
      
lemma P_4_1_0_2' {E F : Type} (f:E →F ):  ∀ x:E, ∃!y:F , y=f x :=
  λ x  ↦ ⟨f x ,⟨ rfl, λ _ ↦ id ⟩ ⟩ 


example (x y : ℝ ) (h: x≤y  ) : -y ≤ -x := by exact neg_le_neg h 
#print neg_le_neg
#print neg_le_neg_iff
#print neg_le



def Im    {E F : Type} (f:E →F ): Set F := {y:F | ∃x:E, y=f x}
def Im'   {E F : Type} {A: Set E} {B : Set F} (f:A → B ): Set F := {y∈ B |  ∃(x:E) (hxA: x∈ A) , y=f ⟨x,hxA⟩  }





namespace ex_4_1_0_8
  noncomputable def f : [-3;2] → [-1;+∞) :=  fun x ↦ ⟨ (x.val) ^2 , (le_trans (by norm_num) (sq_nonneg x.val))⟩ 

--  example : Im f = [0;9] := 
  example : Im' f = [0;9] := 
    Set.ext
    (
      λ y ↦ Iff.intro
      (
        λ ⟨_,⟨x, ⟨hx,hyfx ⟩ ⟩ ⟩    ↦ 
          And.intro
            (
              calc 
                0 ≤ x^2 := sq_nonneg x
                _ = y   := hyfx.symm
            )
            (
              Or.elim (le_or_lt x 0)
              (
                λ hx0 ↦
                  calc
                    y = x^2    := hyfx
                    _ ≤ (-3)^2 := sq_decreasing (-3) x hx0 hx.left
                    _ = 9      := by norm_num
              )
              (
                λ hx0 ↦
                  calc
                    y = x^2    := hyfx
                    _ ≤ 2^2    := sq_increasing x 2  (le_of_lt hx0) hx.right
                    _ ≤ 9      := by norm_num
              )
            )
      )
      (
        λ h ↦ 
          let r:= - (sqrt y h.left)
          have hr0  : r ≤ 0  := neg_nonpos.mpr (sqrt_nonneg y h.left)
          have hrm3 : r ≥ -3 := neg_le_neg (
            calc
              sqrt y _ ≤ sqrt 9     _  := sqrt_increasing y 9 h.left h.right
              _        = sqrt (3^2) _  := by norm_num
              _        = 3               := sqrt_sq_eq_self_of_nonneg _ (by norm_num)
          )
          And.intro
          (le_trans (by norm_num) h.left)
          (
            Exists.intro r
            (
              Exists.intro (And.intro hrm3 (le_trans hr0 (by norm_num)))
              (
                calc
                  y = (sqrt y _) ^2 := (sq_sqrt y _).symm
                  _ = r^2           := by ring_nf
              )
            )
          )
      )
    )

end ex_4_1_0_8


-- 4.2.1.1

def paire   (f:ℝ → ℝ) : Prop := ∀x:ℝ, f (-x) = f x
def impaire (f:ℝ → ℝ) : Prop := ∀x:ℝ, f (-x) = -(f x)



end chap4
