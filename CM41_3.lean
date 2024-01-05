import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic 
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic 
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


namespace ex_1_3_1_2

example :  ∀ a:ℚ  , 3*a+1 ≤ 7 ↔ a ≤ 2 := 
   λ a:ℚ ↦  
     Iff.intro
       (
         λ h1 :  3*a+1 ≤ 7 ↦ 
           calc
             a = (3*a+1-1) / 3 := by ring_nf
             _ ≤ (7-1) / 3     := by rel[h1]
             _ = 2             := by norm_num
       )
       (
         λ h2 :  a ≤ 2 ↦ 
           calc 
             3*a+1 ≤ 3*2+1 := by rel[h2]
             _     = 7     := by norm_num
       )





example :  ∀ x:ℝ   , 2*x-1 = 11 ↔ x=6 := 
   λ x:ℝ ↦  
     Iff.intro
       (
         λ h1 :  2*x-1 = 11 ↦ 
           calc
             x = (2*x-1+1) / 2 := by ring_nf
             _ = (11+1) / 2    := by rw[h1]
             _ = 6             := by norm_num
       )
       (
         λ h2 :  x=6 ↦ 
           calc 
             2*x-1 = 2*6-1 := by rw[h2]
             _     = 11    := by norm_num
       )


example :  ∀ x:ℝ   , 2*x-1 = 11 ↔ x=6 := 
   λ x:ℝ ↦  
     calc 
        2*x-1 = 11   ↔ 2*x-1+1 = 11 + 1  := add_right_cancel_iff.symm
        _            ↔ 2*x     = 12      := by ring_nf
        _            ↔ 2*x/2   = 12/2    := (div_left_inj' (by norm_num)).symm
        _            ↔ x       = 6       := by ring_nf




example :  ∀ x:ℝ , x^2+x-6 = 0 ↔ x=-3 ∨ x=2 := 
  λ x:ℝ ↦  
    Iff.intro

    (
      λ h1: x^2+x-6 = 0 ↦ 
        have h2 : (x+3)*(x-2) = 0 :=
          calc
            (x+3)*(x-2) = x^2+x-6  := by ring_nf
            _           = 0        := h1
        have h3 : x+3=0 ∨ x-2=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
        Or.imp eq_neg_of_add_eq_zero_left  eq_of_sub_eq_zero  h3
        /-
        Or.elim h3
          (
            λ h5 : x+3=0 ↦
              Or.inl (eq_neg_of_add_eq_zero_left h5  :  x=-3)
          )
          (
            λ h4 : x-2=0 ↦
              Or.inr (eq_of_sub_eq_zero h4 : x=2)
          )
          -/
    )
    (
      λ  h: (x=-3 ∨ x=2) ↦
        Or.elim h
        (
          λ hm3 : x=-3 ↦  
            calc
              x^2 + x - 6 = (-3)^2 +(-3) - 6  := by rw[hm3]
              _           = 9-3-6             := by norm_num
              _           = 0                 := by norm_num
        )
        (
          λ h2 : x=2 ↦  
            calc
              x^2 + x - 6 = 2^2 +2 - 6  := by rw[h2]
              _           = 4+2-6       := by norm_num
              _           = 0           := by norm_num
        )

    )

end ex_1_3_1_2


namespace ex_1_3_2_1

notation:76 "√" x:68 => (Real.sqrt x)

example :  ∀ x:ℝ , (x-3)^2 = 2 ↔ x=3-√2 ∨ x=3+√2  := 
  λ x:ℝ ↦  
    Iff.intro
    (
      λ h1: (x-3)^2 = 2 ↦ 
        have h2 : (x-(3-√2))*(x-(3+√2)) = 0 :=
          calc
            (x-(3-√2))*(x-(3+√2)) = (x-3)^2 - (√2)^2  := by ring_nf
            _                     = (x-3)^2 - 2       := by norm_num  -- by rw[Real.sq_sqrt (by norm_num)]
            _                     = 2 -2              := by rw[h1]
            _                     = 0                 := by norm_num

        Or.imp eq_of_sub_eq_zero  eq_of_sub_eq_zero  (eq_zero_or_eq_zero_of_mul_eq_zero h2)
    )
    (
      λ  h:x=3-√2 ∨ x=3+√2   ↦
        Or.elim h
        (
          λ hm : x=3-√2 ↦  
            calc
              (x-3)^2 = (3-√2-3)^2 := by rw[hm]
              _           = 2      := by norm_num
        )
        (
          λ hp : x=3+√2 ↦  
            calc
              (x-3)^2 = (3+√2-3)^2  := by rw[hp]
              _       = 2           := by norm_num
        )

    )

example :  ∀ x:ℝ , (x-3)^2 = 2 ↔ x=3-√2 ∨ x=3+√2  := 
  λ x:ℝ ↦  
    calc
       (x-3)^2 = 2 ↔  (x-3)^2 + (-2)   = 2 + (-2) := add_right_cancel_iff.symm 
       _           ↔  (x-3)^2 - 2      = 0        := by ring_nf
       _           ↔  (x-3)^2 - (√2)^2 = 0        := by norm_num
       _           ↔  (x-(3-√2))*(x-(3+√2)) = 0   := by ring_nf
       _           ↔  x-(3-√2) = 0 ∨ x-(3+√2) =0  := mul_eq_zero 
       _           ↔  x = 3-√2 ∨  x = 3+√2        := Iff.or sub_eq_zero sub_eq_zero

end ex_1_3_2_1


namespace ex_1_3_2_3

example : 7 ∈ {x:ℤ | ∃k:ℤ , x=3*k+1 }  :=
  Exists.intro (2:ℤ) (
    calc
      7=3*(2:ℤ)+1  := by norm_num
  )

open Real
example : sin  ∉  {f :ℝ → ℝ  | f (π/2) ≤ f π } :=
  not_le_of_lt
  (
    calc 
      sin (π / 2) = 1      := sin_pi_div_two
      _           > 0      := by norm_num
      _           = sin π  := sin_pi.symm
  )

example : sin  ∉  {f :ℝ → ℝ  | f (π/2) ≤ f π } :=
  by norm_num

example : sin  ∉  {f :ℝ → ℝ  | f (π/2) ≤ f π } :=
  have h1 : sin (π / 2) = 1           := sin_pi_div_two
  have h2 : sin π       = 0           := sin_pi  
  have h3 : ¬  (sin (π / 2) ≤ sin π ) :=  λ ha ↦ absurd (h1 ▸ h2 ▸ ha  : 1 ≤ (0:ℝ) )  (by norm_num)
  h3

example : sin  ∉  {f :ℝ → ℝ  | f (π/2) ≤ f π } :=
  not_le_of_lt
  (
    have h1 : sin (π / 2) = 1      := sin_pi_div_two
    have h2 : sin π       = 0      := sin_pi
    have h3 : sin (π / 2) > sin π  := h1.symm ▸ h2.symm ▸ (by norm_num :  1 > (0:ℝ))
    h3
  )

end ex_1_3_2_3



namespace ex_1_3_2_6

lemma set_subset_of_eq (E:Type) (A B : Set E) :  A=B  → A ⊆ B   :=
  λ h : A=B ↦
    λ x:E ↦ 
      λ hxA : x∈A ↦ 
      calc
        x ∈ A := hxA
        _ = B := h



example (E:Type) (A B : Set E) :  A=B ↔ (A ⊆ B ∧ B ⊆ A ) :=
  Iff.intro
    (
      λ h : A=B ↦
        And.intro
        (
          set_subset_of_eq E A B h       : A ⊆ B
        ) 
        (
          set_subset_of_eq E B A h.symm  : B ⊆ A
        )
    )
    (
      λ h : A ⊆ B ∧ B ⊆ A ↦ 
        Set.ext
        (
          λ x:E ↦ 
            Iff.intro
            (
              λ hxA : x ∈ A ↦
                (h.left hxA : x ∈ B )
            ) 
            (
              λ hxB : x ∈ B ↦
                (h.right hxB : x ∈ A )
            ) 
        )
    )


example :  ∀ x:ℤ, x ≥0 →(   (x+3)*(x-4) = 0 ↔ x=4 ):= 
  λ x:ℤ   ↦  
    λ h0 : x ≥ 0 ↦  
    Iff.intro
    (
      λ h1:  (x+3)*(x-4) = 0  ↦ 

        have hx34 : x+3=0 ∨ x-4 = 0 :=
          eq_zero_or_eq_zero_of_mul_eq_zero h1

        have hx3 : x+3 ≠ 0 :=
          ne_of_gt (
            calc
              x+3 ≥ 0+3 := by rel[h0] 
              _   > 0   := by norm_num
          )
       
        have hx4 : x-4 = 0  :=
          or_iff_not_imp_left.mp hx34 hx3

        calc
          x = x-4+4 := by ring_nf
          _ = 0+4   := by rw[hx4]
          _ = 4     := by norm_num

--        (eq_of_sub_eq_zero (or_iff_not_imp_left.mp (eq_zero_or_eq_zero_of_mul_eq_zero h1) ( hx3 )))
    )
    (
      λ  h:x=4   ↦
        calc
          (x+3)*(x-4) = (4+3)*(4-4) := by rw[h]
          _           = 0           := by norm_num
    )



example : ∀ x:ℤ  , x ≥ 0 → ( (x+3)*(x-4) = 0 ↔ x=4 ):= 
  λ x:ℤ   ↦  
    λ h0 : x ≥ 0 ↦  
      have hxn3 : x ≠ -3 := -- by aesop
        λ h3 ↦ absurd (
          calc
            0 ≤ x  := h0
            _ = -3 := h3
        ) (by norm_num) 

      calc
         (x+3)*(x-4) = 0  ↔  x+3=0 ∨ x-4 = 0  := mul_eq_zero 
        _           ↔  x = -3 ∨  x = 4        := Iff.or add_eq_zero_iff_eq_neg sub_eq_zero
        _           ↔  x = 4                  := or_iff_right hxn3


example : ∀ x:ℤ  , x ≥ 0 → ( (x+3)*(x-4) = 0 ↔ x=4 ):= 
  λ x:ℤ   ↦  
    λ h0 : x ≥ 0 ↦  
      have hxn3 : x ≠ -3 := by linarith
      calc
        (x+3)*(x-4) = 0  ↔  x+3=0 ∨ x-4 = 0  := mul_eq_zero 
        _           ↔  x = -3 ∨  x = 4        := Iff.or add_eq_zero_iff_eq_neg sub_eq_zero
        _           ↔  x = 4                  := or_iff_right hxn3

example : { x:ℤ | x ≥ 0 ∧ (x+3)*(x-4) = 0 } = {4} := 
  Set.ext (
    λ x:ℤ   ↦  
        calc
          (x ≥ 0) ∧ (x+3)*(x-4) = 0  ↔  (x ≥ 0) ∧ ((x+3=0) ∨ (x-4=0) )  := by rw[mul_eq_zero]
          _                          ↔  (x ≥ 0) ∧ ((x = -3) ∨  (x = 4)) := by rw [Iff.or add_eq_zero_iff_eq_neg sub_eq_zero]
          _                          ↔  x = 4                           := by aesop
  )


open Real
example  (a b: ℝ) :  (∀x:ℝ, a * (exp x) + b*(exp (-x)) = 0) → b = -a :=
  λ h: (∀x:ℝ, a * (exp x) + b*(exp (-x)) = 0) ↦
              calc
                b = a+b-a                      := by ring_nf
                _ = a*1+b*1 - a                := by ring_nf
                _ = a*(exp 0)+b*1 - a          := by rw [exp_zero]
                _ = a*(exp 0)+b*(exp (-0)) - a := by rw [neg_zero,exp_zero]
                _ = 0 - a                      := by rw[h 0]
                _ = -a                         := by ring_nf  

example : {c : ℝ×ℝ | ∀x:ℝ, c.1 * (exp x) + c.2 *(exp (-x)) = 0 } ⊆ {c:ℝ × ℝ |c.2 = -c.1 } :=
  λ c : ℝ×ℝ  ↦ 
    let ⟨a,b⟩ := c
    λ h: (∀x:ℝ, a * (exp x) + b*(exp (-x)) = 0) ↦
              calc
                b = a+b-a                      := by ring_nf
                _ = a*1+b*1 - a                := by ring_nf
                _ = a*(exp 0)+b*1 - a          := by rw [exp_zero]
                _ = a*(exp 0)+b*(exp (-0)) - a := by rw [neg_zero,exp_zero]
                _ = 0 - a                      := by rw[h 0]
                _ = -a                         := by ring_nf  


end ex_1_3_2_6



namespace ex_1_3_5_1



lemma eqR2_CN (x:ℝ) (b:ℝ) (hx: x+(b+2) ≥ 0) :      ( √(x+(b+2)) = x+b)  → (x=-(b+1) ∨ x=-(b-2)) :=
  λ h: √(x+(b+2)) = x+b ↦ 
  have h' : (x-(-(b+1)))*(x-(-(b-2)))=0 :=
    calc
       (x-(-(b+1)))*(x-(-(b-2))) = (x+b)^2        - (x+(b+2)) := by ring_nf
      _                          = (√(x+(b+2)))^2 - (x+(b+2)) := by rw[h]
      _                          = (x+(b+2))      - (x+(b+2)) := by rw[Real.sq_sqrt hx]
      _                          = 0                          := by ring_nf
  Or.imp (sub_eq_zero.mp) (sub_eq_zero.mp) (mul_eq_zero.mp h')


lemma eqR2_CN' (x:ℝ) (b:ℝ) (hx: x+(b+2) ≥ 0) :      ( √(x+(b+2)) = x+b)  → x=-(b-2) :=
  λ h: √(x+(b+2)) = x+b ↦ 
  have hn :¬ (x=-(b+1)) := 
    λ hn' : x=-(b+1) ↦ 
      absurd
      (
        calc
          1 = √1              := by norm_num
          _ = √(-(b+1)+(b+2)) := by ring_nf
          _ = √(x+(b+2))      := by rw[hn']
          _ = x+b             := h
          _ = -(b+1)+b        := by rw[hn']
          _ = -1              := by ring_nf
      )
      (by norm_num)
  or_iff_not_imp_left.mp (eqR2_CN x b hx h) hn

lemma eqR2_CNS (x:ℝ) (b:ℝ) (hx: x+(b+2) ≥ 0) :      ( √(x+(b+2)) = x+b)  ↔  x=-(b-2) :=
  Iff.intro 
    (eqR2_CN' x b hx ) 
    (
      λ h :  x=-(b-2) ↦
        calc 
          √(x+(b+2)) = √(-(b-2)+(b+2))   := by rw[h]
          _          = √(2^2)            := by ring_nf
          _          = 2                 := Real.sqrt_sq (by norm_num)
          _          = -(b-2) + b        := by ring_nf
          _          = x+b               := by rw[h]

    )


lemma eqR6_CN (x:ℝ) (b:ℝ) (hx: x+(b+6) ≥ 0) :      ( √(x+(b+6)) = x+b) → (x=-(b-3) ∨ x=-(b+2)) :=
  λ h: √(x+(b+6)) = x+b ↦ 
  have h' : (x-(-(b-3)))*(x-(-(b+2)))=0 :=
    calc
       (x-(-(b-3)))*(x-(-(b+2))) = (x+b)^2        - (x+(b+6)) := by ring_nf
      _                          = (√(x+(b+6)))^2 - (x+(b+6)) := by rw[h]
      _                          = (x+(b+6))      - (x+(b+6)) := by rw[Real.sq_sqrt hx]
      _                          = 0                          := by ring_nf
  Or.imp (sub_eq_zero.mp) (sub_eq_zero.mp) (mul_eq_zero.mp h')

lemma eqR6_CN' (x:ℝ) (b:ℝ) (hx: x+(b+6) ≥ 0) :      ( √(x+(b+6)) = x+b) → x=-(b-3)  :=
  λ h: √(x+(b+6)) = x+b ↦ 
  have hn :¬ (x=-(b+2)) := 
    λ hn' : x=-(b+2) ↦ 
      absurd
      (
        calc
          2 = √(2^2)          := (Real.sqrt_sq (by norm_num)).symm
          _ = √(-(b+2)+(b+6)) := by ring_nf
          _ = √(x+(b+6))      := by rw[hn']
          _ = x+b             := h
          _ = -(b+2)+b        := by rw[hn']
          _ = -2              := by ring_nf
      )
      (by norm_num)
  or_iff_not_imp_right.mp (eqR6_CN x b hx h) hn

lemma eqR6_CNS (x:ℝ) (b:ℝ) (hx: x+(b+6) ≥ 0) :      ( √(x+(b+6)) = x+b) ↔  x=-(b-3)  :=
  Iff.intro 
    (eqR6_CN' x b hx ) 
    (
      λ h :  x=-(b-3) ↦
        calc 
          √(x+(b+6)) = √(-(b-3)+(b+6))   := by rw[h]
          _          = √(3^2)            := by ring_nf
          _          = 3                 := Real.sqrt_sq (by norm_num)
          _          = -(b-3) + b        := by ring_nf
          _          = x+b               := by rw[h]

    )


example (x:ℝ) (hx: x ≥ -3) :   ( √(x+3) = x-3) ↔  x=6  :=
    have h_sol : ( √(x+((-3)+6)) = x+(-3)) ↔  x=-((-3)-3)  := 
      (
        eqR6_CNS x (-3) (
                        calc
                          x+((-3)+6) = x+3  := by ring_nf
                          _          ≥ -3+3 := by rel[hx]
                          _          = 0    := by norm_num 

                        ) 
      )

    calc
       √(x+3) = x-3 ↔ ( √(x+((-3)+6)) = x+(-3)) := by ring_nf
       _            ↔  x=-((-3)-3)              := h_sol 
       _            ↔  x=6                      := by norm_num






open Real

lemma L : ∀ a b: ℝ, (∀x:ℝ, a * (sin x) + b*(cos x) =0 ) ↔ a=0 ∧ b=0   :=
  λ a b : ℝ  ↦ 
    Iff.intro
    (
      λ h: ∀x:ℝ, a * (sin x) + b*(cos x) = 0 ↦
                have hb0 : b = 0 :=
                  calc
                    b = a*0+b*1              := by ring_nf
                    _ = a*(sin 0)+b*1        := by rw [sin_zero]
                    _ = a*(sin 0)+b*(cos 0 ) := by rw [cos_zero]
                    _ = 0                    := h 0
                have ha0 : a = 0 :=
                  calc
                    a = a*1+b*0                      := by ring_nf
                    _ = a*(sin (π/2))+b*0            := by rw [sin_pi_div_two]
                    _ = a*(sin (π/2))+b*(cos (π/2) ) := by rw [cos_pi_div_two]
                    _ = 0                            := h (π/2)

                And.intro ha0 hb0
    )
    (
      λ h : a=0 ∧ b=0 ↦
        λ x :ℝ ↦   
          calc
             a * (sin x) + b*(cos x) =  0 * (sin x) + 0 * (cos x)  := by rw[h.left, h.right]
             _                       =  0                          := by ring_nf
    )

/-
example : {c : ℝ×ℝ | (∀x:ℝ, c.1 * (sin x) + c.2 *(cos x) =0 ) } =  { ⟨0,0⟩  }   :=
  Set.ext (
    λ c: ℝ× ℝ  ↦ 
      let (a,b) :=c
      L a b 
  )
-/

lemma Q  (c:ℝ× ℝ ) (h: c = (0,0)) : c.1=0 := by aesop
example  (c:ℝ× ℝ ) (h: c = (0,0)) : c.1=0 := h.symm ▸ rfl
example  : (0,0).1=0 := rfl
example  (c d:ℝ× ℝ )  : c=d ↔ (c.1=d.1) ∧(c.2=d.2)  := by exact Prod.ext_iff
#check Prod.mk.injEq
#check Prod.mk.inj_iff

#print Q

example : {c : ℝ×ℝ | (∀x:ℝ, c.1 * (sin x) + c.2 *(cos x) =0 ) } =  { ⟨0,0⟩  }   :=
  Set.ext (
    λ c: ℝ× ℝ  ↦ 
--      let ⟨ a,b⟩  :=c
      let a:= c.1
      let b:= c.2
      Iff.intro
      (
        λ h: ∀x:ℝ, a * (sin x) + b*(cos x) = 0 ↦
                  have hb0 : b = 0 :=
                    calc
                      b = a*0+b*1              := by ring_nf
                      _ = a*(sin 0)+b*1        := by rw [sin_zero]
                      _ = a*(sin 0)+b*(cos 0 ) := by rw [cos_zero]
                      _ = 0                    := h 0
                  have ha0 : a = 0 :=
                    calc
                      a = a*1+b*0                      := by ring_nf
                      _ = a*(sin (π/2))+b*0            := by rw [sin_pi_div_two]
                      _ = a*(sin (π/2))+b*(cos (π/2) ) := by rw [cos_pi_div_two]
                      _ = 0                            := h (π/2)

                  calc
                    c= ⟨a,b⟩ := rfl
                    _ =(0,0) := by rw[ha0,hb0] 
      )
      (
        λ h : c=(0,0) ↦
          λ x :ℝ ↦
            have ha : a=0 := (Prod.mk.inj_iff.mp h).left
            have hb : b=0 := (Prod.mk.inj_iff.mp h).right

            calc
              a * (sin x) + b*(cos x) =  0 * (sin x) + 0 * (cos x)  := by rw[ha,hb]
              _                       =  0                          := by ring_nf
      )
    )

/-
example (c:ℝ×ℝ  ) : c.fst = c.fst :=
 let ⟨ a,b⟩ :=c
 have h:   c.fst =a := sorry -- Eq.refl a
 h
-/

lemma sq_le_iff {a x:ℚ  } : (a-x)^2 ≤ 1 ↔ (a ≤ x+1   ∧ a ≥ x-1 )  := 
  have h1 : ¬  (a-x-1 ≥ 0 ∧ a-x+1 ≤ 0) := λ ha1 :  a-x-1 ≥ 0 ∧ a-x+1 ≤ 0 ↦ 
    absurd
    (
      calc
        0+1 ≤ a-x-1+1 := by rel[ha1.left ]
        _   = a-x+1-1 := by ring_nf
        _   ≤ 0-1     := by rel[ha1.right]
    )
    (by norm_num)
  calc
     (a-x)^2 ≤ 1  ↔ (a-x)^2 - 1 ≤ 1-1                                     := (sub_le_sub_iff_right 1).symm
     _            ↔ (a-x-1)*(a-x+1) ≤ 0                                   := by ring_nf
     _            ↔ (a-x-1 ≥ 0 ∧ a-x+1 ≤ 0)  ∨  (a-x-1 ≤  0 ∧ a-x+1 ≥  0) := mul_nonpos_iff
     _            ↔ (a-x-1 ≤  0 ∧ a-x+1 ≥  0)                             := or_iff_right h1
     _            ↔ (a - (x+1) ≤ (x+1)-(x+1)  ∧ a - (x-1) ≥ (x-1-(x-1)) ) := by ring_nf
     _            ↔ (a ≤ x+1   ∧ a ≥ x-1 )                                := Iff.and (sub_le_sub_iff_right _) (sub_le_sub_iff_right _)


def P (a:ℚ) : Prop :=  ∀ x:ℚ , x≥ 1 ∧ x ≤ 3 → (a-x)^2 ≤ 1

lemma P_CNS (a:ℚ) : P a ↔ a = 2 := 
  Iff.intro
  (
    λ h : P a ↦  
      have h1 : a ≤ 1 + 1 ∧ a ≥ 1 - 1 := sq_le_iff.mp ( (h 1) (And.intro (by norm_num) (by norm_num)))
      have h3 : a ≤ 3 + 1 ∧ a ≥ 3 - 1 := sq_le_iff.mp ( (h 3) (And.intro (by norm_num) (by norm_num)))
      le_antisymm 
        (Trans.trans h1.left  (by norm_num : 1+1=(2:ℚ )))
        (Trans.trans (by norm_num : (2:ℚ )=3-1) h3.right )
  )
  (
    λ h : a=2 ↦  
      λ x:ℚ ↦  
        λ hx : x≥ 1 ∧ x ≤ 3 ↦
          sq_le_iff.mpr 
          (
            And.intro
            (
              calc 
                a = 2       := h 
                _ = 1 + 1   := by norm_num
                _ ≤ x + 1   := by rel[hx.left]                
            )
            (
              calc 
                a = 2       := h 
                _ = 3 - 1   := by norm_num
                _ ≥  x - 1  := by rel[hx.right]
            )
          )
  )

example : ∃! a:ℚ , P a :=
  Exists.intro 2
  (
    And.intro
    (
       (P_CNS 2).mpr rfl
    )
    (
       λ a:ℚ ↦
          (P_CNS a).mp          
    )   
  )


end ex_1_3_5_1

