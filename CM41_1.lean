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

namespace ex_1_1_2_3
    -- Démontrez les assertions de l'exercice 1.1.2.2 dont vous avez conjecturé qu'elles sont vraies.

  namespace assertion1
    --import Mathlib.Data.Real.Basic

    example: ∀x:ℝ, (x-1)^2 = x^2 -2*x + 1  := sorry

    namespace version1
      lemma sub_sub_eq (a b :ℝ) : a-b-b = a-2*b := 
        calc
          a-b-b = a-(b+b) := sub_sub a b b 
          _     = a-2*b   := congr_arg (fun z:ℝ ↦ a-z) (two_mul b).symm

      example: ∀x:ℝ, (x-1)^2 = x^2 -2*x + 1  :=
        λ u:ℝ ↦            -- soit u:ℝ,
        (
          calc
            (u-1)^2= (u-1)*(u-1)   := sq (u-1)
            _      =  u*(u-1)-(u-1):= sub_one_mul u (u - 1)
            _      =  u*u-u-(u-1)  := congr_arg  (fun z:ℝ ↦ z - (u-1)) (mul_sub_one u u)
            _      =  u*u-u-u+1    := (sub_add (u*u-u) u 1).symm
            _      =  u*u-2*u+1    := congr_arg  (fun z:ℝ ↦ z + 1)     (sub_sub_eq (u*u) u)
            _      =  u^2-2*u+1    := congr_arg  (fun z:ℝ ↦ z -2*u+1)  (sq u).symm
        )     
    end version1

    namespace version2

      example: ∀x:ℝ, (x-1)^2 = x^2 -2*x + 1  :=
        λ u:ℝ ↦            -- soit u:ℝ,
        (
          calc
            (u-1)^2= (u-1)*(u-1)   := by ring
            _      =  u*(u-1)-(u-1):= by ring
            _      =  u*u-u-(u-1)  := by ring
            _      =  u*u-u-u+1    := by ring
            _      =  u*u-2*u+1    := by ring
            _      =  u^2-2*u+1    := by ring
        )     
    end version2

    namespace version3
      example: ∀x:ℝ, (x-1)^2 = x^2 -2*x + 1  :=
        λ u:ℝ ↦            -- soit u:ℝ,
        (
          calc
            (u-1)^2 = u^2 -2*u + 1   := by ring
        )     
    end version3

  end assertion1

  namespace assertion2
    --import Mathlib.Data.Real.Basic

    example: ∀x:ℝ, x^2 ≥ 0  := sorry

    namespace version1
      #check sq_nonneg
      example: ∀x:ℝ, x^2 ≥ 0  :=
        λ u:ℝ ↦            -- soit u:ℝ,
        (
          calc
              u^2 ≥ 0    :=  sq_nonneg u
        )
    end version1

  end assertion2

end ex_1_1_2_3



namespace ex_1_1_2_4
  namespace assertion1
    --import Mathlib.Data.Int.Basic
    --import Mathlib.Data.Finset.Basic

    def A : Set ℤ := {-1,2}

    example: ∀x∈ A, x+1 ≤ 5-x := sorry

    namespace version1
      --import Mathlib.Tactic.NormNum

      example : ∀x∈ A, x+1 ≤ 5-x :=
        λ (x:ℤ) (h:x=-1 ∨ x=2) ↦ 
          Or.elim h 
          (
            λ h1:x=-1 ↦ 
              calc
                x+1 = -1+1   := congr_arg (fun z:ℤ ↦ z+1) (h1:       x=-1)
                _   ≤ 5-(-1) := by norm_num
                _   = 5-x    := congr_arg (fun z:ℤ ↦ 5-z) (h1.symm : -1=x)
          )
          (
            λ h2:x=2 ↦ 
              calc
                x+1 = 2+1 := congr_arg (fun z:ℤ ↦ z+1) (h2:       x=2)
                _   ≤ 5-2 := by norm_num
                _   = 5-x := congr_arg (fun z:ℤ ↦ 5-z) (h2.symm:  2=x)
          )  
    end version1
  end assertion1

  namespace assertion2
    --import Mathlib.Data.Int.Basic
    --import Mathlib.Data.Finset.Basic

    def A : Set ℤ := {1,2}

    example: ∀x∈ A, x^3-3*x^2+2*x = 0  := sorry

    namespace version1
      --import Mathlib.Tactic.NormNum
      example : ∀x∈ A, x^3-3*x^2+2*x = 0 :=
        λ (x:ℤ) (h:x=1 ∨ x=2) ↦ 
          Or.elim h 
          (
            λ h1:x=1 ↦ 
              calc
                x^3-3*x^2+2*x = 1^3-3*1^2+2*1 := congr_arg  (fun z:ℤ  ↦ z^3-3*z^2+2*z)  (h1:x=1)
                _             = 0             := by norm_num
          )
          (
            λ h2:x=2 ↦ 
              calc
                x^3-3*x^2+2*x = 2^3-3*2^2+2*2 := congr_arg  (fun z:ℤ ↦ z^3-3*z^2+2*z)   (h2:x=2)
                _             = 0             := by norm_num
          ) 
    end version1
  end assertion2

  namespace assertion3
    --import Mathlib.Data.Real.Basic

    example: ∀ y:ℝ, y^2-4*y+7 ≥ 1  := sorry

    namespace version1
      example : ∀ y:ℝ, y^2-4*y+7 ≥ 1 :=
        λ y:ℝ ↦ 
        have h1 : (y-2)^2 ≥ 0 := sq_nonneg (y-2)
        have h2 : 3 ≥ (3:ℝ)   := by norm_num -- le_refl 3
        calc 
          y^2-4*y+7 = y^2-4*y+4+3  := by ring
          _         = (y-2)^2+3    := by ring
          _         ≥ 0+3          := add_le_add h1 h2
          _         ≥ 1            := by norm_num
    end version1

    namespace version2
      lemma id_rmq (a b:ℝ) : (a-b)^2 = a^2-2*a*b+b^2 := by ring

      example : ∀ y:ℝ, y^2-4*y+7 ≥ 1 :=
        λ y:ℝ ↦ 
          have h1 : (y-2)^2 ≥ 0 := sq_nonneg (y-2)
          have h2 : 3 ≥ (3:ℝ)   := by norm_num -- le_refl 3
          have h3 : 4*y=2*y*2   :=  by ring
          calc 
            y^2-4*y+7 = y^2-2*y*2 + 7         := congr_arg (fun z:ℝ ↦ y^2-z+7) h3 
            _         = y^2-2*y*2 + (2^2 + 3) := by norm_num 
            _         = y^2-2*y*2 + 2^2 + 3   := (add_assoc _ _ _).symm
            _         = (y-2)^2         +3    := congr_arg  (fun z:ℝ ↦ z+3)  (id_rmq y 2).symm
            _         ≥ 0 + 3                 := add_le_add h1 h2
            _         ≥ 1                     := by norm_num
    end version2

    namespace version3
      lemma sub_sub_eq (a b :ℝ) : a-b-b = a-2*b := 
          calc
            a-b-b = a-(b+b) := sub_sub a b b 
            _     = a-2*b   := 
                congr_arg (fun z:ℝ ↦ a-z) (two_mul b).symm

      lemma id_rmq (a b:ℝ) : (a-b)^2 = a^2-2*a*b+b^2 := 
         calc
            (a-b)^2 = (a-b)*(a-b)       := sq (a-b)
            _       = a*(a-b)-b*(a-b)   := sub_mul a b (a-b)
            _       = a*a-a*b-b*(a-b)   := congr_arg (fun z:ℝ  ↦ z-b*(a-b))     (mul_sub a a b)
            _       = a*a-a*b-(b*a -b*b):= congr_arg (fun z:ℝ ↦ a*a-a*b-z)      (mul_sub b a b)
            _       = a*a-a*b- b*a +b*b := (sub_add (a*a-a*b) (b*a) (b*b)).symm
            _       = a*a-a*b- a*b +b*b := congr_arg (fun z:ℝ ↦ a*a-a*b-z+b*b ) (mul_comm b a)
            _       = a*a-2*(a*b) + b*b := congr_arg (fun z:ℝ ↦ z+b*b )         (sub_sub_eq (a*a) (a*b))
            _       = a*a- 2*a*b  + b*b := congr_arg (fun z:ℝ ↦ a*a-z+b*b )     (mul_assoc 2 a b).symm
            _       = a^2- 2*a*b  + b*b := congr_arg (fun z:ℝ ↦ z -2*a*b+b*b)   (sq a).symm
            _       = a^2-2*a*b+b^2     := congr_arg (fun z:ℝ ↦ a^2 -2*a*b+z)   (sq b).symm

      example : ∀ y:ℝ, y^2-4*y+7 ≥ 1 :=
        λ y:ℝ ↦ 
          have h1 : (y-2)^2 ≥ 0 := sq_nonneg (y-2)
          have h2 : 3 ≥ (3:ℝ)   := by norm_num -- le_refl 3
          have h3 : 4*y=2*y*2 := 
            calc
              4*y = (2*2)*y := by norm_num
              _   = 2*(2*y) := mul_assoc _ _ _
              _   = 2*(y*2) := congr_arg _ (mul_comm _ _)
              _   = 2*y*2   := (mul_assoc _ _ _).symm
            calc 
              y^2-4*y+7 = y^2-2*y*2 + 7         := congr_arg (fun z:ℝ ↦ y^2-z+7) h3 
              _         = y^2-2*y*2 + (2^2 + 3) := by norm_num 
              _         = y^2-2*y*2 + 2^2 + 3   := (add_assoc _ _ _).symm
              _         = (y-2)^2         +3    := congr_arg  (fun z:ℝ ↦ z+3) (id_rmq y 2).symm
              _         ≥ 0 + 3                 := add_le_add h1 h2
              _         ≥ 1                     := by norm_num
    end version3

  end assertion3

end ex_1_1_2_4




namespace ex_1_1_2_5
  namespace assertion1
    --import Mathlib.Data.Real.Basic
    example (a:ℝ) (h: ∀x:ℝ,a ≤ x^2 -2*x) : a ≤ -1 :=  sorry

    namespace version1
      example (a:ℝ) (h: ∀x:ℝ,a ≤ x^2 -2*x) : a ≤ -1 := 
        calc
          a ≤ 1^2-2*1 := h 1   -- on applique h à 1
          _ = -1      := by norm_num
    end version1
  end assertion1

end ex_1_1_2_5



namespace ex_1_1_2_6
  namespace assertion1
    --import Mathlib.Data.Real.Basic
    --import Mathlib.Data.Complex.Exponential
    --import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
    open Real

    example (a:ℝ) (h: ∀x:ℝ,a * (sin x) = 0) : a = 0 :=  sorry

    namespace version1
      example : sin (π/2) = 1 := sin_pi_div_two

      example (a:ℝ) (h: ∀x:ℝ,a * (sin x) = 0) : a = 0 := 
        calc
          a = a*1            := (mul_one a).symm
          _ = a*(sin (π/2))  := congr_arg  (fun z:ℝ ↦ a*z) sin_pi_div_two.symm
          _ = 0              := h (π/2)
    end version1

    namespace version2
      example (a:ℝ) (h: ∀x:ℝ,a * (sin x) = 0) : a = 0 := 
        calc
          a = a*1            := by ring
          _ = a*(sin (π/2))  := by norm_num
          _ = 0              := h (π/2)
    end version2
  end assertion1

  namespace assertion2
    --import Mathlib.Data.Real.Basic

    example (a b:ℝ) (h: ∀x:ℝ,(x ≥ a) ∨ (x ≤ b) ) : a ≤ b :=   sorry

    namespace version1
      example (a b:ℝ) (h: ∀x:ℝ,(x ≥ a) ∨ (x ≤ b) ) : a ≤ b := 
        let m:= (a+b)/2 ;
        Or.elim (h m)
          (λ hma : m ≥ a ↦
            calc
              b = a+b-a := by ring
              _ = 2*m-a := by ring
              _ ≥ 2*a-a := by rel[hma]
              _ = a     := by ring
          )
          (λ hmb : m ≤ b ↦
            calc
              a = a+b-b := by ring
              _ = 2*m-b := by ring
              _ ≤ 2*b-b := by rel[hmb]
              _ = b     := by ring
          )
    end version1

    namespace version2
      example (a b c:ℝ) (h: a≤b)  : a-c ≤ b-c := sub_le_sub_right h c
      example (a b c:ℝ) (h: a≤b) (hc: c≥ 0) : c*a ≤ c*b := mul_le_mul_of_nonneg_left h hc

      example (a b:ℝ) (h: ∀x:ℝ,(x ≥ a) ∨ (x ≤ b) ) : a ≤ b := 
        let m:= (a+b)/2 ;
        Or.elim (h m)
          (λ hma : m ≥ a ↦
            calc
              b = a+b-a := by ring
              _ = 2*m-a := by ring
              _ ≥ 2*a-a := sub_le_sub_right (mul_le_mul_of_nonneg_left hma (by norm_num : (0:ℝ) ≤ 2)) a
              _ = a     := by ring
          )
          (λ hmb : m ≤ b ↦
            calc
              a = a+b-b := by ring
              _ = 2*m-b := by ring
              _ ≤ 2*b-b := sub_le_sub_right (mul_le_mul_of_nonneg_left hmb (by norm_num : (0:ℝ) ≤ 2)) b
              _ = b     := by ring
          )
    end version2
  end assertion2

  namespace assertion3
    --import Mathlib.Data.Real.Basic

    def magic (a:ℝ):Prop := (a^2≤2) ∧ (∀y:ℝ,((y^2 ≤ 2)→a≥y))

    example (a :ℝ) (ha: magic a) (hb: magic b) : a = b := sorry

    namespace version1
      example (a :ℝ) (ha: magic a) (hb: magic b) : a = b := 
        have h1  : a ≥ b := ha.right b hb.left
        have h2  : a ≤ b := hb.right a ha.left
        have h3  : a = b := le_antisymm h2 h1
        h3
    end version1
  end assertion3


  namespace assertion4
    --import Mathlib.Data.Real.Basic

    example : ∀ a b:ℝ , (∀x:ℝ,a * x + b = 0) →  (a = 0 ∧ b = 0) :=  
      λ a b:ℝ ↦ 
        λ h:(∀x:ℝ,a * x + b = 0) ↦
          have hb0 :  b=0 :=
            calc
              b = a*0 + b  := by ring_nf
              _ = 0        := h 0
          have ha0 : a=0 :=
            calc
              a = a*1+0 := by ring_nf
              _ = a*1+b := by rw[hb0]
              _ = 0     := h 1
          And.intro ha0 hb0

  end assertion4

end ex_1_1_2_6


namespace ex_1_1_3_3
  namespace question1
    --import Mathlib.Data.Nat.Basic
      
    def impair (n:ℕ) : Prop := ∃ k:ℕ , n=2*k+1
  end question1

  namespace question2
    --import Mathlib.Data.Real.Basic
    --import Mathlib.Data.Complex.Exponential
    --import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
    open Real
    example : ∀ x:ℝ, ((cos x = 0) ↔ ∃ k:ℤ, x=π/2+k*π) := sorry
  end question2

end ex_1_1_3_3


namespace ex_1_1_3_4
  namespace assertion1
    --import Mathlib.Data.Nat.Basic 
    --import Mathlib.Data.Set.Basic 
    --import Mathlib.Data.Finset.Basic
    --import Mathlib.Tactic.NormNum

    def impair (n:ℕ) : Prop := ∃ k:ℕ, n=2*k+1

    def A: Set ℕ :={17,13,25,0,11}

    example  : ∃ n:ℕ , n ∈ A ∧ impair n := sorry

    namespace version1
      example  : ∃ n:ℕ , n ∈ A ∧ impair n :=
        Exists.intro 17 
        (
          And.intro
          (Or.inl (Eq.refl 17) : 17 ∈ A) 
          (Exists.intro 8 (
            calc 17=2*8+1 := by norm_num
          ))
        )
    end version1
  end assertion1

  namespace assertion2
    --import Mathlib.Data.Real.Basic
    example: ∃x:ℝ, (x-1)^2 = x^2 - 2*x +1:= sorry

    namespace version1
      example: ∃x:ℝ, (x-1)^2 = x^2 - 2*x +1:=
        Exists.intro 0 (   -- introduction de 0 comme candidat 
          calc  ((0:ℝ)-1)^2 = 0^2 - 2*0+ 1 := by norm_num
        )
    end version1
  end assertion2

  namespace assertion3
    --import Mathlib.Data.Real.Basic
    example: ∃x:ℝ, (x-1)^2 = x^2 - 1 := sorry
    namespace version1
      example: ∃x:ℝ, (x-1)^2 = x^2 - 1 :=
        Exists.intro 1 (   -- introduction de 1 comme candidat 
          calc  ((1:ℝ)-1)^2 = 1^2 - 1 := by norm_num
        )
    end version1
  end assertion3

  namespace assertion4
    --import Mathlib.Data.Int.Basic
    --import Mathlib.Data.Finset.Basic
    --import Mathlib.Tactic.NormNum

    def A : Set ℤ := {1,2}

    example : ∃ x:ℤ, x ∈ A ∧  x^2-5*x+6 = 0 := sorry

    namespace version1
      example : ∃ x:ℤ, x ∈ A ∧  x^2-5*x+6 = 0 :=
        Exists.intro 2
        (
          And.intro
              (Or.inr (Eq.refl 2 : (2:ℤ)=2))
              (calc
                (2:ℤ)^2-5*2+6=0 := by norm_num
              )
        )
    end version1
  end assertion4

  namespace assertion5
    --import Mathlib.Data.Int.Basic
    --import Mathlib.Tactic.NormNum

    def impair (n:ℤ) : Prop := ∃ k:ℤ , n=2*k+1
    example : impair 7 := sorry

    namespace version1
      example : impair 7 := 
        Exists.intro 3 (
          calc 7=2*(3:ℤ)+1 := by norm_num
        )
    end version1
  end assertion5

end ex_1_1_3_4


namespace ex_1_1_3_5
  namespace assertion1
    --import Mathlib.Data.Int.Basic
    --import Mathlib.Tactic.NormNum
    --import Mathlib.Tactic.Ring

    def impair (n:ℤ) : Prop := ∃ k:ℤ , n=2*k+1

    example : ∀ n:ℤ , impair n → impair (3*n+2) := sorry

    namespace version1
      example : ∀ n:ℤ , impair n → impair (3*n+2) := 
        λ n:ℤ ↦
            λ h: impair n ↦
              Exists.elim h
              (
                  λ (k:ℤ) (hn: n=2*k+1) ↦ 
                    (
                      Exists.intro (3*k+2) (
                          calc
                            3*n+2 = 3*(2*k+1)+2  := congr_arg (fun z:ℤ ↦ 3*z+2) (hn:n=2*k+1)
                            _     = 2*(3*k+2)+1  := by ring
                      )
                    )
              )
    end version1
  end assertion1

  namespace assertion2
    --import Mathlib.Data.Int.Basic
    --import Mathlib.Tactic.NormNum
    --import Mathlib.Tactic.Ring

    def impair (n:ℤ) : Prop := ∃ k:ℤ , n=2*k+1

    example : ∀ x y:ℤ , impair x → impair y → impair (x+y+1) := sorry

    namespace version1
      example : ∀ x y:ℤ , impair x → impair y → impair (x+y+1) := 
      λ x y:ℤ ↦
        λ (hx: impair x) (hy: impair y)  ↦
        Exists.elim hx
        (
          λ (p:ℤ) (hxp: x=2*p+1) ↦ 
          (
          Exists.elim hy
          (
            λ (q:ℤ) (hyq: y=2*q+1) ↦ 
            (
            Exists.intro (p+q+1) (
              calc
              x+y+1 = (2*p+1)+y+1       := congr_arg 
                                            (fun z:ℤ ↦ z+y+1)
                                            (hxp:x=2*p+1)
              _     = (2*p+1)+(2*q+1)+1 := congr_arg
                                            (fun z:ℤ ↦ (2*p+1)+z+1)
                                            (hyq:y=2*q+1)
              _     = 2*(p+q+1)+1       := by ring
            )
            )
          )
          )
      )
    end version1
  end assertion2

  namespace assertion3
    --import Mathlib.Data.Int.Basic
    def pair (n:ℤ) : Prop := ∃ k:ℤ , n=2*k
  end assertion3

end ex_1_1_3_5

namespace ex_1_1_4_1
  --import Mathlib.Data.Int.Basic 
  --import Mathlib.Data.Real.Basic 

  -- des erreurs sont signalées pour chaque variable libre non définie dans le contexte
  def P1 :Prop := b*x^2 ≥ 0
  def P2 :Prop := ∀ x:ℝ , b*x^2 ≥ 0
  def P3 :Prop := f u ≤ M
  def P4 :Prop := t ≥ 0 → f t ≤ M
  def P5 :Prop := ∀ w:ℝ , f w ≤ M
  def P6 :Prop := a ≥ 0 →  ∀ a:ℝ , f a ≤ M
  def P7 :Prop := a ≥ 0 →  ∀ r:ℝ , f r ≤ M
  def P8 :Prop := ∃ M:ℝ ,∀ x:ℝ , f x ≤ M
  def P9 :Prop := ∃ M:ℝ ,∀ u:ℝ , f x ≤ M
  def P10:Prop := ∀ x:ℝ, (x+m=2 ↔ x=-m+2)

  -- on précise les variables libres comme variables dont dépendent ces assertions :
  def Q1 (b:ℝ) (x:ℝ)           :Prop := b*x^2 ≥ 0
  def Q2 (b:ℝ)                 :Prop := ∀ x:ℝ , b*x^2 ≥ 0
  def Q3 (f:ℝ → ℝ) (M:ℝ) (u:ℝ) :Prop := f u ≤ M
  def Q4 (f:ℝ → ℝ) (M:ℝ) (t:ℝ) :Prop := t ≥ 0 → f t ≤ M
  def Q5 (f:ℝ → ℝ) (M:ℝ)       :Prop := ∀ w:ℝ , f w ≤ M
  def Q6 (f:ℝ → ℝ) (M:ℝ) (a:ℝ) :Prop := a ≥ 0 →  ∀ a:ℝ , f a ≤ M -- ambigu !
  def Q7 (f:ℝ → ℝ) (M:ℝ) (a:ℝ) :Prop := a ≥ 0 →  ∀ r:ℝ , f r ≤ M -- mieux !
  def Q8 (f:ℝ → ℝ)             :Prop := ∃ M:ℝ ,(∀ x:ℝ , f x ≤ M)
  def Q9 (f:ℝ → ℝ)       (x:ℝ) :Prop := ∃ M:ℝ ,(∀ u:ℝ , f x ≤ M) -- attention!
  def Q9'(f:ℝ → ℝ)       (x:ℝ) :Prop := ∃ M:ℝ , f x ≤ M          -- Q9 ↔ Q9'   ...
  def Q10      (m:ℝ)           :Prop := ∀ x:ℝ, (x+m=2 ↔ x=-m+2)
end ex_1_1_4_1


namespace ex_1_1_5_1
  namespace assertion1
    --import Mathlib.Data.Real.Basic 

    example : ¬ (∀ x:ℝ , (x-1)^2=x^2-1 ) := sorry

    namespace version1
      example : ¬ (∀ x:ℝ , (x-1)^2=x^2-1 ) := not_forall.mpr (
        Exists.intro 0 
          (
            calc (0-1)^2 ≠ (0:ℝ)^2 -1 := by norm_num 
          )
      )
    end version1
  end assertion1

  namespace assertion2
    --import Mathlib.Data.Nat.Basic 
    --import Mathlib.Data.Set.Basic 
    --import Mathlib.Data.Finset.Basic

    def impair (n:ℕ) : Prop := ∃ k:ℕ, n=2*k+1

    def A: Set ℕ :={17,13,25,0,11}

    example  : ¬ (∀n:ℕ , n ∈ A ∧ impair n) := sorry

    namespace version1
      #check not_forall
      example (n:ℕ): n+1 ≠ 0 := Nat.succ_ne_zero n

      example  : ¬ (∀n:ℕ , n ∈ A ∧ impair n) := not_forall.mpr (
        Exists.intro 0 
        (
          λ h: (0 ∈ A ∧ impair 0) ↦ 
          (
            Exists.elim (h.right)
            (
              λ (k:ℕ ) (hk:0 = 2*k+1) ↦ 
                have hk' : 2*k+1 ≠ 0 := Nat.succ_ne_zero (2*k)
                absurd (hk.symm) hk'
            )
          )
        )
      )
    end version1
  end assertion2

  namespace assertion3
    --import Mathlib.Data.Real.Basic 

    example : ¬ (∀ x:ℝ , x^2 < 0 ) := sorry

    namespace version1
      #check not_forall
      example : ¬ (∀ x:ℝ , x^2 < 0 ) := not_forall.mpr (
        Exists.intro 1 
          (
            have h : ¬ ( 1^2 < (0:ℝ)) := by norm_num 
            h
          )
      )
    end version1
  end assertion3

  namespace assertion4
    --import Mathlib.Data.Real.Basic 

    example : ¬ (∃ x:ℝ , x^2 < 0 ) := sorry

    namespace version1
      #check not_exists
      example : ¬ (∃ x:ℝ , x^2 < 0 ) := not_exists.mpr (
        λ x:ℝ ↦ 
          have h: ¬ (x^2 < 0) := not_lt_of_le (sq_nonneg x)
          h
      )
    end version1
  end assertion4

  namespace assertion5
    --import Mathlib.Data.Complex.Basic 
    -- on voit ici qu'une erreur est retournée car < n'est pas définie sur ℂ 
    def P:Prop := ∃ x:ℂ , x^2 < 0
  end assertion5

  namespace assertion6
    --import Mathlib.Logic.Basic
    #check not_forall
    #check not_exists
    example (E : Type) (P : E → Prop) : ¬(∀ x:E, P x) ↔ ∃ x:E, ¬P x := not_forall
    example (E : Type) (P : E → Prop) : ¬(∃ x:E, P x) ↔ ∀ x:E, ¬P x := not_exists
  end assertion6

end ex_1_1_5_1



namespace ex_1_1_7_1
  --import Mathlib.Data.Real.Basic 

  #check Real.add_lt_add_iff_left
  #check Real.zero_lt_one
  #check Eq.not_lt

  example : ∀ x:ℝ, ∃ y:ℝ , y>x := 
    λ x:ℝ ↦ 
        Exists.intro (x+1)
          (
            calc 
              x+1 > x+0 := (Real.add_lt_add_iff_left x).mpr (by norm_num : (1:ℝ)>(0:ℝ))
              _   = x   := add_zero x
          )

  example : ∀ x:ℝ, ∃ y:ℝ , y>x := 
    λ x:ℝ ↦ 
        Exists.intro (x+1)
          (
            calc 
              x+1 > x   := by norm_num
          )

  example : ∀ x:ℝ, ∃ y:ℝ , y>x := 
    λ x:ℝ ↦ 
        Exists.intro (x+1)
          (
            calc 
              x+1 > x   := lt_add_one x -- by library_search
          )


  example : ¬ (∃ y:ℝ , ∀ x:ℝ, y>x ) := not_exists.mpr (
    λ y:ℝ ↦ not_forall.mpr (
        Exists.intro (y)
          (
            have h: ¬ (y<y) := Eq.not_lt (Eq.refl y) 
            h
          )
      )
  )

end ex_1_1_7_1
