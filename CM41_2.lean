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

namespace ex_1_2_1_2

  namespace assertion1
    --import Mathlib.Data.Real.Basic

    example: ∀x:ℝ, (x-1)^2 = x^2 -2*x + 1  := sorry

    namespace version1
    end version1

    namespace version2
    end version2

    namespace version3
    end version3

  end assertion1

  namespace assertion2
    --import Mathlib.Data.Real.Basic

    example: ∀x:ℝ, x^2 ≥ 0  := sorry

    namespace version1
    end version1

    namespace version2
    end version2

  end assertion2

end ex_1_2_1_2


namespace voc_1_2_1_1

lemma P_imp_Q_iff (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) :=
  Iff.intro
  (
    λ h1 : P → Q ↦ 
      Or.elim (Classical.em P)
      (
        λ hP : P ↦
          have hQ : Q := h1 hP
          Or.inr hQ
      )
      (
         λ hnP : ¬ P ↦ 
         Or.inl hnP 
      )
  )
  (
    λ h2 : ¬P ∨ Q ↦ 
      λ hP :P ↦
        Or.elim h2
        (
          λ hnP : ¬P ↦ 
            absurd hP hnP 
        )
        (
          λ hQ : Q ↦
            hQ  
        ) 
  )


example (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) :=
  ⟨ λ h1  ↦  Classical.byCases (Or.inr ∘ h1) Or.inl, λ h2 hP ↦ Or.elim h2 (absurd hP) id ⟩ 


lemma not_P_imp_Q_iff (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := 
  Iff.intro
  (
    λ hnpq : ¬ (P→ Q) ↦ 
      And.intro
      (
         of_not_not (
           λ hnP : ¬ P ↦ 
             have hpq : P → Q := λ hP : P ↦ absurd hP hnP  
             absurd hpq  hnpq
         )
      )
      (
        λ hQ:Q ↦
          absurd (λ_ ↦ hQ ) hnpq
      )
  )
  ()


end voc_1_2_1_1

namespace ex_1_2_1_2
  --import Mathlib.Data.Real.Basic

  def P (x:ℝ ) : Prop := x=2
  def Q (x:ℝ ) : Prop := x^2=4
  def I (x:ℝ)  : Prop := (P x) → (Q x)
  def R (x:ℝ)  : Prop := (Q x) → (P x)
  
  namespace assertion1

    example: ¬ P 0 := show 0 ≠ 2   by norm_num
    example: ¬ Q 0 := show 0^2 ≠ 4 by norm_num
    example:   I 0 := λ hp0 : 0=2    ↦ absurd hp0 (by norm_num)
    example:   R 0 := λ hq0 : 0^2=4  ↦ absurd hq0 (by norm_num) 

    example: ¬ P 1 := show 1 ≠ 2   by norm_num
    example: ¬ Q 1 := show 1^2 ≠ 4 by norm_num
    example:   I 1 := λ hp1 : 1=2    ↦ absurd hp1 (by norm_num)
    example:   R 1 := λ hq1 : 1^2=4  ↦ absurd hq1 (by norm_num) 

    example:   P 2 := show 2 = 2   from rfl
    example:   Q 2 := show 2^2 = 4 by norm_num
    example:   I 2 := λ hp2 : 2=2    ↦ show 2^2 = 4 by norm_num
    example:   R 2 := λ hq2 : 2^2=4  ↦ show 2 =2    from rfl

    example: ¬ P (-2) := show -2 ≠ 2     by norm_num
    example:   Q (-2) := show (-2)^2 = 4 by norm_num
    example:   I (-2) := λ hpm2: (-2)=2 ↦ absurd hpm2 (by norm_num) 
    example: ¬ R (-2) := λ hrm2 : R (-2)  ↦ 
                            have h1 : (-2)^2 = 4 := by norm_num
                            have h2 : -2=2       := hrm2 h1
                            absurd h2 (by norm_num) 

  end assertion1

  namespace assertion2
    --import Mathlib.Data.Real.Basic

    example: ∀x:ℝ, I x  := 
      λ x:ℝ ↦
        λ hP: x=2 ↦
          calc 
            x^2 = 2^2 := congr_arg (fun z ↦z^2) hP
            _   = 4   := by norm_num

  end assertion2

  namespace assertion3
    --import Mathlib.Data.Real.Basic
    namespace version1
    example: ¬( ∀x:ℝ, R x ) := 
      have hqm2  : (-2)^2 = 4 := by norm_num
      have hnpm2 : -2 ≠ 2     := by norm_num
      not_forall.mpr (
        Exists.intro (-2) ((voc_1_2_1_1.not_P_imp_Q_iff (Q (-2)) (P (-2))).mpr (
          And.intro
            (hqm2:     Q (-2))
            (hnpm2 : ¬ P (-2))
        ))
      )
    end version1

    namespace version2
    example: ¬( ∀x:ℝ, R x ) := 
      λ h :  ∀x:ℝ, R x ↦ 
        have h1 : (-2)^2 = 4 := by norm_num
        have h2 : -2 = 2     := h (-2) h1
        absurd h2 (by norm_num) 
    end version2

  end assertion3

end ex_1_2_1_2

namespace ex_1_2_1_3

  namespace assertion1
    --import Mathlib.Data.Real.Basic

    example: ∀a b:ℚ , (a-b = 4) ∧ a*b=1 → (a+b)^2 = 20  := 
      λ a b : ℚ ↦ 
        λ h :  (a-b = 4) ∧ a*b=1 ↦ 
          calc 
            (a+b)^2 = (a-b)^2 + 4*(a*b)  := by ring_nf
            _       = 4^2     + 4*(a*b)  := congr_arg (fun z ↦ z^2 + 4*(a*b)) h.left
            _       = 4^2     +4*1       := congr_arg (fun z ↦ 4^2 + 4*z    ) h.right
            _       = 20                 := by norm_num


  end assertion1

  namespace assertion2
    --import Mathlib.Data.Real.Basic

    example : ∀ x:ℤ ,∀ y:ℤ , (x+3 ≤ 2   ∧   y+2*x ≥ 3 ) → y>3 :=
      λ x y : ℤ  ↦ 
        λ h  : x+3 ≤ 2   ∧   y+2*x ≥ 3 ↦ 
          calc 
            y = y+2*x - 2*(x+3) + 6 := by ring_nf
            _ ≥ 3 - 2*(x+3) + 6     := by rel [h.right]
            _ ≥ 3 -2*2 + 6          := by rel [h.left]
            _ = 5                   := by norm_num
            _ > 3                   := by norm_num

  end assertion2

  namespace assertion3
    --import Mathlib.Data.Real.Basic

    def pair   (n:ℤ ) : Prop := ∃ k:ℤ, n=2*k 
    def impair (n:ℤ ) : Prop := ∃ k:ℤ, n=2*k+1

    example : ∀ m n :ℤ  , impair m ∧ impair n → pair (m+n) :=
      λ m n : ℤ   ↦
        λ h :   impair m ∧ impair n ↦
          Exists.elim (h.left : impair m) (
            λ j:ℤ ↦  λ hm : m=2*j +1 ↦ 
              Exists.elim (h.right: impair n) (
                λ k:ℤ ↦  λ hn : n=2*k+1  ↦ 
                  have hmn : _ :=
                    calc 
                      m+n =  2*j+1+n        := congr_arg (fun z↦ z+n) hm
                      _   =  2*j+1+(2*k+1)  := congr_arg (fun z↦ 2*j+1+z) hn
                      _   =  2*(j+k+1)      := by ring_nf
                  Exists.intro (j+k+1) hmn
              )
          )
  end assertion3

end ex_1_2_1_3






namespace ex_1_2_1_4

  namespace assertion1
    --import Mathlib.Data.Real.Basic

    def magic (a:ℝ):Prop := (a^2≤2) ∧ (∀y:ℝ,((y^2 ≤ 2)→a≥y))


    example : ∀ a :ℝ, ∀ b :ℝ,   magic a  ∧   magic b →  a = b := 
      λ a b: ℝ ↦
        λ h: magic a ∧  magic b ↦
            have h1  : a ≥ b := h.left.right b h.right.left
            have h2  : a ≤ b := h.right.right a h.left.left
            have h3  : a = b := le_antisymm h2 h1
            h3
  end assertion1

end ex_1_2_1_4

namespace ex_1_2_1_5

  def prop1a           : Prop := ∀ x:ℝ, x ≤ -2 → x^2 ≥ 4
  def prop1b (f:ℝ → ℝ) : Prop := ∀ x:ℝ,∀ y:ℝ, x ≤ y → f x ≤ f y
  def prop1c           : Prop := ∀ x ∈ ({1, 2}:Set ℝ ),  x^2-3*x+2 = 0
  #print prop1c

  def prop2a : Prop := ∃ x ∈ ({0, 1}:Set ℝ  ),  x^2-3*x+2 = 0
  #print prop2a

  def prop2b : Prop := ∃ x:ℝ, x≤0 ∧ x^2-2 = 0

end ex_1_2_1_5

namespace ex_1_2_1_7

def ConditionSuffisante (P Q : Prop): Prop := P → Q


example (x:ℝ) :  ConditionSuffisante (x=1) (x^5-x^4+x^3-x^2+x-1=0) :=
  λ h : x=1 ↦ 
    calc
      x^5-x^4+x^3-x^2+x-1 = 1^5-1^4+1^3-1^2+1-1  := by rw[h]
      _                   = 0                    := by norm_num
end ex_1_2_1_7


namespace ex_1_2_1_8

notation:76 "√" x:68 => (Real.sqrt x)

example (x:ℝ) (hx: x+7 ≥ 0) (h: √(x+7) = x+1) : x=2 ∨ x=-3 :=
  have h' : (x-2)*(x-(-3))=0 :=
    calc
      (x-2)*(x-(-3))  = (x+1)^2    - (x+7) := by ring_nf
      _               = (√(x+7))^2 - (x+7) := by rw[h]
      _               = (x+7)      - (x+7) := by rw[Real.sq_sqrt hx]
      _               = 0                  := by ring_nf
  Or.imp (sub_eq_zero.mp) (sub_eq_zero.mp) (mul_eq_zero.mp h')

example : ∃ (x:ℝ), ( x+7 ≥ 0 ) ∧   ¬ ( (x=2 ∨ x=-3) →  ( √(x+7) = x+1 )  ):=
  Exists.intro (-3)
  (
    And.intro
      (
        by norm_num : -3+7 ≥ (0:ℝ)
      )
      (
        not_imp.mpr (
          And.intro
            (
              Or.inr rfl
            )
            (
              λ h0:  √(-3+7) = -3+1 ↦ 
                have h1: -3+1 = (2:ℝ) :=
                  calc 
                    -3+1    = √(-3+7):= h0.symm
                    _       = √(2^2) := by norm_num
                    _       = 2      := Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)

                absurd h1 (by norm_num)
            )
        )
      )
  )


end ex_1_2_1_8

namespace ex_1_2_1_9

def ConditionNecessaire (P Q : Prop): Prop := Q → P

example (x:ℝ) (hx: x+6 ≥ 0) :  ConditionNecessaire  (x=-2 ∨ x=-5)  ( √(x+6) = x+4) :=
  λ h: √(x+6) = x+4 ↦ 
  have h' : (x-(-2))*(x-(-5))=0 :=
    calc
      (x-(-2))*(x-(-5)) = (x+4)^2    - (x+6) := by ring_nf
      _                 = (√(x+6))^2 - (x+6) := by rw[h]
      _                 = (x+6)      - (x+6) := by rw[Real.sq_sqrt hx]
      _                 = 0                  := by ring_nf
  Or.imp (sub_eq_zero.mp) (sub_eq_zero.mp) (mul_eq_zero.mp h')

example (x:ℝ) (b:ℝ) (hx: x+(b+2) ≥ 0) :
     ConditionNecessaire  (x=-(b+1) ∨ x=-(b-2))  ( √(x+(b+2)) = x+b) :=
  λ h: √(x+(b+2)) = x+b ↦ 
  have h' : (x-(-(b+1)))*(x-(-(b-2)))=0 :=
    calc
       (x-(-(b+1)))*(x-(-(b-2))) = (x+b)^2        - (x+(b+2)) := by ring_nf
      _                          = (√(x+(b+2)))^2 - (x+(b+2)) := by rw[h]
      _                          = (x+(b+2))      - (x+(b+2)) := by rw[Real.sq_sqrt hx]
      _                          = 0                          := by ring_nf
  Or.imp (sub_eq_zero.mp) (sub_eq_zero.mp) (mul_eq_zero.mp h')


example (x:ℝ) (b:ℝ) (hx: x+(b+6) ≥ 0) :
     ConditionNecessaire  (x=-(b-3) ∨ x=-(b+2))  ( √(x+(b+6)) = x+b) :=
  λ h: √(x+(b+6)) = x+b ↦ 
  have h' : (x-(-(b-3)))*(x-(-(b+2)))=0 :=
    calc
       (x-(-(b-3)))*(x-(-(b+2))) = (x+b)^2        - (x+(b+6)) := by ring_nf
      _                          = (√(x+(b+6)))^2 - (x+(b+6)) := by rw[h]
      _                          = (x+(b+6))      - (x+(b+6)) := by rw[Real.sq_sqrt hx]
      _                          = 0                          := by ring_nf
  Or.imp (sub_eq_zero.mp) (sub_eq_zero.mp) (mul_eq_zero.mp h')


end ex_1_2_1_9


namespace th_1_2_2_1
example : ∀ n:ℕ,  n^2 ≥ n :=
  Nat.rec
  -- initialisation
    (calc 0^2 ≥ 0 := by norm_num)
  -- hérédité
    ( 
      λ k: ℕ ↦ 
        λ ih: k^2 ≥ k ↦ 
        calc
          (k+1)^2 = k^2+(2*k+1)  := by ring_nf
          _       ≥ k +(2*k+1)   := add_le_add_right ih _
          _       = (k+1)+2*k    := by ring_nf
          _       ≥ k+1          := le_add_of_nonneg_right
                        (
                          (mul_nonneg (by norm_num : 2 ≥ 0)
                                      (zero_le k: k ≥ 0) 
                          ): 2*k ≥ 0
                        )
    )


example : ∀ n:ℕ , 2^n > n :=
  Nat.rec
    (by norm_num : 2^0 > 0)
    (
       λ k:ℕ  ↦
         λ ih: 2^k > k ↦
           have ih' : 2^k ≥ k+1 := ih 
           calc
             2^(k+1) = 2*2^k   := by ring_nf
             _       ≥ 2*(k+1) := (mul_le_mul_left (by norm_num : 2>0)).mpr ih'
             _       = k+1+1+k := by ring_nf
             _       ≥ k+1+1   := Nat.le_add_right _ k
             _       > k+1     := Nat.lt.base _ 
    )

 example : ∀ n:ℕ , 2^n > n :=
  Nat.rec
    (by norm_num : 2^0 > 0)
    (
       λ k:ℕ  ↦
         λ ih: 2^k > k ↦
           have ih' : 2^k ≥ k+1 := ih 
           calc
             2^(k+1) = 2*2^k   := by ring_nf
             _       ≥ 2*(k+1) := by simp[ih']
             _       = k+1+1+k := by ring_nf
             _       ≥ k+1+1   := by simp
             _       > k+1     := by simp 
    )

def P (n:ℕ ) : Prop := ∃ k:ℤ , 4^n+1 = 3*k
def Q (n:ℕ ) : Prop := ∃ k:ℤ , 4^n+1 = 3*k+2

lemma Phered : ∀ n:ℕ, P n → P (n+1) :=
  λ n:ℕ ↦  
    λ ih : P n ↦ 
      Exists.elim ih 
      (
        λ (k:ℤ) (h:4^n+1 = 3*k) ↦  
          Exists.intro (4*k-1)
          (
            calc
              4^(n+1)+1 = 4*(4^n+1)-(3:ℤ) := by ring_nf
              _         = 4*(3*k)-3       := by rw[h]
              _         = 3*(4*k-1)       := by ring_nf
          )
      )

lemma Qhered : ∀ n:ℕ, Q n → Q (n+1) :=
  λ n:ℕ ↦  
    λ ih : Q n ↦ 
      Exists.elim ih 
      (
        λ (k:ℤ) (h:4^n+1 = 3*k+2) ↦  
          Exists.intro (4*k+1)
          (
            calc
              4^(n+1)+1 = 4*(4^n+1)-(3:ℤ) := by ring_nf
              _         = 4*(3*k+2)-3     := by rw[h]
              _         = 3*(4*k+1) +2    := by ring_nf
          )
      )

lemma Qtrue : ∀ n:ℕ, Q n :=
  Nat.rec
    (Exists.intro 0 (by norm_num))
    (Qhered)


lemma not_3_div_2 : ¬(∃ k:ℤ , 2=3*k) :=
  λ h : ∃ k:ℤ , 2=3*k  ↦ 
    Exists.elim h
    (
      λ(k:ℤ )  (h' :2 = 3*k) ↦
        Or.elim (le_or_gt k 0)
        (
          λ h0 : k ≤ 0 ↦
            absurd
              (
                calc
                  2 = 3*k := h'
                  _ ≤ 3*0 := by rel[h0] 
              )
              (by norm_num)
        )
        (
          λ h1 : k ≥ 1 ↦
            absurd
              (
                calc
                  2 = 3*k := h'
                  _ ≥ 3*1 := by rel[h1] 
              )
              (by norm_num)
        )
    )

example : ¬ (∃n:ℕ, P n) :=
  not_exists.mpr 
  (
    λ n:ℕ ↦
      λ h: P n ↦ 
        Exists.elim h
        (
          λ(k:ℤ )  (hP:4^n+1 = 3*k) ↦
            Exists.elim (Qtrue n)
            (
              λ(k':ℤ )  (hQ:4^n+1 = 3*k'+2) ↦
              have h_3_div_2 : ∃ a:ℤ, 2 = 3*a := Exists.intro (k-k')
                (
                  calc 
                    2 = 3*k'+2-3*k' := by ring_nf
                    _ = 4^n+1-3*k'  := by rw[hQ]
                    _ = 3*k-3*k'    := by rw[hP]
                    _ = 3*(k-k')    := by ring_nf
                )
              absurd h_3_div_2 not_3_div_2

            )
        )
  )


end th_1_2_2_1

namespace ex_1_2_2_3


theorem rec_double {motive : ℕ → Prop} {m : ℕ }  :
  (motive m) →   (motive (m+1)) →
  (∀n:ℕ, n≥ m → motive n → motive (n+1) → motive (n+2)  ) → 
  (∀ n:ℕ ,n≥ m → motive n)
    :=
    λ base1 base2 step ↦ 
    let P (n:ℕ ):= (motive n)∧ (motive (n+1))
    have hle : ∀ n:ℕ, n≥m → P n   := 
      Nat.le_induction
        (And.intro base1 base2 : P m)
        (λ (k:ℕ) (hk:k ≥ m) (ik:P k) ↦
          (And.intro ik.right (step k hk ik.left ik.right)  : (P (k+1)) )
        ) 
    λ n hn ↦ (hle n hn).left



def F (n:ℕ) :ℚ := match n with
  | 0 => 0
  | 1 => 1
--  | Nat.succ (Nat.succ n) => (F (Nat.succ n) )+ (F n)
  | n+2 => (F (n+1) )+ (F n)

#eval F 7


example : ∀n:ℕ , n ≥ 0 → F n < (5/3)^n :=
  rec_double 
  (
    by norm_num : (0:ℚ)  < (5/3)^0
  )
  (
    by norm_num : (1:ℚ) < (5/3)^1
  )
  (
    λ n : ℕ ↦ 
     λ _ : n ≥ 0 ↦ 
       λ ih1 :   F n     < (5/3)^n     ↦ 
       λ ih2 :   F (n+1) < (5/3)^(n+1) ↦ 
         have hu1 : (24/9:ℚ) < ((5^2)/(3^2):ℚ) := by norm_num
         calc
           F (n+2)  = (F (n+1) )   + (F n)      := rfl
           _        <  (5/3)^(n+1) + (5/3)^n    := by rel [ih1,ih2]
           _        = (5/3)^n * (24/9:ℚ)        := by ring_nf
           _        ≤ (5/3)^n * ((5^2)/(3^2):ℚ) := by rel[hu1]
           _        = (5/3)^n * ((5/3:ℚ)^2)     := by norm_num
           _        = (5/3)^(n+2)               := by ring_nf
  )

end ex_1_2_2_3


namespace ex_1_2_2_4


theorem rec_forte {motive : ℕ → Prop} {m : ℕ }  :
  (motive m) →   
  (∀n:ℕ, n≥ m → (∀ j:ℕ , m ≤ j ∧ j ≤ n → motive j) → motive (n+1)   ) → 
  (∀ n:ℕ ,n≥ m → motive n)
    :=
    λ base step ↦ 
    let P (n:ℕ ):= ∀ j:ℕ , m ≤ j ∧ j ≤ n → motive j
    have hle : ∀ n:ℕ, n≥m → P n   := 
      Nat.le_induction
        (λ j hmjm ↦  ((le_antisymm hmjm.left hmjm.right) ▸ base )      )
        (λ (k:ℕ) (hk:k ≥ m) (ik:P k) ↦
          ((λ j (hmjk1:( m ≤ j ∧ j ≤ k+1)) ↦ 
            Or.elim (Nat.le_or_eq_of_le_succ hmjk1.right)
            (λ hjk  ↦ ik j (And.intro hmjk1.left hjk) )
            (λ hjk1 ↦ hjk1.symm ▸   (step k hk ik) )  
          ) : (P (k+1)))
        )
    λ n hn ↦ hle n hn n (And.intro hn (le_refl n))


mutual 
  def u (n:ℕ) : ℚ := match n with
    | 0   => 1
    | n+1 => ( (v n) + (u n)^2  )/(n+1)

  def v (n:ℕ) : ℚ := match n with
    | 0   => 0
    | n+1 => (v n) + (u n)^2 -- ( BigSumN 0 n u )/(n+1)
end

#eval (u 0) -- 1
#eval (v 1) -- 1^2

#eval (u 1) -- 1/1 * (1^2) = 1
#eval (v 2) -- 1^2 + 1^2

#eval (u 2) -- 1/2 * (1^2 + 1^2) = 1
#eval (v 3) -- 1^2 + 1^2 + 1^2


lemma L0E (n:ℕ ) : n   + 1^2 = (↑(n+1)  : ℚ ) := 
  calc
     n + 1 ^ 2      = ((n + 1) : ℚ ) := by rw[one_pow 2]
     (n:ℚ) + 1      = (n:ℚ) + (1:ℚ)  := congrArg (HAdd.hAdd (n:ℚ)) Nat.cast_one.symm
     (n:ℚ) + (1:ℚ)  = ↑(n+1)         := (Nat.cast_add n 1).symm
   
example : ∀ n:ℕ , n≥ 0 →  v n = n ∧ u n = 1 :=
  rec_forte
  (And.intro (rfl:v 0 = 0) (rfl : u 0 = 1))
  (
    λ n : ℕ ↦ 
     λ _ : n ≥ 0 ↦ 
      λ ih : ∀ j:ℕ , 0 ≤ j ∧ j ≤ n → v j = j ∧  u j = 1   ↦  
        have ih1 : v n = n ∧ u n = 1  := 
         ih n (And.intro (zero_le n) (le_refl n) )
        And.intro
        (
          calc
            v (n+1) = v n + (u n)^2 := rfl
            _       = n   + 1^2     := by rw[ ih1.left, ih1.right ]
            _       = ↑(n+1)        := L0E n
        )
        (
          calc 
            u (n+1) = ((v n) + (u n)^2)/(n+1)  := rfl
            _       =  (n +1^2)/(n+1)          := by rw[ ih1.left, ih1.right ]
            _       =  (n +1)/(n+1)            := by norm_num
            _       = 1                        := div_self (Nat.cast_add_one_ne_zero n)
        )
  )

end ex_1_2_2_4


namespace ex_1_2_2_5

theorem rec_finie {motive : ℕ → Prop} {a  b: ℕ }   :
  (motive a)  →
  (∀ n:ℕ, n ≥ a → n + 1 ≤ b → motive n → motive (n+1) ) → 
  (∀ n:ℕ ,n ≥ a → n ≤ b → motive n)
    :=
    λ base step ↦ 
    let P (n:ℕ) (_ : n ≥ a) := n ≥ a → n ≤ b → (motive n)
    have hle : ∀ n:ℕ, (hn: n≥ a)  → P n hn  := 
      Nat.le_induction
        (λ_ _  ↦ base)
        (λ n hna ih ↦ 
          λ _ hn1b ↦
              step n hna hn1b (ih hna (Nat.le_of_succ_le hn1b))
        )
    λ n ha hb ↦ (hle n ha) ha hb


end ex_1_2_2_5
