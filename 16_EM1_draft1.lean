import Esisar.Exam

namespace exam


-- Exercice 1
example : ∃ k:ℤ, 17 = 3*k+2        := sorry
example : ∃ k:ℤ, 14 = 5*k-1        := sorry
example : ∃ k:ℤ, 26 = 7*k+5        := sorry

-- Exercice 2
example : ∀ x:ℝ, 3*x+5 = 2  → x=-1   := sorry
example : ∀ x:ℝ, 2*x+5 = 9  → x= 2   := sorry
example : ∀ x:ℝ, 7*x-8 =-1  → x= 1   := sorry

-- Exercice 3
example : ∀ x:ℝ, x=-1 → 3*x+5 = 2    := sorry
example : ∀ x:ℝ, x= 2 → 2*x+5 = 9    := sorry
example : ∀ x:ℝ, x= 1 → 7*x-8 =-1    := sorry

-- Exercice 4
example : ∀ x:ℝ, 3*x+5 = 2  ↔ x=-1   := sorry
example : ∀ x:ℝ, 2*x+5 = 9  ↔ x= 2   := sorry
example : ∀ x:ℝ, 7*x-8 =-1  ↔ x= 1   := sorry


-- Exercice 5
def impair (x:ℕ) : Prop := ∃ k:ℤ, x = 2*k+1 
def pair   (x:ℕ) : Prop := ∃ k:ℤ, x = 2*k
example : ∀x:ℕ,∀y:ℕ, impair x ∧ impair y → pair (x+y)     := sorry
example : ∀x:ℕ,∀y:ℕ, pair   x ∧ impair y → impair (x+y)     := sorry
example : ∀x:ℕ,∀y:ℕ, pair   x ∧ pair   y → pair (x+y)     := sorry


-- Exercice 6
example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P  := λ _ _ ↦ And.symm
example : ∀ (P Q : Prop), P ∨ Q → Q ∨ P  := sorry
example : ∀ (P Q : Prop), P ∧ Q → Q ∨ P  := sorry
example : ∀ (P Q : Prop), P ∧ Q → P ∨ Q  := sorry


-- Exercice 7
example : ∀ (P Q R : Prop), (P → R) → (P ∨ Q → Q ∨ R )  := sorry
--example : ∀ (P Q R : Prop), (P → R) → (P ∧ Q → Q ∧ R )  := sorry
--example : ∀ (P Q : Prop), (P → Q) → (P ∨ Q → Q )  := sorry
--example : ∀ (P Q : Prop), (P → Q) → (P → P ∧ Q )  := sorry
example : ∀ (P Q : Prop), (P → Q) → (P ∨ Q ↔  Q )  := sorry
example : ∀ P Q :Prop,  (P → Q) → (P ↔ (P ∧ Q)) :=  sorry

--example : ∀ (P Q : Prop), (P → Q) ↔ (P ∨ Q ↔  Q )  := sorry
--example : ∀ P Q :Prop,  (P → Q) ↔ (P ↔ (P ∧ Q)) :=  sorry
example : ∀ (P Q : Prop),  (P ∨ Q →   Q ) → (P → Q)   := sorry

example : ∀ P Q :Prop, (P →  (P ∧ Q)) →  (P → Q)  :=  by sorry


-- Exercice 8

example : ∀ a b :ℝ , (∀ x:ℝ,  x ≥ b → x ≥ a ) ↔  (a ≤ b) := sorry
example : ∀ a b :ℝ , (∀ x:ℝ,  x ≥ b → x ≥ a ) ↔  (a ≤ b) := sorry
example : ∀ a b :ℝ , (∀ x:ℝ,  x ≤ b → x ≤ a ) ↔  (b ≤ a) := sorry


-- Exercice 9

example : ∀ a b:ℝ , (∀x:ℝ, (a+1) * b *  x + a = 0) ↔   (a = 0 ∧ b = 0) :=  sorry
example : ∀ a b:ℝ , (∀x:ℝ,a * x - b = 0) ↔  (a = 0 ∧ b = 0) :=  sorry
example : ∀ a b:ℝ , (∀x:ℝ,a  + b * x^2 = 0) ↔  (a = 0 ∧ b = 0) :=  sorry


-- Exercice 10
example : ∀ P Q R:Prop,  P ∨ (Q ∧ R)  ↔ (P ∨ Q) ∧ (P ∨ R) := sorry
example : ∀ P Q R:Prop,  P ∧ (Q ∨ R)  ↔ (P ∧ Q) ∨ (P ∧ R) := sorry


-- Exercice 11
example : ∀ x:ℝ, x^2=x → ¬(x=3 ∨ x=-4 ) := sorry
example : ∀ x:ℝ, x^3 - 2*x  = 1 → ¬(x=2 ∨ x=-1 ) := sorry
example : ∀ x:ℝ, 2*x^4+x^2 = 2 → ¬(x=3 ∨ x=-2 ) := sorry

-- Exercice 12
example : ∀ P Q : Prop,  (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) :=sorry
example : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) := sorry
example : ∀ P Q : Prop,  (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) := sorry 
--example : ∀ P Q : Prop, ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q) := sorry -- classical

-- Exercice 13
lemma imp_of_ccl' : ∀ P Q : Prop,  Q →  (P → Q) := sorry
lemma imp_of_not' : ∀ P Q : Prop,  (¬ P) →  (P → Q) := sorry

#check of_not_not

example (P Q: Prop) :  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := sorry
example : ∀ P Q : Prop,   (P → Q) ↔ (¬ P ∨ Q)  := sorry
example :  ∀ P Q : Prop,  (¬Q → ¬P) ↔(P → Q)  :=  sorry

example :  ∀ P Q : Prop,  (¬Q → ¬P) ↔(P → Q)  :=  sorry
example : ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  := sorry
example : ∀ P Q : Prop,   (P → Q) ↔ (¬ P ∨ Q)  := sorry
example : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := sorry






example : ∀ P Q R:Prop,  (P ∧ Q) ∧ R  ↔ P ∧ (Q ∧ R) :=  sorry
example : ∀ P Q R:Prop,  (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=   sorry
lemma and_iff_of_imp' : ∀ P Q :Prop,  (P → Q) → ((P ∧ Q) ↔ P) :=  sorry
lemma imp_of_le' : ∀ a b :ℝ ,(a ≤ b) → (∀ x:ℝ,  x ≥ b → x ≥ a ) := sorry
example : ∀ s:ℝ,  (s ≥ 3 ∧ s ≥ 2) ↔ (s ≥ 3)  :=  sorry
example : ∀ s:ℝ,  (s ≥ 3 ∧ s ≥ 2) ↔ (s ≥ 3)  :=  sorry

example : ∀ x:ℝ, x^2=4 → x ≠ 3 := sorry
example : ∀ P Q : Prop,  (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) :=sorry
example : ∀ x:ℝ, x^2=x → ¬(x=2 ∨ x=-1 ) := sorry
lemma imp_of_ccl' : ∀ P Q : Prop,  Q →  (P → Q) := sorry
lemma imp_of_not' : ∀ P Q : Prop,  (¬ P) →  (P → Q) := sorry
example : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) := sorry
example : ∀ P Q : Prop,  (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) := sorry 
example : ∀ P Q : Prop, ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q) := sorry -- classical
set_option push_neg.use_distrib true
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by push_neg ; rfl
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x > M ) ↔ (∀ M:ℝ, ∃ x:ℝ , f x ≤  M ) := by push_neg ; rfl  -- f n'est pas minorée
example : ¬ (∃ y:ℝ, ∀ x:ℕ  , y > x ) ↔ (∀ y:ℝ, ∃ x:ℕ  , y ≤  x ) := by push_neg ; rfl   -- il n'existe pas de réel strictement supérieur à n'importe quel entier naturel
example (f:ℝ → ℝ ): ¬ (∃ m:ℝ,∃ M:ℝ, ∀ x:ℝ , (f x ≥ m) ∧ (f x ≤ M)  ) ↔ (∀ m:ℝ, ∀ M:ℝ, ∃ x:ℝ , (f x < m) ∨ (f x > M)  ) := by push_neg ; rfl  -- f n'est pas bornée
theorem not_exists_esisar' (α : Type) (P : α → Prop) : ¬ (∃ x:α, P x) ↔ ∀ x:α, ¬ P x := sorry
theorem not_forall_esisar' (α : Type) (P : α → Prop) : ¬ (∀ x:α, P x) ↔ ∃ x:α, ¬ P x := sorry
theorem not_forall_not_esisar' (α : Type) (P : α → Prop) : ¬ (∀ x:α, ¬ P x) ↔ ∃ x:α, P x := sorry
theorem not_exists_not_esisar' (α : Type) (P : α → Prop) : ¬ (∃ x:α, ¬ P x) ↔ ∀ x:α, P x := sorry

def nulle'  (f:ℝ→ℝ) : Prop := ∀ x:ℝ, f x = 0
def positive' (f:ℝ→ℝ) : Prop :=  ∀ x:ℝ, f x ≥  0
def s_annule' (f:ℝ→ℝ) : Prop :=  ∃ x:ℝ, f x =  0
def g' (a:ℝ) : ℝ → ℝ :=  fun   x:ℝ ↦  x^2 + a

example : ¬(s_annule' (g' 1))  := sorry
example : (s_annule' (g' 0)) := sorry
example : ¬ (nulle' (g' 0)) := sorry
example : (positive' (g' 2)) := sorry  
example : ¬ (positive' (g' (-1))) := sorry


lemma not_imp_not_esisar' :  ∀ P Q : Prop,  (¬Q → ¬P) ↔(P → Q)  :=  sorry
example : ∀ n:ℕ,  pair (n^2) → pair n := sorry
lemma not_or_of_imp_esisar' : ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  := sorry
lemma imp_iff_not_or_esisar' : ∀ P Q : Prop,   (P → Q) ↔ (¬ P ∨ Q)  := sorry
example (P Q: Prop) : ¬ (¬ P ∨ Q ) ↔ (P ∧ ¬ Q) := sorry
lemma not_imp_esisar' : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := sorry
example (P Q: ℝ →  Prop) : ¬(∀ x:ℝ , P x → Q x) ↔ (∃x:ℝ, P x ∧ (¬ Q x ) ) := by push_neg ; rfl
example  : ¬ (∀ x:ℝ,  x^2=4 → x=2 ) := sorry
def tend_vers_plus_infini' (u: ℕ → ℝ) : Prop := ∀ A:ℝ, ∃ n0:ℕ, ∀ n:ℕ , n ≥ n0 → (u n) ≥ A  
example (u:ℕ → ℝ) : ¬ (tend_vers_plus_infini' u) ↔ ( ∃ A:ℝ, ∀ n0:ℕ, ∃ n:ℕ , n ≥ n0 ∧  (u n) < A ) := by unfold tend_vers_plus_infini; push_neg ; rfl
open Real
example : ¬ (∃ a b: ℝ, ∀x:ℝ, a * (exp x) + b*(exp (-x)) = x^2)  := sorry
example : ¬ (∃ a b: ℝ, ∀x:ℝ, a * (sin x) + b*(cos x) = (sin (2*x)))  := sorry
example : ∀ x:ℝ, x ≠ -2 → (x+1)/(x+2) ≠ 1  := sorry

example : ∀ x:ℝ , x≥-1 →  ∀ n:ℕ, (1+x)^n ≥ n*x := sorry
example : ∀ n:ℕ , 2^n > n := sorry
example : ∀ n:ℕ , 2^n > n := sorry
open Nat
def P' (n:ℕ) : Prop := n ! ≥ 2^n
example : ∀ n:ℕ , n ≥ 4 → P' n :=sorry
example : ∀ n:ℕ , n ≥ 5 → 2^n > 5*(n+1) :=sorry
example : ∀ n:ℕ, pair n ∨ impair n := sorry



end exam



example : ¬ (∃ k:ℤ, 16 = 3*k+2) := sorry



example : ∀ x:ℝ, 3*x+4=2 → x=-2/3     
  :=
  λ x:ℝ  ↦ 
    λ h:3*x+4=2 ↦ 
      calc
        x = (3*x+4-4)/3 := by ring_nf
        _ = (2  -4)/3   := by rw[h]
        _ = -2/3        := by norm_num


-- Exercice 1.1
example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      calc
        x = (2*x+11-11)/2 := by ring_nf
        _ = (6  -11)/2    := by rw[h]
        _ = -5/2          := by norm_num



-- Exercice 1.2
example  : ∀ c:ℚ,  4*c+1 =3*c-2 →  c = -3 :=
  λ  c:ℚ ↦ 
    λ  h:  4*c+1 =3*c-2 ↦ 
      calc
        c =  (4*c+1)-(3*c-2)  - 3  := by ring_nf
        _ =  (3*c-2)-(3*c-2)  - 3 := by rw[h]
        _ = -3                    := by norm_num


-- Exercice 1.3
example : ∀ a b :ℝ ,(a ≤ b) → (∀ x:ℝ,  x ≥ b → x ≥ a ) :=
  λ a b :ℝ ↦ 
    λ h : a ≤ b ↦    
      λ x : ℝ ↦
        λ hxb : x ≥ b ↦ 
          calc 
            x ≥ b := hxb
            _ ≥ a := h




example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P  :=
  λ P  Q : Prop ↦
    λ  h: P ∧ Q ↦
      And.intro
        (h.right:Q)
        (h.left :P)



-- Exercice 2.1
example : ∀ (P : Prop), P → P ∧ P := 
  λ P : Prop ↦
    λ h:P ↦
      And.intro (h:P) (h:P)    


-- Exercice 2.2
example : ∀ (P Q : Prop), P ∧ Q → P :=
  λ P Q : Prop ↦ 
    λ h: P ∧ Q ↦ 
      (h.left:P) 


-- Exercice 2.3
example : ∀ (P Q : Prop), P ∧ Q → Q :=
  λ P Q : Prop ↦ 
    λ h: P ∧ Q ↦ 
      (h.right:Q) 


-- Exercice 2.4
example : ∀ (P Q R: Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := 
  λ P Q R : Prop ↦ 
    λ h : (P∧Q)∧ R ↦
      And.intro
        (h.left.left : P)
        (
          And.intro
            (h.left.right: Q)
            (h.right:      R)
        )  


-- Exercice 2.5
example : ∀ (P Q R: Prop), (P → Q) ∧ (Q → R) → (P → R) := 
  λ P Q R : Prop ↦ 
    λ h : (P → Q) ∧ (Q → R) ↦
      λ hP:P ↦ 
        (h.right (h.left  hP : Q) : R)

example : ∀ (P Q R: Prop), (P → Q) ∧ (Q → R) → (P → R) := 
  λ P Q R : Prop ↦ 
    λ h : (P → Q) ∧ (Q → R) ↦
      λ hP:P ↦ 
        have hQ : Q := h.left  hP
        have hR : R := h.right hQ
        hR


example : ∀ (P Q R: Prop), (P → Q) → (Q → R) → (P → R) :=
  λ P Q R : Prop ↦ 
    λ hPQ : P → Q ↦
      λ hQR : Q → R ↦
        λ hP:P ↦ 
          (hQR (hPQ  hP : Q) : R)




def impairZ (n:ℤ) : Prop := ∃ k:ℤ, n=2*k+1     

example : impairZ 7 :=
  Exists.intro 3            -- Pour démontrer ∃k... il faut fournir à Exists.intro une valeur de k (ici 3)
  (                         -- Et donner une preuve que cette valeur convient (calcul ci-dessous)
    calc                    -- Cette opération s'appelle l'introduction de ∃ 
      (7:ℤ)  = 2*3+1  := by norm_num  -- petit point malcommode :
                                      -- pour que Lean considère bien 7 comme élément de ℤ et non de ℕ  on doit préciser (7:ℤ)
  )

-- Exercice 3.1
def pairZ (n:ℤ) : Prop := ∃ k:ℤ, n=2*k

example : pairZ (-10) := 
  Exists.intro (-5)
  (
    calc (-10:ℤ) = 2*(-5) := by norm_num
  )

example : pairZ (-10) := 
  Exists.intro (-5)
  (
    by norm_num :  (-10:ℤ) = 2*(-5)
  )




example : ∀ x:ℝ, ∃ y:ℝ , y>x := 
  λ x:ℝ ↦ 
      Exists.intro (x+1)
        (
          calc 
            x+1 > x   := lt_add_one x
        )

-- Exercice 4.1
example (x:ℝ) : x-1 < x := by exact?
#check sub_one_lt
example : ∀ u:ℝ, ∃ t:ℝ , t + 1 < u  := 
  λ u:ℝ ↦ 
      Exists.intro (u-2)
        (
          calc 
            (u-2)+1 = u-1  := by ring
            _        < u   := sub_one_lt u
        )




------------------------------------------------------------------
-- Exemple 5
------------------------------------------------------------------

example : ∀n:ℤ,  (∃k:ℤ, n = 4*k+3) → (impairZ n) :=
  λ n:ℤ ↦
    λ h1:(∃k:ℤ, n = 4*k+3) ↦
      Exists.elim h1 
      (
        λ (k:ℤ)  (h2:n=4*k+3) ↦ 
          Exists.intro (2*k+1)
          (
            calc
              n = 4*k+3       := h2
              _ = 2*(2*k+1)+1 := by ring_nf
          )
      )


-- Exercice 5.1
example : ∀n:ℤ,  (∃k:ℤ, n = 6*k) → (pairZ n) :=
  λ n:ℤ ↦
    λ h1:(∃k:ℤ, n = 6*k) ↦
      Exists.elim h1 
      (
        λ (k:ℤ)  (h2:n=6*k) ↦ 
          Exists.intro (3*k)
          (
            calc
              n = 6*k     := h2
              _ = 2*(3*k) := by ring_nf
          )
      )

example : ∀n:ℤ,  (∃k:ℤ, n = 6*k) → (pairZ n) :=
  λ  n:ℤ ↦ 
    λ  h1:(∃k:ℤ, n = 6*k) ↦ 
      Exists.elim h1 
      (
        λ  k:ℤ ↦ 
          supposons h2:(n=6*k),
          (
              Exists.intro (3*k)
              (
                calc
                  n = 6*k     := h2
                  _ = 2*(3*k) := by ring_nf
              )
            : pairZ n
          )
      )



------------------------------------------------------------------
-- Exemple 6
------------------------------------------------------------------

example : ∀ a:ℝ, (∀x:ℝ,a ≤ x^2 -2*x) →  a ≤ -1 := 
  λ a:ℝ ↦
    λ h:  (∀x:ℝ,a ≤ x^2 -2*x) ↦
      calc
        a ≤ 1^2-2*1 := h 1
        _ = -1      := by norm_num


-- Exercice 6.1
example : ∀ a:ℝ, (∀x:ℝ,a * x^2 = 0) →  a = 0 :=  
  λ a:ℝ ↦
    λ h:  (∀x:ℝ,a * x^2 = 0) ↦
      calc
        a = a*1^2   := by ring_nf
        _ = 0       := h 1

example : ∀ a:ℝ, (∀x:ℝ,a * x^2 = 0) →  a = 0 :=  
  soit a:ℝ,
    supposons h:  (∀x:ℝ,a * x^2 = 0),
      calc
        a = a*1^2   := by ring_nf
        _ = 0       := h 1


------------------------------------------------------------------
-- Exemple 7
------------------------------------------------------------------
 
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


-- Exercice 7.1 
example : ∀ a b:ℝ , (∀x:ℝ,a * x^2 - b*x = 0) →  (a = 0 ∧ b = 0) :=  
  λ a b:ℝ ↦ 
    λ h:(∀x:ℝ,a * x^2 - b*x = 0) ↦
      have h1  : a-b=0 :=
        calc
          a -b = a*1^2 -b*1 := by ring_nf
          _    = 0          := h 1

      have hm1  : a+b =0 :=
        calc
          a+b = a*(-1)^2 -b*(-1) := by ring_nf
          _   = 0                := h (-1)


      have ha0 : a=0 := 
        calc
          a = ((a+b)+(a-b))/2 := by ring_nf
          _ = (0+0)/2         := by rw[h1,hm1]
          _ = 0               := by norm_num

      have hb0 :  b=0 :=
        calc            
          b = ((a+b)-(a-b))/2 := by ring_nf
          _ = (0-0)/2         := by rw[h1,hm1]
          _ = 0               := by norm_num

      And.intro ha0 hb0 








------------------------------------------------------------------
--- Exemple 1
------------------------------------------------------------------


example : ∀x:ℝ, ∀y:ℝ, (x=1 ∨ y=-1) → x*y+x = y+1 := 
  λ  x:ℝ ↦   
    λ  y:ℝ ↦ 
      λ h :  (x=1 ∨ y=-1) ↦  
        Or.elim h            
        (
          λ hx : x=1 ↦       
            calc
              x*y+x = 1*y+1  := by rw[hx]
              _      = y+1   := by ring_nf
        )
        (
          λ hy: y=-1 ↦       
            calc 
              x*y+x = x*(-1)+x  := by rw[hy]
              _      = -1+1     := by ring_nf
              _      = y+1      := by rw[hy]
        )


-- Exercice 1.1
example :  ∀x:ℝ, (x=2 ∨ x=-3) →  x^3 + x^2 - 6*x = 0 := 
  λ x:ℝ ↦ 
    λ  h: (x=2 ∨ x=-3) ↦
      Or.elim h
      (
        λ h2 : x=2 ↦  
          calc
            x^3 + x^2 - 6*x = 2^3 + 2^2 - 6*2   := by rw[h2]
            _               = 0                 := by norm_num
      )
      (
        λ h3 : x=-3 ↦  
          calc
            x^3 + x^2 - 6*x = (-3)^3 + (-3)^2 - 6*(-3) := by rw[h3]
            _               = -27+9+18                 := by norm_num
            _               = 0                        := by norm_num
      )


-- Exercice 1.2
example : ∀ x:ℝ , x=-1 ∨ x=2 → x^2-x-2 = 0 :=
  λ x:ℝ ↦ 
    λ  h: (x=-1 ∨ x=2) ↦
      Or.elim h
      (
        λ hm1 : x=-1 ↦  
          calc
            x^2 - x - 2 = (-1)^2 - (-1) - 2   := by rw[hm1]
            _           = 1+1-2               := by norm_num
            _           = 0                   := by norm_num
      )
      (
        λ h2 : x=2 ↦  
          calc
            x^2 - x - 2 = 2^2 - 2 - 2 := by rw[h2]
            _           = 4-2-2       := by norm_num
            _           = 0           := by norm_num
      )


example :  ∀n:ℕ , n^2 ≠ 2  := 
  λ n:ℕ ↦ 
    have h : n ≤ 1 ∨ n > 1 := le_or_gt n 1
    Or.elim h
    (
      λ h1: n ≤ 1 ↦ 
        have hn2lt2 : n^2 < 2 :=     
          calc  
            n^2 ≤ 1^2 := Nat.pow_le_pow_of_le_left h1 2 
            _   < 2   := by norm_num

        ne_of_lt hn2lt2
      
    )
    (
      λ h2: n ≥ 2  ↦  
        have hn2gt2: n^2>2 :=
          calc  
            n^2 ≥ 2^2 := Nat.pow_le_pow_of_le_left h2 2 
            _   > 2   := by norm_num

        ne_of_gt hn2gt2
    ) 

------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------


example : ∀ x:ℝ , 2*x+1 = 5 → x=1 ∨ x=2 :=
  λ x:ℝ ↦  
    λ h1: 2*x+1 = 5 ↦ 

      have h2:  x = 2 :=
        calc 
          x = (2*x+1 -1)/2  := by ring_nf
          _ = (5-1)/2       := by rw[h1]
          _ = 2             := by norm_num

      Or.inr h2  


-- Exercice 2.1
example :  ∀x:ℝ, 3*x+4 = 22 →  x=6 ∨ x= 9 := 
  λ x:ℝ ↦  
    λ h1: 3*x+4 = 22 ↦ 

      have h2:  x = 6 :=
        calc 
          x = (3*x+4 -4)/3  := by ring_nf
          _ = (22-4)/3      := by rw[h1]
          _ = 6             := by norm_num

      Or.inl h2 


------------------------------------------------------------------
--- Exemple 3
------------------------------------------------------------------

#check eq_zero_or_eq_zero_of_mul_eq_zero

example : ∀ x:ℝ , x^2-x-2 = 0 → x=-1 ∨ x=2 :=
  λ x:ℝ ↦  
    λ h1: x^2-x-2 = 0 ↦ 
      have h2 : (x+1)*(x-2) = 0 :=
        calc
          (x+1)*(x-2) = x^2-x-2  := by ring_nf
          _           = 0        := h1
      have h3 : x+1=0 ∨ x-2=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
      Or.elim h3
        (
          λ h4 : x+1=0 ↦
            have h5 : x=-1 :=
              calc
                x = x+1-1  := by ring_nf
                _ = 0  -1  := by rw[h4]
                _ =    -1  := by norm_num
            Or.inl h5     
        )
        (
          λ h6 : x-2=0 ↦
            have h7 : x=2 :=
              calc
                x = x-2+2  := by ring_nf
                _ = 0  +2  := by rw[h6]
                _ =    2   := by norm_num

            Or.inr h7
        )


example : ∀ x:ℝ , x^2-x-2 = 0 → x=-1 ∨ x=2 :=
  λ x:ℝ ↦  
    λ h1: x^2-x-2 = 0 ↦ 
      have h2 : (x+1)*(x-2) = 0 :=
        calc
          (x+1)*(x-2) = x^2-x-2  := by ring_nf
          _           = 0        := h1
      have h3 : x+1=0 ∨ x-2=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
      Or.elim h3
        (
          λ h4 : x+1=0 ↦
            Or.inl (eq_neg_of_add_eq_zero_left h4 : x=-1)
        )
        (
          λ h6 : x-2=0 ↦
            Or.inr (eq_of_sub_eq_zero h6  :  x=2)
        )


-- Exercice 3.1
example :  ∀ x:ℝ , x^2+x-6 = 0 → x=2 ∨ x=-3 := 
  λ x:ℝ ↦  
    λ h1: x^2+x-6 = 0 ↦ 
      have h2 : (x-2)*(x+3) = 0 :=
        calc
          (x-2)*(x+3) = x^2+x-6  := by ring_nf
          _           = 0        := h1
      have h3 : x-2=0 ∨ x+3=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
      Or.elim h3
        (
          λ h4 : x-2=0 ↦
            Or.inl (eq_of_sub_eq_zero h4 : x=2)
        )
        (
          λ h5 : x+3=0 ↦
            Or.inr (eq_neg_of_add_eq_zero_left h5  :  x=-3)
        )

-- Exercice 3.2 
example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q → P ∨ Q := 
  λ P: Prop ↦ 
    λ Q: Prop ↦ 
      λ h : P ∧ Q ↦
        (Or.inl (h.left:P)   : P ∨ Q)

example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q → P ∨ Q := 
  λ P: Prop ↦ 
    λ Q: Prop ↦ 
      λ h : P ∧ Q ↦
        (Or.inr (h.right:Q)   : P ∨ Q)



------------------------------------------------------------------
--- Exemple 4
------------------------------------------------------------------


example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q ↔ Q ∧ P :=
  λ P: Prop ↦  
    λ Q: Prop ↦  
      Iff.intro
      (
        λ hPQ : P ∧ Q ↦ 
          (And.intro (hPQ.right:Q) (hPQ.left:P) : Q ∧ P)
      )
      (
        λ hQP : Q ∧ P ↦ 
          And.intro hQP.right hQP.left 
      )

example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q ↔ Q ∧ P :=
  λ P: Prop ↦  
    λ Q: Prop ↦  

      have hAB : P ∧ Q → Q ∧ P :=
        λ hPQ : P ∧ Q ↦ 
          (And.intro (hPQ.right:Q) (hPQ.left:P) : Q ∧ P)

      have hBA : Q ∧ P → P ∧ Q :=
        λ hQP : Q ∧ P ↦ 
          And.intro hQP.right hQP.left

      Iff.intro   hAB hBA


lemma  PQ_imp_QP : ∀ P :Prop, ∀ Q : Prop, P ∧ Q → Q ∧ P :=
  λ P: Prop ↦  
    λ Q: Prop ↦  
        λ hPQ : P ∧ Q ↦ 
          (And.intro (hPQ.right:Q) (hPQ.left:P) : Q ∧ P)

example : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P :=
  λ P Q: Prop ↦  Iff.intro 
    (PQ_imp_QP P Q : P ∧ Q → Q ∧ P )   
    (PQ_imp_QP Q P : Q ∧ P → P ∧ Q)



-- Exercice 4.2 

-- 4.2 version1
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     Iff.intro 
     (
       λ h : P ∨ Q ↦
        Or.elim h
        (
          λ hP : P ↦ 
            (Or.inr hP : Q ∨ P)
        )
        (
          λ hQ : Q ↦ 
            (Or.inl hQ : Q ∨ P)
        )
      )
     (
       λ h : Q ∨ P ↦
        Or.elim h
        (
          λ hQ : Q ↦ 
            (Or.inr hQ : P ∨ Q)
        )
        (
          λ hP : P ↦ 
            (Or.inl hP : P ∨ Q)
        )
      )

-- 4.2 version2
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     have h_impR: P ∨ Q →  Q ∨ P  :=
       λ h : P ∨ Q ↦
        Or.elim h
        (
          λ hP : P ↦ 
            (Or.inr hP : Q ∨ P)
        )
        (
          λ hQ : Q ↦ 
            (Or.inl hQ : Q ∨ P)
        )
     have h_impL: Q ∨ P → P ∨ Q  :=
       λ h : Q ∨ P ↦
        Or.elim h
        (
          λ hQ : Q ↦ 
            (Or.inr hQ : P ∨ Q)
        )
        (
          λ hP : P ↦ 
            (Or.inl hP : P ∨ Q)
        )

     Iff.intro h_impR h_impL



-- 4.2 version3
lemma PorQ_imp_QorP : ∀ P :Prop, ∀ Q : Prop, P ∨ Q →  Q ∨ P :=
   λ P Q : Prop ↦ 
       λ h : P ∨ Q ↦
        Or.elim h
        (
          λ hP : P ↦ 
            (Or.inr hP : Q ∨ P)
        )
        (
          λ hQ : Q ↦ 
            (Or.inl hQ : Q ∨ P)
        )

-- version 3a
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     Iff.intro 
     ( λ hPQ : P ∨ Q ↦ PorQ_imp_QorP P Q hPQ )
     ( λ hQP : Q ∨ P ↦ PorQ_imp_QorP Q P hQP )

-- version 3b
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     Iff.intro      ( PorQ_imp_QorP P Q)     ( PorQ_imp_QorP Q P)



-- Exercice 4.3
example :  ∀ x:ℝ , x^2+x-6 = 0 ↔ x=2 ∨ x=-3 := 
  λ x:ℝ ↦  
    Iff.intro

    (
      λ h1: x^2+x-6 = 0 ↦ 
        have h2 : (x-2)*(x+3) = 0 :=
          calc
            (x-2)*(x+3) = x^2+x-6  := by ring_nf
            _           = 0        := h1
        have h3 : x-2=0 ∨ x+3=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
        Or.elim h3
          (
            λ h4 : x-2=0 ↦
              Or.inl (eq_of_sub_eq_zero h4 : x=2)
          )
          (
            λ h5 : x+3=0 ↦
              Or.inr (eq_neg_of_add_eq_zero_left h5  :  x=-3)
          )
    )
    (
      λ  h: (x=2 ∨ x=-3) ↦
        Or.elim h
        (
          λ h2 : x=2 ↦  
            calc
              x^2 + x - 6 = 2^2 +2 - 6  := by rw[h2]
              _           = 4+2-6       := by norm_num
              _           = 0           := by norm_num
        )
        (
          λ hm3 : x=-3 ↦  
            calc
              x^2 + x - 6 = (-3)^2 +(-3) - 6  := by rw[hm3]
              _           = 9-3-6             := by norm_num
              _           = 0                 := by norm_num
        )

    )

-- Exercice 4.3
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

  


-- Exercice 4.4
lemma Int.le_of_two_mul_le : ∀ x a:ℤ, 2*x ≤ 2*a →  x≤ a   := 
  λ x a: ℤ ↦  
    λ h :2*x ≤ 2*a ↦ 
      have h' : x+x ≤ a+a :=
        calc 
          x+x = 2*x := (two_mul x).symm
          _   ≤ 2*a := h
          _   = a+a := two_mul a 
        
        bit0_le_bit0.mp h'   


lemma Int.le_and_le_add_one_iff : ∀ x a: ℤ, x≥ a ∧ x ≤ a+1 →  x=a ∨ x=a+1    := 
  λ x a: ℤ ↦  
    λ h: x ≥ a ∧ x ≤ a + 1 ↦ 
      Or.elim (lt_or_le x (a+1) : x < a + 1 ∨ a + 1 ≤ x)
      (
        λ h_x_lt_succ_a : x < a+1 ↦  Or.inl (le_antisymm  (Int.lt_add_one_iff.mp h_x_lt_succ_a : x ≤ a) (h.left: x ≥ a ))
      )
      (
        λ h_x_ge_succ_a : x ≥ a+1 ↦  Or.inr (le_antisymm (h.right: x ≤ (a+1)) (h_x_ge_succ_a : x ≥ a+1 ))

      )

example :  ∀ a:ℤ , a^2-5*a+5 ≤ -1 ↔ a = 2 ∨ a=3 := 
   λ a:ℤ ↦  
     Iff.intro
       (
         λ h1 :  a^2-5*a+5 ≤ -1 ↦ 
           have h11 : (2*a-5)^2 ≤ 1 := 
            calc
              (2*a-5)^2 = 4*(a^2-5*a+5)+5   := by ring_nf
              _ ≤ 4*(-1) +5                 := by rel[h1]
              _ = 1^2                       := by norm_num
          have h12 : 2*a-5 ≥ -1 ∧ 2*a-5 ≤ 1 := abs_le_of_sq_le_sq' h11 (by norm_num : (1:ℤ) ≥ 0 )
          have h13 : 2*a ≥ 2*2 :=
            calc
              2*a = 2*a-5+5  := by ring_nf
              _   ≥ -1+5     := by rel[h12.left]
              _   = 2*2      := by norm_num

          have h13' : a ≥ 2 := Int.le_of_two_mul_le 2 a h13

          have h14 : 2*a ≤ 2*3 :=
            calc
              2*a = 2*a-5+5  := by ring_nf
              _   ≤ 1+5      := by rel[h12.right]
              _   = 2*3      := by norm_num

          have h14' : a ≤ 3 := Int.le_of_two_mul_le a 3 h14
          
          Int.le_and_le_add_one_iff a 2 (And.intro h13' h14')
       )
       (
         λ h2 : a = 2 ∨ a=3  ↦ 
           Or.elim h2
           (
             λ ha2 : a = 2 ↦ 
               calc
                 a^2-5*a+5 = 2^2-5*2+5  := by rw[ha2]
                 _         ≤ -1         := by norm_num
           )
           (
             λ ha3 : a = 3 ↦ 
               calc
                 a^2-5*a+5 = 3^2-5*3+5  := by rw[ha3]
                 _         ≤ -1         := by norm_num
           )
       )

-- Exercice 4.5
example :  ∀ a:ℝ,∀ b:ℝ, ∀ x:ℝ, x^2 -(a+b)*x+a*b = 0 ↔  x = a ∨ x = b := 
  λ a b:ℝ ↦  
    λ x:ℝ ↦  
      Iff.intro
      (
        λ h1: x^2 -(a+b)*x+a*b = 0 ↦ 
          have h2 : (x-a)*(x-b) = 0 :=
            calc
              (x-a)*(x-b) = x^2 -(a+b)*x+a*b  := by ring_nf
              _           = 0                 := h1
          have h3 : x-a=0 ∨ x-b=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
          Or.elim h3
            (
              λ h4 : x-a=0 ↦
                Or.inl (eq_of_sub_eq_zero h4 : x=a)
            )
            (
              λ h5 : x-b=0 ↦
                Or.inr (eq_of_sub_eq_zero h5 : x=b)
            )
      )
      (
        λ  h: (x=a ∨ x=b) ↦
          Or.elim h
          (
            λ ha : x=a ↦  
              calc
                x^2 -(a+b)*x+a*b = a^2 -(a+b)*a+a*b  := by rw[ha]
                _                = a^2-a^2-b*a+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )
          (
            λ hb : x=b ↦  
              calc
                x^2 -(a+b)*x+a*b = b^2 -(a+b)*b+a*b  := by rw[hb]
                _                = b^2-a*b-b^2+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )

      )

------------------------------------------------------------------
--- Exemple 5
------------------------------------------------------------------


-- donnons ici la résolution de l'équation du 1er degré dans ℝ :
theorem  equation_premier_degre :  ∀ b c:ℝ , b≠ 0 → ∀x:ℝ , b*x + c = 0 ↔ x=-c/b := 

λ b c:ℝ ↦ 
  λ hb: b≠ 0 ↦  
    λ x:ℝ ↦ 
      Iff.intro
      (
        λ h1 : b*x + c = 0  ↦ 
          calc
            x = (b*x)/b     := by rw[mul_div_cancel_left x hb] 
            _ = (b*x+c-c)/b := by ring_nf
            _ = (0-c)/b     := by rw[h1]
            _ = -c/b        := by ring_nf
      )
      (
        λ h2 : x = -c/b ↦
          calc 
            b*x+c = b*(-c/b) +c := by rw[h2]
            _     = -(b*c/b)+c  := by ring_nf
            _     = -c+c        := by rw[mul_div_cancel_left c hb]
            _     = 0           := by ring_nf
      )

-- Utilisons ce théorème pour trouver une CN pour que : 3*x-4 =0 :

example: ∀x:ℝ , 3*x - 4 = 0 → x=4/3 := 
  λ x:ℝ ↦ 
    λ h : 3*x - 4 = 0  ↦ 

      have h2 : 3*x+(-4) = 0 := 
        calc 
          3*x+(-4) = 3*x-4  := by ring_nf 
          _        = 0      := h


      have h3 : _ :=
        (equation_premier_degre 3 (-4) (by norm_num: (3:ℝ) ≠ 0) x).mp  h2
      
      calc 
         x = -(-4)/3 := h3
         _ = 4/3     := by norm_num

-- Utilisons ce théorème pour trouver une CS pour que : 2*x+3 =0 :
example: ∀x:ℝ , x=-3/2 → 2*x + 3 = 0   := 
  λ x:ℝ ↦ 
    λ h : x=-3/2 ↦ 
       (equation_premier_degre 2 3 (by norm_num: (2:ℝ) ≠ 0) x).mpr h


-- Exercice 5.1
example : ∀x:ℝ , 5*x +2 = 0 → x=-2/5 := λ x:ℝ ↦  (equation_premier_degre 5 2 (by norm_num: 5 ≠ (0:ℝ)) x).mp

-- Exercice 5.2
example : ∀x:ℝ ,  x=4 → -4+x = 0 := 
  λ x:ℝ  ↦ 
    λ h: x=4 ↦ 
      have h1 : x= -(-4) /1 :=
        calc
          x = 4         := h
          _ = -(-4) /1  := by norm_num

      calc
        -4+x = 1*x+(-4) := by ring_nf
        _    = 0        := (equation_premier_degre 1 (-4) (by norm_num : 1 ≠ (0:ℝ )) x).mpr h1


-- Exercice 5.3

lemma Int.eq_sum_product :  ∀ a:ℤ ,∀ b:ℤ, ∀ x:ℤ, x^2 -(a+b)*x+a*b = 0 ↔  x = a ∨ x = b := 
  λ a b:ℤ ↦  
    λ x:ℤ ↦  
      Iff.intro
      (
        λ h1: x^2 -(a+b)*x+a*b = 0 ↦ 
          have h2 : (x-a)*(x-b) = 0 :=
            calc
              (x-a)*(x-b) = x^2 -(a+b)*x+a*b  := by ring_nf
              _           = 0                 := h1
          have h3 : x-a=0 ∨ x-b=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
          Or.elim h3
            (
              λ h4 : x-a=0 ↦
                Or.inl (eq_of_sub_eq_zero h4 : x=a)
            )
            (
              λ h5 : x-b=0 ↦
                Or.inr (eq_of_sub_eq_zero h5 : x=b)
            )
      )
      (
        λ  h: (x=a ∨ x=b) ↦
          Or.elim h
          (
            λ ha : x=a ↦  
              calc
                x^2 -(a+b)*x+a*b = a^2 -(a+b)*a+a*b  := by rw[ha]
                _                = a^2-a^2-b*a+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )
          (
            λ hb : x=b ↦  
              calc
                x^2 -(a+b)*x+a*b = b^2 -(a+b)*b+a*b  := by rw[hb]
                _                = b^2-a*b-b^2+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )

      )


--def pair (n:ℤ) : Prop := ∃ k:ℤ, n=2*k
example : ∀ n:ℤ,  n^2-10*n+24=0 → pairZ n := 
  λ n:ℤ ↦ 
    λ h:  n^2-10*n+24=0 ↦ 
      have h_eq : n^2 -(4+6)*n+4*6 = 0 :=
        calc 
          n^2 -(4+6)*n+4*6 = n^2-10*n+24 := by ring_nf
          _                = 0           := h
      have h46 : n= 4 ∨ n=6 := (Int.eq_sum_product  4 6 n).mp h_eq

      Or.elim h46
      (
        λ h4 : n=4 ↦ 
          Exists.intro 2 (
            calc
              n = 4   := h4
              _ = 2*2 := by norm_num
          )
      )
      (
        λ h6 : n=6 ↦ 
          Exists.intro 3 (
            calc
              n = 6   := h6
              _ = 2*3 := by norm_num
          )
      )





------------------------------------------------------------------
--- Exemple 1
------------------------------------------------------------------

example : ∀ P Q :Prop,  P ∧ Q ↔ Q ∧ P := sorry  -- commutativite de ∧ 
example : ∀ P Q :Prop,  P ∨ Q ↔ Q ∨ P := sorry  -- commutativite de ∨ 

example : ∀ P Q R:Prop,  P ∧ (Q ∨ R)  ↔ (P ∧ Q) ∨ (P ∧ R) :=  -- distributivité de ∧ par rapport à ∨
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h: P ∧ (Q ∨ R) ↦ 
        Or.elim (h.right : Q ∨ R)
        (
           λ hQ: Q ↦ 
             Or.inl (And.intro (h.left:P) hQ  : P ∧ Q )
        )
        (
           λ hR: R ↦ 
             Or.inr (And.intro (h.left:P) hR  : P ∧ R )
        )
    )
    (
      λ h: (P ∧ Q) ∨ (P ∧ R) ↦ 
        Or.elim h
        (
           λ hPQ: P ∧ Q ↦ 
             (And.intro (hPQ.left:P) (Or.inl (hPQ.right:Q) : Q ∨ R)  : P ∧ (Q ∨ R) )
        )
        (
           λ hPR: P ∧ R ↦ 
             (And.intro (hPR.left:P) (Or.inr (hPR.right:R) : Q ∨ R)  : P ∧ (Q ∨ R) )
        )

    )


-- Exercice 1.1
-- complétez la preuve d'associativité de ∨  ci dessous
example : ∀ P Q R:Prop,  (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=  
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h: (P ∨ Q) ∨ R ↦ 
        Or.elim h
        (
          λ hPQ :  P ∨ Q ↦ 
            Or.elim hPQ
            (
               λ hP : P ↦ 
                have h_P_QR   : P ∨ (Q ∨ R) := Or.inl hP
                h_P_QR
            )
            (
              λ hQ : Q ↦ 
                have h_QR   : Q ∨ R       := Or.inl hQ
                have h_P_QR   : P ∨ (Q ∨ R) := Or.inr h_QR
                h_P_QR
            )
        )
        (
          λ hR :  R ↦ 
            have h_QR   : Q ∨ R       := Or.inr hR
            have h_P_QR : P ∨ (Q ∨ R) := Or.inr h_QR
            h_P_QR
        )
        
    ) 
    (
      λ h: P ∨ (Q ∨ R)  ↦ 
        Or.elim h
        (
          λ hP :  P ↦ 
            have h_PQ   : P ∨ Q       := Or.inl hP
            have h_PQ_R : (P ∨ Q) ∨ R := Or.inl h_PQ
            h_PQ_R
        )
        (
          λ hQR :  Q ∨ R ↦ 
            Or.elim hQR
            (
               λ hQ : Q ↦ 
                have h_PQ   : P ∨ Q       := Or.inr hQ
                have h_PQ_R : (P ∨ Q) ∨ R := Or.inl h_PQ
                h_PQ_R
            )
            (
              λ hR : R ↦ 
                have h_PQ_R  : (P ∨ Q) ∨ R := Or.inr hR
                h_PQ_R
            )
        )
    ) 

example : ∀ P Q R:Prop,  (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=  
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h: (P ∨ Q) ∨ R ↦ 
        Or.elim h
        ( Or.elim · Or.inl  (Or.inr ∘ Or.inl)  )
        ( Or.inr ∘ Or.inr )
    ) 
    (
      λ h: P ∨ (Q ∨ R)  ↦ 
        Or.elim h
        ( Or.inl ∘ Or.inl )
        ( Or.elim ·  (Or.inl ∘ Or.inr) Or.inr  )
    ) 



-- Exercice 1.2
example : ∀ P Q R:Prop,  P ∨ (Q ∧ R)  ↔ (P ∨ Q) ∧ (P ∨ R) :=
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h:P ∨ (Q ∧ R) ↦ 
        Or.elim h
        ( 
          λ hP:P ↦ 
            And.intro
              (Or.inl hP)
              (Or.inl hP)
        )
        ( 
          λ hQR : Q ∧ R  ↦ 
            And.intro
              (Or.inr hQR.left)
              (Or.inr hQR.right)
        )
    ) 
    (
      λ h: (P ∨ Q) ∧ (P ∨ R)  ↦ 
        Or.elim h.left
        ( 
          λ hP : P  ↦
            (Or.inl hP:  P ∨ ( Q ∧ R) )
        )
        (
          λ hQ : Q  ↦
            Or.elim h.right
            (
              λ hP : P  ↦
                (Or.inl hP :  P ∨ ( Q ∧ R)  ) 
            )
            (
              λ hR: R ↦ 
                have h_QR    : Q ∧ R         := And.intro hQ hR
                have h_P_QR  : P ∨ ( Q ∧ R)  := Or.inr h_QR
                h_P_QR
            )
        )
    )

-- Exercice 1.3
example : ∀ P Q R:Prop,  (P ∧ Q) ∧ R  ↔ P ∧ (Q ∧ R) :=
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h_PQ_R: (P ∧ Q) ∧ R ↦ 
        have h_PQ : P ∧ Q := h_PQ_R.left
        have h_R  : R     := h_PQ_R.right
        have h_QR : Q ∧ R := And.intro (h_PQ.right : Q)  (h_R:R)
        And.intro  (h_PQ.left : P)  (h_QR : Q ∧ R)
    ) 
    (
      λ h_P_QR:  P ∧ (Q ∧ R)  ↦ 
        have h_P  : P     := h_P_QR.left
        have h_QR : Q ∧ R := h_P_QR.right
        have h_PQ : P ∧ Q := And.intro  (h_P:P) (h_QR.left : Q)
        And.intro  (h_PQ: P ∧ Q )  (h_QR.right : R)
    )


-- Exercice 1.4
-- (a) Montrez le lemme suivant
lemma and_iff_of_imp : ∀ P Q :Prop,  (P → Q) → ((P ∧ Q) ↔ P) := 
  λ P Q : Prop ↦
    λ h_PimpQ : P → Q ↦   
     Iff.intro
     (
       λ h_PandQ : P ∧ Q  ↦
         (h_PandQ.left : P)       
     )
     (
       λ h_P : P ↦
         have h_Q : Q := h_PimpQ h_P 
        (And.intro (h_P : P) (h_Q : Q) : (P ∧ Q) )
     )
     

-- (b) Montrez le lemme suivant
-- cet exemple a déjà été traité comme exercice 1.3 de 10_tuto.lean
lemma imp_of_le : ∀ a b :ℝ ,(a ≤ b) → (∀ x:ℝ,  x ≥ b → x ≥ a ) :=
  λ a b :ℝ ↦ 
    λ h : a ≤ b ↦    
      λ x : ℝ ↦
        λ hxb : x ≥ b ↦ 
          calc 
            x ≥ b := hxb
            _ ≥ a := h


-- (c) Et utilisez ces lemmes pour prouver :
example : ∀ s:ℝ,  (s ≥ 3 ∧ s ≥ 2) ↔ (s ≥ 3)  := 
  λ s:ℝ ↦ 
    have h0 :  (2:ℝ) ≤ 3                 := by norm_num 
    have h1 :  ∀ x:ℝ,  x ≥ 3 → x ≥ 2     := imp_of_le 2 3 h0
    have h2 :  s ≥ 3 → s ≥ 2             := h1 s
    have h3 :  (s ≥ 3 ∧ s ≥ 2) ↔ (s ≥ 3) := and_iff_of_imp (s ≥ 3) ( s ≥ 2) h2
    h3

  -- écriture compacte...
example : ∀ s:ℝ,  (s ≥ 3 ∧ s ≥ 2) ↔ (s ≥ 3)  := 
  λ s:ℝ ↦ 
    and_iff_of_imp (s ≥ 3) ( s ≥ 2) (imp_of_le 2 3 (by norm_num : (2:ℝ) ≤ 3 ) s  )



------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------

example : False → 3^2 = 1 :=  
  λ h : False ↦ 
    (False.elim h : 3^2 = 1 ) 

example : False → ∃ x:ℝ, x^2 < 0  :=
  λ h : False ↦ 
    False.elim h                 

-- Exercice 2.1
example : False → 2=3  := 
  λ h : False ↦ 
    False.elim h 

-- Exercice 2.2
example : False → ∀ x:ℝ, x = 1  := 
  λ h : False ↦ 
    False.elim h 




------------------------------------------------------------------
--- Exemple 3
------------------------------------------------------------------
-- Nouvelles notions
--  La Négation d'une assertion


example : ∀ x:ℝ, x^2=4 → x ≠ 3 :=
  λ x:ℝ ↦  
    λ h1 : x^2 = 4 ↦ 
      λ h2 : x = 3 ↦
        have h3 : (4:ℝ)=3^2 :=
          calc
            4   = x^2 := by rw[h1]
            _   = 3^2 := by rw[h2]
        absurd h3 (by norm_num : (4:ℝ) ≠ 3^2)


example : ∀ P Q : Prop,  (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) :=
  λ P Q : Prop ↦ 
    λ h1 : (¬ P) ∨ (¬ Q) ↦ 
      λ h2 : P ∧ Q ↦ 
        Or.elim h1
        (λ hnP: ¬ P ↦ absurd h2.left hnP )
        (λ hnQ: ¬ Q ↦ absurd h2.right hnQ )



-- Exercice 3.1
example : ∀ x:ℝ, x^2=x → ¬(x=2 ∨ x=-1 ) :=
  λ x:ℝ ↦
    λ h: x^2=x ↦ 
      λ ha: x=2 ∨ x=-1  ↦ 
        Or.elim ha
        (
          λ ha2 : x=2 ↦ 
            absurd (calc 2^2=(2:ℝ) := ha2 ▸ h ) (by norm_num)
        )
        (
          λ ham1 : x=-1 ↦ 
            absurd (calc (-1)^2=(-1:ℝ) := ham1 ▸ h ) (by norm_num)
        )

--  version sans ▸ 
example : ∀ x:ℝ, x^2=x → ¬(x=2 ∨ x=-1 ) :=
  λ x:ℝ ↦
    λ h: x^2=x ↦ 
      λ ha: x=2 ∨ x=-1  ↦ 
        Or.elim ha
        (
          λ ha2 : x=2 ↦ 
            absurd (calc 
              2^2=x^2  := by rw[ha2]    -- ha2 ▸ rfl
              _  = x   := h 
              _  = 2   := ha2 
            ) (by norm_num)
        )
        (
          λ ham1 : x=-1 ↦ 
            absurd (calc 
              (-1)^2=x^2  := by rw[ham1]    -- ham1 ▸ rfl
              _  = x      := h 
              _  = -1     := ham1 
            ) (by norm_num)
        )


-- Exercice 3.2
lemma imp_of_ccl : ∀ P Q : Prop,  Q →  (P → Q) := 
  λ P Q : Prop ↦  
    λ hQ : Q ↦ 
      λ hP: P ↦  
        (hQ:Q)


-- ensuite, si P est fausse, alors P → Q est vraie. En effet, supposer ¬ P,  puis P (comme intro de → ) 
-- conduit à une absurdité,  et on obtient donc une preuve de Q  'ex falso'
-- Exercice 3.3
lemma imp_of_not : ∀ P Q : Prop,  (¬ P) →  (P → Q) := 
  λ P Q : Prop ↦  
    λ hnP : ¬ P ↦ 
      λ hP: P ↦  
       absurd hP hnP


-- Encore des lois de De Morgan

-- Exercice 3.4
-- Lois de De Morgan suite
example : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) :=
  λ P Q : Prop ↦  
    λ hnPQ : ¬ (P ∨ Q)  ↦ 
      And.intro
        (
          λ hP : P ↦ 
            have hPQ : P ∨ Q := Or.inl hP
            absurd hPQ hnPQ 
        )
        (
          λ hQ : Q ↦ 
            have hPQ : P ∨ Q := Or.inr hQ
            absurd hPQ hnPQ 
        )


-- Exercice 3.5
-- Lois de De Morgan suite
example : ∀ P Q : Prop,  (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
  λ P Q : Prop ↦  
    λ hnPnQ : (¬ P) ∧ (¬ Q) ↦ 
      λ hPQ : P ∨ Q ↦ 
        Or.elim hPQ
          (
            λ hP:P ↦  
              absurd hP (hnPnQ.left : ¬ P )
          )
          (
            λ hQ:Q ↦  
              absurd hQ (hnPnQ.right : ¬ Q )
          )



------------------------------------------------------------------
--- Exemple 4
------------------------------------------------------------------

example : ∀ P Q : Prop, ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q) :=
  λ P Q : Prop ↦ 
    λ h : ¬ (P ∧ Q) ↦ 
      Or.elim (Classical.em P)
      (
        λ hP:P ↦  

          have hnQ : ¬ Q :=
            λ hQ:Q ↦ 
              absurd (And.intro hP hQ : P ∧ Q  ) (h : ¬ (P ∧ Q))

          Or.inr hnQ
      )
      (
        λ hnP: ¬ P ↦  
          Or.inl hnP
      )


------------------------------------------------------------------
--- Exemple 5
------------------------------------------------------------------

set_option push_neg.use_distrib true


example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by push_neg ; rfl

-- ou encore:
def majoree (f:ℝ → ℝ) := ∃ M:ℝ, ∀ x:ℝ , f x ≤ M
example (f:ℝ → ℝ ): ¬ (majoree f ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by unfold majoree ; push_neg ; rfl


-- Exercice 5.1
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x > M ) ↔ (∀ M:ℝ, ∃ x:ℝ , f x ≤  M ) := by push_neg ; rfl  -- f n'est pas minorée

-- Exercice 5.2
example : ¬ (∃ y:ℝ, ∀ x:ℕ  , y > x ) ↔ (∀ y:ℝ, ∃ x:ℕ  , y ≤  x ) := by push_neg ; rfl   -- il n'existe pas de réel strictement supérieur à n'importe quel entier naturel

-- Exercice 5.2
example (f:ℝ → ℝ ): ¬ (∃ m:ℝ,∃ M:ℝ, ∀ x:ℝ , (f x ≥ m) ∧ (f x ≤ M)  ) ↔ (∀ m:ℝ, ∀ M:ℝ, ∃ x:ℝ , (f x < m) ∨ (f x > M)  ) := by push_neg ; rfl  -- f n'est pas bornée



-- Exercice 5.3
namespace ex53 -- pour que les notation P,Q, n'interferent pas avec les autres exos

-- (a) Vrai ou faux :une et une seule des deux assertions suivantes à prouver :

def P : Prop := ∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2

/- celle-ci est fausse
example :    P := 
  λ u:ℝ  ↦  
    λ b:ℝ  ↦  
      sorry 
-/

example : ¬ P :=  
   -- si vous choisissez cette assertion à prouver, 
   -- l'utilisation du lemme not_forall permet de ramener une preuve de ¬ ∀ ... à une preuve de ∃ ...
  not_forall.mpr (  
    Exists.intro 1 (
      not_forall.mpr (  
        Exists.intro 1 (
          by norm_num : ((1:ℝ)+1)^2 ≠ 1^2+1^2
        )
      )
   )
  )

-- (b) Vrai ou faux :une et une seule des deux assertions suivantes à prouver :
def Q : Prop := ∀ u:ℝ, ∀ b:ℝ, (u+b)^2 ≠ u^2 + b^2

/- celle-ci est fausse
example :    Q := sorry 
-/

example : ¬ Q  :=
  not_forall.mpr (  
    Exists.intro 0 (
      not_forall.mpr (  
        Exists.intro 1 (
          by norm_num : ¬ ((0:ℝ)+1)^2 ≠ 0^2+1^2
        )
      )
   )
  )

example : ¬ Q  :=
  not_forall.mpr (  
    Exists.intro 0 (
      not_forall.mpr (  
        Exists.intro 1 (
          not_not_intro (by norm_num : ((0:ℝ)+1)^2 = 0^2+1^2 )  -- ou:   not_not.mpr
        )
      )
   )
  )


end ex53


------------------------------------------------------------------
--- Exemple 6
------------------------------------------------------------------

theorem not_exists_esisar (α : Type) (P : α → Prop) : ¬ (∃ x:α, P x) ↔ ∀ x:α, ¬ P x := 
  Iff.intro
    (
      λ hne : ¬ (∃ x:α, P x) ↦ 
        λ x : α            ↦ 
          λ hPx : P x      ↦ 
                             
            have he :  ∃ t:α, P t :=
               Exists.intro x hPx
            absurd he hne   
    )
    (
      λ hfx : ∀ x:α , ¬ (P x)   ↦  
        λ he : ∃ x:α, P x    ↦
                              
          Exists.elim he (
            λ (x:α)   (hPx : P x )  ↦ 
              have hnPx : ¬ P x  := hfx x
              absurd hPx hnPx  
          )
          
                
    )



-- Voila la preuve de not_forall :
theorem not_forall_esisar (α : Type) (P : α → Prop) : ¬ (∀ x:α, P x) ↔ ∃ x:α, ¬ P x := 
  Iff.intro
    (
      λ hnf : ¬ (∀ x:α, P x) ↦ 
        of_not_not (
          λ hne : ¬ (∃ x:α, ¬ P x) ↦
          have hf : ∀ x:α, P x := λ x:α  ↦  
            have h_notnotPx : ¬ ¬ (P x) :=
              λ hnPx : ¬ (P x) ↦  absurd (Exists.intro x hnPx) hne 
            of_not_not h_notnotPx
          absurd hf hnf
        )
    )
    (
      λ henPx : ∃ x:α, ¬ P x   ↦  
        λ hf : ∀ x:α, P x    ↦ 
          Exists.elim henPx (
            λ (x:α)   (hnPx : ¬ P x )  ↦ 
              have hPx : P x  := hf x 
              absurd hPx hnPx 
          )
    )    

-- Exercice 6.2

theorem not_forall_not_esisar (α : Type) (P : α → Prop) : ¬ (∀ x:α, ¬ P x) ↔ ∃ x:α, P x := 
  Iff.intro
    (
      λ hnf : ¬ (∀ x:α, ¬ P x) ↦ 
        have hnne : ¬¬  (∃ x:α, P x) :=
                      λ hne : ¬ (∃ x:α, P x) ↦
                      have hf : ∀ x, ¬ P x := 
                        λ x:α  ↦ 
                          (      
                            ( λ hPx : P x ↦  absurd (Exists.intro x hPx) hne) : ¬(P x) 
                          )
                      absurd hf hnf
        of_not_not hnne
    )
    (
      λ hePx : ∃ x:α, P x   ↦  
        λ hf : ∀ x:α, ¬ P x    ↦ 
          Exists.elim hePx (     
            λ (x:α)   (hPx : P x )  ↦
              have hnPx : ¬ P x  := hf x
              absurd hPx hnPx           
          )
          
    )



-- Exercice 6.3

theorem not_exists_not_esisar (α : Type) (P : α → Prop) : ¬ (∃ x:α, ¬ P x) ↔ ∀ x:α, P x := 
  Iff.intro
    (
      λ hne : ¬ (∃ x, ¬ P x) ↦ 
        λ x : α              ↦ 
          have hnnPx : ¬¬(P x)  :=
                λ hnPx : ¬ (P x)   ↦
                  have he : ∃ x, ¬ P x := Exists.intro x hnPx  
                  absurd he hne
          of_not_not hnnPx
    )
    (
      λ hfx : ∀ x, P x   ↦  
        λ he : ∃ x, ¬ P x    ↦ 
          Exists.elim he (
            λ (x:α)   (hnPx : ¬( P x) )  ↦ 
              have hPx : P x  := hfx x 
              absurd hPx hnPx 
          )
    )




------------------------------------------------------------------
--- Exemple 7
------------------------------------------------------------------


def nulle  (f:ℝ→ℝ) : Prop := ∀ x:ℝ, f x = 0
def positive (f:ℝ→ℝ) : Prop :=  ∀ x:ℝ, f x ≥  0
def s_annule (f:ℝ→ℝ) : Prop :=  ∃ x:ℝ, f x =  0
def g (a:ℝ) : ℝ → ℝ :=  fun   x:ℝ ↦  x^2 + a

example : ¬(s_annule (g 1))  :=
  not_exists.mpr (
    λ x:ℝ ↦ 
      have h: g 1 x > 0 :=
        calc
          g 1 x = x^2 + 1 := rfl
          _     ≥ 0+1     := add_le_add (sq_nonneg x) (by norm_num : (1:ℝ) ≥ 1 )
          _     > 0       := by norm_num

      (ne_of_gt h : g 1 x ≠ 0)
  ) 


-- Exercice 7.1
example : (s_annule (g 0)) := 
  Exists.intro 0     --  elle s'annule en 0 car...
  (
     by norm_num : (0:ℝ)^2 + 0 = 0
  )

example : ¬ (nulle (g 0)) := 
  not_forall.mpr (   -- pour montrer ¬∀  on montre ∃...  
     Exists.intro 1        -- elle ne s'annule pas en 1 car ...
     (
       by norm_num : (1:ℝ)^2 + 0 ≠ 0
     )
  )

example : (positive (g 2)) := 
  λ x:ℝ  ↦
    calc
      g 2 x = x^2+2 := rfl 
      _     ≥ 0+2   := by rel[sq_nonneg x]
      _     ≥ 0     := by norm_num
  

example : ¬ (positive (g (-1))) := 
  not_forall.mpr (      -- pour montrer ¬∀  on montre ∃...  
     Exists.intro 0     -- g -1 0 < 0...
     (
       by norm_num :  ¬ ((0:ℝ)^2 + (-1) ≥  0)
     )
  )


------------------------------------------------------------------
--- Exemple 8
------------------------------------------------------------------
-- Exercice 8.1

lemma not_imp_not_esisar :  ∀ P Q : Prop,  (¬Q → ¬P) ↔(P → Q)  := 
   λ P Q : Prop ↦ 
     Iff.intro
     (
       λ hc:  ¬Q → ¬P ↦ 
         λ hP:P ↦ 
           of_not_not (
              λ hnQ : ¬Q ↦
                absurd (hP:P) (hc hnQ :¬ P)

           )
     )
     (
       λ hd:  P → Q ↦ 
         λ hnQ : ¬ Q ↦
           λ hP : P ↦ 
             absurd (hd hP : Q)  (hnQ : ¬ Q)
     )

-- Exercice 8.2
namespace ex82 

-- Trouvez une assertion A de la forme P → Q  telle que A soit vraie mais sa réciproque R := Q → P  soit fausse:
def P : Prop := (-2)=2
def Q : Prop := (-2)^2=4
def A : Prop := P → Q
def R : Prop := Q → P 
example : A := λ h : (-2) = 2 ↦ (by norm_num : (-2)^2 =4)
example : ¬ R := λ (h: R) ↦ absurd (h (by norm_num : (-2)^2 = 4)) (by norm_num : (-2)≠ 2)

end ex82

namespace ex83
--def pair   (n:ℕ) : Prop := ∃ k:ℕ , n=2*k
--def impair (n:ℕ) : Prop := ∃ k:ℕ , n=2*k+1
def pair   (n:ℕ) : Prop := Even n
def impair (n:ℕ) : Prop := Odd n

example (n:ℕ) : pair n ↔   (∃ k:ℕ , n=k+k)   := Iff.rfl
example (n:ℕ) : impair n ↔ (∃ k:ℕ , n=2*k+1) := Iff.rfl

example : ∀ n:ℕ,  pair (n^2) → pair n :=
  λ n:ℕ  ↦ 
    not_imp_not.mp 
    (
      λ hne : ¬ pair n ↦
        have hi  : impair n := Nat.odd_iff_not_even.mpr hne
        have hi2 : impair (n^2) := 
          Exists.elim hi
          (
            λ (k:ℕ ) (hn: n = 2*k+1) ↦ 
              Exists.intro (2*k^2+2*k)
              (
                calc
                  n^2 = (2*k+1)^2         := by rw[hn]
                  _   = 2*(2*k^2+2*k)+1   := by ring_nf
              )
          )
        
        (Nat.odd_iff_not_even.mp hi2 : ¬(pair (n^2)) )
    )
    
end ex83  


------------------------------------------------------------------
--- Exemple 9
------------------------------------------------------------------
-- Nouvelles notions

-- Exercice 9.1
lemma not_or_of_imp_esisar : ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  := 
  λ P Q:Prop ↦
   λ hPQ : P →  Q  ↦ 
     Or.elim (Classical.em P)
     (
        λ hP:P ↦
          Or.inr ((hPQ hP):Q)
     )
     (
        λ hnP: ¬ P ↦
          Or.inl (hnP : ¬ P)
     )
  
-- Exercice 9.2
lemma imp_iff_not_or_esisar : ∀ P Q : Prop,   (P → Q) ↔ (¬ P ∨ Q)  := 
  λ P Q:Prop ↦
    Iff.intro
    (
      not_or_of_imp_esisar P Q
    )
    (
      λ hnPorQ : ¬ P ∨ Q ↦ 
        Or.elim (hnPorQ)
        (
          imp_of_not P Q
        )
        (
          imp_of_ccl P Q
        )
    )   

-- Exercice 9.3
example (P Q: Prop) : ¬ (¬ P ∨ Q ) ↔ (P ∧ ¬ Q) := by push_neg ; rfl


--Exercice 9.4
lemma not_imp_esisar : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := 
  λ P Q : Prop ↦ 
    Iff.intro
    (
      λ hnPQ : ¬ (P → Q)  ↦ 
        And.intro
        (
          of_not_not (
            λ hnP : ¬ P ↦
              absurd (imp_of_not P Q hnP) hnPQ            
          )
        )
        (
          λ hQ : Q ↦ 
            absurd (imp_of_ccl P Q hQ) hnPQ
        )
    )
    (
      λ hPnQ :  P ∧ ¬ Q  ↦ 
        λ hPQ : P → Q ↦ 
          have hQ : Q := hPQ (hPnQ.left:P)
          absurd hQ (hPnQ.right: ¬ Q )
    )

-- Exercice 9.5
example (P Q: ℝ →  Prop) : ¬(∀ x:ℝ , P x → Q x) ↔ (∃x:ℝ, P x ∧ (¬ Q x ) ) := by push_neg ; rfl

-- Exercice 9.6
example  : ¬ (∀ x:ℝ,  x^2=4 → x=2 ) :=
  not_forall.mpr (
    Exists.intro (-2)
    (
       not_imp.mpr (
         And.intro
          (by norm_num : (-2:ℝ )^2 = 4 )
          (by norm_num : (-2:ℝ ) ≠ 2   )
       )
    )
  )


-- Exercice 9.7
def tend_vers_plus_infini (u: ℕ → ℝ) : Prop := ∀ A:ℝ, ∃ n0:ℕ, ∀ n:ℕ , n ≥ n0 → (u n) ≥ A  
example (u:ℕ → ℝ) : ¬ (tend_vers_plus_infini u) ↔ ( ∃ A:ℝ, ∀ n0:ℕ, ∃ n:ℕ , n ≥ n0 ∧  (u n) < A ) := by unfold tend_vers_plus_infini; push_neg ; rfl



------------------------------------------------------------------
--- Exemple 10
------------------------------------------------------------------
open Real

example : ¬ (∃ a b: ℝ, ∀x:ℝ, a * (exp x) + b*(exp (-x)) = x^2)  :=
  λ h: (∃ a b: ℝ, ∀x:ℝ, a * (exp x) + b*(exp (-x)) = x^2) ↦
    Exists.elim h
    (
      λ (a:ℝ) (h':(∃ b: ℝ, ∀x:ℝ, a * (exp x) + b*(exp (-x)) = x^2)) ↦
        Exists.elim h' 
        (
          λ (b:ℝ) (h'':(∀x:ℝ, a * (exp x) + b*(exp (-x)) = x^2 )) ↦
            let e:= exp 1
            have h0 : a+b = 0 :=
              calc
                a+b = a*1+b*1                := by ring_nf
                _   = a*(exp 0)+b*1          := by rw [exp_zero]
                _   = a*(exp 0)+b*(exp (-0)) := by rw [neg_zero,exp_zero]
                _   = 0^2                    := h'' 0
                _   = 0                      := by norm_num
            have he : a*e+b/e = 1 :=
              calc
                a*e+b/e = a*(exp 1)+b*e⁻¹        := rfl
                _       = a*(exp 1)+b*(exp (-1)) := by rw [exp_neg 1]
                _       = 1^2                    := h'' 1
                _       = 1                      := by norm_num
            have h1e : a/e+b*e = 1 :=
              calc
                a/e+b*e = a*e⁻¹+b*e                    := rfl
                _       = a*(exp (-1))+b*e             := by rw [exp_neg 1]
                _       = a*(exp (-1))+b*(exp (-(-1))) := by norm_num
                _       = (-1)^2                       := h'' (-1)
                _       = 1                            := by norm_num
            have h0' : b =-a :=  (neg_eq_of_add_eq_zero_right h0).symm
            have he' : a*(e-1/e) = 1 :=
              calc
                a*(e-1/e) = a*e+(-a)/e := by ring_nf
                _         = a*e+b/e    := by rw[h0']
                _         = 1          := by rw[he]
            have h1e' : a*(e-1/e) = -1 :=
              calc
                a*(e-1/e) = -(a/e +(-a)*e) := by ring_nf
                _         = -(a/e +b*e) := by rw[h0']
                _         = -1          := by rw[h1e]
            have ha : (1:ℝ) = -1 :=
              calc 
                1 = a*(e-1/e)  := he'.symm
                _ = -1         := h1e'
              
            absurd ha (by norm_num)
        )
    )



-- Exercice 10.1

example : ¬ (∃ a b: ℝ, ∀x:ℝ, a * (sin x) + b*(cos x) = (sin (2*x)))  :=
  λ h: (∃ a b: ℝ, ∀x:ℝ, a * (sin x) + b*(cos x) = (sin (2*x))) ↦
    Exists.elim h
    (
      λ (a:ℝ) (h':(∃ b: ℝ, ∀x:ℝ, a * (sin x) + b*(cos x) = (sin (2*x)))) ↦
        Exists.elim h' 
        (
          λ (b:ℝ) (h'':(∀x:ℝ, a * (sin x) + b*(cos x) = (sin (2*x)))) ↦
            have h0 : b = 0 :=
              calc
                b = a*0+b*1              := by ring_nf
                _ = a*(sin 0)+b*1        := by rw [sin_zero]
                _ = a*(sin 0)+b*(cos 0 ) := by rw [cos_zero]
                _ = sin (2*0)            := h'' 0
                _ = sin 0                := by norm_num
                _ = 0                    := sin_zero
            have hpi2 : a = 0 :=
              calc
                a = a*1+b*0                      := by ring_nf
                _ = a*(sin (π/2))+b*0            := by rw [sin_pi_div_two]
                _ = a*(sin (π/2))+b*(cos (π/2) ) := by rw [cos_pi_div_two]
                _ = sin (2*(π/2))                := h'' (π/2)
                _ = sin π                        := by ring_nf
                _ = 0                            := sin_pi
            have hpi4 : (0:ℝ) = 1 :=
              calc
                0 = 0*(sin (π/4))+0*(cos (π/4))  := by ring_nf
                _ = a*(sin (π/4))+b*(cos (π/4))  := by rw [h0,hpi2]
                _ = sin (2*(π/4))                := h'' (π/4)
                _ = sin (π/2)                    := by ring_nf
                _ = 1                            := sin_pi_div_two
            absurd hpi4 (by norm_num)
        )
    ) 



-- Exercice 10.2
example : ∀ x:ℝ, x ≠ -2 → (x+1)/(x+2) ≠ 1  :=
  λ x:ℝ ↦ 
    λ h : x ≠ -2 ↦ 
      λ ha :   (x+1)/(x+2) = 1 ↦ 
        have h0 : x+2 ≠ 0 :=
         λ h1 : x+2 = 0 ↦ 
            have h2 : x=-2 :=
              calc
                x = x+2-2 := by ring_nf
                _ = 0-2   := by rw[h1]
                _ = -2    := by norm_num
            absurd h2 h
          
        have h2 : x+1 = x+2 := 
          calc 
            x+1 = (x+1)/(x+2)*(x+2) := (div_mul_cancel (x+1) h0).symm
            _   = 1*(x+2)           := by rw[ha]
            _   = x+2               := by ring_nf

        have h3 : 1=2 := add_left_cancel h2
        absurd h3 (by norm_num)


------------------------------------------------------------------
--- Exemple 11
------------------------------------------------------------------
-- Nouvelles notions
example : ∀ x:ℝ , x≥-1 →  ∀ n:ℕ, (1+x)^n ≥ n*x :=
  λ x:ℝ ↦ 
    λ h: x ≥ -1 ↦ 
      Or.elim (le_or_gt 0 x  :  x ≥ 0  ∨  x < 0 )
      (
        λ h1 : x ≥  0 ↦ 
          have h' : 1+x ≥ 1 := 
            calc 
              1+x ≥ 1+0 := by rel[h1] -- by simp[h1] -- add_le_add_left h1 1
              _   = 1   := by norm_num

          Nat.rec
            (
              calc
                (1+x)^0 = 1       := by ring_nf
                _       ≥ 0       := by norm_num
                _       = (0:ℕ)*x := by ring_nf
            )
            (
              λ k:ℕ ↦
                λ ih : (1+x)^k ≥ k*x ↦ 
                  have h'' : (1+x)^k ≥ 1 := one_le_pow_of_one_le h' k

                  calc
                    (1+x)^(k+1) = (1+x)^k + (1+x)^k *x := by ring_nf
                    _           ≥ k*x + (1+x)^k *x     := by rel[ih]     -- add_le_add_right ih _
                    _           ≥ k*x + 1*x            := by rel[h'',h1] -- add_le_add_left (mul_le_mul_of_nonneg_right h'' h1) _
                    _           = (k+1)*x              := by ring_nf
                    _           = ((k+1):ℕ)*x          := by norm_num
            )
      )
      (
        λ h1 : x < 0 ↦ 
          have h' : 1+x ≥ 0 := 
            calc 
              1+x ≥ 1+(-1) := by rel[h]   -- add_le_add_left h 1
              _   = 0      := by norm_num
          λ n:ℕ ↦ 
            calc
              (1+x)^n ≥ 0    := by simp[h']   -- pow_nonneg h' n
              _       = 0*n  := by ring_nf    -- (zero_mul (n:ℝ)).symm
              _       ≥ x*n  := by rel[h1]    -- mul_le_mul_of_nonneg_right (le_of_lt h1) (Nat.cast_nonneg n)
              _       = n*x  := by ring_nf    -- mul_comm x n
          
      )



-- Exercice 11.1
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


--- Exemple -----
open Nat

def P (n:ℕ) : Prop := n ! ≥ 2^n

example : ∀ n:ℕ , n ≥ 4 → P n :=
  Nat.le_induction
  (
    by norm_num : 4 ! ≥ 2^4
  )
  (
    λ k:ℕ ↦ 
      λ h : k ≥ 4 ↦
        have h'  : k+1 ≥ 2 :=  add_le_add_right (le_trans (by norm_num : 4 ≥ 1) h) 1
        λ ih : k ! ≥ 2^k ↦ 
          calc
            (k+1) ! = (k+1) * (k !)  := rfl
            _       ≥ (k+1) * 2^k    := by rel[ih] -- mul_le_mul_of_nonneg_left   ih (Nat.zero_le (k+1))   
            _       ≥ 2     * 2^k    := by rel[h'] -- mul_le_mul_of_nonneg_right  (h' ) (pow_nonneg (by norm_num: 2 ≥ 0 ) k)
            _       = 2^(k+1)        := by ring_nf -- (Nat.pow_succ').symm
  )


-- Exercice 11.2
example : ∀ n:ℕ , n ≥ 5 → 2^n > 5*(n+1) :=
  Nat.le_induction
  (
    by norm_num : 2^5  > 5*(5+1)
  )
  (
    λ k:ℕ ↦ 
      λ h : k ≥ 5 ↦
        λ ih : 2^k  > 5*(k+1) ↦ 
          calc
            2^(k+1) = 2*2^k           := by ring_nf
            _       > 2*(5*(k+1))     := by rel[ih] 
            _       = 5*(k+1+1) + 5*k := by ring_nf
            _       ≥ 5*(k+1+1) + 5*5 := by rel[h]
            _       ≥ 5*(k+1+1)       := by norm_num
  )


-- Exercice 11.3
def pair   (n:ℕ) : Prop := ∃ k:ℕ , n=2*k
def impair (n:ℕ) : Prop := ∃ k:ℕ , n=2*k+1

example : ∀ n:ℕ, pair n ∨ impair n := 
  Nat.rec
  (
    Or.inl (Exists.intro 0 (by norm_num): pair 0)
  )
  (
    λ k:ℕ  ↦
      λ ih : pair k ∨ impair k ↦
        Or.elim ih
        (
          λ hkpair : pair k ↦ 
            Exists.elim hkpair
            (
              λ (a:ℕ) (hk : k = 2*a) ↦
                have hk1impair : impair (k+1) :=
                  Exists.intro a 
                  (
                    calc
                      k+1 = 2*a+1 := by rw[hk]
                  )
                Or.inr hk1impair
            )
        ) 
        (
          λ hkimpair : impair k ↦ 
            Exists.elim hkimpair
            (
              λ (a:ℕ) (hk : k = 2*a+1) ↦
                have hk1pair : pair (k+1) :=
                  Exists.intro (a+1) 
                  (
                    calc
                      k+1 = (2*a+1)+1 := by rw[hk]
                      _   = 2*(a+1)   := by ring_nf
                  )
                Or.inl hk1pair
            )
        ) 
  )



