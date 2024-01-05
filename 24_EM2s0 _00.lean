import Esisar.Exam

/-! # Epreuve Machine 2  -/


/-
Dans cet examen, les seules tactiques autorisées sont :

by rw[_]
by rel[_]
by norm_num
by ring_nf



Le seul lemme externe autorisé est celui proposé à l'exercice 10  (of_not_not)


***********
Attention :
***********

si vos preuves sont imcomplètes, veillez à ce que leur structure
soit syntaxiquement correcte , en utilisant éventuellement le mot clé sorry pour
remplacer les termes de preuves absents

-/

namespace exam


------------EX 1 --------------

/-
-- not_imp_not
lemma not_imp_not_esisar :  ∀ P Q : Prop,  (¬Q → ¬P) ↔(P → Q)  :=  sorry --of_not_not
-/


--S1
example :  ∀ P Q : Prop,  (P → Q) → (¬Q → ¬P)   :=  sorry

--S2
example :  ∀ P Q : Prop,  (¬Q → ¬P) →  (P → Q)  :=  sorry --of_not_not



------------EX 2 --------------

-- not_or_of_imp
-- imp_iff_not_or

--S1
lemma not_or_of_imp_esisar : ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  := sorry -- Classical.em

--S2
example : ∀ P Q : Prop, (¬ P ∨ Q) →   (P → Q)   :=
  λ P Q:Prop ↦
      λ hnPorQ : ¬ P ∨ Q ↦
        Or.elim (hnPorQ)
        (
          λ hnP : ¬ P ↦
            λ hP: P ↦
            absurd hP hnP
        )
        (
          λ hQ : Q ↦
            λ hP: P ↦
              (hQ:Q)
        )



-- lemma imp_iff_not_or_esisar : ∀ P Q : Prop,   (P → Q) ↔ (¬ P ∨ Q)  := sorry
-- lemma not_imp_esisar : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) :=

------------EX 3 --------------

-- S1
example :  {x:ℕ  | ∃ k:ℕ, x = 2*k } ⊈ {x:ℕ | ∃ k:ℕ, x = 6*k }  := sorry


-- S2
example :  {x:ℕ | ∃ k:ℕ, x = 9*k } ≠ {x:ℕ | ∃ k:ℕ, x = 3*k }  := sorry


/-

example : 8 ∉ {x:ℤ | ∃ k:ℤ, x = 3*k+1 } := sorry   -- le_or_lt
example :  {x:ℤ | ∃ k:ℤ, x = 6*k } ⊆ {x:ℤ | ∃ k:ℤ, x = 3 * k }  := sorry

--notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

example : {x : ℝ | 0 ≤ x ^ 2} ⊈  {t : ℝ | 0 ≤ t} := sorry
example :  {x:ℤ | ∃ k:ℤ, x = 3 * k } ⊈ {x:ℤ | ∃ k:ℤ, x = 6 * k }  := sorry
example :  {x:ℤ | ∃ k:ℤ, x = 4 * k } ≠ {x:ℤ | ∃ k:ℤ, x = 2 * k }  := sorry

-/

------------EX 4 --------------

lemma subset_refl_esisar  : ∀ E:Type,  ∀ A:Set E, A ⊆ A  := sorry   -- Eq.subset rfl


------------EX 5 --------------

--S1
def pair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k
example : {x : ℤ | pair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k + 2} := sorry

-- S2
def impair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k+1
example : {x : ℤ | impair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k - 3} := sorry



/--/
example (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  := Set.Subset.antisymm_iff
example (E : Type) (A B : Set E ) : A = B → A ⊆ B :=
    λ h: A= B ↦
      have hAA  : A ⊆ A := subset_refl_esisar E A   -- on a prouvé ça plus haut
      have hAB  : A ⊆ B := h ▸ hAA                             --  l'égalité h:A=B  permet de remplacer A par B dans hAA : A ⊆ A   ;  on utilise ▸  qui s'obtient avec \t
      hAB

example (E : Type) (A B : Set E ) :  A ⊆ B ∧ B ⊆ A → A = B := sorry

lemma set_eq_iff_esisar (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  := sorry  -- subset_refl_esisar

example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := sorry
-- eq_zero_or_eq_zero_of_mul_eq_zero
-- eq_of_sub_eq_zero
-- eq_neg_of_add_eq_zero_left
-- mul_eq_zero
-- sub_eq_zero


example :  {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4}  := sorry

example : ∀ E:Type, ∀ A : Set E,(Aᶜ)ᶜ = A := sorry -- compl_compl
example : ∀ E:Type, ∀ A B : Set E, A ⊆ B ↔ (Bᶜ ⊆ Aᶜ)  := sorry
-/

------------EX 6 --------------

-- S1
example : ∀ E:Type, ∀ A B : Set E, A ⊆ B →  (Bᶜ ⊆ Aᶜ)  := sorry

--S2
example : ∀ E:Type, ∀ A B : Set E, (Bᶜ ⊆ Aᶜ) → A ⊆ B   := sorry


------------EX 7 --------------

-- S1
example : { x:ℝ| x ≥  2 } ∩ { x:ℝ| x < -2 } ⊆  ∅ := sorry

-- S2
example : ∀ t : ℝ, t ∈ {x : ℝ | -2 < x} ∪ {x : ℝ | x ≤  2}  := sorry


/-
example : { x:ℝ| x > 1 } ∩ { x:ℝ| x ≤ 0 } = ∅ := sorry
example (E:Type) (A: Set E) (h : A ⊆ ∅ ) : A = ∅  := Set.eq_empty_of_subset_empty h
-/

------------EX 8 --------------

-- S1
example : ∀ E:Type, ∀ A B : Set E,  B ⊆ A ↔ (A ∪ B  = A) := sorry

-- S2
example : ∀ E:Type, ∀ A B : Set E,  A ⊆ B ↔ (A ∩ B = A) := sorry


/-
example : ∀ E:Type, ∀ A B : Set E, A ∪ B = B ∪ A := sorry
lemma inter_comm : ∀ E:Type, ∀ A B : Set E, A ∩ B = B ∩ A := sorry
-/

------------EX 9 --------------

-- S1

lemma distrib_union : ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := sorry

-- S2

lemma distrib_inter : ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := sorry

/-

lemma de_morgan1 : ∀ E:Type, ∀ A B : Set E,  (A ∪ B)ᶜ = (Aᶜ) ∩ (Bᶜ) := sorry
lemma de_morgan2 : ∀ E:Type, ∀ A B : Set E, (A ∩ B)ᶜ = (Aᶜ) ∪ (Bᶜ) := sorry  -- Classical.em
-/


------------EX 10 --------------

-- S1

example : ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C := sorry

-- S2

example : ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C := sorry

/-
example : ∀ E:Type, ∀ A B : Set E,  A ∪ B  = A ∩ B →  A = B := sorry

lemma inter_compl_subset_of_inter_subset : ∀ E:Type, ∀ A B C : Set E,    (A ∩ B  ⊆   A ∩ C)  → (  A ∩ Cᶜ ⊆ A ∩ Bᶜ )  := sorry
-/


-- Exercice 1

/- 2 points -/
theorem em1s0ex01 : ∃ k:ℕ, 17 = 3*k+2        := sorry

/- 2 points -/
theorem em1s1ex01 : ∃ k:ℕ, 14 = 5*k-1        := sorry

/- 2 points -/
theorem em1s2ex01 : ∃ k:ℕ, 26 = 7*k+5        := sorry



-- Exercice 2

-- Question 2a

/- 2 points -/
theorem em1s0ex02a : ∀ x:ℝ, 3*x+5 = 2  → x=-1   := sorry

/- 2 points -/
theorem em1s1ex02a : ∀ x:ℝ, 2*x+5 = 9  → x= 2   := sorry

/- 2 points -/
theorem em1s2ex02a : ∀ x:ℝ, 7*x-8 =-1  → x= 1   := sorry



-- Question 2b

/- 2 points -/
theorem em1s0ex02b : ∀ x:ℝ, x=-1 → 3*x+5 = 2    := sorry

/- 2 points -/
theorem em1s1ex02b : ∀ x:ℝ, x= 2 → 2*x+5 = 9    := sorry

/- 2 points -/
theorem em1s2ex02b : ∀ x:ℝ, x= 1 → 7*x-8 =-1    := sorry



-- Question 2c
-- Dans cette question il est recommandé d'utiliser (faire appel) aux théorèmes em1s?ex02a et em1s?ex02b
-- Par exemple, le terme  (em1s?ex02a x)  est une preuve de ( 3*x+5 = 2  → x=-1 )

/- 1 point -/
theorem em1s0ex02c : ∀ x:ℝ, 3*x+5 = 2  ↔ x=-1   := sorry

/- 1 point -/
theorem em1s1ex02c : ∀ x:ℝ, 2*x+5 = 9  ↔ x= 2   := sorry

/- 1 point -/
theorem em1s2ex02c : ∀ x:ℝ, 7*x-8 =-1  ↔ x= 1   := sorry



-- Exercice 3

def impair (x:ℕ) : Prop := ∃ k:ℕ, x = 2*k+1
def pair   (x:ℕ) : Prop := ∃ k:ℕ, x = 2*k

/- 2 points -/
theorem em1s0ex03 : ∀x:ℕ,∀y:ℕ, impair x ∧ impair y → pair (x+y)     := sorry

/- 2 points -/
theorem em1s1ex03 : ∀x:ℕ,∀y:ℕ, pair   x ∧ impair y → impair (x+y)     := sorry

/- 2 points -/
theorem em1s2ex03 : ∀x:ℕ,∀y:ℕ, pair   x ∧ pair   y → pair (x+y)     := sorry


-- Exercice 4

/- 2 points -/
theorem em1s0ex04 : ∀ P Q : Prop, P ∨ Q → Q ∨ P  := sorry

/- 2 points -/
theorem em1s1ex04 : ∀ P Q : Prop, P ∧ Q → Q ∧ P  := sorry

/- 2 points -/
theorem em1s2ex04 : ∀ P Q : Prop, P ∧ Q → Q ∨ P  := sorry


-- Exercice 5

/- 2 points -/
theorem em1s0ex05 : ∀ (P Q R : Prop), (P ↔  R) → (P ∨ Q ↔  Q ∨ R )  := sorry

/- 2 points -/
theorem em1s1ex05 : ∀ P Q :Prop,  (P → Q) → (P ↔ (P ∧ Q)) :=  sorry

/- 2 points -/
theorem em1s2ex05 : ∀ (P Q : Prop), (P → Q) → (P ∨ Q ↔  Q )  := sorry



-- Exercice 6

/- 2 points -/
theorem em1s0ex06 : ∀ a b:ℝ , (∀x:ℝ, (a+1) * b *  x + a = 0) ↔   (a = 0 ∧ b = 0) :=  sorry

/- 2 points -/
theorem em1s1ex06 : ∀ a b:ℝ , (∀x:ℝ,a * x - b = 0) ↔  (a = 0 ∧ b = 0) :=  sorry

/- 2 points -/
theorem em1s2ex06 : ∀ a b:ℝ , (∀x:ℝ,a  + b * x^2 = 0) ↔  (a = 0 ∧ b = 0) :=  sorry


-- Exercice 7

-- Ex7: Il y a deux questions d'exemple dans le sujet 0 mais l'examen n'en comportera qu'une seule !

/- 2 points -/
theorem em1s0ex07   : ∀ P Q R:Prop,  P ∨ (Q ∧ R)  ↔ (P ∨ Q) ∧ (P ∨ R) := sorry

/- 2 points -/
theorem em1s0'ex07  : ∀ P Q R:Prop,  P ∧ (Q ∨ R)  ↔ (P ∧ Q) ∨ (P ∧ R) := sorry

/- 2 points -/
theorem em1s1ex07   : ∀ P Q R:Prop,  (R ∨ Q)  ∧ P  ↔ (R ∧ P) ∨ (Q ∧ P) := sorry

/- 2 points -/
theorem em1s2ex07   : ∀ P Q R:Prop,  (Q ∧ R) ∨ P ↔ (Q ∨ P) ∧ (R ∨ P) := sorry


-- Exercice 8
/- 2 points -/
theorem em1s0ex08 : ∀ x:ℝ, x^2=x → ¬(x=3 ∨ x=-4 ) := sorry

/- 2 points -/
theorem em1s1ex08 : ∀ x:ℝ, x^3 - 2*x  = 1 → ¬(x=2 ∨ x=-2 ) := sorry

/- 2 points -/
theorem em1s2ex08 : ∀ x:ℝ, 2*x^4+x^2 = 2 → ¬(x=3 ∨ x=-2 ) := sorry

-- Exercice 9

/- 2 points -/
theorem em1s0ex09 : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) := sorry

/- 2 points -/
theorem em1s1ex09 : ∀ P Q : Prop,  (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) := sorry

/- 2 points -/
theorem em1s2ex09 : ∀ P Q : Prop,  (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) :=sorry

-- Exercice 10

-- Dans cet exercice il est possible (mais pas obligatoire, cela dépend des sujets) qu'il soit nécessaire
-- d'utiliser le lemme of_not_not  décrit ci-dessous :

-- lemma of_not_not :  ∀ {P : Prop} ,  ¬¬P → P := sorry
#check of_not_not

--exemple d'utilisatation:
example (P:Prop) ( h:  ¬¬P  ) : P := of_not_not h

/- 2 points -/
theorem em1s0ex10 : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := sorry

/- 2 points -/
theorem em1s1ex10 : ∀ P Q : Prop,    (¬ P ∨ Q) → (P → Q)   := sorry

/- 2 points -/
theorem em1s2ex10 : ∀ P Q : Prop,  (¬Q → ¬P) ↔(P → Q)  :=  sorry



end exam
