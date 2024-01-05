import Esisar.Exam

/-! # Epreuve Machine 1 Sujet 0 -/


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


-- Exercice 1

/- 2 points -/
theorem em1s0ex01 : ∃ k:ℕ, 17 = 3*k+2        := sorry


-- Exercice 2

-- Question 2a

/- 2 points -/
theorem em1s0ex02a : ∀ x:ℝ, 3*x+5 = 2  → x=-1   := sorry



-- Question 2b

/- 2 points -/
theorem em1s0ex02b : ∀ x:ℝ, x=-1 → 3*x+5 = 2    := sorry



-- Question 2c
-- Dans cette question il est recommandé d'utiliser (faire appel) aux théorèmes em1s?ex02a et em1s0ex02b
-- Par exemple, le terme  (em1s0ex02a x)  est une preuve de ( 3*x+5 = 2  → x=-1 )

/- 1 point -/
theorem em1s0ex02c : ∀ x:ℝ, 3*x+5 = 2  ↔ x=-1   := sorry



-- Exercice 3

def impair (x:ℕ) : Prop := ∃ k:ℕ, x = 2*k+1 
def pair   (x:ℕ) : Prop := ∃ k:ℕ, x = 2*k

/- 2 points -/
theorem em1s0ex03 : ∀x:ℕ,∀y:ℕ, impair x ∧ impair y → pair (x+y)     := sorry



-- Exercice 4

/- 2 points -/
theorem em1s0ex04 : ∀ P Q : Prop, P ∨ Q → Q ∨ P  := sorry



-- Exercice 5

/- 2 points -/
theorem em1s0ex05 : ∀ (P Q R : Prop), (P ↔  R) → (P ∨ Q ↔  Q ∨ R )  := sorry




-- Exercice 6

/- 2 points -/
theorem em1s0ex06 : ∀ a b:ℝ , (∀x:ℝ, (a+1) * b *  x + a = 0) ↔   (a = 0 ∧ b = 0) :=  sorry



-- Exercice 7

-- Ex7: Il y a deux questions d'exemple dans le sujet 0 mais l'examen n'en comportera qu'une seule !

/- 2 points -/
theorem em1s0ex07   : ∀ P Q R:Prop,  P ∨ (Q ∧ R)  ↔ (P ∨ Q) ∧ (P ∨ R) := sorry

/- 2 points -/
theorem em1s0'ex07  : ∀ P Q R:Prop,  P ∧ (Q ∨ R)  ↔ (P ∧ Q) ∨ (P ∧ R) := sorry



-- Exercice 8
/- 2 points -/
theorem em1s0ex08 : ∀ x:ℝ, x^2=x → ¬(x=3 ∨ x=-4 ) := sorry


-- Exercice 9

/- 2 points -/
theorem em1s0ex09 : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) := sorry


-- Exercice 10

-- Dans cet exercice il est possible (mais pas obligatoire, cela dépend des sujets) qu'il soit nécessaire 
-- d'utiliser le lemme of_not_not  décrit ci-dessous :

-- lemma of_not_not :  ∀ {P : Prop} ,  ¬¬P → P := sorry
#check of_not_not

--exemple d'utilisatation:
example (P:Prop) ( h:  ¬¬P  ) : P := of_not_not h

/- 2 points -/
theorem em1s0ex10 : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := sorry




end exam

