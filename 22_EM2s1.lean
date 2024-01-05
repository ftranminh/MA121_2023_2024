import Esisar.Exam

/-! # Epreuve Machine 2 sujet 1 -/


/-
Dans cet examen, les seules tactiques autorisées sont :

by rw[_]
by rel[_]
by norm_cast
by ring_nf




***********
Attention :
***********

si vos preuves sont imcomplètes, veillez à ce que leur structure
soit syntaxiquement correcte , en utilisant éventuellement le mot clé sorry pour
remplacer les termes de preuves absents

-/

namespace exam


-- Exercice 1

-- Dans cet exercice, vous pouvez utiliser le lemme of_not_not  décrit ci-dessous :
-- lemma of_not_not :  ∀ {P : Prop} ,  ¬¬P → P := sorry
#check of_not_not

/- 2 points -/
theorem em2s1ex01 :  ∀ P Q : Prop,  (¬Q → ¬P) →  (P → Q)  :=  sorry


-- Exercice 2

/- 2 points -/
theorem em2s1ex02 :  ∀ P Q : Prop, (¬ P ∨ Q) →   (P → Q)   := sorry


-- Exercice 3

/- 2 points -/
theorem em2s1ex03 :   {x:ℕ  | ∃ k:ℕ, x = 2*k } ⊈ {x:ℕ | ∃ k:ℕ, x = 6*k }  := sorry


-- Exercice 4

/- 2 points -/
theorem em2s1ex04 :  ∀ E : Type, ∀ A B : Set E,  A ⊆ B ∧ B ⊆ A → A = B := sorry


-- Exercice 5

def pair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k

/- 2 points -/
theorem em2s1ex05 :  {x : ℤ | pair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k + 2} := sorry


-- Exercice 6

/- 2 points -/
theorem em2s1ex06 :  ∀ E:Type, ∀ A B : Set E, A ⊆ B →  (Bᶜ ⊆ Aᶜ)  := sorry


-- Exercice 7

/- 2 points -/
theorem em2s1ex07 :  { x:ℝ| x ≥  2 } ∩ { x:ℝ| x < -2 } ⊆  ∅ := sorry


-- Exercice 8

/- 2 points -/
theorem em2s1ex08 :  ∀ E:Type, ∀ A B : Set E,  A ⊆ B ↔ (A ∩ B = A) := sorry


-- Exercice 9

/- 2 points -/
theorem em2s1ex09 :  ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := sorry


-- Exercice 10

/- 2 points -/
theorem em2s1ex10 :  ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C := sorry





end exam
