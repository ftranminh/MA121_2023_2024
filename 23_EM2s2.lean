import Esisar.Exam

/-! # Epreuve Machine 2 sujet 2 -/


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

/- 2 points -/
theorem em2s2ex01 :  ∀ P Q : Prop,  (P → Q) → (¬Q → ¬P)   :=  sorry


-- Exercice 2

/- 2 points -/
-- Dans cet exercice, vous pouvez utiliser le lemme Classical.em  décrit ci-dessous :
-- lemma Classical.em :  ∀ {P : Prop} ,  P ∨ ¬P  := sorry
#check Classical.em

theorem em2s2ex02 :  ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  := sorry


-- Exercice 3

/- 2 points -/
theorem em2s2ex03 :   {x:ℕ | ∃ k:ℕ, x = 9*k } ≠ {x:ℕ | ∃ k:ℕ, x = 3*k }  := sorry


-- Exercice 4

/- 2 points -/
theorem em2s2ex04 :  ∀ E : Type, ∀ A B : Set E,  A = B → A ⊆ B := sorry


-- Exercice 5

def impair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k+1

/- 2 points -/
theorem em2s2ex05 :  {x : ℤ | impair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k - 3} := sorry


-- Exercice 6
-- Dans cet exercice, vous pouvez utiliser le lemme of_not_not  décrit ci-dessous :
-- lemma of_not_not :  ∀ {P : Prop} ,  ¬¬P → P := sorry
#check of_not_not

/- 2 points -/
theorem em2s2ex06 :  ∀ E:Type, ∀ A B : Set E, (Bᶜ ⊆ Aᶜ) → A ⊆ B   := sorry


-- Exercice 7

/- 2 points -/
theorem em2s2ex07 :  ∀ t : ℝ, t ∈ {x : ℝ | -2 < x} ∪ {x : ℝ | x ≤  2}  := sorry


-- Exercice 8

/- 2 points -/
theorem em2s2ex08 :  ∀ E:Type, ∀ A B : Set E,  B ⊆ A ↔ (A ∪ B  = A) := sorry


-- Exercice 9

/- 2 points -/
theorem em2s2ex09 :  ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := sorry


-- Exercice 10

/- 2 points -/
theorem em2s2ex10 :  ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C := sorry





end exam
