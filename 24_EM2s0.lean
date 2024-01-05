import Esisar.Exam

/-! # Epreuve Machine 2  -/


/-
Dans cet examen, les seules tactiques autorisées sont :

by rw[_]
by rel[_]
by norm_num
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


--S1

-- Dans cet exercice, vous pouvez utiliser le lemme of_not_not  décrit ci-dessous :
-- lemma of_not_not :  ∀ {P : Prop} ,  ¬¬P → P := sorry
#check of_not_not

/- 2 points -/
theorem em2s1ex01 :  ∀ P Q : Prop,  (¬Q → ¬P) →  (P → Q)  :=  sorry

--S2

/- 2 points -/
theorem em2s2ex01 :  ∀ P Q : Prop,  (P → Q) → (¬Q → ¬P)   :=  sorry




-- Exercice 2

--S1

/- 2 points -/
theorem em2s1ex02 :  ∀ P Q : Prop, (¬ P ∨ Q) →   (P → Q)   :=
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


--S2

/- 2 points -/
-- Dans cet exercice, vous pouvez utiliser le lemme Classical.em  décrit ci-dessous :
-- lemma Classical.em :  ∀ {P : Prop} ,  P ∨ ¬P  := sorry
#check Classical.em

theorem em2s2ex02 :  ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  := sorry


-- Exercice 3

-- S1

/- 2 points -/
theorem em2s1ex03 :   {x:ℕ  | ∃ k:ℕ, x = 2*k } ⊈ {x:ℕ | ∃ k:ℕ, x = 6*k }  := sorry


-- S2

/- 2 points -/
theorem em2s2ex03 :   {x:ℕ | ∃ k:ℕ, x = 9*k } ≠ {x:ℕ | ∃ k:ℕ, x = 3*k }  := sorry


-- Exercice 4

--S1

/- 2 points -/
theorem em2s1ex04 :  ∀ E : Type, ∀ A B : Set E,  A ⊆ B ∧ B ⊆ A → A = B := sorry

-- S2

/- 2 points -/
theorem em2s2ex04 :  ∀ E : Type, ∀ A B : Set E,  A = B → A ⊆ B :=
  λ E A B ↦
    λ h: A= B ↦
      have hAA  : A ⊆ A := sorry   -- on a prouvé ça plus haut
      have hAB  : A ⊆ B := h ▸ hAA                             --  l'égalité h:A=B  permet de remplacer A par B dans hAA : A ⊆ A   ;  on utilise ▸  qui s'obtient avec \t
      hAB




-- Exercice 5

--S1
def pair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k

/- 2 points -/
theorem em2s1ex05 :  {x : ℤ | pair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k + 2} := sorry

-- S2
def impair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k+1

/- 2 points -/
theorem em2s2ex05 :  {x : ℤ | impair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k - 3} := sorry


-- Exercice 6

-- S1

/- 2 points -/
theorem em2s1ex06 :  ∀ E:Type, ∀ A B : Set E, A ⊆ B →  (Bᶜ ⊆ Aᶜ)  := sorry

--S2

/- 2 points -/
theorem em2s2ex06 :  ∀ E:Type, ∀ A B : Set E, (Bᶜ ⊆ Aᶜ) → A ⊆ B   := sorry


-- Exercice 7

-- S1

/- 2 points -/
theorem em2s1ex07 :  { x:ℝ| x ≥  2 } ∩ { x:ℝ| x < -2 } ⊆  ∅ := sorry

-- S2

/- 2 points -/
theorem em2s2ex07 :  ∀ t : ℝ, t ∈ {x : ℝ | -2 < x} ∪ {x : ℝ | x ≤  2}  := sorry



-- Exercice 8

-- S1

/- 2 points -/
theorem em2s1ex08 :  ∀ E:Type, ∀ A B : Set E,  B ⊆ A ↔ (A ∪ B  = A) := sorry

-- S2

/- 2 points -/
theorem em2s2ex08 :  ∀ E:Type, ∀ A B : Set E,  A ⊆ B ↔ (A ∩ B = A) := sorry


-- Exercice 9

-- S1

/- 2 points -/
theorem em2s1ex09 :  ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := sorry

-- S2

/- 2 points -/
theorem em2s2ex09 :  ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := sorry


-- Exercice 10

-- S1

/- 2 points -/
theorem em2s1ex10 :  ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C := sorry

-- S2

/- 2 points -/
theorem em2s2ex10 :  ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C := sorry


-- Exercice 11

-- S1

/- 2 points -/
theorem em2s1ex11 :  ∀ E:Type, ∀ A B C : Set E,    (A ∩ B  ⊆   A ∩ C)  → (  A ∩ Cᶜ ⊆ A ∩ Bᶜ )  := sorry

-- S2
/- 2 points -/
theorem em2s2ex11 :  ∀ E:Type, ∀ A B C : Set E,    (A ∩ B  ⊆   A ∩ C)  → (  A ∩ Cᶜ ⊆ A ∩ Bᶜ )  := sorry





end exam
