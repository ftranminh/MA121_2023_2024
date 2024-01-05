import Esisar.Exam

/-! # Epreuve Machine 2 sujet 1 corrigé -/


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
theorem em2s1ex01 :  ∀ P Q : Prop,  (¬Q → ¬P) →  (P → Q)  :=
   λ P Q : Prop ↦
      λ hc:  ¬Q → ¬P ↦
        λ hP:P ↦
          of_not_not (
            λ hnQ : ¬Q ↦
              absurd (hP:P) (hc hnQ :¬ P)

          )


-- Exercice 2

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



-- Exercice 3

/- 2 points -/
theorem em2s1ex03 :   {x:ℕ  | ∃ k:ℕ, x = 2*k } ⊈ {x:ℕ | ∃ k:ℕ, x = 6*k }  :=
  λ h:    {x:ℕ  | ∃ k:ℕ, x = 2*k } ⊆  {x:ℕ | ∃ k:ℕ, x = 6*k } ↦

    have h2 : ∃ k:ℕ, 4 = 2*k := Exists.intro 2 (by norm_cast : (4:ℕ ) = 2*2)
    have h6 : ∃ k:ℕ, 4 = 6*k := h h2

    Exists.elim h6
    (
      λ (k:ℕ) (hk : 4=6*k) ↦
      (
        Or.elim (le_or_lt k 0)
          (
            λ hk0 : k ≤ 0 ↦
              absurd
              (
                calc
                  4 = 6*k := hk
                  _ ≤ 6*0:= by rel[hk0]
              )
              (by norm_cast)
          )
          (
            λ hk1 : k ≥ 1 ↦
              absurd
              (
                calc
                  4 = 6*k := hk
                  _ ≥ 6*1:= by rel[hk1]
              )
              (by norm_cast)
          )
      )
    )



-- Exercice 4

/- 2 points -/
theorem em2s1ex04 :  ∀ E : Type, ∀ A B : Set E,  A ⊆ B ∧ B ⊆ A → A = B :=
  λ  E:Type ↦
    λ  A B : Set E ↦
    λ h : A ⊆ B ∧ B ⊆ A  ↦
      Set.ext
        λ x:E ↦
          Iff.intro
            (
              λ hxA : x ∈ A ↦
                (h.left hxA : x∈B )
            )
            (
              λ hxB : x ∈ B ↦
                (h.right hxB : x∈A )
            )



-- Exercice 5

def pair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k

/- 2 points -/
theorem em2s1ex05 :  {x : ℤ | pair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k + 2} :=
  Set.ext
  (
    λ y:ℤ ↦
      Iff.intro
      (
        λ h : pair y ↦
          Exists.elim h
          (
             λ (k:ℤ) (hk: y = 2*k) ↦
              Exists.intro (k-1)
              (
                calc
                  y = 2*k     := hk
                  _ = 2*(k-1)+2 := by ring_nf
              )
          )
      )
      (
        λ h : ∃ k:ℤ,  y = 2 * k + 2 ↦
          Exists.elim h
          (
             λ (k:ℤ) (hk: y = 2*k+2) ↦
              Exists.intro (k+1)
              (
                calc
                  y = 2*k+2   := hk
                  _ = 2*(k+1) := by ring_nf
              )
          )

      )
  )




-- Exercice 6

/- 2 points -/
theorem em2s1ex06 :  ∀ E:Type, ∀ A B : Set E, A ⊆ B →  (Bᶜ ⊆ Aᶜ)  :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      λ h : A ⊆ B  ↦
        λ x:E ↦
          λ hxBc : x ∈ Bᶜ  ↦
            λ hxA : x ∈ A ↦
              absurd ( (h hxA) : x∈B ) hxBc



-- Exercice 7

/- 2 points -/
theorem em2s1ex07 :  { x:ℝ| x ≥  2 } ∩ { x:ℝ| x < -2 } ⊆  ∅ :=
  λ x: ℝ ↦
    λ h: x ≥ 2  ∧ x < -2 ↦
      absurd
        (
          calc
            2 ≤ x  := h.left
            _ < -2 := h.right
        )
        (by norm_cast)



-- Exercice 8

/- 2 points -/
theorem em2s1ex08 :  ∀ E:Type, ∀ A B : Set E,  A ⊆ B ↔ (A ∩ B = A) :=
  λ  E:Type ↦
    λ A B : Set E ↦
      Iff.intro
        (
          λ h : A ⊆ B  ↦
            Set.ext
              λ x : E ↦
                Iff.intro
                (
                  λ hAB : x ∈ A ∩ B ↦
                    (hAB.left : x ∈ A)
                )
                (
                  λ hA : x∈A ↦
                    And.intro (hA : x ∈ A)  (h hA : x ∈ B)
                )
        )
        (
          λ h : (A ∩ B  = A) ↦
            λ x:E ↦
              λ hA : x ∈ A ↦
                have hAB : x ∈ A ∩ B :=   -- variante ( a la place de calc...):     h.symm ▸ (hA : x ∈ A )
                  calc
                    x ∈ A     := hA
                    _ = A ∩ B := by rw[h]

                (hAB.right : x ∈ B)
        )



-- Exercice 9

/- 2 points -/
theorem em2s1ex09 :  ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) :=
  λ  E:Type ↦
    λ A B C: Set E ↦
      Set.ext
        λ x:E ↦
          Iff.intro
          (
            λ h : x ∈ (A ∪ B) ∩ C ↦
              Or.elim h.left
              (
                λ hA : x ∈ A ↦
                  Or.inl (And.intro (hA : x ∈ A) (h.right : x ∈ C))
              )
              (
                λ hB : x ∈ B ↦
                  Or.inr (And.intro (hB : x ∈ B) (h.right : x ∈ C))
              )
          )
          (
            λ h : x ∈ (A ∩ C) ∪ (B ∩ C)  ↦
              Or.elim h
              (
                λ hAC : x ∈ A ∩ C ↦
                  (And.intro (Or.inl hAC.left : x ∈ A ∪ B) (hAC.right : x ∈ C))
              )
              (
                λ hBC : x ∈ B ∩ C ↦
                  (And.intro (Or.inr hBC.left : x ∈ A ∪ B) (hBC.right : x ∈ C))
              )
          )


-- Exercice 10

/- 2 points -/
theorem em2s1ex10 :  ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C :=
  λ  E:Type ↦
    λ A B C : Set E ↦
      Iff.intro
      (
        λ h :  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↦
          λ x:E ↦
            λ hB: x ∈ B ↦
              Or.elim (Classical.em (x ∈ A))
              (
                λ hA : x ∈ A ↦
                  have hAiB : x ∈ A ∩ B := And.intro hA hB
                  have hAiC : x ∈ A ∩ C := h.right hAiB
                  (hAiC.right : x ∈ C)
              )
              (
                λ hnA : x ∉ A ↦
                  have hAuB : x ∈ A ∪ B := Or.inr hB
                  have hAuC : x ∈ A ∪ C := h.left hAuB
                  Or.elim hAuC
                  (
                    λ hA : x ∈ A ↦
                      absurd hA hnA
                  )
                  (
                    λ hC : x ∈ C ↦
                      hC
                  )
              )
      )
      (
        λ h : B ⊆ C ↦
          And.intro
            (
              λ x: E ↦
                λ hAuB : x ∈ A ∪ B ↦
                  Or.elim hAuB
                  (
                    λ hA : x ∈ A ↦
                      (Or.inl hA : x ∈ A ∪ C)
                  )
                  (
                    λ hB : x ∈ B ↦
                      have hC : x∈C := h hB
                      (Or.inr hC : x ∈ A ∪ C)
                  )
            )
            (
              λ x: E ↦
                λ hAiB : x ∈ A ∩ B ↦
                  And.intro
                    (hAiB.left    : x ∈ A)
                    (h hAiB.right : x ∈ C)
            )
      )
