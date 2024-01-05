import Esisar.Exam

/-! # Epreuve Machine 2 sujet 2  corrigé -/


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
theorem em2s2ex01 :  ∀ P Q : Prop,  (P → Q) → (¬Q → ¬P)   :=
    λ P Q : Prop ↦
      λ hd:  P → Q ↦
        λ hnQ : ¬ Q ↦
          λ hP : P ↦
            absurd (hd hP : Q)  (hnQ : ¬ Q)


-- Exercice 2

/- 2 points -/
-- Dans cet exercice, vous pouvez utiliser le lemme Classical.em  décrit ci-dessous :
-- lemma Classical.em :  ∀ {P : Prop} ,  P ∨ ¬P  := sorry
#check Classical.em

theorem em2s2ex02 :  ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  :=
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


-- Exercice 3

/- 2 points -/
theorem em2s2ex03 :   {x:ℕ | ∃ k:ℕ, x = 9*k } ≠ {x:ℕ | ∃ k:ℕ, x = 3*k }  :=
  λ h :  {x:ℕ | ∃ k:ℕ, x = 9*k } = {x:ℕ | ∃ k:ℕ, x = 3*k }  ↦

    have h3  : 6 ∈ {x:ℕ | ∃ k:ℕ, x = 3*k }  := Exists.intro 2 (  by norm_cast : (6:ℕ) = 3 * 2 )
    have h9  : 6 ∈ {x:ℕ | ∃ k:ℕ, x = 9*k }  := h ▸ h3

    have h9' : 6 ∈ {x:ℕ | ∃ k:ℕ, x = 9*k }  :=
      calc
        6 ∈ {x:ℕ | ∃ k:ℕ, x = 3*k }  := Exists.intro 2 (  by norm_cast : (6:ℕ) = 3 * 2 )
        _ = {x:ℕ | ∃ k:ℕ, x = 9*k }  := h.symm

    Exists.elim h9
    (
      λ (k:ℕ) (hk:6=9*k) ↦
        Or.elim (le_or_lt k 0)
        (
          λ hk0 : k ≤  0 ↦
            absurd
            (
              calc
                6 = 9 * k   := hk
                _ ≤ 9 * 0   := by rel[hk0]
            )
            (by norm_cast)
        )
        (
          λ hk1 : k ≥ 1 ↦
            absurd
            (
              calc
                6 = 9 * k   := hk
                _ ≥ 9 * 1   := by rel[hk1]
            )
            (by norm_cast)
        )
    )



-- Exercice 4

/- 2 points -/
theorem em2s2ex04 :  ∀ E : Type, ∀ A B : Set E,  A = B → A ⊆ B :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      λ h: A= B ↦
        have hAA  : A ⊆ A := λ (x:E) (hx:x∈A ) ↦ hx
        have hAB  : A ⊆ B := h ▸ hAA      --  l'égalité h:A=B  permet de remplacer A par B dans hAA : A ⊆ A   ;  on utilise ▸  qui s'obtient avec \t
        hAB

theorem em2s2ex04' :  ∀ E : Type, ∀ A B : Set E,  A = B → A ⊆ B :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      λ h: A= B ↦
        λ x:E ↦
         λ hxA : x∈ A ↦
           calc
             x ∈ A := hxA
             _ = B := h




-- Exercice 5

def impair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k+1

/- 2 points -/
theorem em2s2ex05 :  {x : ℤ | impair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k - 3} :=
  Set.ext
  (
    λ y:ℤ ↦
      Iff.intro
      (
        λ h : impair y ↦
          Exists.elim h
          (
             λ (k:ℤ) (hk: y = 2*k+1) ↦
              Exists.intro (k+2)
              (
                calc
                  y = 2*k+1     := hk
                  _ = 2*(k+2)-3 := by ring_nf
              )
          )
      )
      (
        λ h : ∃ k:ℤ,  y = 2 * k - 3 ↦
          Exists.elim h
          (
             λ (k:ℤ) (hk: y = 2*k-3) ↦
              Exists.intro (k-2)
              (
                calc
                  y = 2*k-3     := hk
                  _ = 2*(k-2)+1 := by ring_nf
              )
          )

      )
  )



-- Exercice 6

-- Dans cet exercice, vous pouvez utiliser le lemme of_not_not  décrit ci-dessous :
-- lemma of_not_not :  ∀ {P : Prop} ,  ¬¬P → P := sorry
#check of_not_not


/- 2 points -/
theorem em2s2ex06 :  ∀ E:Type, ∀ A B : Set E, (Bᶜ ⊆ Aᶜ) → A ⊆ B   :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      λ h : Bᶜ ⊆ Aᶜ  ↦
        λ x:E ↦
          λ hxA : x ∈ A  ↦
            of_not_not
            (
              λ hxBc : x ∉ B ↦
                absurd (hxA : x ∈ A )   ( (h hxBc) : x ∉ A)
            )




-- Exercice 7

/- 2 points -/
theorem em2s2ex07 :  ∀ t : ℝ, t ∈ {x : ℝ | -2 < x} ∪ {x : ℝ | x ≤  2}  :=
  λ t:ℝ ↦
    Or.elim (le_or_lt t 2)
    (
      λ h : t ≤ 2 ↦
        Or.inr h
    )
    (
      λ h : t > 2 ↦
        have h' : t > -2 :=
          calc
            t > 2  := h
            _ > -2 := by norm_cast
        Or.inl h'
    )



-- Exercice 8

/- 2 points -/
theorem em2s2ex08 :  ∀ E:Type, ∀ A B : Set E,  B ⊆ A ↔ (A ∪ B  = A) :=
  λ  E:Type ↦
    λ A B : Set E ↦
      Iff.intro
        (
          λ h : B ⊆ A  ↦
            Set.ext
              λ x : E ↦
                Iff.intro
                (
                  λ hxAB : x ∈ A ∪ B  ↦
                    Or.elim hxAB
                    (
                      λ hxA : x ∈ A ↦
                        hxA
                    )
                    (
                      λ hxB : x ∈ B ↦
                        (h hxB : x∈A )
                    )
                )
                (
                  λ hxA : x∈A ↦
                    Or.inl hxA
                )
        )
        (
          λ h : (A ∪ B  = A) ↦
            λ x:E ↦
              λ hB : x ∈ B ↦  -- variante ( a la place de  calc...) :               h ▸ (Or.inr hB : x ∈ A ∪ B )
                calc
                  x ∈ A ∪ B := Or.inr hB
                  _ = A     := h
        )



-- Exercice 9

/- 2 points -/
theorem em2s2ex09 :  ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) :=
  λ  E:Type ↦
    λ A B C: Set E ↦
      Set.ext
        λ x:E ↦
          Iff.intro
          (
            λ h : x ∈ (A ∩ B) ∪ C ↦
              Or.elim h
              (
                λ hAB : x ∈ A ∩ B ↦
                (
                  And.intro
                    (Or.inl (hAB.left  : x ∈ A) : x ∈ A ∪ C )
                    (Or.inl (hAB.right : x ∈ B) : x ∈ B ∪ C )
                )
              )
              (
                λ hC : x ∈ C ↦
                (
                  And.intro
                    (Or.inr hC : x ∈ A ∪ C )
                    (Or.inr hC : x ∈ B ∪ C )
                )
              )
          )
          (
            λ h : x ∈ (A ∪ C) ∩ (B ∪ C) ↦
              Or.elim (h.left : x ∈ A ∪ C)
              (
                λ hA : x∈A ↦
                  Or.elim (h.right : x ∈ B ∪ C)
                  (
                    λ hB : x∈B ↦
                      (Or.inl (And.intro hA hB : x∈ A ∩ B) : x ∈ (A ∩ B) ∪ C )
                  )
                  (
                    λ hC : x∈C ↦
                      (Or.inr hC : x ∈ (A ∩ B) ∪ C)
                  )
              )
              (
                λ hC : x∈C ↦
                  (Or.inr hC : x ∈ (A ∩ B) ∪ C)
              )
          )


-- Exercice 10

/- 2 points -/
theorem em2s2ex10 :  ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C :=
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





end exam
