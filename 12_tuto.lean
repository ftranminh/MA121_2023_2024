import Mathlib.Data.Nat.Basic   -- librairie à importer pour utiliser les entiers naturels (ℕ)
import Mathlib.Data.Int.Basic   -- librairie à importer pour utiliser les entiers (ℤ)
import Mathlib.Data.Real.Basic   -- librairie à importer pour utiliser les réels (ℝ)



-- Vous pouvez tester immédiatement ces exemples dans le Lean Web Editor :
-- https://lean.math.hhu.de/

-- Ou vous pouvez installer sur votre machine VS Code et l'extension Lean4 en suivant ces instructions :
-- https://leanprover.github.io/lean4/doc/quickstart.html


------------------------------------------------------------------
--- Exemple 1
------------------------------------------------------------------

-- Nouvelles notions
--  Propriétés de ∧ et ∨ 


-- Précedemment on a déjà prouvé
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
                 Or.inl hP 
            )
            (
               λ hQ : Q ↦ 
                 Or.inr (Or.inl hQ)
            )
        )
        (
          sorry 
        )
        
    ) 
    (
      λ h: P ∨ (Q ∨ R)  ↦ 
        sorry       
    ) 

-- Exercice 1.2
-- distributivité de ∨ par rapport à ∧
example : ∀ P Q R:Prop,  P ∨ (Q ∧ R)  ↔ (P ∨ Q) ∧ (P ∨ R) :=
  sorry


-- Exercice 1.3
-- associativité de ∧ 
example : ∀ P Q R:Prop,  (P ∧ Q) ∧ R  ↔ P ∧ (Q ∧ R) :=
  sorry 



------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------

-- Nouvelles notions
--  le FAUX (False) , l'élimination de False,  raisonnement 'ex falso'


-- Par définition, il n'existe pas de preuve de FAUX  (donc pas d'introduction de False)
-- FAUX veut dire "les poules ont des dents"
-- Comme il n'existe pas de preuve de FAUX, 
-- celle-celui qui viendrait avec une preuve de FAUX serait maître du monde : 
-- une preuve de FAUX donne accès à une preuve de N'IMPORTE QUEL  énoncé.
-- Cet axiome s'appelle l'élimination du FAUX ou Ex Falso.

example : False → 3^2 = 1 :=   -- si les poules ont des dents, 3^2 vaut 1
  λ h : False ↦ 
    (False.elim h : 3^2 = 1 )    -- elimination du FAUX

example : False → ∃ x:ℝ, x^2 < 0  :=   -- si les poules ont des dents, il existe x réel tq x^2 < 0
  λ h : False ↦ 
    False.elim h                 -- elimination du FAUX

-- Exercice 2.1
example : False → 2=3  := 
  sorry

-- Exercice 2.2
example : False → ∀ x:ℝ, x = 1  := 
  sorry



------------------------------------------------------------------
--- Exemple 3
------------------------------------------------------------------
-- Nouvelles notions
--  La Négation d'une assertion


--  La Négation d'une assertion  P se note  ¬ P    ( ¬ s'obtient en tapant \not )
--  La définition interne de (¬ P) est (P → False)
--  Pour comprendre cela, j'ai bien aimé l'explication de Pr Altenkirch  sur youtube :
--     False veut dire "les poules ont des dents"   (en anglais ils disent : pigs have wings, les porcs ont des ailes)
--     Si tu lui demandes (P) :"veux tu te marier avec moi ?"     |
--     Et qu'elle-il répond "Quand les poules auront des dents"   |   P → False
--     Tu as compris ce que ça veut dire ...                      ... ¬ P


-- Conséquence : pour prouver ¬P  (ie P → False ) ,
-- on suppose P  (introduction de → )
-- et on aboutit à une contradiction (seule façon de produire une preuve de False)
-- Cette contradiction ne pourra elle meme etre produite que par:
--       une preuve hQ   d'une autre assertion Q
--       une preuve hnQ  de sa négation ¬ Q  (ou encore Q → False)
--  de sorte que (hnQ hQ)  est une preuve de False...
--  On peut utiliser le lemme absurd de la bibliothèque  pour éliminer False dans la foulée
--  (absurd hQ hnQ) est synonyme de   (False.elim (hnQ hQ))

example : ∀ x:ℝ, x^2=4 → x ≠ 3 :=    -- ≠ s'obtient avec \ne  ; x ≠ 3  est synonyme de ¬(x=3)  
  λ x:ℝ ↦  
    λ h1 : x^2 = 4 ↦ 
      λ h2 : x = 3 ↦       -- on s'apprete a prouver ¬(x=3)  c'est a dire x=3 → False
        have h3 : (4:ℝ)=3^2 :=   -- on doit préciser (4:ℝ) pour que Lean ne considère pas qu'il s'agit d'entiers
          calc
            4   = x^2 := by rw[h1]
            _   = 3^2 := by rw[h2]
        absurd h3 (by norm_num : (4:ℝ) ≠ 3^2)


-- Lois de De Morgan
example : ∀ P Q : Prop,  (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) :=
  λ P Q : Prop ↦ 
    λ h1 : (¬ P) ∨ (¬ Q) ↦ 
      λ h2 : P ∧ Q ↦ 
        Or.elim h1
        (λ hnP: ¬ P ↦ absurd h2.left hnP )
        (λ hnQ: ¬ Q ↦ absurd h2.right hnQ )




-- Exercice 3.1
example : ∀ x:ℝ, x^2=x → ¬(x=2 ∨ x=-1 ) :=
  sorry


-- Exercice 3.2
-- Lois de De Morgan suite
example : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) :=
  sorry

-- Exercice 3.3
-- Lois de De Morgan suite
example : ∀ P Q : Prop,  (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
  sorry



------------------------------------------------------------------
--- Exemple 4
------------------------------------------------------------------
-- Nouvelles notions
--  Le tiers exclu

-- La  loi du tiers exclu stipule que pour toute assertion P, on a forcément P ∨ ¬ P  
-- Dans la bibliothèque, elle est nommée Classical.em  parce qu'elle est caractéristique de la logique dite classique
#check Classical.em


-- derniere loi de De Morgan nécessitant l'utilisation du tiers exclu

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

#check not_exists
#check not_forall
#check not_exists_not
#check not_forall_not


#check forall_congr'
#check forall_congr
#check exists_congr

example (x y : ℝ ) : (¬ x ≤ y) ↔ (x>y) := by exact not_le
example (α :Type) (P Q : α → Prop) (h: ∀ x, (P x ↔ Q x) ) : (∀ x, P x) ↔ (∀ x , Q x) :=  forall_congr' h
example (α :Type) (P Q : α → Prop) (h: ∀ x, (P x ↔ Q x) ) : (∀ x, P x) ↔ (∀ x , Q x) := by aesop

example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by push_neg ; tauto
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by push_neg ; rfl
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := 
  calc
    ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M )  ↔  (∀ M:ℝ,¬ (∀ x:ℝ , f x ≤ M ) ) := not_exists
    _                            ↔  (∀ M:ℝ,∃ x:ℝ, ¬( f x ≤  M))   := forall_congr' (λ_ ↦ not_forall )
    _                            ↔  (∀ M:ℝ,∃ x:ℝ, f x > M)        := forall_congr' (λ_ ↦ exists_congr ( λ _ ↦ not_le) )

def majoree (f:ℝ → ℝ) := ∃ M:ℝ, ∀ x:ℝ , f x ≤ M
example (f:ℝ → ℝ ): ¬ (majoree f ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by unfold majoree; push_neg ; rfl


theorem not_exists_iff_l  (α : Type) (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := not_exists     -- by library_search
theorem not_forall_iff_l  (α : Type) (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := not_forall     -- by library_search
theorem not_exists_iff'_l (α : Type) (P : α → Prop) : ¬ (∃ x, ¬ P x) ↔ ∀ x, P x := not_exists_not -- by library_search
theorem not_forall_iff'_l (α : Type) (P : α → Prop) : ¬ (∀ x, ¬ P x) ↔ ∃ x, P x := not_forall_not -- by library_search



theorem not_exists_iff' (α : Type) (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := sorry
theorem not_forall_iff' (α : Type) (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := sorry
theorem not_exists_iff'' (α : Type) (P : α → Prop) : ¬ (∃ x, ¬ P x) ↔ ∀ x, P x := sorry
theorem not_forall_iff'' (α : Type) (P : α → Prop) : ¬ (∀ x, ¬ P x) ↔ ∃ x, P x := sorry

theorem not_exists_iff (α : Type) (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := 
  Iff.intro
    (
      λ hne : ¬ (∃ x, P x) ↦ 
        λ x : α            ↦ 
          λ hPx : P x      ↦
            have he : ∃ x, P x := Exists.intro x hPx  
            absurd he hne
    )
    (
      λ hfx : ∀ x, ¬ P x   ↦  
        λ he : ∃ x, P x    ↦ 
          Exists.elim he (
            λ (x:α)   (hPx : P x )  ↦ 
              have hnPx : ¬ P x  := hfx x 
              absurd hPx hnPx 
          )
    )

theorem not_exists_iff_short (α : Type) (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := 
  ⟨ λ hne x hPx  ↦  hne ⟨x,hPx⟩ , λ hfx ⟨x,hPx⟩ ↦ hfx x hPx ⟩ 

theorem not_forall_iff (α : Type) (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := 
  Iff.intro
    (
      λ hnf : ¬ (∀ x, P x) ↦ 
        of_not_not (
          λ hne : ¬ (∃ x, ¬ P x) ↦
          have hf : ∀ x, P x := λ x:α  ↦  of_not_not (λ hnPx : ¬ (P x) ↦  absurd (Exists.intro x hnPx) hne )
          absurd hf hnf
        )
    )
    (
      λ henPx : ∃ x, ¬ P x   ↦  
        λ hf : ∀ x, P x    ↦ 
          Exists.elim henPx (
            λ (x:α)   (hnPx : ¬ P x )  ↦ 
              have hPx : P x  := hf x 
              absurd hPx hnPx 
          )
    )    

theorem not_forall_iff_short (α : Type) (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := 
  ⟨ 
      λ hnf  ↦ of_not_not ( λ hne  ↦ hnf (λ x ↦ of_not_not (λ hnPx ↦ hne ⟨x ,hnPx ⟩  )) ) ,
      λ ⟨x,hnPx⟩ hf ↦  hnPx (hf x )
  ⟩   

#check of_not_not


theorem not_exists_iff' (α : Type) (P : α → Prop) : ¬ (∃ x, ¬ P x) ↔ ∀ x, P x := 
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

theorem not_forall_iff' (α : Type) (P : α → Prop) : ¬ (∀ x, ¬ P x) ↔ ∃ x, P x := 
  Iff.intro
    (
      λ hnf : ¬ (∀ x, ¬ P x) ↦ 
        have hnne : ¬¬  (∃ x, P x) :=
                      λ hne : ¬ (∃ x, P x) ↦
                      have hf : ∀ x, ¬ P x := λ x:α  ↦ (( λ hPx : P x ↦  absurd (Exists.intro x hPx) hne) : ¬(P x) )
                      absurd hf hnf
        of_not_not hnne
    )
    (
      λ hePx : ∃ x, P x   ↦  
        λ hf : ∀ x, ¬ P x    ↦ 
          Exists.elim hePx (
            λ (x:α)   (hPx : P x )  ↦ 
              have hnPx : ¬ P x  := hf x 
              absurd hPx hnPx 
          )
    )


