import Mathlib.Data.Nat.Basic   -- librairie à importer pour utiliser les entiers naturels (ℕ)
import Mathlib.Data.Int.Basic   -- librairie à importer pour utiliser les entiers (ℤ)
import Mathlib.Data.Real.Basic   -- librairie à importer pour utiliser les réels (ℝ)
import Mathlib.Data.Nat.Parity   -- chose utiles à propos de odd (impair) et even (pair)
import Mathlib.Data.Complex.Exponential                          -- pour la trigo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic     -- pour la trigo
import Mathlib.Data.Nat.Factorial.Basic                          -- pour n!


-- Vous pouvez tester immédiatement ces exemples dans le Lean Web Editor :
-- https://lean.math.hhu.de/

-- Ou vous pouvez installer sur votre machine VS Code et l'extension Lean4 en suivant ces instructions :
-- https://leanprover.github.io/lean4/doc/quickstart.html
-- https://leanprover-community.github.io/install/project.html

-----------------------
-- 12_tuto.lean
-- Nouvelles notions
-----------------------

--  Exemple 1 -----------------------
--    Propriétés de ∧ et ∨

--  Exemple 2 -----------------------
--    le FAUX (False) , l'élimination de False,  raisonnement 'ex falso'

--  Exemple 3 -----------------------
--    La Négation d'une assertion
--    Premieres loi de De Morgan

--  Exemple 4 -----------------------
--    Le tiers exclu
--    De Morgan suite et fin

--  Exemple 5 -----------------------
--    La négation de (∃ x:E, P x)  est (∀ x:E, ¬ P x)
--    De même, ¬  (∀ x:E, P x)  ↔  (∃ x:E, ¬ P x)

--  Exemple 6 -----------------------
--    Démonstration des lemmes précédents (négations de ∀ et ∃)

--  Exemple 7 -----------------------
--    définir une fonction
--    montrer qu'une assertion est fausse = montrer sa négation

--  Exemple 8 -----------------------
--    contraposée d'une implication (ne pas la confondre avec la réciproque)

--  Exemple 9 -----------------------
--    formulation de l'implication avec ¬ et ∨
--    négation d'une implication

--  Exemple 10 -----------------------
--   Raisonnement par l'absurde

--  Exemple 11 -----------------------
--   Raisonnement par récurrence



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
-- distributivité de ∨ par rapport à ∧
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
-- associativité de ∧
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



-- Exercice 1.5
example : ∀ P Q :Prop,  (P → Q) → ((P ∨ Q) ↔ Q) :=
  λ P Q : Prop ↦
    λ hPimpQ : P → Q ↦
      Iff.intro
      (
        λ hPouQ : P ∨ Q ↦
          Or.elim (hPouQ)
          (
            λ hP:P ↦
              have hQ :Q := hPimpQ hP
              hQ
          )
          (
            λ hQ:Q ↦
              hQ
          )
      )
      (
        λ hQ : Q ↦
          (Or.inr hQ : P ∨ Q)
      )


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



-- Remarque : ▸ s'obtient en tapant \t
-- lorsque hab est une preuve de a=b  , et hP une preuve de P,
--     hab ▸ hP     tente de donner une preuve de P dans lequel certains a (ou tous)
--                  auraient été remplacés par des b

-- En cela le terme   hab ▸ rfl    s'apparente un peu à   by rw[hab]

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


-- Les deux exercices suivants permettent de se convaincre que :
-- *  d'une   part, Q    est une condition suffisante pour que P → Q   soit vraie
-- *  d'autre part, ¬ P  est une condition suffisante pour que P → Q   soit vraie
-- Les résultats obtenus seront nommés respectivement imp_of_ccl  et   imp_of_not
-- pour réutilisation dans l'exemple 9.

-- tout d'abord, si Q est vraie, alors P → Q est vraie (simplement pour le prouver on n'utilise pas le fait que P est vraie)
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

-- Exercice 3.6

def pairZ   (n:ℤ) : Prop := ∃ k:ℤ, n=2*k
def impairZ (n:ℤ) : Prop := ∃ k:ℤ, n=2*k+1

example : ∀ n:ℤ, ¬ (pairZ n ∧ impairZ n) :=
  λ n h ↦
    Exists.elim h.left
    (
      λ k hk ↦
      Exists.elim h.right
      (
        λ k' hk' ↦
          have h1 : _ :=
          (
            calc
              1 = (2*k'+1) - (2*k') := by ring_nf
              _ = n   - 2*k'        := by rw[hk']
              _ = 2*k - 2*k'        := by rw[hk]
              _ = 2*(k-k')          := by ring_nf
          )
          Or.elim (le_or_gt (k-k') 0)
            (
              λ h0 ↦
                have h01 : _ :=
                  (
                    calc
                      1 = 2*(k-k')  := h1
                      _ ≤ 2* 0      := by rel[h0]
                  )
                absurd h01 (by norm_num)
            )
            (
              λ h2 ↦
                have h20 : k-k' ≥ 1 := h2
                have h21 : _ :=
                  (
                    calc
                      1 = 2*(k-k')  := h1
                      _ ≥ 2* 1      := by rel[h20]
                  )
                absurd h21 (by norm_num)
            )
      )
    )


-- Exercice 3.7
example : ∀ P Q : Prop, ¬ Q →  (P ∨ Q ↔ P) := by exact?

example : ∀ P Q : Prop, ¬ Q →  (P ∨ Q ↔ P) :=
  λ P Q : Prop ↦
    λ hnQ : ¬ Q ↦
      Iff.intro
      (
        λ hPQ : P ∨ Q ↦
          Or.elim hPQ
          (
            λ hP :P ↦
              hP
          )
          (
            λ hQ : Q ↦
              absurd hQ hnQ
          )
      )
      (
        λ hP :P ↦
          Or.inl hP
      )




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

-- La négation de (∃ x:E, P x)  est (∀ x:E, ¬ P x)
-- De même, ¬  (∀ x:E, P x)  ↔  (∃ x:E, ¬ P x)

-- je vous laisse prendre le temps nécessaire pour que ceci fasse du sens pour vous, indépendamment de toute justification formelle.

-- quatre lemmes de la bibliothèque rendent compte de ces règles ;
-- nous les redémontrerons nous même dans l'exemple 6.

#check not_exists
#check not_forall
#check not_exists_not
#check not_forall_not

-- Conjointement  à quelques autres lemmes utilitaires, ...

#check forall_congr'
#check forall_congr
#check exists_congr
#check not_le   -- et compagnie

-- .. on peut justifier la négation d'assertions où les quantificateurs sont imbriqués.
-- Par exemple, la négation de  (∃ M:ℝ, ∀ x:ℝ , f x ≤ M) est (∀ M:ℝ,∃ x:ℝ, f x > M)  :

example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) :=
  calc
    ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M )  ↔  (∀ M:ℝ,¬ (∀ x:ℝ , f x ≤ M ) ) := not_exists
    _                            ↔  (∀ M:ℝ,∃ x:ℝ, ¬( f x ≤  M))   := forall_congr' (λ_ ↦ not_forall )
    _                            ↔  (∀ M:ℝ,∃ x:ℝ, f x > M)        := forall_congr' (λ_ ↦ exists_congr ( λ _ ↦ not_le) )

-- Mais dans cet exemple, nous serons plus intéressé-es par le fait de trouver ces négations,
-- et de les valider, que de démontrer que c'est correct, et la preuve un peu pénible ci-dessus peut être remplacée
-- par un appel à la tactique  push_neg , qui s'occupe d'appeler ces lemmes dans le bon ordre :

-- pour une raison  liée au fonctionnement interne de push_neg, nous devons régler une option
-- pour qu'elle  fasse ce que nous voulons (https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/push_neg.20of.20.5Cand.html)
set_option push_neg.use_distrib true


example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by push_neg ; rfl

-- ou encore:
def majoree (f:ℝ → ℝ) := ∃ M:ℝ, ∀ x:ℝ , f x ≤ M
example (f:ℝ → ℝ ): ¬ (majoree f ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by unfold majoree ; push_neg ; rfl



-- Exercice 5.1
-- Complétez en remplaçant sorry par la négation de l'assertion (∃ ... )
-- Tip : en déplaçant le curseur sur 'push_neg', vous verrez apparaitre la solution dans LeanInfoView, mais essayez de ne pas regarder!!
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x > M ) ↔ (∀ M:ℝ, ∃ x:ℝ , f x ≤  M ) := by push_neg ; rfl  -- f n'est pas minorée

-- Exercice 5.2
-- Complétez en remplaçant sorry par la négation de l'assertion (∃ ... )
example : ¬ (∃ y:ℝ, ∀ x:ℕ  , y > x ) ↔ (∀ y:ℝ, ∃ x:ℕ  , y ≤  x ) := by push_neg ; rfl   -- il n'existe pas de réel strictement supérieur à n'importe quel entier naturel

-- Exercice 5.2
-- Complétez en remplaçant sorry par la négation de l'assertion (∃ ... )
set_option push_neg.use_distrib true
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


-- (c)  : commentaire : P et Q sont-elles contraires  ? expliquez
/-
  P et Q sont toutes les deux fausses :

  L'assertion                ∀ u:ℝ, ∀ b:ℝ, (u+b)^2 ≠ u^2 + b^2
  n'est pas le contraire de  ∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2
-/

end ex53


------------------------------------------------------------------
--- Exemple 6
------------------------------------------------------------------

-- Nouvelles notions :
--   Démonstration des lemmes précédents (négations de ∀ et ∃)

-- Même si not_exists, not_forall, not_exists_not, et not_forall_not  sont dans la bibliothèque Mathlib,
-- il est intéressant de s'entrainer à les démontrer.


-- Exercice  6.1
-- Complétez la démontration ci-dessous:

theorem not_exists_esisar (α : Type) (P : α → Prop) : ¬ (∃ x:α, P x) ↔ ∀ x:α, ¬ P x :=
  Iff.intro
    (
      λ hne : ¬ (∃ x:α, P x) ↦
        λ x : α            ↦
          λ hPx : P x      ↦   -- prouver ¬ (P x)  revient à prouver P x → False.
                               -- on suppose donc P x et on cherche à aboutir à une contradiction
            have he :  ∃ t:α, P t :=  -- mais si on avait P x,  il existerait x:α   tel que  P x
               Exists.intro x hPx
            absurd he hne         -- ce qui contredirait (absurd)   hne ...
    )
    (
      λ hfx : ∀ x:α , ¬ (P x)   ↦
        λ he : ∃ x:α, P x    ↦   -- pour prouver ¬ (∃ x:α, P x) , on suppose (∃ x:α, P x)
                               -- et on cherche False (une contradiction)
          Exists.elim he (
            λ (x:α)   (hPx : P x )  ↦      -- Mais alors, on aurait un x:α   tel que   P x  ;
              have hnPx : ¬ P x  := hfx x  -- en appliquant hfx à ce même x,  on aurait ¬ (P x)
              absurd hPx hnPx              -- ce qui est absurde !
          )


    )



-- La démonstration des trois autres (not_forall, not_exists_not, not_forall_not)
-- nécessite le lemme of_not_not   qui stipule que ¬ ¬ P → P
#check of_not_not
-- ça a l'air évident, mais cela résulte de la loi du tiers exclu (exemple 4), (par disjonction de cas P ∨ ¬ P)

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
-- La preuve de not_forall_not  à compléter :

theorem not_forall_not_esisar (α : Type) (P : α → Prop) : ¬ (∀ x:α, ¬ P x) ↔ ∃ x:α, P x :=
  Iff.intro
    (
      λ hnf : ¬ (∀ x:α, ¬ P x) ↦
        have hnne : ¬¬  (∃ x:α, P x) :=
                      λ hne : ¬ (∃ x:α, P x) ↦
                        -- supposer ¬ (∃ x:α, P x) est censé aboutir à une contradiction
                        -- pour obtenir cette contradiction, on prouve (∀ x:α, ¬ P x) ...
                      have hf : ∀ x, ¬ P x :=
                        λ x:α  ↦     -- En effet pour un (x:α) , si on suppose (P x)...
                          (          -- cela contredit hne, donc forcément ¬ (P x)
                            ( λ hPx : P x ↦  absurd (Exists.intro x hPx) hne) : ¬(P x)
                          )
                        -- ce qui vient contredire hnf
                      absurd hf hnf
        of_not_not hnne
    )
    (
      λ hePx : ∃ x:α, P x   ↦
        λ hf : ∀ x:α, ¬ P x    ↦    -- on suppose   (∀ x:α, ¬ P x)   et on veut une contradiction
          Exists.elim hePx (                -- mais comme il existe x:α  ...
            λ (x:α)   (hPx : P x )  ↦       -- tel que   P x   ...
              have hnPx : ¬ P x  := hf x    --  on aura aussi ¬ (P x)  d'après hf
              absurd hPx hnPx               -- voilà l'absurdité  !
          )

    )



-- Exercice 6.3
-- Allez, celle-ci vous la faites seul-e !!   Elle nécessite aussi of_not_not

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
-- Nouvelles notions
--  définir une fonction
--  montrer qu'une assertion est fausse = montrer sa négation


-- On donne les définitions suivantes
-- f est nulle
def nulle  (f:ℝ→ℝ) : Prop := ∀ x:ℝ, f x = 0

-- f est positive
def positive (f:ℝ→ℝ) : Prop :=  ∀ x:ℝ, f x ≥  0

-- f est s'annule
def s_annule (f:ℝ→ℝ) : Prop :=  ∃ x:ℝ, f x =  0


-- on définit la famille de fonctions  g_a :
def g (a:ℝ) : ℝ → ℝ :=  fun   x:ℝ ↦  x^2 + a


-- Montrons que g 1  ne s'annule pas :
#check add_le_add
#check sq_nonneg
#check ne_of_gt

example : ¬(s_annule (g 1))  :=
  -- la négation de ∃  est ∀
  not_exists.mpr (
    λ x:ℝ ↦
      have h: g 1 x > 0 :=
        calc
          g 1 x = x^2 + 1 := rfl   -- rfl veut dire "réflexivité" mais il a aussi pour effet de déplier les définitions
          _     ≥ 0+1     := add_le_add (sq_nonneg x) (by norm_num : (1:ℝ) ≥ 1 )
          _     > 0       := by norm_num

      (ne_of_gt h : g 1 x ≠ 0)
  )


-- Exercice 7.1
-- Montrez que g 0  s'annule
example : (s_annule (g 0)) :=
  Exists.intro 0     --  elle s'annule en 0 car...
  (
     by norm_num : (0:ℝ)^2 + 0 = 0
  )

-- Montrez que g 0  n'est pas nulle
example : ¬ (nulle (g 0)) :=
  not_forall.mpr (   -- pour montrer ¬∀  on montre ∃...
     Exists.intro 1        -- elle ne s'annule pas en 1 car ...
     (
       by norm_num : (1:ℝ)^2 + 0 ≠ 0
     )
  )

-- Montrez que g 2  est positive
example : (positive (g 2)) :=
  λ x:ℝ  ↦
    calc
      g 2 x = x^2+2 := rfl
      _     ≥ 0+2   := by rel[sq_nonneg x]
      _     ≥ 0     := by norm_num


-- Montrez que g (-1)  n'est pas positive
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
-- Nouvelles notions
--   contraposée d'une implication

-- La contraposée d'une implication P → Q  est l'implication  ¬Q → ¬P
-- la contraposée (¬Q → ¬P )  est EQUIVALENTE à (P → Q)  (elle dit la meme chose)

-- ATTENTION : à ne surtout pas confondre avec la réciproque de (P → Q) qui est (Q → P)
--             et qui ne lui est en général pas équivalente !

-- Si l'installation éléctrique est correcte :
--    Si l'interrupteur est sur OFF, alors l'ampoule est éteinte : (*)
--    Autrement dit : Si l'ampoule est allumée, c'est (forcément) que l'interrupteur est sur ON :  contraposée de (*)

--    Par contre,
--      le fait que l'ampoule soit éteinte n'implique pas que l'interrupteur soit sur OFF : elle peut être grillée
--   La réciproque de (*) est fausse

-- Le lemme   not_imp_not  traduit que (¬Q → ¬P) ↔(P→ Q)
#check not_imp_not


-- Exercice 8.1
-- Ecrivez votre démonstration de  not_imp_not :
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
namespace ex82 -- pour que les notation P,Q,A,R n'interferent pas avec les autres exos

-- Trouvez une assertion A de la forme P → Q  telle que A soit vraie mais sa réciproque R := Q → P  soit fausse:
def P : Prop := (-2)=2
def Q : Prop := (-2)^2=4
def A : Prop := P → Q
def R : Prop := Q → P
example : A := λ h : (-2) = 2 ↦ (by norm_num : (-2)^2 =4)
example : ¬ R := λ (h: R) ↦ absurd (h (by norm_num : (-2)^2 = 4)) (by norm_num : (-2)≠ 2)

end ex82


-- Raisonner par la contraposée
-- Parfois, il est plus commode d'essayer de prouver la contraposée ¬ Q →  ¬ P  que l'implication directe P → Q
-- Attention : si l'implication directe est possible à prouver, elle vaut mieux ! (c'est moins alambiqué)

-- Exercice 8.3
-- Exemple : prouvez par la contraposée que : pour tout entier naturel n, si n^2 est pair alors n est pair

-- Nous allons avoir besoin d'un résultat qui vous parait peut etre évident :
-- un entier naturel est impair si et seulement si il n'est pas pair.
-- La bibliothèque Mathlib propose le lemme   Nat.odd_iff_not_even
-- (Vous pourrez en donner une démonstration, par exemple par récurrence, quand nous étudierons la récurrence dans Lean)
-- Pour l'utiliser, il faut importer le bon module en début de fichier   :  import Mathlib.Data.Nat.Parity
-- Par ailleurs, ce lemme fonctionne mieux avec les définitions natives de pair (Even) et impair (Odd)
-- qu'avec nos définitions 'maison' ; nous allons donc nous caler dessus et vérifier que c'est bien équivalent :


namespace ex83
--def pair   (n:ℕ) : Prop := ∃ k:ℕ , n=2*k
--def impair (n:ℕ) : Prop := ∃ k:ℕ , n=2*k+1
def pair   (n:ℕ) : Prop := Even n
def impair (n:ℕ) : Prop := Odd n

example (n:ℕ) : pair n ↔   (∃ k:ℕ , n=k+k)   := Iff.rfl
example (n:ℕ) : impair n ↔ (∃ k:ℕ , n=2*k+1) := Iff.rfl

-- Maintenant, vous pouvez démarrer votre raisonnement par la contraposée:

example : ∀ n:ℕ,  pair (n^2) → pair n :=
  λ n:ℕ  ↦
    not_imp_not.mp   --- utilise la contraposée
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
--   formulation de l'implication avec ¬ et ∨
--   négation d'une implication

-- Nous allons d'abord voir qu'on peut exprimer P → Q   comme (¬ P ∨ Q )

-- Aux exercices 3.2 et 3.3 vous avez prouvé deux lemmes  imp_of_ccl  et  imp_of_not
-- affirmant respectivement que  Q →  (P → Q)    et que    (¬ P) →  (P → Q)

-- Maintenant, vous allez prouver la réciproque : (P → Q)→ (¬ P ∨ Q)
-- Ce résultat existe dans la bibliothèque ( not_or_of_imp )  mais vous allez donner ici votre démonstration
#check not_or_of_imp

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

-- Maintenant vous disposez de tous les ingrédients pour établir l'équivalence :       (P → Q) ↔ (¬ P ∨ Q)
-- Encore une fois ce résultat existe dans la bibliothèque sous le nom imp_iff_not_or  mais vous donnez ici votre démonstration ,
-- qui utilisera les lemmes déjà prouvés aux ex 3.2 (imp_of_ccl) ; 3.3 (imp_of_not)  ; et 9.1 (not_or_of_imp_esisar)
#check imp_iff_not_or

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
-- Les lois de De Morgan précedemment vues donnent que ¬ (¬ P ∨ Q ) équivaut à ....
--  (complétez sans regarder l'exercice 9.4 !!)
example (P Q: Prop) : ¬ (¬ P ∨ Q ) ↔ (P ∧ ¬ Q) := by push_neg ; rfl


--Exercice 9.4
-- La remarque précédente vous donne la négation de (P → Q)
-- Cela doit faire du sens avec la notion de contre exemple : pour prouver que P n'implique pas Q,
-- il faut se trouver dans une situation où P est vraie mais Q est fausse
-- Ce résultat existe dans la bibliothèque Mathlib et s'appelle   not_imp
-- Vous allez le redémontrer directement, en utilisant les lemmes   imp_of_not  et imp_of_ccl
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
-- Donnez la négation de ∀ x :ℝ , P x → Q x
example (P Q: ℝ →  Prop) : ¬(∀ x:ℝ , P x → Q x) ↔ (∃x:ℝ, P x ∧ (¬ Q x ) ) := by push_neg ; rfl

-- Exercice 9.6
-- Application : utilisez  not_forall.mpr    et  not_imp.mpr  pour prouver :
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
-- Donnons d'abord la définition (que nous reverrons plus tard) d'une suite réelle tendant vers +∞

def tend_vers_plus_infini (u: ℕ → ℝ) : Prop := ∀ A:ℝ, ∃ n0:ℕ, ∀ n:ℕ , n ≥ n0 → (u n) ≥ A

-- L'objectif n'est pas de comprendre maintenant la signification d'une telle assertion, mais
-- d'exprimer mécaniquement sa négation, c'est-à-dire d'exprimer que u ne tend pas vers +∞

-- Remplacez le sorry par la négation de : (tend_vers_plus_infini u)

example (u:ℕ → ℝ) : ¬ (tend_vers_plus_infini u) ↔ ( ∃ A:ℝ, ∀ n0:ℕ, ∃ n:ℕ , n ≥ n0 ∧  (u n) < A ) := by unfold tend_vers_plus_infini; push_neg ; rfl



------------------------------------------------------------------
--- Exemple 10
------------------------------------------------------------------
-- Nouvelles notions
--   Raisonnement par l'absurde

-- Raisonner par l'absurde pour prouver P, c'est supposer ¬P et aboutir à une contradiction.

--  En fait, on a déjà fait cette démarche dans le cas où l'on voulait prouver ¬ P:
--  pour prouver ¬P, on supposait P et on arrivait à False, puisque ¬ P a été défini comme P → False.

-- Maintenant, si on veut prouver P, par l'absurde on peut essayer de supposer ¬ P :
-- Si on suppose ¬P et qu'on arrive à False, on a donc prouvé ¬ P → False,  c'est-à-dire ¬¬ P
-- On doit donc utiliser le lemme   of_not_not  (lié au prinicpe du tiers exclu)   pour conclure que  P es vraie
#check of_not_not



-- Dans les exemples qui suivent, pour utliser sin, cos, exp, on a besoin d'importer en début de fichier :
--    import Mathlib.Data.Complex.Exponential
--    import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- puis :
open Real


-- Exemple
-- On veut Montrer qu'on ne peut pas trouver deux réels a et b tels que
--    ∀x:ℝ, a * (exp x) + b*(exp (-x)) = x^2)
-- On procède par l'absurde en supposant qu'on a trouvé deux réels a et b satisfaisant ceci

-- Les lemmes suivants pourront être utiles :
#check exp_zero                     -- valeur de exp(0)
#check exp_neg                      -- exp(-x) = exp(x)⁻¹
#check neg_eq_of_add_eq_zero_right  -- a+b=0 → -a=b


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
                _         = -(a/e +b*e)    := by rw[h0']
                _         = -1             := by rw[h1e]
            have ha : (1:ℝ) = -1 :=
              calc
                1 = a*(e-1/e)  := he'.symm
                _ = -1         := h1e'

            absurd ha (by norm_num)
        )
    )



-- Exercice 10.1

-- On reprend ici l'exercice : TD1.1 ex8
--   Peut-on trouver deux réels a et b tels que
--     ∀x ∈ R, a sin(x) + b cos(x) = sin(2x)

-- Conjecture: on ne peut pas, on le prouve par l'absurde

-- les lemmes suivants pourront être utiles :
#check sin_zero
#check cos_zero
#check sin_pi
#check sin_pi_div_two
#check cos_pi_div_two

-- le nombre π   s'obtient en tapant : \pi

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
-- Montrez que pour tout nombre réel x différent de −2 on a : (x+1)/(x+2) ≠ 1

-- vous aurez peut être besoin du lemme div_mul_cancel :
#check div_mul_cancel
example (a b:ℝ ) (h: b≠ 0) : a/b*b = a := div_mul_cancel a h
-- éventuellement de add_left_cancel
#check add_left_cancel
example (a b c : ℝ) :  a + b = a + c →  b = c := add_left_cancel

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
--   Raisonnement par récurrence


#check Nat.rec
-- Pour une assertion P dépendant d'un entier n
-- Le lemme Nat.rec  de la bibliothèque prend  deux arguments :
--    * une preuve de (P 0)
--    * une preuve de (∀ k:ℕ, P k → P (k+1) )

-- et retourne une preuve de (∀ n:ℕ, P n )

-- Exemple
-- Montrons par récurrence que :   ∀ x:ℝ , x≥-1 →  ∀ n:ℕ, (1+x)^n ≥ n*x



-- Voici quelques lemmes éventuellement utiles

#check le_or_gt
example (a b c:ℝ  ) (h1 : a≤b  ) (h2 : c≥ 0) : a*c ≤ b*c :=  mul_le_mul_of_nonneg_right h1 h2
example (a b c:ℝ  ) (h1 : a≤b  ) (h2 : c≥ 0) : a+c ≤ b+c :=  add_le_add_right h1 c
example (a b c:ℝ  ) (h1 : a≤b  ) (h2 : c≥ 0) : c+a ≤ c+b :=  add_le_add_left h1 c
example (a b:ℝ  ) (h1 : 1≤b  ) (k:ℕ ) : 1 ≤ b^k          :=  one_le_pow_of_one_le h1 k
example (a b:ℝ  ) (h1 : 0≤b  ) (k:ℕ ) : 0 ≤ b^k          :=  pow_nonneg h1 k
#check Nat.cast_nonneg
#check zero_mul
#check pow_nonneg

-- Observez dans l'exemple comment on a essayé de remplacer l'appel à ces lemmes par les tactiques
-- by rel[...]
-- by simp[...]



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
      (                      -- dans ce cas là on ne procède pas par récurrence
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
-- Montrez par récurrence que
--  ∀ n:ℕ , 2^n > n

-- Voici des lemmes dont vous pourriez avoir besoin, si vous n'utlisez pas les tactiques rel et simp
#check mul_le_mul_left
#check Nat.le_add_right
#check Nat.lt.base

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
-- On s'intéresse à P (n:ℕ)  := n ! ≥ 2^n

------------------
-- Pour avoir les factorielles :
-- import Mathlib.Data.Nat.Factorial.Basic
-- puis :
open Nat


def P (n:ℕ) : Prop := n ! ≥ 2^n

#reduce P 1    -- Nat.le a b  signifie a ≤ b
#reduce P 2
#reduce P 3
#reduce P 4


-- A l'aide des résultats ci-dessus, conjecturez un rang n0 pour lequel : ∀ n:ℕ , n≥ n0 → P n

-- La récurrence à partir d'un certain rang n0 se prouve avec Nat.le_induction  (au lieu de Nat.rec)
-- On lui fournit:
--   * une preuve de P n0
--   * une preuve de ∀ k:ℕ , k ≥ n0 → P k → P (k+1)

-- et elle renvoie :
--   une preuve de ∀ n:ℕ , n ≥ n0 → P n

-- Lemmes utiles si on n'utilise pas les tactiques rel et simp
#check add_le_add_right
#check mul_le_mul_of_nonneg_left
#check mul_le_mul_of_nonneg_right
#check Nat.zero_le
#check pow_nonneg
example (k:ℕ ) : 2*2^k = 2^(k+1) := ( Nat.pow_succ').symm


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
-- Montrez, par récurrence, que tout entier naturel est pair ou impair
-- (sans utiliser le lemme de la bibliothèque...)
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
