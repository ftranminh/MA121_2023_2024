import Mathlib.Data.Set.Basic   -- librairie à importer pour utiliser les ensembles (Set)
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic   -- librairie à importer pour utiliser les entiers naturels (ℕ)
import Mathlib.Data.Int.Basic   -- librairie à importer pour utiliser les entiers (ℤ)
import Mathlib.Data.Real.Basic   -- librairie à importer pour utiliser les réels (ℝ)
import Mathlib.Data.Nat.Parity   -- chose utiles à propos de odd (impair) et even (pair)
import Mathlib.Data.Complex.Exponential                          -- pour la trigo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic     -- pour la trigo
import Mathlib.Data.Nat.Factorial.Basic                          -- pour n!

set_option push_neg.use_distrib true

-- Vous pouvez tester immédiatement ces exemples dans le Lean Web Editor :
-- https://lean.math.hhu.de/

-- Ou vous pouvez installer sur votre machine VS Code et l'extension Lean4 en suivant ces instructions :
-- https://leanprover.github.io/lean4/doc/quickstart.html
-- https://leanprover-community.github.io/install/project.html

-----------------------
-- 14_tuto.lean
-- Nouvelles notions
-----------------------

--  Exemple 1 -----------------------
--    Notion d'ensemble
--    Notation d'un ensemble en compréhension
--    Appartenance (et non-appartenance) à un ensemble

--  Exemple 2 -----------------------
--    Inclusion de deux ensembles (assertion)

--  Exemple 3 -----------------------
--    Egalité de deux ensembles (assertion)

--  Exemple 4 -----------------------
--   Complémentaire d'un ensemble   (ensemble)

--  Exemple 5 -----------------------
--    Réunion de deux ensembles   (ensemble)
--    propriétés : commutativité, associativité

--  Exemple 6 -----------------------
--    Intersection de deux ensembles   (ensemble)
--    propriétés : commutativité, associativité
--    propriétés : distributivités de ∩ / ∪ et de ∪ / ∪
--    propriétés : lois de De Morgan

--  Exemple 7 -----------------------
--    Ensemble privé d'un autre

--  Exemple 8 -----------------------
--    Ensemble des parties

--  Exemple 9 -----------------------
--    Produit Cartésien



------------------------------------------------------------------
--- Exemple 1
------------------------------------------------------------------
-- Nouvelles notions
--    Notion d'ensemble
--    Notation d'un ensemble en compréhension
--    Appartenance (et non-appartenance) à un ensemble

-- En Lean, la notion d'ensemble se confond avec la notion de propriété caractéristique
-- Elle s'apparente à la notion de sous-ensemble d'un ensemble de référence, défini en compréhension :
--    {x:E | P x}  est l'ensemble des éléments de type E vérifiant la propriété caractéristique P
-- En Lean la notion d'ensemble (Set) se distingue de la notion de Type qui lui correspondrait plutot à l'ensemble de référence (ℝ, ℤ...)
-- Techniquement, Lean le défini de la façon suivante :
--    def Set (E:Type) : Type := E → Prop

-- Ainsi :
--    Pour y:E
--        y ∈  {x:E | P x}  signifie P y      -- ∈  s'obtient en tapant \in
--        y ∉  {x:E | P x}  signifie ¬(P y)   -- ∉  s'obtient en tapant \nin

-- Exemples

example : 1 ∈ {x:ℤ | x+3 ≥ 2 } :=
  calc
    (1:ℤ)+3 ≥ 2 := by norm_num

example : 14 ∈ {x:ℤ | ∃ k:ℤ, x = 3*k+2 } :=
  Exists.intro 4
  (
    calc
      (14:ℤ) = 3*4+2 := by norm_num
  )


-- La notation en extension {a,b,c}  peut être utilisée, mais il faut préciser le type (ici Set ℕ) :
def A : Set ℕ := {1,2}
-- par définition
example : A = {x:ℕ | x=1 ∨ x=2} := rfl    -- rfl permet de prouver des égalités du type A=A

-- Comme 1:ℕ  ,   1 ∈ A  signifie : 1=1 ∨ 1=2
example : 1 ∈ A :=  Or.inl (rfl : 1=1)    -- rfl permet de prouver 1=1



-- Une preuve de non appartenance qui se fait par l'absurde:
example : 5 ∉ {x:ℤ | ∃ k:ℤ, x = 2*k } :=
  λ h0 : ∃ k:ℤ, 5 = 2*k ↦
    Exists.elim h0 (
      λ (k:ℤ)  (h1: 5 = 2*k ) ↦
        Or.elim (le_or_lt k 2  : ( (k ≤ 2) ∨ (k ≥ 3)   ))
        (
          λ h2: k ≤ 2 ↦
            have ha2 :  (5:ℤ) ≤ 4 :=
              calc
                5 = 2*k  := h1
                _ ≤  2*2 := by rel[h2]
                _ = 4    := by norm_num

            absurd ha2 (by norm_num)
        )
        (
          λ h3: k ≥ 3 ↦
            have ha3 : (5:ℤ) ≥ 6 :=
              calc
                5 = 2*k := h1
                _ ≥ 2*3 := by rel[h3]
                _ = 6   := by norm_num

            absurd ha3 (by norm_num)
        )
    )



-- Exercice 1.1

example : 2 ∈ {x:ℚ | x*3 ≤ 7 } :=
  calc
    (2:ℚ)*3 ≤ 7  := by norm_num

example : 2 ∈ {x:ℚ | x*3 ≤ 7 } :=
     (by norm_num :    (2:ℚ)*3 ≤ 7 )

example : 2 ∈ {x:ℚ | x*3 ≤ 7 } :=
  have h :  (2:ℚ)*3 ≤ 7  := by norm_num
  h

-- Exercice 1.2

example : 22 ∈ {x:ℕ | ∃ k:ℕ , x = 4*k+2 } :=
  Exists.intro 5 (by norm_num : 22 = 4*5+2)

example : 22 ∈ {x:ℕ | ∃ k:ℕ , x = 4*k+2 } :=
  Exists.intro 5 (calc 22 = 4*5+2 := by norm_num)




-- Exercice 1.3


def B : Set ℕ := {4,6,8}
--  ceci signifie :
-- def B : Set ℕ := { x:ℕ | x=4 ∨ x=6 ∨ x=8  }

-- ou encore :
-- def B : Set ℕ := { x:ℕ | x=4 ∨ (x=6 ∨ x=8)  }    -- l'opérateur ∨ associe à droite par défaut


example : 6 ∈ B :=  Or.inr (Or.inl (rfl : 6=6))


example : 6 ∈ B :=
  have h0 : 6=6                := rfl
  have h1 : 6=6 ∨ 6=8          := Or.inl h0
  have h2 : 6=4 ∨ (6=6 ∨ 6=8)  := Or.inr h1
  h2


--example : 7 ∉ B :=  sorry
--  7 ∉ B  signifie  ¬ (7 ∈ B )

-- Rappel :   (¬ P)   signifie  (P → False )
-- Ainsi :   7 ∉ B  signifie  ((7 ∈ B ) → False)

example : 7 ∉ B :=
  λ h: 7 ∈ B ↦     -- h signifie ((7=4) ∨ ( (7=6) ∨ (7=8)) )
    Or.elim h
    (
       λ h4 : 7 = 4 ↦
         absurd h4 (by norm_num)
    )
    (
       λ h68 : (7 = 6) ∨ ( 7 = 8)  ↦
        Or.elim h68
        (
          λ h6 : 7 = 6 ↦
            absurd h6 (by norm_num)
        )
        (
          λ h8 :  7 = 8  ↦
            absurd h8 (by norm_num)
        )
    )

-- Or.elim3  permet de simplifier la preuve ci-dessus

example : 7 ∉ B :=
  λ h: ((7=4) ∨ ( (7=6) ∨ (7=8)) ) ↦    -- h signifie   7 ∈ B
    Or.elim3 h
    (
       λ h4 : 7 = 4 ↦
         absurd h4 (by norm_num)
    )
    (
      λ h6 : 7 = 6 ↦
        absurd h6 (by norm_num)
    )
    (
      λ h8 :  7 = 8  ↦
        absurd h8 (by norm_num)
    )

-- On peut aussi utiliser les lois de De Morgan
#check not_or
example (P Q : Prop )  :  ¬ P ∧ ¬ Q  →    ¬ (P ∨ Q)        := not_or.mpr
#check And.imp_right
example (P Q R: Prop)  :  (Q → R)    →    (P ∧ Q → P ∧ R)  := And.imp_right

-- un petit lemme utile
lemma not_or_3 {P Q R: Prop}  :  ¬ P ∧ (¬ Q ∧ ¬ R)  →  ¬ (P ∨ (Q ∨ R)) :=

  λ h :  ¬ P ∧ (¬ Q ∧ ¬ R) ↦

     have h0  : ¬ Q ∧ ¬ R        :=  h.right
     have h1  : ¬ (Q ∨ R)        :=  not_or.mpr h0
     have h2  : ¬ P ∧ ¬ (Q ∨ R)  :=  And.intro h.left h1
     have h3 :  ¬ (P ∨ (Q ∨ R))  :=  not_or.mpr h2
     h3

-- ou encore
lemma not_or_3' {P Q R: Prop}  :  ¬ P ∧ (¬ Q ∧ ¬ R)  →  ¬ (P ∨ (Q ∨ R)) :=
  λ h :  ¬ P ∧ (¬ Q ∧ ¬ R) ↦
       (not_or.mpr (And.imp_right not_or.mpr h) :   ¬ (P ∨ (Q ∨ R)) )

-- et voila
example : 7 ∉ B :=
  not_or_3
  (
    And.intro
      (by norm_num : ¬7=4)
    (
      And.intro
      (by norm_num : ¬7=6)
      (by norm_num : ¬7=8)
    )
  )


-- Exercice 1.4
-- example : 8 ∉ {x:ℤ | ∃ k:ℤ, x = 3*k+1 } :=  sorry

-- L'énoncé peut se réécrire
-- example : ¬ (8  ∈  {x:ℤ | ∃ k:ℤ, x = 3*k+1 }) :=  sorry

-- ou encore
-- example : ¬ ( ∃ k:ℤ, 8 = 3*k+1 ) :=  sorry

-- ou encore
-- example :  ( ∃ k:ℤ, 8 = 3*k+1 ) → False :=  sorry

-- ce petit lemme sera utile :
#check le_or_lt
example  (k:ℤ  ) : k ≤ 2  ∨ k ≥ 3 := le_or_lt k 2


example : 8 ∉ {x:ℤ | ∃ k:ℤ, x = 3*k+1 } :=
  λ h :  ( ∃ k:ℤ, 8 = 3*k+1 ) ↦
  (
    Exists.elim h
    (
      λ (k:ℤ) (hk : 8 = 3*k+1) ↦
      (
        -- on a deux cas :
        have hk23 : k ≤ 2  ∨ k ≥ 3 := le_or_lt k 2
        Or.elim hk23
        (
          λ hk2 : k ≤ 2 ↦

            have hk2donne : (8:ℤ) ≤ 3*2+1 :=
              calc
                8 = 3*k+1 := hk
                _ ≤ 3*2+1 := by rel[hk2]

            absurd hk2donne (by norm_num)
        )
        (
          λ hk3 : k ≥ 3 ↦
            have hk3donne : (8:ℤ) ≥ 3*3+1 :=
              calc
                8 = 3*k+1 := hk
                _ ≥ 3*3+1 := by rel[hk3]

            absurd hk3donne (by norm_num)
        )
      )
    )
  )


-- On peut aussi procéder avec not_exists

#check not_exists.mpr

example : 8 ∉ {x:ℤ | ∃ k:ℤ, x = 3*k+1 } :=
  not_exists.mpr
  (
    λ k:ℤ ↦                    -- la suite est identique
      λ (hk : 8 = 3*k+1) ↦
      (
        Or.elim (le_or_lt k 2)
        (
          λ hk2 : k ≤ 2 ↦
            absurd ( calc
                8 = 3*k+1 := hk
                _ ≤ 3*2+1 := by rel[hk2]
            ) (by norm_num)
        )
        (
          λ hk3 : k ≥ 3 ↦
            absurd ( calc
                8 = 3*k+1 := hk
                _ ≥ 3*3+1 := by rel[hk3]
            ) (by norm_num)
        )
      )

  )


------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------
-- Nouvelles notions
--   Inclusion de deux ensembles (assertion)

-- si s₁ et s₂ sont deux ensembles d'éléments de type α, l'assertion "inclusion de s₁ dans s₂ "
-- est définie dans la bibliothèque Mathlib de la façon suivante :
def subset_esisar  (E : Type) (A B : Set E) : Prop  :=  ∀ a:E,   a ∈ A → a ∈ B
#print Set.Subset

-- (Set.Subset s₁ s₂)  se note aussi s₁ ⊆ s₂
-- Le symbole ⊆ s'obtient en tapant \sub  ou \subseteq

-- Notez la barre horizontale inférieure du symbole signifiant "inclus ou égal"
-- Attention, dans la notation française nous utilisons ⊂ (sans la barre) pour signifier "inclus ou égal"
-- Alors que dans la notation anglosaxone (et dans Lean), ⊂ signifie "strictement inclus" (ce que nous notons ⊊  : barre inférieure barrée)


example :  {x:ℤ | ∃ k:ℤ, x = 6*k } ⊆ {x:ℤ | ∃ k:ℤ, x = 3*k }  :=
  λ x:ℤ ↦
    λ h : ∃ k:ℤ, x = 6*k  ↦
      Exists.elim h
      (
        λ (k:ℤ)  (hk: x=6*k) ↦
          Exists.intro (2*k)
          (
            calc
              x = 6*k     := hk
              _ = 3*(2*k) := by ring_nf
          )
      )

-- Exercice 2.1
example : {1, 3, 6} ⊆ {t : ℚ | t < 10}  := sorry

-- autre façon d'écrire cet exercice :
-- example : ∀ t:ℚ , t=1 ∨  t=3 ∨  t=6 →   t < 10  := sorry

example : {1, 3, 6} ⊆ {t : ℚ | t < 10}  :=
  λ t:ℚ ↦
    λ h:    t=1 ∨  t=3 ∨  t=6  ↦   -- ou bien : t ∈ {1, 3, 6}
      Or.elim3 h
      (
        λ h1 : t=1 ↦
          calc
            t = 1  := h1
            _ < 10 := by norm_num
      )
      (
        λ h3 : t=3 ↦
          calc
            t = 3  := h3
            _ < 10 := by norm_num
      )
      (
        λ h6 : t=6 ↦
          calc
            t = 6  := h6
            _ < 10 := by norm_num
      )

-- ou encore

example : {1, 3, 6} ⊆ {t : ℚ | t < 10}  :=
  λ t:ℚ ↦
    λ h:   t ∈ {1, 3, 6}   ↦     -- ou bien :t=1 ∨  t=3 ∨  t=6
      Or.elim3 h
      ( λ h1 : t=1 ↦ trans h1 (by norm_num : (1:ℚ) < 10) )
      ( λ h3 : t=3 ↦ trans h3 (by norm_num : (3:ℚ) < 10) )
      ( λ h6:  t=6 ↦ trans h6 (by norm_num : (6:ℚ) < 10) )


-- ou encore

example : {1, 3, 6} ⊆ {t : ℚ | t < 10}  :=
  λ t:ℚ ↦
    λ h:    t=1 ∨  t=3 ∨  t=6  ↦
      Or.elim3 h
      ( trans · (by norm_num) )
      ( trans · (by norm_num) )
      ( trans · (by norm_num) )



-- Exercice 2.2

example :  {x:ℕ  | ∃ k:ℕ , x = 14*k } ⊆ {x:ℕ | ∃ k:ℕ , x = 2*k }  :=  sorry

-- se réécrit :
-- example : ∀  y:ℕ , y ∈  {x:ℕ  | | ∃ k:ℕ , x = 14 * k } → y ∈  {x:ℕ | ∃ k:ℕ , x = 2 * k }  :=  sorry

-- ou encore :
-- example : ∀  x:ℕ ,  ∃ k:ℕ , x = 14 * k  →  ∃ k:ℕ , x = 2 * k  :=  sorry

example :  {x:ℕ  | ∃ k:ℕ , x = 14*k } ⊆ {x:ℕ | ∃ k:ℕ , x = 2*k }  :=
  λ x:ℕ ↦
    λ h: ∃  k:ℕ , x = 14*k ↦
      Exists.elim h
      (
        λ (k:ℕ) (hk: x= 14*k) ↦
        (
          Exists.intro (7*k)
          (
            calc
              x = 14*k    := hk
              _ = 2*(7*k) := by ring_nf
          )
        )
      )



-- Exercice 2.3

-- Redémontrez ce lemme de la bibliothèque :
example  : ∀ E:Type,  ∀ A:Set E, A ⊆ A  :=  λ (E:Type) (A:Set E) ↦ Eq.subset rfl

-- on veut prouver :
--lemma subset_refl_esisar  : ∀ E:Type,  ∀ A:Set E, A ⊆ A  :=

-- c'est à dire :
--lemma subset_refl_esisar  : ∀ E:Type,  ∀ A:Set E, ∀ x:E, x∈ A → x∈ A  :=  sorry

lemma subset_refl_esisar  : ∀ E:Type,  ∀ A:Set E, A ⊆ A  :=
  λ E:Type ↦
    λ A: Set E ↦
      λ (x:E) ↦
        λ (hxA: x ∈ A )  ↦
            (hxA: x ∈ A )



-- La notation ⊈ ("n'est pas inclus dans")  n'est pas définie en standard mais nous pouvons la définir:
notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

-- Voici une preuve de non inclusion :
--  not_forall.mpr permet de ramener une preuve de ¬∀ à une preuve de ∃
--  not_imp.mpr    permet de ramener une preuve de ¬(p → q) à une preuve de p ∧ (¬ q)

example : {x : ℝ | 0 ≤ x ^ 2} ⊈  {t : ℝ | 0 ≤ t} :=
 not_forall.mpr (
  Exists.intro (-1)
  (not_imp.mpr (
    And.intro
      (by norm_num : (0:ℝ) ≤  (-1)^2)
      (by norm_num : ¬((0:ℝ) ≤ -1) )
  ))
 )

-- Autre façon de l'écrire
example : {x : ℝ | 0 ≤ x ^ 2} ⊈  {t : ℝ | 0 ≤ t} :=
  λ h : {x : ℝ | 0 ≤ x ^ 2} ⊆ {t : ℝ | 0 ≤ t} ↦
    have h1 : (-1) ∈ {x : ℝ | 0 ≤ x ^ 2} := (by norm_num  : (0:ℝ) ≤ (-1)^2)
    have h2 : (-1) ∈  {t : ℝ | 0 ≤ t}    := h h1
    absurd h2 (by norm_num)


-- Exercice 2.4

example :  {x:ℤ | ∃ k:ℤ, x = 3*k } ⊈ {x:ℤ | ∃ k:ℤ, x = 6*k }  := sorry

-- signifie :
-- example :  ¬ ( {x:ℤ | ∃ k:ℤ, x = 3*k } ⊆ {x:ℤ | ∃ k:ℤ, x = 6*k } ) := sorry

-- ou encore :
-- example :  ( {x:ℤ | ∃ k:ℤ, x = 3*k } ⊆ {x:ℤ | ∃ k:ℤ, x = 6*k } )  → False := sorry

-- idée : supposer par l'absurde {x:ℤ | ∃ k:ℤ, x = 3* k } ⊆ {x:ℤ | ∃ k:ℤ, x = 6* k }
-- donner un élément (a) de {x:ℤ | ∃ k:ℤ, x = 3* k } qui n'est pas dans  {x:ℤ | ∃ k:ℤ, x = 6* k }
-- déduire de l'hypothèse absurde que a ∈ {x:ℤ | ∃ k:ℤ, x = 6* k } et aboutir une contradiction
-- ici , ce a pourrait etre 15=3*5 mais qui n'est pas multiple de 6, par exemple

example :  {x:ℤ | ∃ k:ℤ, x = 3*k } ⊈ {x:ℤ | ∃ k:ℤ, x = 6*k }  :=
  λ h:    {x:ℤ | ∃ k:ℤ, x = 3*k } ⊆  {x:ℤ | ∃ k:ℤ, x = 6*k } ↦

    have h3 : ∃ k:ℤ, 15 = 3*k := Exists.intro 5 (by norm_num : (15:ℤ ) = 3*5)
    have h6 : ∃ k:ℤ, 15 = 6*k := h h3

    Exists.elim h6
    (
      λ (k:ℤ) (hk : 15=6*k) ↦
      (
        Or.elim (le_or_lt k 2)
          (
            λ hk2 : k ≤ 2 ↦
              absurd
              (
                calc
                  15 = 6*k := hk
                  _  ≤ 6*2:= by rel[hk2]
              )
              (by norm_num)
          )
          (
            λ hk3 : k ≥ 3 ↦
              absurd
              (
                calc
                  15 = 6*k := hk
                  _  ≥ 6*3:= by rel[hk3]
              )
              (by norm_num)
          )
      )
    )


-- On peut aussi démontrer un petit lemme :

lemma not_subseteq_of_exists {E:Type} {A B : Set E} :
                                     (∃ x:E, x ∈ A ∧ x ∉ B) → A ⊈ B :=

    λ hE : (∃ x:E, x ∈ A ∧ x ∉ B) ↦
      Exists.elim hE
        λ (w:E) (hw : w ∈ A ∧ ¬w ∈ B) ↦
          λ hInclus : A ⊆ B ↦
            absurd
              ((hInclus : A ⊆ B) (hw.left : w ∈ A) : w ∈ B )
              (hw.right : w ∉ B)


-- (ou la version courte...)
lemma not_subseteq_of_exists' {E:Type} {A B : Set E} : (∃ x:E, x ∈ A ∧ x ∉ B) → A ⊈ B :=
    λ ⟨_,⟨hA,hnB⟩ ⟩ hS ↦ hnB (hS hA : _ ∈ B)

-- et ensuite :
example :  {x:ℤ | ∃ k:ℤ, x = 3*k } ⊈ {x:ℤ | ∃ k:ℤ, x = 6*k }  :=
  not_subseteq_of_exists
  (
    Exists.intro 15
    (
      And.intro
        (Exists.intro 5 (by norm_num : (15:ℤ ) = 3*5))
        (
          λ h : ∃ k:ℤ, 15=6*k ↦

            Exists.elim h            -- la suite est identique
            (
              λ (k:ℤ) (hk : 15=6*k) ↦
              (
                Or.elim (le_or_lt k 2)
                (
                  λ hk2 : k ≤ 2 ↦
                    absurd
                    (
                      calc
                        15 = 6*k := hk
                        _  ≤ 6*2:= by rel[hk2]
                    )
                    (by norm_num)
                )
                (
                  λ hk3 : k ≥ 3 ↦
                    absurd
                    (
                      calc
                        15 = 6*k := hk
                        _  ≥ 6*3:= by rel[hk3]
                    )
                    (by norm_num)
                )
              )
            )
        )
    )
  )

------------------------------------------------------------------
--- Exemple 3
------------------------------------------------------------------

-- Nouvelles notions
--   Egalité de deux ensembles (assertion)

-- L'égalité de deux ensembles est caractérisée par l'axiome d'extensionnalité ensembliste:
example (E : Type) (A B : Set E ) :  (∀ x:E , x ∈ A ↔ x ∈ B ) → A = B := Set.ext
#check Set.ext


-- Exercice 3.1

def impair (x: ℤ ) : Prop := ∃ k:ℤ, x=2*k+1
example : {x : ℤ | impair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k - 1} := sorry


-- On va utiliser Set.ext  qui  convertit une preuve de (∀ x:E, x∈ A ↔ x ∈ B) en une preuve de A = B
#check Set.ext

example : {x : ℤ | impair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k - 1} :=
  Set.ext
  (
    sorry : ∀ y:ℤ ,  y∈ {x : ℤ | impair x} ↔  y∈ {a : ℤ | ∃ k:ℤ, a = 2 * k - 1}
  )


-- allez c'est parti

example : {x : ℤ | impair x} = {a : ℤ | ∃ k:ℤ, a = 2 * k - 1} :=
  Set.ext
  (
    λ y:ℤ ↦
      Iff.intro
      (
        λ h : impair y ↦
          Exists.elim h
          (
             λ (k:ℤ) (hk: y = 2*k+1) ↦
              Exists.intro (k+1)
              (
                calc
                  y = 2*k+1     := hk
                  _ = 2*(k+1)-1 := by ring_nf
              )
          )
      )
      (
        λ h : ∃ k:ℤ,  y = 2 * k - 1 ↦
          Exists.elim h
          (
             λ (k:ℤ) (hk: y = 2*k-1) ↦
              Exists.intro (k-1)
              (
                calc
                  y = 2*k-1     := hk
                  _ = 2*(k-1)+1 := by ring_nf
              )
          )

      )
  )

-- Exercice 3.2
-- Redémontrez ce lemme de la bibliothèque :
example (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  := Set.Subset.antisymm_iff

-- Ce lemme (utile seulement pour la deuxieme version de hAB) est disponible dans    Esisar.Basic
lemma subst.{v}  {α : Sort v} (motive : α → Prop) {a b : α} (h₁ : a = b) (h₂ : motive a) : motive b
  := @Eq.subst α motive a b h₁ h₂


--vous pouvez utiliser  subset_refl_esisar  démontré à l'exercice 2.3
lemma set_eq_iff_esisar (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  :=
  Iff.intro
  (
    λ h: A= B ↦
      have hAA  : A ⊆ A := subset_refl_esisar E A   -- on a prouvé ça plus haut

      have hAB  : A ⊆ B := h ▸ hAA                             --  l'égalité h:A=B  permet de remplacer A par B dans hAA : A ⊆ A   ;  on utilise ▸  qui s'obtient avec \t
      have hAB' : A ⊆ B := subst (λ X: Set E ↦ A ⊆ X ) h hAA   --  autre façon plus précise (parce qu'on précise QUEL A (le 2e) il faut remplacer par un B dans hAA),  mais moins concise, d'obtenir la meme chose

      -- et de même (cette fois c'est le 1er A qu'on remplace par B dans hAA : A ⊆ A)
      have hBA  : B ⊆ A := h ▸ hAA
      have hBA' : B ⊆ A := subst (λ X: Set E ↦ X ⊆ A ) h hAA

      -- finalement:
      And.intro hAB hBA
  )
  (
    λ h: A ⊆ B ∧ B ⊆ A ↦
      Set.ext
      (
        λ x:E ↦
          Iff.intro
          (
            λ hxA : x ∈ A ↦
              (((h.left : A ⊆ B ) (hxA : x ∈ A)) : x∈ B)
          )
          (
            λ hxB : x ∈ B ↦
              (((h.right : B ⊆ A ) (hxB : x ∈ B)) : x∈ A)
          )
      )
  )

-- version plus courte :
lemma set_eq_iff_esisar' (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  :=
  Iff.intro
  (
    λ h: A = B ↦
      have hAA  : A ⊆ A := subset_refl_esisar E A
      And.intro (h ▸ hAA ) (h ▸ hAA)
  )
  (
    λ h: A ⊆ B ∧ B ⊆ A ↦
      Set.ext
      (
        λ x:E ↦
          Iff.intro
            (λ hxA : x ∈ A ↦  h.left hxA )
            (λ hxB : x ∈ B ↦  h.right hxB )
      )
  )



-- Exercice 3.3
example :  {x:ℤ | ∃ k:ℤ, x = 4*k } ≠ {x:ℤ | ∃ k:ℤ, x = 2*k }  :=

  λ h :  {x:ℤ | ∃ k:ℤ, x = 4*k } = {x:ℤ | ∃ k:ℤ, x = 2*k }  ↦

    have h2 : 2 ∈ {x:ℤ | ∃ k:ℤ, x = 2*k }  := Exists.intro 1 (  by norm_num : (2:ℤ) = 2 *  1 )
    have h4 : 2 ∈ {x:ℤ | ∃ k:ℤ, x = 4*k }  := h ▸ h2

    Exists.elim h4
    (
      λ (k:ℤ) (hk:2=4*k) ↦
        Or.elim (le_or_lt k 0)
        (
          λ hk0 : k ≤  0 ↦
            absurd
            (
              calc
                2 = 4 * k   := hk
                _ ≤ 4 * 0   := by rel[hk0]
            )
            (by norm_num)
        )
        (
          λ hk1 : k ≥ 1 ↦
            absurd
            (
              calc
                2 = 4 * k   := hk
                _ ≥ 4 * 1   := by rel[hk1]
            )
            (by norm_num)
        )
    )



-- Exercice 3.4

-- version 1
example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} :=
  Set.ext
  (
    λ x:ℝ ↦
      Iff.intro

      (
        λ h1: x ^ 2 - x - 2 = 0 ↦

          have h2 : (x+1)*(x-2) = 0 :=    --    (-1) et 2 sont  solutions évidentes
            calc
               (x+1)*(x-2) = x^2-x-2  := by ring_nf
              _            = 0        := h1

          have h3 : x+1=0 ∨ x-2=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2

          Or.elim h3
            (
              λ h4 : x+1=0 ↦
                Or.inl (eq_neg_of_add_eq_zero_left h4 : x=-1)
            )
            (
              λ h5 : x-2=0 ↦
                Or.inr ( eq_of_sub_eq_zero h5  :  x=2)
            )
      )
      (
        λ  h: (x=-1 ∨ x=2) ↦
          Or.elim h
          (
            λ h2 : x=-1 ↦
              calc
                x^2 - x - 2 = (-1)^2 -(-1) - 2  := by rw[h2]
                _           = 1+1-2             := by norm_num
                _           = 0                 := by norm_num
          )
          (
            λ hm3 : x=2 ↦
              calc
                x^2 - x - 2 = 2^2 - 2 - 2  := by rw[hm3]
                _           = 4-2-2       := by norm_num
                _           = 0           := by norm_num
          )

      )
  )


lemma eq_or_eq_of_mul_eq_zero {x a b :ℝ } (h: (x-a)*(x-b)=0 ) : x=a ∨ x=b :=
  Or.imp eq_of_sub_eq_zero eq_of_sub_eq_zero  (eq_zero_or_eq_zero_of_mul_eq_zero h)

lemma eq_or_eq_iff_mul_eq_zero {x a b :ℝ } : (x-a)*(x-b)=0 ↔ x=a ∨ x=b :=
   Iff.trans  mul_eq_zero (Iff.or sub_eq_zero sub_eq_zero)


-- version 2
example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} :=
  Set.ext
  (
    λ x:ℝ ↦
      calc
        x^2 - x - 2 = 0 ↔ (x-(-1))*(x-2) = 0 := by ring_nf
        _               ↔ x=-1 ∨ x=2         := eq_or_eq_iff_mul_eq_zero
  )




-- Exercice 3.5
example :  {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4}  :=

  λ h :  {t : ℝ | t ^ 2 - 5 * t + 4 = 0} = {4}  ↦

    have h1 : 1 ∈ {t : ℝ | t ^ 2 - 5 * t + 4 = 0} :=   (by norm_num : (1^2-5*1+4 = (0:ℝ)))
    have h4  : 1 ∈ {4}                            := h ▸ h1

    absurd h4 (by norm_num)



-- Exercice 3.6
example :  {t : ℝ  | t≥0 ∧  t ^ 2 - 3 * t - 4 = 0} = {4}  :=
  Set.ext
  (
    λ t:ℝ ↦
      calc
        t≥0 ∧  (t^2 - 3*t - 4 = 0) ↔ t≥0 ∧  ( (t-4)*(t-(-1)) = 0 ) := by ring_nf
        _                          ↔ t≥0 ∧  (t=4 ∨ t=-1)           := Iff.and Iff.rfl eq_or_eq_iff_mul_eq_zero
        _                          ↔ t=4                           := Iff.intro    -- ça c'est compact mais dur à lire, voir ci-après pour une version plus lisible
                                                                        (λ h ↦ Or.elim h.right id (λ ht ↦  absurd (trans ht.symm h.left) (by norm_num)) )
                                                                        (λht4 ↦  And.intro (trans ht4 (by norm_num)) (Or.inl ht4) )

  )


-- version plus lisible :

example :  {t : ℝ  | t≥0 ∧  t ^ 2 - 3 * t - 4 = 0} = {4}  :=
  Set.ext
  (
    λ t:ℝ ↦
      calc
        t≥0 ∧  (t^2 - 3*t - 4 = 0) ↔ t≥0 ∧  ( (t-4)*(t-(-1)) = 0 ) := by ring_nf
        _                          ↔ t≥0 ∧  (t=4 ∨ t=-1)           := Iff.and (Iff.rfl: t≥0  ↔ t≥0 ) (eq_or_eq_iff_mul_eq_zero :  (t-4)*(t-(-1)) = 0  ↔ (t=4 ∨ t=-1))
        _                          ↔ t=4                           :=
            Iff.intro
            (
              λ h : t≥0 ∧  (t=4 ∨ t=-1) ↦
                Or.elim (h.right : t=4 ∨ t=-1)
                  (
                    λ ht4 : t=4 ↦
                        (ht4 : t=4)
                  )
                  (
                    λ htm1 : t=-1 ↦
                      absurd (
                        calc
                          -1 = t := htm1.symm
                          _  ≥ 0 := h.left

                      ) (by norm_num)
                  )
            )
            (
              λht4 : t=4  ↦
                And.intro
                  (
                     calc
                       t = 4 := ht4
                       _ ≥ 0 := by norm_num
                  )
                  (
                    Or.inl ht4  : (t=4) ∨ (t=-1)
                  )
            )

  )





------------------------------------------------------------------
--- Exemple 4
------------------------------------------------------------------

-- Nouvelles notions
--   Complémentaire d'un ensemble   (ensemble)


def complementaire_esisar (E : Type) (A : Set E) : Set E := {a:E | a ∉ A}

-- def Set.compl (s : Set α) : Set α := {a | a ∉ s}
#print Set.compl
-- (Set.compl s)  se note aussi sᶜ
-- Le symbole   ᶜ  s'obtient en tapant \compl

-- Exercice 4.1
-- En utilisant :
example (a b : ℝ ): ¬ (a ≤ b) ↔ (a>b) := not_le

-- Montrez que :
example : ∀ a : ℝ, Set.compl { x:ℝ | x ≤ a} = { x:ℝ | x > a} :=
 λ a: ℝ ↦
   Set.ext
     λ x:ℝ ↦
       Iff.intro
         (
           λ h: ¬ (x ≤ a) ↦
            not_le.mp h
         )
         (
           λ h: x>a ↦
            not_le.mpr h
         )


-- Exercice 4.2
example : ∀ E:Type, ∀ A : Set E,(Aᶜ)ᶜ = A :=
  λ  E:Type ↦
    λ  A : Set E ↦
     Set.ext
       λ x:E ↦
         Iff.intro
           (
            λ h : x ∈ (Aᶜ)ᶜ ↦
              not_not.mp h
           )
           (
            λ h : x ∈ A ↦
              not_not.mpr h
           )

-- ou, plus court :

lemma compl_compl_esisar : ∀ E:Type, ∀ A : Set E,(Aᶜ)ᶜ = A :=   -- on le nomme au cas où ça resserve plus tard
  λ  E:Type ↦
    λ  A : Set E ↦
     Set.ext
       λ x:E ↦
         not_not


-- ∅  (tapez \ empty) dénote l'ensemble vide   et Set.univ l'ensemble de tous les éléments d'un type
example : ∀ E:Type, (∅ : Set E)ᶜ        = (Set.univ : Set E) :=
  λ  E:Type ↦
     Set.ext
       λ x:E ↦
         Iff.intro
           (
            λ h : x ∈ ∅ᶜ ↦
              trivial     -- x ∈ Set.univ est synonyme de True et 'trivial' est une preuve de True
           )
           (
            λ h : x ∈ Set.univ ↦
              (λ h' : x∈ ∅ ↦ h' )   -- montrer (x ∈ ∅ᶜ) revient à montrer (¬ (x∈∅)) c'est à dire supposer (x∈∅) (False) et prouver False...
           )


example : ∀ E:Type, (Set.univ : Set E)ᶜ = (∅ : Set E) :=
  λ  E:Type ↦
     Set.ext
       λ x:E ↦
         Iff.intro
           (
            λ h : x ∈ (Set.univ)ᶜ ↦
              h trivial     -- on veut prouver (x∈∅) c'est à dire False mais on dispose d'une preuve h de True → False ...
           )
           (
            λ h : x ∈ ∅ ↦
              (False.elim h : x ∈ (Set.univ)ᶜ)   -- h est une preuve de False : on peut tout prouver avec ! (élimination du False)
           )




example : ∀ E:Type, ∀ A B : Set E, A ⊆ B ↔ (Bᶜ ⊆ Aᶜ)  :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      Iff.intro
        (
          λ h : A ⊆ B  ↦
            λ x:E ↦
              λ hxBc : x ∈ Bᶜ  ↦
               λ hxA : x ∈ A ↦
                 absurd ( (h hxA) : x∈B ) hxBc
        )
        (
          λ h : Bᶜ ⊆ Aᶜ  ↦
            λ x:E ↦
              λ hxA : x ∈ A  ↦
               not_not.mp
               (
                 λ hxBc : x ∉ B ↦
                   absurd (hxA : x ∈ A )   ( (h hxBc) : x ∉ A)
               )
        )


-- ou en deux temps en prouvant d'abord une implication comme un lemme puis en le réutilisant ensuite:

lemma subset_impl_compl_subset : ∀ E:Type, ∀ A B : Set E, A ⊆ B →  (Bᶜ ⊆ Aᶜ)  :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      λ h : A ⊆ B  ↦
        λ x:E ↦
          λ hxBc : x ∈ Bᶜ  ↦
            λ hxA : x ∈ A ↦
              absurd ( (h hxA) : x∈B ) hxBc


example : ∀ E:Type, ∀ A B : Set E, A ⊆ B ↔ (Bᶜ ⊆ Aᶜ)  :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      Iff.intro
        (
          subset_impl_compl_subset E A B
        )
        (
          λ h : Bᶜ ⊆ Aᶜ ↦
            calc
              A = Aᶜ ᶜ := (compl_compl_esisar E A).symm
              _ ⊆ Bᶜ ᶜ := subset_impl_compl_subset E  (Bᶜ)  (Aᶜ)  h
              _ = B    := compl_compl_esisar E B
        )



-- Exercice 4.3

-- 4.x (a) un résultat préliminaire utile :
--def impair   (n:ℤ) : Prop := ∃ k:ℤ, n=2*k+1
def pair   (n:ℤ) : Prop := ∃ k:ℤ, n=2*k
lemma int_not_odd_even : ∀ n:ℤ, ¬ (pair n ∧ impair n) :=
  λ n:ℤ ↦
    λ h :  (pair n ∧ impair n) ↦
      Exists.elim h.left
      (
        λ (j:ℤ) (hj : n=2*j) ↦
          (
            Exists.elim h.right
            (
              λ (k:ℤ) (hk : n=2*k+1) ↦
                have h_zero_eq : 0 = 2*(k-j) +1 :=
                  calc
                    0 = n-n            := by ring_nf
                    _ = (2*k+1)-n      := by rw[hk]
                    _ = (2*k+1)-(2*j)  := by rw[hj]
                    _ = 2*(k-j) +1     := by ring_nf

                Or.elim (le_or_lt (k-j) (-1))
                (
                  λ hkmj1 : (k-j ≤ -1 ) ↦
                    absurd
                      (
                        calc
                          0 = 2*(k-j) +1     := h_zero_eq
                          _ ≤ 2*(-1) + 1     := by rel[hkmj1]
                      )
                      (by norm_num)
                )
                (
                  λ hkmj0 : (k-j ≥ 0 ) ↦
                    absurd
                      (
                        calc
                          0 = 2*(k-j) +1     := h_zero_eq
                          _ ≥ 2*0  + 1     := by rel[hkmj0]
                      )
                      (by norm_num)
                )
            )

          )
      )


def pairN   (n:ℕ) : Prop := (∃ k:ℕ, n = 2*k )
def impairN (n:ℕ) : Prop := (∃ k:ℕ, n = 2*k + 1 )

-- 4.x (b)
--A l'aide de l'exercice 11.3 de 12_tuto.lean ...
lemma int_odd_or_evenN  : ∀ n:ℕ, (pairN n) ∨ (impairN n) :=
  Nat.rec
  (
    Or.inl (Exists.intro 0 (by norm_num): ((pairN 0)))
  )
  (
    λ k:ℕ  ↦
      λ ih : pairN k ∨ impairN k ↦
        Or.elim ih
        (
          λ hkpair : pairN k ↦
            Exists.elim hkpair
            (
              λ (a:ℕ) (hk : k = 2*a) ↦
                have hk1impair : impairN (k+1) :=
                  Exists.intro a
                  (
                    calc
                      k+1 = 2*a+1 := by rw[hk]
                  )
                Or.inr hk1impair
            )
        )
        (
          λ hkimpair : impairN k ↦
            Exists.elim hkimpair
            (
              λ (a:ℕ) (hk : k = 2*a+1) ↦
                have hk1pair : pairN (k+1) :=
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



-- difficile, et peu naturel, parce qu'avec Lean il faut 'jongler' entre ℤ et ℕ
lemma int_odd_or_even : ∀ n:ℤ, pair n ∨ impair n :=
 λ n:ℤ ↦
   let a := Int.natAbs n
   Or.elim (Int.natAbs_eq n)
   (
     λ hnnonneg : n = a ↦
       Or.elim (int_odd_or_evenN a)
       (
         λ he : pairN a ↦
          Exists.elim he
          (
             λ (k:ℕ) (hk : a = 2*k) ↦
             Or.inl
             (
                Exists.intro (↑k)
                (
                  calc
                    n = a        := hnnonneg
                    _ = ↑ (2*k)  := by rw[hk]
                    _ = 2*(↑k)   := by simp
                )
              )
          )
       )
       (
         λ ho : impairN a ↦
          Exists.elim ho
          (
             λ (k:ℕ) (hk : a = 2*k + 1) ↦
             Or.inr
             (
                Exists.intro (↑k)
                (
                  calc
                    n = a          := hnnonneg
                    _ = ↑ (2*k+1)  := by rw[hk]
                    _ = 2*(↑k) + 1 := by simp
                )
              )
          )
       )
   )
   (
     λ hnneg : n = -a ↦
       Or.elim (int_odd_or_evenN a)
       (
         λ he : pairN a ↦
          Exists.elim he
          (
             λ (k:ℕ) (hk : a = 2*k) ↦
             Or.inl
             (
                Exists.intro (-↑k)
                (
                  calc
                    n = -a          := hnneg
                    _ = - ↑ (2*k)   := by rw[hk]
                    _ = 2*(-↑k)     := by simp
                )
              )
          )
       )
       (
         λ ho : impairN a ↦
          Exists.elim ho
          (
             λ (k:ℕ) (hk : a = 2*k + 1) ↦
             Or.inr
             (
                Exists.intro (-(↑k+1))
                (
                  calc
                    n = -a                := hnneg
                    _ = -↑ (2*k+1)        := by rw[hk]
                    _ = - (2*(↑k) +1)     := by simp
                    _ = 2*(-((↑k)+1)) + 1 := by ring_nf
                )
              )
          )
       )
   )



-- ... en déduire que :
example : Set.compl {n:ℤ | pair n} = {n:ℤ | impair n} :=
  Set.ext
    λ n:ℤ ↦
      Iff.intro
      (
        λ h : ¬ (pair n) ↦
         Or.elim (int_odd_or_even n)
         (
           λ hnpair: pair n ↦
             absurd hnpair h
         )
         (
           λ hnimpair: impair n ↦
             hnimpair
         )
      )
      (
        λ h : impair n ↦
          λ hnpair : pair n ↦
            absurd (And.intro hnpair h)  (int_not_odd_even n)
      )

-- ( vous pouvez admettre les deux lemmes précédents...)






------------------------------------------------------------------
--- Exemple 5
------------------------------------------------------------------

-- Nouvelles notions
--   Réunion de deux ensembles   (ensemble)
--   propriétés : commutativité, associativité

 -- si A et B sont deux ensembles d'éléments de type E, l'ensemble  "réunion de A et B "
--  est définie dans la bibliothèque Mathlib de la façon suivante :
def union_esisar (E : Type)  (A:Set E) (B:Set E) : Set E := {a:E  | a ∈ A ∨ a ∈ B}

#print Set.union
-- (Set.union s₁ s₂)  se note aussi s₁ ∪ s₂
--  Le symbole   ∪   s'obtient en tapant \union  ou  \cup


-- Exercice 5.1
example : ∀ t : ℝ, t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1}  :=
  λ t:ℝ ↦
    Or.elim (lt_or_le t 1)
    (
      λ h : t < 1 ↦
        Or.inr h
    )
    (
      λ h : t ≥ 1 ↦
        have h' : t > -1 :=
          calc
            t ≥ 1  := h
            _ > -1 := by norm_num
        Or.inl h'
    )


-- Exercice 5.2
example : { x:ℝ| x < 1 } ∪ { x:ℝ| x ≥ 0 } = Set.univ :=
  Set.ext
    λ x:ℝ ↦
      Iff.intro
      (
        λ h : x ∈ { x:ℝ| x < 1 } ∪ { x:ℝ| x ≥ 0 } ↦
          (trivial : (x ∈ Set.univ) )
      )
      (
        λ h : True ↦
          Or.elim (lt_or_le x 1)
          (
            λ h : x < 1 ↦
              Or.inl h
          )
          (
            λ h : x ≥ 1 ↦
              have h' : x ≥ 0 :=
                calc
                  x ≥ 1  := h
                  _ ≥ 0  := by norm_num
              Or.inr h'
          )
      )


-- Exercice 5.3
example : ∀ E:Type, ∀ A B : Set E, A ∪ B = B ∪ A :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      Set.ext
        λ x: E ↦
          Iff.intro
          (
            λ h: x ∈ A ∪ B ↦
              Or.elim h
              (
                λ hxA : x∈ A ↦
                  (Or.inr hxA : x ∈ B ∪ A  )
              )
              (
                λ hxB : x∈ B ↦
                  (Or.inl hxB : x ∈ B ∪ A  )
              )
          )
          (
            λ h: x ∈ B ∪ A ↦
              Or.elim h
              (
                λ hxB : x∈ B ↦
                  (Or.inr hxB : x ∈ A ∪ B  )
              )
              (
                λ hxA : x∈ A ↦
                  (Or.inl hxA : x ∈ A ∪ B  )
              )
          )


-- Autre solution : montrer un lemme affirmant l'une des inclusion et l'utiliser deux fois
lemma une_inclusion : ∀ E:Type, ∀ A B : Set E, A ∪ B ⊆  B ∪ A :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      λ x: E ↦
      (
        λ h: x ∈ A ∪ B ↦
          Or.elim h
          (
            λ hxA : x∈ A ↦
              (Or.inr hxA : x ∈ B ∪ A  )
          )
          (
            λ hxB : x∈ B ↦
              (Or.inl hxB : x ∈ B ∪ A  )
          )
      )

example : ∀ E:Type, ∀ A B : Set E, A ∪ B = B ∪ A :=
  λ  E:Type ↦
    λ  A B : Set E ↦
      (set_eq_iff_esisar E (A ∪ B) (B ∪ A)).mpr
      (
        And.intro
          (une_inclusion E A B)
          (une_inclusion E B A)
      )



-- Exercice 5.4
example : ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
  λ  E:Type ↦
    λ A B C: Set E ↦
      Set.ext
        λ x:E ↦
          Iff.intro
          (
            λ h : x ∈ (A ∪ B) ∪ C ↦
              Or.elim h
              (
                λ hAB : x ∈ A ∪ B ↦
                  Or.elim hAB
                  (
                    λ hA : x ∈ A ↦
                      Or.inl hA
                  )
                  (
                    λ hB : x ∈ B ↦
                      Or.inr (Or.inl hB)
                  )
              )
              (
                λ hC : x ∈ C ↦
                  Or.inr (Or.inr hC)
              )
          )
          (
            λ h : x ∈ A ∪ (B ∪ C) ↦
              Or.elim h
              (
                λ hA : x ∈ A ↦
                  Or.inl (Or.inl hA)
              )
              (
                λ hBC : x ∈ B ∪ C ↦
                  Or.elim hBC
                  (
                    λ hB : x ∈ B ↦
                      Or.inl (Or.inr hB)
                  )
                  (
                    λ hC : x ∈ C ↦
                      Or.inr hC
                  )
              )
          )


-- Exercice 5.5
example : ∀ E:Type, ∀ A B : Set E,  B ⊆ A ↔ (A ∪ B  = A) :=
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


------------------------------------------------------------------
--- Exemple 6
------------------------------------------------------------------

-- Nouvelles notions
--   Intersection de deux ensembles   (ensemble)
--   propriétés : commutativité, associativité
--   propriétés : distributivités de ∩ / ∪ et de ∪ / ∪
--   propriétés : lois de De Morgan

-- si A et B sont deux ensembles d'éléments de type E, l'ensemble  "intersection de A et B"
--  est définie dans la bibliothèque Mathlib de la façon suivante :
def inter_esisar (E : Type)  (A:Set E) (B:Set E) : Set E := {a:E  | a ∈ A ∧ a ∈ B}

#print Set.inter
-- (Set.inter s₁ s₂)  se note aussi s₁ ∩ s₂
--  Le symbole   ∩   s'obtient en tapant \inter  ou  \cap


-- Exercice 6.1
example : { x:ℝ| x > 1 } ∩ { x:ℝ| x ≤ 0 } = ∅ :=
  Set.ext
    λ x: ℝ ↦
      Iff.intro
      (
        λ h: x >1 ∧ x ≤ 0 ↦
          absurd
            (
              calc
                1 < x := h.left
                _ ≤ 0 := h.right
            )
            (by norm_num)
      )
      (
        λ h: x ∈ ∅  ↦
          False.elim h
      )


-- Autre écriture : comme le vide est inclus dans tout ensemble, une seule inclusion est en fait à prouver:

example (E:Type) (A: Set E) (h : A ⊆ ∅ ) : A = ∅  := Set.eq_empty_of_subset_empty h

example : { x:ℝ| x > 1 } ∩ { x:ℝ| x ≤ 0 } = ∅ :=
  Set.eq_empty_of_subset_empty
    λ x: ℝ ↦
      λ h: x >1 ∧ x ≤ 0 ↦
        absurd
          (
            calc
              1 < x := h.left
              _ ≤ 0 := h.right
          )
          (by norm_num)


-- Exercice 6.2
example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} :=
  λ x : ℚ ↦
    λ h: (x=-2 ∨  x=3) ∧ (x^2 = 9) ↦
      Or.elim h.left
        (
          λ hxm2 : x = -2 ↦
            absurd
              (
                calc
                  (-2)^2 = x^2 := by rw[hxm2]
                  _      = 9   := h.right
              )
              (by norm_num)
        )
        (
          λ hx3 : x = 3 ↦
            calc
              0 < 3 := by norm_num
              _ = x := hx3.symm  -- by rw[hx3]
        )


-- Exercice 6.3
lemma inter_comm : ∀ E:Type, ∀ A B : Set E, A ∩ B = B ∩ A :=
  λ  E:Type ↦
    λ A B : Set E ↦
      Set.ext
        λ x:E ↦
          Iff.intro
          (
            λ h : x ∈ A ∩ B ↦
              And.intro h.right h.left
          )
          (
            λ h : x ∈ B ∩ A ↦
              And.intro h.right h.left
          )

-- Exercice 6.4
example : ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∩ C = A ∩ (B ∩ C) :=
  λ  E:Type ↦
    λ A B C: Set E ↦
      Set.ext
        λ x:E ↦
          Iff.intro
          (
            λ h :  x ∈ A ∩ B ∩ C ↦
              And.intro
                (h.left.left : x ∈ A )
                (And.intro  (h.left.right : x ∈ B) (h.right : x ∈ C))
          )
          (
            λ h : x ∈ A ∩ (B ∩ C)↦
              And.intro
                (And.intro  (h.left : x ∈ A) (h.right.left : x ∈ B))
                (h.right.right : x ∈ C )
          )

-- Exercice 6.5
lemma distrib_union : ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) :=
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

-- Exercice 6.6
lemma distrib_inter : ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) :=
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


-- Exercice 6.7
--lemma de_morgan1 : ∀ E:Type, ∀ A B : Set E, Set.compl (A ∪ B) = (Set.compl A) ∩ (Set.compl B) :=
lemma de_morgan1 : ∀ E:Type, ∀ A B : Set E,  (A ∪ B)ᶜ = (Aᶜ) ∩ (Bᶜ) :=
  λ  E:Type ↦
    λ A B : Set E ↦
      Set.ext
        λ x:E ↦
          Iff.intro
          (
            λ h : x ∈ (A ∪ B)ᶜ  ↦
              And.intro
                (
                  λ hA : x∈ A ↦
                    absurd (Or.inl hA : x ∈ A ∪ B) (h : x ∉ A ∪ B )
                )
                (
                  λ hB : x∈ B ↦
                    absurd (Or.inr hB : x ∈ A ∪ B) (h : x ∉ A ∪ B )
                )
          )
          (
            λ h : x ∈ Aᶜ ∩ Bᶜ  ↦
              λ hAB : x ∈ A ∪ B ↦
                Or.elim hAB
                (
                  λ hA : x∈ A ↦
                    absurd hA (h.left : x ∉ A)
                )
                (
                  λ hB : x∈ B ↦
                    absurd hB (h.right : x ∉ B)
                )
          )


-- Exercice 6.8
--lemma de_morgan2 : ∀ E:Type, ∀ A B : Set E, Set.compl (A ∩ B) = (Set.compl A) ∪ (Set.compl B) :=
lemma de_morgan2 : ∀ E:Type, ∀ A B : Set E, (A ∩ B)ᶜ = (Aᶜ) ∪ (Bᶜ) :=
  λ  E:Type ↦
    λ A B : Set E ↦
      Set.ext
        λ x:E ↦
          Iff.intro
          (
            λ h : x ∈ (A ∩ B)ᶜ ↦
              Or.elim (Classical.em (x∈A))
              (
                λ hA : x∈ A ↦

                  have hnB : x ∉ B :=
                    λ hB : x ∈ B ↦
                      absurd (And.intro hA hB : x ∈ A ∩ B) h

                  (Or.inr hnB : x ∈ Aᶜ ∪ Bᶜ)
              )
              (
                λ hnA : x ∉ A ↦
                  (Or.inl hnA : x ∈ Aᶜ ∪ Bᶜ)
              )
          )
          (
            λ h : x ∈ Aᶜ ∪ Bᶜ  ↦
              Or.elim h
              (
                λ hnA : x∉A ↦
                  λ hAB : x∈ A ∩ B ↦
                    absurd (hAB.left : x∈ A) (hnA : x∉A)
              )
              (
                λ hnB : x∉B ↦
                  λ hAB : x∈ A ∩ B ↦
                    absurd (hAB.right : x∈ B) (hnB : x∉B)
              )
          )




-- Exercice 6.9
example : ∀ E:Type, ∀ A B : Set E,  A ⊆ B ↔ (A ∩ B = A) :=
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


-- Exercice 6.10
example : ∀ E:Type, ∀ A B : Set E,  A ∪ B  = A ∩ B →  A = B :=
  λ  E:Type ↦
    λ A B : Set E ↦
      λ h : A ∪ B  = A ∩ B ↦
        Set.ext
          λ x:E ↦
            Iff.intro
            (
              λ hA: x ∈ A ↦
                have hAB : x ∈ A ∩ B :=
                  calc
                    x ∈ A ∪ B := Or.inl hA
                    _ = A ∩ B := by rw[h]
                (hAB.right : x ∈ B)
            )
            (
              λ hB: x ∈ B ↦
                have hAB : x ∈ A ∩ B :=
                  calc
                    x ∈ A ∪ B := Or.inr hB
                    _ = A ∩ B := by rw[h]
                (hAB.left : x ∈ A)
            )


-- Exercice 6.11
example : ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C :=
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



-- Exercice 6.12

example : ∀ E:Type, ∀ A B C : Set E,  (A ∩ Bᶜ  =  A ∩ Cᶜ ) ↔  (A ∩ B  =  A ∩ C)  :=
  λ  E:Type ↦
    λ A B C : Set E ↦
      Iff.intro
      (
        λ h : (A ∩ Bᶜ  =  A ∩ Cᶜ) ↦
          Set.ext
            λ x:E ↦
              Iff.intro
              (
                λ hAB : x ∈ A ∩ B ↦
                  have hnnC : ¬ (x ∈ Cᶜ) :=
                    λ hnC : x ∈ Cᶜ ↦
                      have hAnB : x  ∈ A ∩ Bᶜ :=
                        calc
                          x ∈ A ∩ Cᶜ := And.intro hAB.left hnC
                          _ = A ∩ Bᶜ := h.symm
                      absurd (hAB.right : x ∈ B) (hAnB.right : x ∉ B)

                  And.intro (hAB.left: x ∈ A) (not_not.mp hnnC : x ∈ C)
              )
              (
                λ hAC : x∈ A ∩ C ↦
                  have hnnB : ¬ (x ∈ Bᶜ) :=
                    λ hnB : x ∈ Bᶜ ↦
                      have hAnC : x  ∈ A ∩ Cᶜ :=
                        calc
                          x ∈ A ∩ Bᶜ := And.intro hAC.left hnB
                          _ = A ∩ Cᶜ := h
                      absurd (hAC.right : x ∈ C) (hAnC.right : x ∉ C)

                  And.intro (hAC.left: x ∈ A) (not_not.mp hnnB : x ∈ B)
              )
      )
      (
        λ h : (A ∩ B  =  A ∩ C) ↦
          Set.ext
          λ x:E ↦
            Iff.intro
            (
              λ hAnB : x ∈ A ∩ Bᶜ ↦
                And.intro
                  (hAnB.left : x ∈ A)
                  (
                    λ hC : x ∈ C ↦
                      have hAB : x ∈ A ∩ B :=
                        calc
                          x ∈ A ∩ C :=  And.intro (hAnB.left : x ∈ A) hC
                          _ = A ∩ B := h.symm

                      absurd (hAB.right : x ∈ B) (hAnB.right : x ∉ B)
                  )
            )
            (
              λ hAnC : x ∈ A ∩ Cᶜ ↦
                And.intro
                  (hAnC.left : x ∈ A)
                  (
                    λ hB : x ∈ B ↦
                      have hAC : x ∈ A ∩ C :=
                        calc
                          x ∈ A ∩ B :=  And.intro (hAnC.left : x ∈ A) hB
                          _ = A ∩ C := h

                      absurd (hAC.right : x ∈ C) (hAnC.right : x ∉ C)
                  )
            )

      )


--Pour éviter les redondances on peut prouver un petit lemme et l'utiliser plusieurs fois :


lemma inter_compl_subset_of_inter_subset : ∀ E:Type, ∀ A B C : Set E,    (A ∩ B  ⊆   A ∩ C)  → (  A ∩ Cᶜ ⊆ A ∩ Bᶜ )  :=
  λ  E:Type ↦
    λ A B C : Set E ↦
        λ h : (A ∩ B  ⊆  A ∩ C) ↦
          λ x:E ↦
            λ hAnC : x ∈ A ∩ Cᶜ ↦
              And.intro
                (hAnC.left : x ∈ A)
                (
                  λ hB : x ∈ B ↦
                    have hAC : x ∈ A ∩ C :=   h (And.intro (hAnC.left : x ∈ A) hB)   --- (*)

                    absurd (hAC.right : x ∈ C) (hAnC.right : x ∉ C)
                )




--- (*) a cet endroit on peut donner une preuve avec  calc,  à condition  de définir l'instance ci-dessus permettant à calc de fonctionner avec ∈  et  ⊆

instance instTransMemSubset {E:Type} : Trans (λ (x:E)  (A:Set E) ↦ x ∈ A ) (λ (A:Set E) (B:Set E) ↦ A ⊆ B)  (λ (x:E)  (B:Set E) ↦ x ∈ B ) :=
  {
    trans := λ {x:E} {A:Set E} {B:Set E} (hxA : x∈ A) (hAB : A⊆ B ) ↦  (hAB hxA : x∈ B )
  }

lemma inter_compl_subset_of_inter_subset' : ∀ E:Type, ∀ A B C : Set E,    (A ∩ B  ⊆   A ∩ C)  → (  A ∩ Cᶜ ⊆ A ∩ Bᶜ )  :=
  λ  E:Type ↦
    λ A B C : Set E ↦
        λ h : (A ∩ B  ⊆  A ∩ C) ↦
          λ x:E ↦
            λ hAnC : x ∈ A ∩ Cᶜ ↦
              And.intro
                (hAnC.left : x ∈ A)
                (
                  λ hB : x ∈ B ↦
                    have hAC : x ∈ A ∩ C := --   h (And.intro (hAnC.left : x ∈ A) hB)
                      calc
                        x ∈ A ∩ B :=  And.intro (hAnC.left : x ∈ A) hB
                        _ ⊆ A ∩ C := h


                    absurd (hAC.right : x ∈ C) (hAnC.right : x ∉ C)
                )

-- et finalement une solution à l'exercice en utilisant le lemme :
example : ∀ E:Type, ∀ A B C : Set E,  (A ∩ Bᶜ  =  A ∩ Cᶜ ) ↔  (A ∩ B  =  A ∩ C)  :=
  λ  E:Type ↦
    λ A B C : Set E ↦
      Iff.intro
      (
        λ h : (A ∩ Bᶜ  =  A ∩ Cᶜ) ↦
          have h' : (A ∩ Bᶜ  ⊆  A ∩ Cᶜ) ∧ (A ∩ Cᶜ  ⊆   A ∩ Bᶜ) := (set_eq_iff_esisar E (A ∩ Bᶜ) (A ∩ Cᶜ)).mp h

          (set_eq_iff_esisar E (A ∩ B) (A ∩ C)).mpr
          (
            And.intro
            (
              calc
                A ∩ B = A ∩ Bᶜᶜ :=  by rw[compl_compl_esisar E B]
                _     ⊆ A ∩ Cᶜᶜ :=  inter_compl_subset_of_inter_subset E A Cᶜ Bᶜ h'.right
                _     = A ∩ C   :=  by rw[compl_compl_esisar E C]

            )
            (
              calc
                A ∩ C = A ∩ Cᶜᶜ :=  by rw[compl_compl_esisar E C]
                _     ⊆ A ∩ Bᶜᶜ :=  inter_compl_subset_of_inter_subset E A Bᶜ Cᶜ h'.left
                _     = A ∩ B   :=  by rw[compl_compl_esisar E B]

            )
          )
      )
      (
        λ h : (A ∩ B  =  A ∩ C) ↦
          have h' : (A ∩ B  ⊆  A ∩ C) ∧ (A ∩ C  ⊆   A ∩ B) := (set_eq_iff_esisar E (A ∩ B) (A ∩ C)).mp h

          (set_eq_iff_esisar E (A ∩ Bᶜ) (A ∩ Cᶜ)).mpr
          (
            And.intro
            (
              inter_compl_subset_of_inter_subset E A C B h'.right
            )
            (
              inter_compl_subset_of_inter_subset E A B C h'.left
            )
          )

      )





------------------------------------------------------------------
--- Exemple 7
------------------------------------------------------------------

-- Nouvelles notions
--    Ensemble privé d'un autre

-- si A et B sont deux ensembles d'éléments de type E, l'ensemble  "A privé de B"
--  est définie dans la bibliothèque Mathlib de la façon suivante :
def diff_esisar (E : Type)  (A:Set E) (B:Set E) : Set E := {a:E  | a ∈ A ∧ a ∉ B}

#print Set.diff
-- (Set.diff s₁ s₂)  se note aussi s₁ \ s₂
--  Le symbole   \    s'obtient en tapant \  suivi d'un espace

-- Exercice 7.1
example : { x:ℝ| x < 1 } \  { x:ℝ| x ≥  0 } = { x:ℝ| x < 0 }  :=
  Set.ext
    λ x:ℝ ↦
      Iff.intro
      (
        λ h : x <1 ∧ ¬(x ≥0 ) ↦
          (lt_of_not_ge h.right : x < 0)
      )
      (
        λ h : x < 0 ↦
          And.intro
          (
            calc
              x < 0  := h
              _ < 1  := by norm_num
          )
          (not_le_of_lt h)
      )

-- Exercice 7.2
-- on pourrait faire la preuve avec les elements (Set.ext λ x:E ↦ ... ) comme pour les preuves precedentes
-- on choisit ici de donner une preuve reutilisant les resultats prouves precedemment
example : ∀ E:Type, ∀ A B C: Set E,  A \ (B ∩ C) = (A \ B) ∪  (A \ C)  :=
  λ  E:Type ↦
    λ A B C : Set E ↦
      calc
        A \ (B ∩ C) = A ∩ ((B ∩ C)ᶜ )       := rfl
        _           = A ∩ (Bᶜ∪Cᶜ )          := by rw [de_morgan2 E B C] -- congr_arg _ (de_morgan2 E B C)
        _           = (Bᶜ∪Cᶜ ) ∩ A          := inter_comm E A (Bᶜ∪Cᶜ )
        _           = ( Bᶜ ∩ A )∪ (Cᶜ ∩ A ) := distrib_inter E  Bᶜ Cᶜ  A
        _           = (A ∩ Bᶜ)∪ (A ∩ Cᶜ )   := by rw[inter_comm E A Bᶜ, inter_comm E A Cᶜ]






-------------------------------------------------------------------------------
--------Cuisine interne pour accepter la notation E \ A où E est un type ------
-------------------------------------------------------------------------------

    /-- Notation type class for the set difference `\`. -/
    class HDiff  where
      /--
      `a \ b` is the set difference of `a` and `b`,
      consisting of all elements in `a` that are not in `b`.
      -/
      hdiff : (E:Type) → (A: Set E) → Set E
    /--
    `a \ b` is the set difference of `a` and `b`,
    consisting of all elements in `a` that are not in `b`.
    -/
    infix:70 " \\ " => HDiff.hdiff

    instance : HDiff := ⟨ (λ _ A ↦ (Set.univ ) \ A)  ⟩


    --instance : CoeDep Type : _ := λ E:Type → @Set.univ E

    #check ℝ \ {0}

----------------------------------------------------------------------------------







------------------------------------------------------------------
--- Exemple 8
------------------------------------------------------------------

-- Nouvelles notions
--   Ensemble des parties

-- Si E est un type: les ensembles d'éléments de type E ont eux même un type, noté (Set E)
-- Par exemple    {n:ℕ | 6 < n+1 }   est de type  (Set ℕ)
#check  {n:ℕ | 6 < n+1 }

-- On peut donc considérer des ensembles d'éléments de type (Set E) ... qui seront de type Set (Set E)
-- Par exemple {A: Set ℕ | 3 ∈ A}  est l'ensemble des sous-ensembles de ℕ contenant 3
#check {A: Set ℕ | 3 ∈ A}

-- Exercice 8.1
example :  {2,3,4} ∈  {A: Set ℕ | 3 ∈ A} :=  -- il s'agit ici de prouver que 3 ∈ {2,3,4}
  Or.inr (Or.inl (rfl : 3=3))

-- Exercice 8.2
example : {n:ℤ | pair n} ∉ {A: Set ℤ | 3 ∈ A} :=
  λ h : 3 ∈ {n:ℤ | pair n}  ↦
    Exists.elim h
    (
      λ (k:ℤ) (hk : 3=2*k) ↦
        Or.elim (le_or_lt k 1)
        (
          λ hk1 : k ≤ 1 ↦
            absurd
            (
              calc
                3 = 2*k := hk
                _ ≤ 2*1 := by rel[hk1]
            )
            (by norm_num)
        )
        (
          λ hk2 : k ≥ 2 ↦
            absurd
            (
              calc
                3 = 2*k := hk
                _ ≥ 2*2 := by rel[hk2]
            )
            (by norm_num)
        )
    )


-- si A est un ensemble d'éléments de type E, l'ensemble des parties de A
-- est l'ensemble d'éléments X de type (Set E) vérifiant X ⊆ A
-- il est défini par :
def powerset_esisar (E : Type)  (A:Set E) : Set (Set E) := {X: Set E  | X ⊆ A }

#print Set.powerset
-- (Set.powerset s)  se note aussi 𝒫 s
--  Le symbole  𝒫   s'obtient en tapant \powerset


-- Exercice 8.3

example (E:Type) (x:E) (h: x ∈ (∅: Set E)) : False := h

lemma Or.elim4 {p1 p2 p3 p4 R : Prop} (h: p1 ∨ (p2 ∨ p3 ∨ p4  ) ) (i1 : p1 → R )(i2 : p2 → R )(i3 : p3 → R )(i4 : p4 → R ) : R :=
  Or.elim h
  (
    λ h1 : p1 ↦
      i1 h1
  )
  (
    λ h234 : p2 ∨ p3 ∨ p4 ↦
      Or.elim3 h234 i2 i3 i4
  )

lemma Or.in1 {p1 p2 p3 p4 : Prop} (h:p1) : p1 ∨ p2 ∨ p3 ∨ p4 := Or.inl h
lemma Or.in2 {p1 p2 p3 p4 : Prop} (h:p2) : p1 ∨ p2 ∨ p3 ∨ p4 := Or.inr $ Or.inl h
lemma Or.in3 {p1 p2 p3 p4 : Prop} (h:p3) : p1 ∨ p2 ∨ p3 ∨ p4 := Or.inr $ Or.inr $ Or.inl h
lemma Or.in4 {p1 p2 p3 p4 : Prop} (h:p4) : p1 ∨ p2 ∨ p3 ∨ p4 := Or.inr $ Or.inr $ Or.inr h

def A01 : Set ℕ := {0,1}
example : 𝒫 A01 = {∅ , {0}, {1}, {0,1}} :=
  Set.ext
    λ X : Set ℕ ↦
      Iff.intro
      (
        λ h : X ∈ 𝒫 A01 ↦
          Or.elim (Classical.em (0 ∈ X))
          (
            λ h0X : 0 ∈ X ↦
              Or.elim (Classical.em (1 ∈ X))
              (
                λ h1X : 1 ∈ X ↦
                  Or.in4
                  (
                    (set_eq_iff_esisar ℕ X {0,1} ).mpr
                    (
                      And.intro
                        h
                        (
                          λ x:ℕ ↦ λ hx : x ∈ {0,1} ↦
                            Or.elim hx
                            (
                              λ hx0 : x = 0 ↦
                                hx0 ▸ h0X
                            )
                            (
                              λ hx1 : x = 1 ↦
                                hx1 ▸ h1X
                            )
                        )
                    )
                  )
              )
              (
                λ h1nX : 1 ∉ X ↦
                  Or.in2
                  ( Set.ext
                      λ x: ℕ ↦
                        Iff.intro
                        (
                          λ hx: x ∈ X ↦
                            have hx01 : x ∈ {0,1} :=
                              calc
                                x ∈ X     := hx
                                _ ⊆ {0,1} := h
                            Or.elim hx01
                            (
                              λ hx0 : x=0 ↦
                                hx0
                            )
                            (
                              λ hx1 : x=1 ↦
                                absurd (hx1 ▸ hx : 1 ∈ X )  (h1nX : 1 ∉ X)
                            )
                        )
                        (
                          λ hx : x ∈ {0} ↦
                            hx ▸ h0X
                        )
                  )
              )
          )
          (
            λ h0nX : 0 ∉ X ↦
              Or.elim (Classical.em (1 ∈ X))
              (
                λ h1X : 1 ∈ X ↦
                  Or.in3
                  (
                    Set.ext
                      λ x: ℕ ↦
                        Iff.intro
                        (
                          λ hx: x ∈ X ↦
                            have hx01 : x ∈ {0,1} :=
                              calc
                                x ∈ X     := hx
                                _ ⊆ {0,1} := h
                            Or.elim hx01
                            (
                              λ hx0 : x=0 ↦
                                absurd (hx0 ▸ hx : 0 ∈ X )  (h0nX : 0 ∉ X)
                            )
                            (
                              λ hx1 : x=1 ↦
                                hx1
                            )
                        )
                        (
                          λ hx : x ∈ {1} ↦
                            hx ▸ h1X
                        )
                  )
              )
              (
                λ h1nX : 1 ∉ X ↦
                  Or.in1
                  (
                    Set.ext
                      λ x: ℕ ↦
                        Iff.intro
                        (
                          λ hx: x ∈ X ↦
                            have hx01 : x ∈ {0,1} :=
                              calc
                                x ∈ X     := hx
                                _ ⊆ {0,1} := h
                            Or.elim hx01
                            (
                              λ hx0 : x=0 ↦
                                absurd (hx0 ▸ hx : 0 ∈ X )  (h0nX : 0 ∉ X)
                            )
                            (
                              λ hx1 : x=1 ↦
                                absurd (hx1 ▸ hx : 1 ∈ X )  (h1nX : 1 ∉ X)
                            )
                        )
                        (
                          λ hx : x ∈ ∅  ↦
                            False.elim hx
                        )
                  )
              )
          )
      )
      (
        λ h : X = ∅ ∨ X = {0} ∨ X = {1} ∨ X ={0,1}   ↦
          Or.elim4 h
            (λ hX : X = ∅     ↦  λ (x:ℕ) (hx : x∈X) ↦ have hxe  : x ∈ (∅    : Set ℕ)   := (hX ▸ hx)  ;  False.elim hxe )
            (λ hX : X = {0}   ↦  λ (x:ℕ) (hx : x∈X) ↦ have hx0  : x ∈ ({0}  : Set ℕ)   := (hX ▸ hx)  ;  Or.inl     hx0 )
            (λ hX : X = {1}   ↦  λ (x:ℕ) (hx : x∈X) ↦ have hx1  : x ∈ ({1}  : Set ℕ)   := (hX ▸ hx)  ;  Or.inr     hx1 )
            (λ hX : X = {0,1} ↦  λ (x:ℕ) (hx : x∈X) ↦ have hx01 : x ∈ ({0,1}: Set ℕ)   := (hX ▸ hx)  ;  hx01 )
      )



example : ∀ E: Type, ∀ A: Set E, ∀ B: Set E, A ⊆ B → 𝒫 A ⊆ 𝒫 B   :=
  λ  E:Type ↦
    λ A B : Set E ↦
      λ h: A ⊆ B ↦
        λ X : Set E ↦
          λ hX : X ⊆ A ↦
            λ x:E ↦
              λ hxX: x ∈ X ↦
                have hxA : x ∈  A  := hX hxX
                have hxB : x ∈  B  := h hxA
                (hxB : x ∈ B )


------------------------------------------------------------------
--- Exemple 9
------------------------------------------------------------------
-- Nouvelles notions
--   produit cartésien


-- si E et F sont deux types, E × F
--  est le type des couples (x,y) où x:E  et y:F
--  Le symbole   ×    s'obtient en tapant \times
#check ℝ × (Set ℕ)


-- Exercice 9.1

def disque (A: ℝ × ℝ) (r:ℝ)  (hr: r≥0) : Set (ℝ × ℝ) :=
  { M:ℝ×ℝ  | let (x,y):= M ; let (xA,yA):= A ;(x-xA)^2+(y-yA)^2 ≤ r^2  }


--def disque :=
--   λ ((xA,yA): ℝ × ℝ) (r:ℝ)  (hr: r≥0) ((x,y): ℝ × ℝ) ↦
--    (x-xA)^2+(y-yA)^2 ≤ r^2

def disque_unite  : Set (ℝ × ℝ) := disque (0,0) 1 (by norm_num)


-- Notons [a;b] l'ensemble {x:ℝ | x ≥ a ∧ x ≤ b }
macro " [ " a:term  " ; " b:term  " ] "  : term => do
  `({x:ℝ | x ≥ ($a) ∧ x ≤ ($b) })


-- vu dans CM43

macro " [ " a:term  " ; " b:term  " ) "  : term => do
    `({x:ℝ | x ≥ ($a) ∧ x < ($b) })

  #check [1;3)

  macro " ( " a:term  " ; " b:term  " ] "  : term => do
    `({x:ℝ | x ≥ ($a) ∧ x < ($b) })

  #check (1;3]

  macro " ( " a:term  " ; " b:term  " ) "  : term => do
    `({x:ℝ | x > ($a) ∧ x < ($b) })

  #check (1;3)


  macro " [ " a:term  ";+∞) "  : term => do
    `({x:ℝ | x ≥ ($a)  })

  #check [1;+∞)

  macro " ( " a:term  ";+∞) "  : term => do
    `({x:ℝ | x > ($a)  })

  #check (1;+∞)

  macro "(-∞; " b:term  " ] "  : term => do
    `({x:ℝ |  x < ($b) })

  #check (-∞;3]

  macro "(-∞; " b:term  " ) "  : term => do
    `({x:ℝ |  x < ($b) })

  #check (-∞;3)

  macro "(-∞;+∞)"  : term => do
    `(@Set.univ ℝ)

  #check (-∞;+∞)


-- Si A:Set E et B: Set F,  Notons A × B  :Set (E×F)
-- l'ensemble des (x,y) tels que x∈ A et y∈ B
def produit {E:Type} {F:Type} (A:Set E) (B:Set F)  :=
  {M: E × F | let (x,y):= M ; x ∈ A ∧ y ∈ B }

notation:60 lhs:61 " × " rhs:61 =>  (produit lhs rhs)


example : disque_unite ⊆ ([-1;1] × [-1;1])   := sorry

example : disque_unite ⊆ ([-1;1] × [-1;1])   :=
  λ M : ℝ × ℝ  ↦
    let (x,y) := M
    λ h : (x,y) ∈ disque_unite ↦
      And.intro sorry sorry

example : disque_unite ⊆ ([-1;1] × [-1;1])   :=
  λ ((x,y): ℝ × ℝ)   ↦
    λ h : (x,y) ∈ disque_unite ↦
      And.intro sorry sorry

example : disque_unite ⊆ ([-1;1] × [-1;1])
  | ((x,y) : ℝ × ℝ ),  (h : (x,y) ∈ disque_unite)  =>  And.intro sorry sorry



#check abs_le_of_sq_le_sq'
#check sq_nonneg

example : disque_unite ⊆ ([-1;1] × [-1;1])   :=
  λ ((x,y): ℝ × ℝ)   ↦
    λ h : (x,y) ∈ disque_unite ↦
      And.intro
        (
          abs_le_of_sq_le_sq'
            (
              calc
                x^2 = x^2 + 0           := by ring_nf
                _   ≤ x^2 + y^2         := by rel[sq_nonneg y]
                _   = (x-0)^2 + (y-0)^2 := by ring_nf
                _   ≤ 1^2               := h
            )
            (by norm_num : (1:ℝ) ≥ 0)
        )
        (
          abs_le_of_sq_le_sq'
            (
              calc
                y^2 = 0  + y^2          := by ring_nf
                _   ≤ x^2 + y^2         := by rel[sq_nonneg x]
                _   = (x-0)^2 + (y-0)^2 := by ring_nf
                _   ≤ 1^2               := h
            )
            (by norm_num : (1:ℝ) ≥ 0)
        )



-- Exercice 9.2

-- Ecrivez (ℝ × ℝ)  \ ([-1;1] × [2;3])  sous forme d'une réunion de produits cartésiens

--example :  ((@Set.univ (ℝ × ℝ)))  \ ([-1;1] × [2;3])  =  sorry := sorry

--example :  ((@Set.univ (ℝ × ℝ)))  \ ([-1;1] × [2;3]) =  ((-∞;-1)× ℝ) ∪ ([-1;1] × (-∞;2)) ∪   ([-1;1] × (3;+∞)) ∪  ((1;+∞) × ℝ)  := sorry

example (P Q : Prop) (h: ¬ (P ∧ Q)  ) : ¬P ∨ ¬Q := not_and_or.mp h


lemma left_or_center_or_right  (x a b : ℝ) : x < a ∨ (x ≥  a ∧ x ≤  b) ∨ x > b :=
  Or.elim  (lt_or_le x a ) Or.inl
  (
    λ hxa ↦
      Or.elim  (lt_or_le b x )
      (
        Or.inr  ∘  Or.inr
      )
      (
          Or.inr  ∘  Or.inl ∘  And.intro hxa
      )
  )


lemma Or.elim4' {p1 p2 p3 p4 R : Prop} (h: ((p1 ∨ p2) ∨ p3) ∨ p4   ) (i1 : p1 → R )(i2 : p2 → R )(i3 : p3 → R )(i4 : p4 → R ) : R :=
  Or.elim h
  (
      λ h123 : (p1 ∨ p2) ∨ p3 ↦
        Or.elim h123
        (
            λ h12 : (p1 ∨ p2) ↦
            Or.elim h12
            (
              λ h1 : p1 ↦
                i1 h1
            )
            (
              λ h2 : p2 ↦
                i2 h2
            )
        )
        (
          λ h3 : p3 ↦
            i3 h3
        )
  )
  (
    λ h4 : p4 ↦
      i4 h4
  )

lemma Or.in1' {p1 p2 p3 p4 : Prop} (h:p1) : ((p1 ∨ p2) ∨ p3) ∨ p4 := Or.inl $ Or.inl $ Or.inl h
lemma Or.in2' {p1 p2 p3 p4 : Prop} (h:p2) : ((p1 ∨ p2) ∨ p3) ∨ p4 := Or.inl $ Or.inl $ Or.inr h
lemma Or.in3' {p1 p2 p3 p4 : Prop} (h:p3) : ((p1 ∨ p2) ∨ p3) ∨ p4 := Or.inl $ Or.inr h
lemma Or.in4' {p1 p2 p3 p4 : Prop} (h:p4) : ((p1 ∨ p2) ∨ p3) ∨ p4 := Or.inr h


example : (ℝ × ℝ)    \ ([-1;1] × [2;3])  =  ((-∞;-1)× (@Set.univ ℝ) : Set (ℝ × ℝ) ) ∪ ([-1;1] × (-∞;2)) ∪   ([-1;1] × (3;+∞)) ∪  ((1;+∞) × (@Set.univ ℝ))  :=
  Set.ext
    λ ((x,y) : ℝ × ℝ) ↦
     Iff.intro
     (
       λ h : (x,y) ∈ (ℝ × ℝ)    \ ([-1;1] × [2;3]) ↦

         have h' : (x< -1 ∨ x > 1) ∨ (y< 2 ∨ y > 3)   :=
           Or.imp  ( (Or.imp lt_of_not_ge lt_of_not_ge) ∘ not_and_or.mp ) ( (Or.imp lt_of_not_ge lt_of_not_ge) ∘ not_and_or.mp ) (not_and_or.mp h.right)

         Or.elim h'
         (
           λ hx : x< -1 ∨ x > 1 ↦
            Or.elim hx
            (
              λ hxm1 : x < -1  ↦
                Or.in1' (And.intro hxm1 trivial)
            )
            (
              λ hx1 : x > 1 ↦
                Or.inr (And.intro hx1 trivial)
            )
         )
         (
           λ hy : y<2 ∨ y>3 ↦
            Or.elim hy
            (
              λ hy2 : y<2  ↦
                Or.elim3 (left_or_center_or_right x (-1) 1)
                (
                  λhxm1 : x < -1 ↦
                    Or.in1' (And.intro hxm1 trivial)
                )
                (
                  λhxm11 : x ∈ [-1;1]  ↦
                    Or.in2' (And.intro hxm11 hy2)
                )
                (
                  λhx1 : x > 1 ↦
                    Or.inr (And.intro hx1 trivial)
                )
            )
            (
              λ hy3 : y>3 ↦
                Or.elim3 (left_or_center_or_right x (-1) 1)
                (
                  λhxm1 : x < -1 ↦
                    Or.in1' (And.intro hxm1 trivial)
                )
                (
                  λhxm11 : x ∈ [-1;1]  ↦
                    Or.in3' (And.intro hxm11 hy3)
                )
                (
                  λhx1 : x > 1 ↦
                    Or.inr (And.intro hx1 trivial)
                )
            )
         )

     )
     (
       λ h : (x,y) ∈ ((-∞;-1)× (@Set.univ ℝ) : Set (ℝ × ℝ) ) ∪ ([-1;1] × (-∞;2)) ∪   ([-1;1] × (3;+∞)) ∪  ((1;+∞) × (@Set.univ ℝ)) ↦
         And.intro trivial
         (
           λ ha : (x,y) ∈ (([-1;1] × [2;3] ): Set ( ℝ × ℝ  )) ↦
             Or.elim4' h
             (
                λ h1 :  (x,y) ∈ ((-∞;-1)× (@Set.univ ℝ) : Set ( ℝ × ℝ  ) ) ↦
                  absurd (ha.left.left) (not_le_of_lt h1.left)
             )
             (
                λ h2 :  (x,y) ∈ ([-1;1] × (-∞;2) : Set ( ℝ × ℝ  )) ↦
                  absurd (ha.right.left) (not_le_of_lt h2.right)
             )
             (
                λ h3 :  (x,y) ∈  ([-1;1] × (3;+∞) : Set ( ℝ × ℝ  )) ↦
                  absurd (ha.right.right) (not_le_of_lt h3.right)
             )
             (
                λ h4 :  (x,y) ∈ ((1;+∞) × (@Set.univ ℝ) : Set ( ℝ × ℝ  )) ↦
                  absurd (ha.left.right) (not_le_of_lt h4.left)
             )
         )
     )




-- Exercice 9.3
-- Montrez que {(x,y)∈ℝ ×ℝ | x^2+y^2 ≤ 1 } ne peut s'écrire comme un produit cartésien

-- l'idée est de voir, par l'absurde, que dans un tel cas (0,1) et (1,0) seraient élément du disque unité et donc de E × F
-- ce qui imposerait que 1 ∈ E et 1 ∈ F et par suite (1,1) ∈ E × F = disque_unite : absurde

example : ¬ (∃ E: Set ℝ , ∃ F: Set ℝ , disque_unite = E × F) :=
  λ h : ∃ E: Set ℝ , ∃ F: Set ℝ , disque_unite = E × F ↦
    Exists.elim h
    (
      λ (E: Set ℝ) (hE :  ∃ F: Set ℝ , disque_unite = E × F) ↦
        Exists.elim hE
        (
          λ (F: Set ℝ) (hF :  disque_unite = E × F) ↦
            have h01 :  (0,1) ∈ disque_unite := (by norm_num :  ((0:ℝ )-0)^2 + (1-0)^2 ≤ 1^2 )
            have h10 :  (1,0) ∈ disque_unite := (by norm_num :  ((1:ℝ )-0)^2 + (0-0)^2 ≤ 1^2 )
            have h1F : 1 ∈ F := (hF ▸ h01).right
            have h1E : 1 ∈ E := (hF ▸ h10).left
            have h11 : (1,1) ∈ disque_unite := hF ▸  (And.intro h1E h1F : (1,1) ∈ E × F )
            absurd h11 (by norm_num  :  ¬  ((1:ℝ )-0)^2 + (1-0)^2 ≤ 1^2 )
        )
    )
