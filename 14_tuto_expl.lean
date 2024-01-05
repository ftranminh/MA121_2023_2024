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

example : 2 ∈ {x:ℚ | x*3 ≤ 7 } := sorry

-- Exercice 1.2

example : 22 ∈ {x:ℕ | ∃ k:ℕ , x = 4*k+2 } :=  sorry


-- Exercice 1.3
def B : Set ℕ := {4,6,8} 

-- définitions équivalentes
def B1 : Set ℕ := {x:ℕ | x=4 ∨ x=6 ∨ x=8 } 
def B2 : Set ℕ := {x:ℕ | x=4 ∨ (x=6 ∨ x=8) } 

example : 6 ∈ B             :=  sorry
example : 6=4 ∨ (6=6 ∨ 6=8) :=  sorry -- est le meme exercice

example : 7 ∉ B            :=  sorry
-- révisez la def de ¬ P  (12_tuto, exemple 3)
example : ¬ (7 ∈  B)       :=  sorry  
-- révisez: comment prouver P → Q ?
example : (7 ∈  B) → False :=  λ h : 7 ∈ B ↦ sorry     
 


-- Exercice 1.4
example : 8 ∉ {x:ℤ | ∃ k:ℤ, x = 3*k+1 } :=  sorry




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

-- Exercice 2.2

example :  {x:ℕ  | ∃ k:ℕ , x = 14*k } ⊆ {x:ℕ | ∃ k:ℕ , x = 2*k }  :=  sorry


-- Exercice 2.3

-- Redémontrez ce lemme de la bibliothèque :
example  : ∀ E:Type,  ∀ A:Set E, A ⊆ A  :=  λ (E:Type) (A:Set E) ↦ Eq.subset rfl

lemma subset_refl_esisar  : ∀ E:Type,  ∀ A:Set E, A ⊆ A  :=  sorry


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
example : {x : ℤ | impair x} = {a : ℤ | ∃ k, a = 2 * k - 1} := sorry


-- Exercice 3.2
-- Redémontrez ce lemme de la bibliothèque :
example (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  := Set.Subset.antisymm_iff

--vous pouvez utiliser  subset_refl_esisar  démontré à l'exercice 2.3
lemma set_eq_iff_esisar (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  := sorry



-- Exercice 3.3
example :  {x:ℤ | ∃ k:ℤ, x = 4*k } ≠ {x:ℤ | ∃ k:ℤ, x = 2*k }  := sorry


-- Exercice 3.4
example :  {t : ℝ | t ^ 2 - 5 * t + 4 = 0} = {4}  := sorry


-- Exercice 3.5

example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := sorry






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
example : ∀ a : ℝ, Set.compl { x:ℝ | x ≤ a} = { x:ℝ | x > a}ᶜ := sorry



-- Exercice 4.2
example : ∀ E:Type, ∀ A : Set E,(Aᶜ)ᶜ = A := sorry

-- ∅  (tapez \ empty) dénote l'ensemble vide   et Set.univ l'ensemble de tous les éléments d'un type
example : ∀ E:Type, (∅ : Set E)ᶜ        = (Set.univ : Set E) := sorry
example : ∀ E:Type, (Set.univ : Set E)ᶜ = (∅ : Set E) := sorry


example : ∀ E:Type, ∀ A B : Set E, A ⊆ B ↔ (Bᶜ ⊆ Aᶜ)  := sorry



-- Exercice 4.3

-- 4.x (a) un résultat préliminaire utile :
def pair   (n:ℤ) : Prop := ∃ k:ℤ, n=2*k
lemma int_not_odd_even : ∀ n:ℤ, ¬ (pair n ∧ impair n) := sorry

-- 4.x (b) 
--A l'aide de l'exercice 11.3 de 12_tuto.lean ...
lemma int_odd_or_even : ∀ n:ℤ, pair n ∨ impair n := sorry

-- ... en déduire que :
example : Set.compl {n:ℤ | pair n} = {n:ℤ | impair n} := sorry 

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
example : ∀ t : ℝ, t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1}  := sorry


-- Exercice 5.2
example : { x:ℝ| x < 1 } ∪ { x:ℝ| x ≥ 0 } = Set.univ := sorry


-- Exercice 5.3
example : ∀ E:Type, ∀ A B : Set E, A ∪ B = B ∪ A := sorry 


-- Exercice 5.4
example : ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∪ C = A ∪ (B ∪ C) := sorry 


-- Exercice 5.5
example : ∀ E:Type, ∀ A B : Set E,  B ⊆ A ↔ (A ∪ B  = A) := sorry


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
example : { x:ℝ| x > 1 } ∩ { x:ℝ| x ≤ 0 } = ∅ := sorry


-- Exercice 6.2
example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := sorry


-- Exercice 6.3
example : ∀ E:Type, ∀ A B : Set E, A ∩ B = B ∩ A := sorry 

-- Exercice 6.4
example : ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∩ C = A ∩ (B ∩ C) := sorry 

-- Exercice 6.5
example : ∀ E:Type, ∀ A B C: Set E, (A ∩ B) ∪ C = (A ∪ C) ∩ (B ∪ C) := sorry 

-- Exercice 6.6
example : ∀ E:Type, ∀ A B C: Set E, (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := sorry 

-- Exercice 6.7
example : ∀ E:Type, ∀ A B : Set E, Set.compl (A ∪ B) = (Set.compl A) ∩ (Set.compl B) := sorry 

-- Exercice 6.8
example : ∀ E:Type, ∀ A B : Set E, Set.compl (A ∩ B) = (Set.compl A) ∪ (Set.compl B) := sorry 



-- Exercice 6.9
example : ∀ E:Type, ∀ A B : Set E,  A ⊆ B ↔ (A ∩ B  = A) := sorry


-- Exercice 6.10
example : ∀ E:Type, ∀ A B : Set E,  A ∪ B  = A ∩ B →  A = B := sorry

-- Exercice 6.11
example : ∀ E:Type, ∀ A B C : Set E,  (A ∪ B  ⊆  A ∪ C) ∧ (A ∩ B  ⊆  A ∩ C) ↔  B ⊆ C := sorry



-- Exercice 6.12
example : ∀ E:Type, ∀ A B C : Set E,  (A ∩ Bᶜ  =  A ∩ Cᶜ ) ↔  (A ∩ B  =  A ∩ C)  := sorry



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
example : { x:ℝ| x < 1 } \  { x:ℝ| x ≥  0 } = { x:ℝ| x < 0 }  := sorry

-- Exercice 7.2
example : ∀ E:Type, ∀ A B C: Set E,  A \ (B ∩ C) = (A \ B) ∩ (A \ C)  := sorry





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
example :  {2,3,4} ∈  {A: Set ℕ | 3 ∈ A} := sorry

-- Exercice 8.2
example : {n:ℤ | pair n} ∉ {A: Set ℤ | 3 ∈ A} := sorry


-- si A est un ensemble d'éléments de type E, l'ensemble des parties de A
-- est l'ensemble d'éléments X de type (Set E) vérifiant X ⊆ A
-- il est défini par :  
def powerset_esisar (E : Type)  (A:Set E) : Set (Set E) := {X: Set E  | X ⊆ A }

#print Set.powerset
-- (Set.powerset s)  se note aussi 𝒫 s    
--  Le symbole  𝒫   s'obtient en tapant \powerset 


-- Exercice 8.3
def A01 : Set ℕ := {0,1}
example : 𝒫 A01 = {∅ , {0}, {1}, {0,1}} := sorry


example : ∀ E: Type, ∀ A: Set E, ∀ B: Set E, A ⊆ B → 𝒫 A ⊆ 𝒫 B   := sorry



------------------------------------------------------------------
--- Exemple 9
------------------------------------------------------------------
-- Nouvelles notions
--   produit cartésien


-- si E et F sont deux types, E × F
--  est l'ensemble des couples (x,y) où x:E  et y:F
--  Le symbole   ×    s'obtient en tapant \times
#check ℝ × (Set ℕ) 


-- Exercice 9.1

def disque (A: ℝ × ℝ) (r:ℝ)  (hr: r≥0) : Set (ℝ × ℝ) :=
  { M:ℝ×ℝ  | let (x,y):= M ; let (xA,yA):= A ;(x-xA)^2+(y-yA)^2 ≤ r^2  } 

def disque_unite  : Set (ℝ × ℝ) := disque (0,0) 1 (by norm_num)


-- Notons [a;b] l'ensemble {x:ℝ | x ≥ a ∧ x ≤ b }
macro " [ " a:term  " ; " b:term  " ] "  : term => do
  `({x:ℝ | x ≥ ($a) ∧ x ≤ ($b) })

-- Si A:Set E et B: Set F,  Notons A × B  :Set (E×F) 
-- l'ensemble des (x,y) tels que x∈ A et y∈ B
def produit {E:Type} {F:Type} (A:Set E) (B:Set F)  :=
  {M: E × F | let (x,y):= M ; x ∈ A ∧ y ∈ B }

notation:60 lhs:61 " × " rhs:61 =>  (produit lhs rhs)


example : disque_unite ⊆ ([-1;1] × [-1;1])   := sorry



-- Exercice 9.2

-- Ecrivez (ℝ × ℝ)  \ ([-1;1] × [2;3])  sous forme d'une réunion de produits cartésiens

--example :  ((@Set.univ (ℝ × ℝ)))  \ ([-1;1] × [2;3])  =  sorry := sorry

example : (ℝ × ℝ)    \ ([-1;1] × [2;3])  =  sorry := sorry



-- Exercice 9.3 
-- Montrez que {(x,y)∈ℝ ×ℝ | x^2+y^2 ≤ 1 } ne peut s'écrire comme un produit cartésien

example : ¬ (∃ E: Set ℝ , ∃ F: Set ℝ , disque_unite = E × F) := sorry






