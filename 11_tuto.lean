import Esisar.Basic
--import Mathlib.Data.Nat.Basic   -- librairie à importer pour utiliser les entiers naturels (ℕ)
--import Mathlib.Data.Int.Basic   -- librairie à importer pour utiliser les entiers (ℤ)
--import Mathlib.Data.Real.Basic   -- librairie à importer pour utiliser les réels (ℝ)



-- Vous pouvez tester immédiatement ces exemples dans le Lean Web Editor :
-- https://lean.math.hhu.de/

-- Ou vous pouvez installer sur votre machine VS Code et l'extension Lean4 en suivant ces instructions :
-- https://leanprover.github.io/lean4/doc/quickstart.html
-- https://leanprover-community.github.io/install/project.html

-----------------------
-- 11_tuto.lean
-- Nouvelles notions
-----------------------

--  Exemple 1 -----------------------
--    connecteur logique OU (∨) : élimination

--  Exemple 2 -----------------------
--    connecteur logique OU (∨) : introduction

--  Exemple 3 -----------------------
--    réutilisation des notions précédentes

--  Exemple 4 -----------------------
--    L'équivalence  ↔  :  introduction de ↔ 
--    Ecrire un lemme

--  Exemple 5 -----------------------
--    Elimination de ↔ 




------------------------------------------------------------------
--- Exemple 1
------------------------------------------------------------------

-- Nouvelles notions
--  connecteur logique OU (∨) : élimination

example : ∀x:ℝ, ∀y:ℝ, (x=1 ∨ y=-1) → x*y+x = y+1 :=  -- ∨ signifie "OU" et s'obtient avec \or 
  λ  x:ℝ ↦                      -- introduction de ∀x
    λ  y:ℝ ↦                    -- introduction de ∀y
      λ h :  (x=1 ∨ y=-1) ↦     -- introduction de → 
        Or.elim h               -- disjonction de cas : élimination du OU
        (
          λ hx : x=1 ↦          -- 1er cas : on suppose x=1
            calc
              x*y+x = 1*y+1  := by rw[hx]
              _      = y+1   := by ring_nf
        )
        (
          λ hy: y=-1 ↦          -- 2e cas : on suppose y=-1
            calc 
              x*y+x = x*(-1)+x  := by rw[hy]
              _      = -1+1     := by ring_nf
              _      = y+1      := by rw[hy]
        )


-- Exercice 1.1
example :  ∀x:ℝ, (x=2 ∨ x=-3) →  x^3 + x^2 - 6*x = 0 := 
  sorry


-- Exercice 1.2
example : ∀ x:ℝ , x=-1 ∨ x=2 → x^2-x-2 = 0 :=
  sorry


-- Exercice 1.3
example :  ∀n:ℕ , n^2 ≠ 2  :=    -- ≠ s'obtient avec \ne
  sorry
-- indication : utilisez le lemme le_or_gt  :  
-- example (n m:ℕ) : (n≤m) ∨ (n ≥m+1) := le_or_gt n m
-- ... avec m bien choisi ... Et effectuez une disjonction de cas
-- voici deux autres lemmes utiles
#check Nat.pow_le_pow_of_le_left
#check ne_of_lt
example  (n m :ℕ ) (h: n≤m) : n^2 ≤ m^2 := Nat.pow_le_pow_of_le_left h 2

------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------

-- Nouvelles notions
--  connecteur logique OU (∨) : introduction

example : ∀ x:ℝ , 2*x+1 = 5 → x=1 ∨ x=2 :=
  λ x:ℝ ↦  
    λ h1: 2*x+1 = 5 ↦ 

      have h2:  x = 2 :=
        calc 
          x = (2*x+1 -1)/2  := by ring_nf
          _ = (5-1)/2       := by rw[h1]
          _ = 2             := by norm_num

      Or.inr h2  -- ici vient l'introduction de ∨  :
                 --    "comme x=2 est vraie, on a (x=1) ∨ (x=2) vraie "
                 -- inr : le 'r' comme right : (x=2) est à droite de (x=1) ∨ (x=2) 
                 -- pour prouver (x=2) ∨ (x=3) on aurait écrit :  Or.inl h2   ('l' comme left)


-- Exercice 2.1
example :  ∀x:ℝ, 3*x+4 = 22 →  x=6 ∨ x= 9 := 
   sorry


------------------------------------------------------------------
--- Exemple 3
------------------------------------------------------------------

#check eq_zero_or_eq_zero_of_mul_eq_zero

example : ∀ x:ℝ , x^2-x-2 = 0 → x=-1 ∨ x=2 :=
  λ x:ℝ ↦  
    λ h1: x^2-x-2 = 0 ↦ 
      have h2 : (x+1)*(x-2) = 0 :=
        calc
          (x+1)*(x-2) = x^2-x-2  := by ring_nf
          _           = 0        := h1
      have h3 : x+1=0 ∨ x-2=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
      Or.elim h3
        (
          λ h4 : x+1=0 ↦
            have h5 : x=-1 :=
              calc
                x = x+1-1  := by ring_nf
                _ = 0  -1  := by rw[h4]
                _ =    -1  := by norm_num
            Or.inl h5     
        )
        (
          λ h6 : x-2=0 ↦
            have h7 : x=2 :=
              calc
                x = x-2+2  := by ring_nf
                _ = 0  +2  := by rw[h6]
                _ =    2   := by norm_num

            Or.inr h7
        )

-- autre version un peu raccourcie en utlisant deux lemmes supplémentaires

#check eq_of_sub_eq_zero
#check eq_neg_of_add_eq_zero_left

example : ∀ x:ℝ , x^2-x-2 = 0 → x=-1 ∨ x=2 :=
  λ x:ℝ ↦  
    λ h1: x^2-x-2 = 0 ↦ 
      have h2 : (x+1)*(x-2) = 0 :=
        calc
          (x+1)*(x-2) = x^2-x-2  := by ring_nf
          _           = 0        := h1
      have h3 : x+1=0 ∨ x-2=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
      Or.elim h3
        (
          λ h4 : x+1=0 ↦
            Or.inl (eq_neg_of_add_eq_zero_left h4 : x=-1)
        )
        (
          λ h6 : x-2=0 ↦
            Or.inr (eq_of_sub_eq_zero h6  :  x=2)
        )


-- Exercice 3.1
example :  ∀ x:ℝ , x^2+x-6 = 0 → x=2 ∨ x=-3 := 
   sorry

-- Exercice 3.2 
-- consigne : n'utilisez aucun lemme (en dehors de .left, .right, Or.inr, Or.inl)
example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q → P ∨ Q := 
  sorry



------------------------------------------------------------------
--- Exemple 4
------------------------------------------------------------------
-- Nouvelles notions
--  L'équivalence  ↔  (s'obtient en tapant \lr ) :  introduction de ↔ 
--  Ecrire un lemme


example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q ↔ Q ∧ P :=
  λ P: Prop ↦  
    λ Q: Prop ↦  
      Iff.intro   -- introduction de ↔ :  pour prouver A ↔ B, 
                  -- on fournit Iff.intro un preuve de A → B   suivie d'une preuve de B → A 
      (
        λ hPQ : P ∧ Q ↦ 
          (And.intro (hPQ.right:Q) (hPQ.left:P) : Q ∧ P)
      )
      (
        λ hQP : Q ∧ P ↦ 
          And.intro hQP.right hQP.left  -- on n'est pas obligé d'annoter les termes de preuve, mais ça peut clarifier
      )

-- autre version
-- on peut aussi introduire les preuves A ↔ B et B → A comme resultats intermediaires ('have')
-- puis invoquer Iff.intro après
example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q ↔ Q ∧ P :=
  λ P: Prop ↦  
    λ Q: Prop ↦  

      have hAB : P ∧ Q → Q ∧ P :=
        λ hPQ : P ∧ Q ↦ 
          (And.intro (hPQ.right:Q) (hPQ.left:P) : Q ∧ P)

      have hBA : Q ∧ P → P ∧ Q :=
        λ hQP : Q ∧ P ↦ 
          And.intro hQP.right hQP.left

      Iff.intro   hAB hBA

-- troisieme version
-- on prouve que   ∀ P :Prop, ∀ Q : Prop, P ∧ Q → Q ∧ P   
-- et on donne un nom a ce théorème, ou lemme  (par exemple: PQ_imp_QP)
-- ça nous permet de le réutiliser pour prouver l'exercice demandé

lemma  PQ_imp_QP : ∀ P :Prop, ∀ Q : Prop, P ∧ Q → Q ∧ P :=
    -- lemma <name> :    ça fonctionne comme  example :   sauf qu'on lui donne un nom
    -- on peut aussi écrire   theorem <name> :  ç'est la même chose
    -- un lemme est un théorème pas très important

  λ P: Prop ↦  
    λ Q: Prop ↦  
        λ hPQ : P ∧ Q ↦ 
          (And.intro (hPQ.right:Q) (hPQ.left:P) : Q ∧ P)

-- maintenant nous allons prouver le résultat demandé
example : ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P :=
  λ P Q: Prop ↦  Iff.intro 
    (PQ_imp_QP P Q : P ∧ Q → Q ∧ P )   
    (PQ_imp_QP Q P : Q ∧ P → P ∧ Q)



-- Exercice 4.2 
-- exercice à réaliser de trois façons différentes, comme dans l'exemple ci-dessus
-- consigne : n'utilisez aucun lemme (en dehors de Or.elim, Or.inr, Or.inl)
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   sorry

-- Exercice 4.3
example :  ∀ x:ℝ , x^2+x-6 = 0 ↔ x=2 ∨ x=-3 := 
   sorry

-- Exercice 4.4
example :  ∀ a:ℚ  , 3*a+1 ≤ 7 ↔ a ≤ 2 := 
   sorry

-- Exercice 4.5
example :  ∀ a:ℤ , a^2-5*a+5 ≤ -1 ↔ a = 2 ∨ a=3 := 
   sorry

-- Exercice 4.6
example :  ∀ a:ℝ,∀ b:ℝ, ∀ x:ℝ, x^2 -(a+b)*x+a*b = 0 ↔  x = a ∨ x = b := 
   sorry

-- Exercice 4.7
example :  ∀ x:ℝ , (x-3)^2 = 2 ↔ x=3-√2 ∨ x=3+√2  := sorry

------------------------------------------------------------------
--- Exemple 5
------------------------------------------------------------------
-- Nouvelles notions
--   Elimination de ↔ 

-- Si on dispose d'une preuve h de P ↔ Q  mais qu'on a besoin d'une preuve de P→Q,
-- on peut l'obtenir avec h.mp   (mp veut dire Modus Ponens)
-- De même,  h.mpr  est une preuve de Q → P   (Modus Ponens Reversed)

#check mul_eq_zero  -- ce lemme donne une équivalence
example (x:ℝ) (h: (x-1)*(x-2)=0) : x-1=0 ∨ x-2=0 := mul_eq_zero.mp h  
example (u v:ℝ ) (h:v≠ 0) : v*u/v = u := by exact?  -- ≠ s'obtient avec \ne


-- donnons ici la résolution de l'équation du 1er degré dans ℝ :
theorem  equation_premier_degre :  ∀ b c:ℝ , b≠ 0 → ∀x:ℝ , b*x + c = 0 ↔ x=-c/b := 

λ b c:ℝ ↦ 
  λ hb: b≠ 0 ↦  
    λ x:ℝ ↦ 
      Iff.intro
      (
        λ h1 : b*x + c = 0  ↦ 
          calc
            x = (b*x)/b     := by rw[mul_div_cancel_left x hb] 
            _ = (b*x+c-c)/b := by ring_nf
            _ = (0-c)/b     := by rw[h1]
            _ = -c/b        := by ring_nf
      )
      (
        λ h2 : x = -c/b ↦
          calc 
            b*x+c = b*(-c/b) +c := by rw[h2]
            _     = -(b*c/b)+c  := by ring_nf
            _     = -c+c        := by rw[mul_div_cancel_left c hb]
            _     = 0           := by ring_nf
      )

-- Utilisons ce théorème pour trouver une CN pour que : 3*x-4 =0 :

example: ∀x:ℝ , 3*x - 4 = 0 → x=4/3 := 
  λ x:ℝ ↦ 
    λ h : 3*x - 4 = 0  ↦ 

      have h2 : 3*x+(-4) = 0 := 
        calc 
          3*x+(-4) = 3*x-4  := by ring_nf 
          _        = 0      := h


      have h3 : _ :=
        (equation_premier_degre 3 (-4) (by norm_num: (3:ℝ) ≠ 0) x).mp  h2    -- ≠ s'obtient avec \ne
        -- mp pour extraire → de ↔ 
      
      calc 
         x = -(-4)/3 := h3
         _ = 4/3     := by norm_num

-- Utilisons ce théorème pour trouver une CS pour que : 2*x+3 =0 :
example: ∀x:ℝ , x=-3/2 → 2*x + 3 = 0   := 
  λ x:ℝ ↦ 
    λ h : x=-3/2 ↦ 
       (equation_premier_degre 2 3 (by norm_num: (2:ℝ) ≠ 0) x).mpr h
        -- mpr pour extraire ←  de ↔ 


-- Exercice 5.1
-- De meme que dans les exemples :
-- Utilisez le théorème précédent pour donner une CN pour que 5*x+2=0
-- (meme si ça aurait semblé + court sans utiliser le théorème...)
example : ∀x:ℝ , 5*x +2 = 0 → sorry := sorry

-- Exercice 5.2
-- De meme que dans les exemples :
-- Utilisez le théorème précédent pour donner une CS pour que -4+x=0
-- (meme si ça aurait semblé + court sans utiliser le théorème...)
example : ∀x:ℝ ,  sorry → -4+x = 0 := sorry


-- Exercice 5.3
-- Réécrivez l'exercice 4.5 pour a,b,x dans ℤ, 
-- faites en un lemme, nommé, et utilisez le pour prouver :
def pair (n:ℤ) : Prop := ∃ k:ℤ, n=2*k
example : ∀ n:ℤ,  n^2-10*n+24=0 → pair n := sorry 



