import Esisar.Basic

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
  λ x:ℝ ↦ 
    λ  h: (x=2 ∨ x=-3) ↦
      Or.elim h
      (
        λ h2 : x=2 ↦  
          calc
            x^3 + x^2 - 6*x = 2^3 + 2^2 - 6*2   := by rw[h2]
            _               = 0                 := by norm_num
      )
      (
        λ h3 : x=-3 ↦  
          calc
            x^3 + x^2 - 6*x = (-3)^3 + (-3)^2 - 6*(-3) := by rw[h3]
            _               = -27+9+18                 := by norm_num
            _               = 0                        := by norm_num
      )

example :  ∀x:ℝ, (x=2 ∨ x=-3) →  x^3 + x^2 - 6*x = 0 := 
  soit x:ℝ,
    supposons  h: (x=2 ∨ x=-3),
      Or.elim h
      (
        λ h2 : x=2 ↦  
          calc
            x^3 + x^2 - 6*x = 2^3 + 2^2 - 6*2   := by rw[h2]
            _               = 0                 := by norm_num
      )
      (
        λ h3 : x=-3 ↦  
          calc
            x^3 + x^2 - 6*x = (-3)^3 + (-3)^2 - 6*(-3) := by rw[h3]
            _               = -27+9+18                 := by norm_num
            _               = 0                        := by norm_num
      )


-- Exercice 1.2
example : ∀ x:ℝ , x=-1 ∨ x=2 → x^2-x-2 = 0 :=
  λ x:ℝ ↦ 
    λ  h: (x=-1 ∨ x=2) ↦
      Or.elim h
      (
        λ hm1 : x=-1 ↦  
          calc
            x^2 - x - 2 = (-1)^2 - (-1) - 2   := by rw[hm1]
            _           = 1+1-2               := by norm_num
            _           = 0                   := by norm_num
      )
      (
        λ h2 : x=2 ↦  
          calc
            x^2 - x - 2 = 2^2 - 2 - 2 := by rw[h2]
            _           = 4-2-2       := by norm_num
            _           = 0           := by norm_num
      )



-- Exercice 1.3
-- indication : utilisez le lemme le_or_gt  :  
-- example (n m:ℕ) : (n≤m) ∨ (n ≥m+1) := le_or_gt n m
-- ... avec m bien choisi ... Et effectuez une disjonction de cas
-- voici deux autres lemmes utiles
#check Nat.pow_le_pow_of_le_left
#check ne_of_lt
example  (n m :ℕ ) (h: n≤m) : n^2 ≤ m^2 := Nat.pow_le_pow_of_le_left h 2


example :  ∀n:ℕ , n^2 ≠ 2  :=    -- ≠ s'obtient avec \ne
  soit n:ℕ ,
    have h : n ≤ 1 ∨ n > 1 := le_or_gt n 1
    Or.elim h
    (
      supposons h1: n ≤ 1, 
        have hn2lt2 : n^2 < 2 :=     
          calc  
            n^2 ≤ 1^2 := Nat.pow_le_pow_of_le_left h1 2 
            _   < 2   := by norm_num

        ne_of_lt hn2lt2
      
    )
    (
      supposons h2: n ≥ 2, 
        have hn2gt2: n^2>2 :=
          calc  
            n^2 ≥ 2^2 := Nat.pow_le_pow_of_le_left h2 2 
            _   > 2   := by norm_num

        ne_of_gt hn2gt2
    ) 

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
  λ x:ℝ ↦  
    λ h1: 3*x+4 = 22 ↦ 

      have h2:  x = 6 :=
        calc 
          x = (3*x+4 -4)/3  := by ring_nf
          _ = (22-4)/3      := by rw[h1]
          _ = 6             := by norm_num

      Or.inl h2 


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
  λ x:ℝ ↦  
    λ h1: x^2+x-6 = 0 ↦ 
      have h2 : (x-2)*(x+3) = 0 :=
        calc
          (x-2)*(x+3) = x^2+x-6  := by ring_nf
          _           = 0        := h1
      have h3 : x-2=0 ∨ x+3=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
      Or.elim h3
        (
          λ h4 : x-2=0 ↦
            Or.inl (eq_of_sub_eq_zero h4 : x=2)
        )
        (
          λ h5 : x+3=0 ↦
            Or.inr (eq_neg_of_add_eq_zero_left h5  :  x=-3)
        )

-- Exercice 3.2 
-- consigne : n'utilisez aucun lemme (en dehors de .left, .right, Or.inr, Or.inl)
example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q → P ∨ Q := 
  λ P: Prop ↦ 
    λ Q: Prop ↦ 
      λ h : P ∧ Q ↦
        (Or.inl (h.left:P)   : P ∨ Q)

example : ∀ P :Prop, ∀ Q : Prop, P ∧ Q → P ∨ Q := 
  λ P: Prop ↦ 
    λ Q: Prop ↦ 
      λ h : P ∧ Q ↦
        (Or.inr (h.right:Q)   : P ∨ Q)



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

-- 4.2 version1
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     Iff.intro 
     (
       λ h : P ∨ Q ↦
        Or.elim h
        (
          λ hP : P ↦ 
            (Or.inr hP : Q ∨ P)
        )
        (
          λ hQ : Q ↦ 
            (Or.inl hQ : Q ∨ P)
        )
      )
     (
       λ h : Q ∨ P ↦
        Or.elim h
        (
          λ hQ : Q ↦ 
            (Or.inr hQ : P ∨ Q)
        )
        (
          λ hP : P ↦ 
            (Or.inl hP : P ∨ Q)
        )
      )

-- 4.2 version2
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     have h_impR: P ∨ Q →  Q ∨ P  :=
       λ h : P ∨ Q ↦
        Or.elim h
        (
          λ hP : P ↦ 
            (Or.inr hP : Q ∨ P)
        )
        (
          λ hQ : Q ↦ 
            (Or.inl hQ : Q ∨ P)
        )
     have h_impL: Q ∨ P → P ∨ Q  :=
       λ h : Q ∨ P ↦
        Or.elim h
        (
          λ hQ : Q ↦ 
            (Or.inr hQ : P ∨ Q)
        )
        (
          λ hP : P ↦ 
            (Or.inl hP : P ∨ Q)
        )

     Iff.intro h_impR h_impL



-- 4.2 version3
lemma PorQ_imp_QorP : ∀ P :Prop, ∀ Q : Prop, P ∨ Q →  Q ∨ P :=
   λ P Q : Prop ↦ 
       λ h : P ∨ Q ↦
        Or.elim h
        (
          λ hP : P ↦ 
            (Or.inr hP : Q ∨ P)
        )
        (
          λ hQ : Q ↦ 
            (Or.inl hQ : Q ∨ P)
        )

-- version 3a
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     Iff.intro 
     ( λ hPQ : P ∨ Q ↦ PorQ_imp_QorP P Q hPQ )
     ( λ hQP : Q ∨ P ↦ PorQ_imp_QorP Q P hQP )

-- version 3b
example : ∀ P :Prop, ∀ Q : Prop, P ∨ Q ↔ Q ∨ P :=
   λ P Q : Prop ↦ 
     Iff.intro      ( PorQ_imp_QorP P Q)     ( PorQ_imp_QorP Q P)



-- Exercice 4.3
example :  ∀ x:ℝ , x^2+x-6 = 0 ↔ x=2 ∨ x=-3 := 
  λ x:ℝ ↦  
    Iff.intro

    (
      λ h1: x^2+x-6 = 0 ↦ 
        have h2 : (x-2)*(x+3) = 0 :=
          calc
            (x-2)*(x+3) = x^2+x-6  := by ring_nf
            _           = 0        := h1
        have h3 : x-2=0 ∨ x+3=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
        Or.elim h3
          (
            λ h4 : x-2=0 ↦
              Or.inl (eq_of_sub_eq_zero h4 : x=2)
          )
          (
            λ h5 : x+3=0 ↦
              Or.inr (eq_neg_of_add_eq_zero_left h5  :  x=-3)
          )
    )
    (
      λ  h: (x=2 ∨ x=-3) ↦
        Or.elim h
        (
          λ h2 : x=2 ↦  
            calc
              x^2 + x - 6 = 2^2 +2 - 6  := by rw[h2]
              _           = 4+2-6       := by norm_num
              _           = 0           := by norm_num
        )
        (
          λ hm3 : x=-3 ↦  
            calc
              x^2 + x - 6 = (-3)^2 +(-3) - 6  := by rw[hm3]
              _           = 9-3-6             := by norm_num
              _           = 0                 := by norm_num
        )

    )

lemma eq_or_eq_of_mul_eq_zero {x a b :ℝ } (h: (x-a)*(x-b)=0 ) : x=a ∨ x=b := 
  Or.imp eq_of_sub_eq_zero eq_of_sub_eq_zero  (eq_zero_or_eq_zero_of_mul_eq_zero h)

lemma eq_or_eq_iff_mul_eq_zero {x a b :ℝ } : (x-a)*(x-b)=0 ↔ x=a ∨ x=b := 
   Iff.trans  mul_eq_zero (Iff.or sub_eq_zero sub_eq_zero)


example :  ∀ x:ℝ , x^2+x-6 = 0 ↔ x=2 ∨ x=-3 := 
  λ x:ℝ ↦  
    calc
      x^2+x-6 = 0 ↔ (x-2)*(x-(-3)) = 0 := by ring_nf
      _           ↔ x=2 ∨ x=-3         := eq_or_eq_iff_mul_eq_zero 
 
-- Exercice 4.4
example :  ∀ a:ℚ  , 3*a+1 ≤ 7 ↔ a ≤ 2 := 
   λ a:ℚ ↦  
     Iff.intro
       (
         λ h1 :  3*a+1 ≤ 7 ↦ 
           calc
             a = (3*a+1-1) / 3 := by ring_nf
             _ ≤ (7-1) / 3     := by rel[h1]
             _ = 2             := by norm_num
       )
       (
         λ h2 :  a ≤ 2 ↦ 
           calc 
             3*a+1 ≤ 3*2+1 := by rel[h2]
             _     = 7     := by norm_num
       )

  


-- Exercice 4.5
lemma Int.le_of_two_mul_le : ∀ x a:ℤ, 2*x ≤ 2*a →  x≤ a   := 
  λ x a: ℤ ↦  
    λ h :2*x ≤ 2*a ↦ 
      have h' : x+x ≤ a+a :=
        calc 
          x+x = 2*x := (two_mul x).symm
          _   ≤ 2*a := h
          _   = a+a := two_mul a 
        
        bit0_le_bit0.mp h'   


lemma Int.le_and_le_add_one_iff : ∀ x a: ℤ, x≥ a ∧ x ≤ a+1 →  x=a ∨ x=a+1    := 
  λ x a: ℤ ↦  
    λ h: x ≥ a ∧ x ≤ a + 1 ↦ 
      Or.elim (lt_or_le x (a+1) : x < a + 1 ∨ a + 1 ≤ x)
      (
        λ h_x_lt_succ_a : x < a+1 ↦  Or.inl (le_antisymm  (Int.lt_add_one_iff.mp h_x_lt_succ_a : x ≤ a) (h.left: x ≥ a ))
      )
      (
        λ h_x_ge_succ_a : x ≥ a+1 ↦  Or.inr (le_antisymm (h.right: x ≤ (a+1)) (h_x_ge_succ_a : x ≥ a+1 ))

      )

example :  ∀ a:ℤ , a^2-5*a+5 ≤ -1 ↔ a = 2 ∨ a=3 := 
   λ a:ℤ ↦  
     Iff.intro
       (
         λ h1 :  a^2-5*a+5 ≤ -1 ↦ 
           have h11 : (2*a-5)^2 ≤ 1 := 
            calc
              (2*a-5)^2 = 4*(a^2-5*a+5)+5   := by ring_nf
              _ ≤ 4*(-1) +5                 := by rel[h1]
              _ = 1^2                       := by norm_num
          have h12 : 2*a-5 ≥ -1 ∧ 2*a-5 ≤ 1 := abs_le_of_sq_le_sq' h11 (by norm_num : (1:ℤ) ≥ 0 )
          have h13 : 2*a ≥ 2*2 :=
            calc
              2*a = 2*a-5+5  := by ring_nf
              _   ≥ -1+5     := by rel[h12.left]
              _   = 2*2      := by norm_num

          have h13' : a ≥ 2 := Int.le_of_two_mul_le 2 a h13

          have h14 : 2*a ≤ 2*3 :=
            calc
              2*a = 2*a-5+5  := by ring_nf
              _   ≤ 1+5      := by rel[h12.right]
              _   = 2*3      := by norm_num

          have h14' : a ≤ 3 := Int.le_of_two_mul_le a 3 h14
          
          Int.le_and_le_add_one_iff a 2 (And.intro h13' h14')
       )
       (
         λ h2 : a = 2 ∨ a=3  ↦ 
           Or.elim h2
           (
             λ ha2 : a = 2 ↦ 
               calc
                 a^2-5*a+5 = 2^2-5*2+5  := by rw[ha2]
                 _         ≤ -1         := by norm_num
           )
           (
             λ ha3 : a = 3 ↦ 
               calc
                 a^2-5*a+5 = 3^2-5*3+5  := by rw[ha3]
                 _         ≤ -1         := by norm_num
           )
       )

-- Exercice 4.6
example :  ∀ a:ℝ,∀ b:ℝ, ∀ x:ℝ, x^2 -(a+b)*x+a*b = 0 ↔  x = a ∨ x = b := 
  λ a b:ℝ ↦  
    λ x:ℝ ↦  
      Iff.intro
      (
        λ h1: x^2 -(a+b)*x+a*b = 0 ↦ 
          have h2 : (x-a)*(x-b) = 0 :=
            calc
              (x-a)*(x-b) = x^2 -(a+b)*x+a*b  := by ring_nf
              _           = 0                 := h1
          have h3 : x-a=0 ∨ x-b=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
          Or.elim h3
            (
              λ h4 : x-a=0 ↦
                Or.inl (eq_of_sub_eq_zero h4 : x=a)
            )
            (
              λ h5 : x-b=0 ↦
                Or.inr (eq_of_sub_eq_zero h5 : x=b)
            )
      )
      (
        λ  h: (x=a ∨ x=b) ↦
          Or.elim h
          (
            λ ha : x=a ↦  
              calc
                x^2 -(a+b)*x+a*b = a^2 -(a+b)*a+a*b  := by rw[ha]
                _                = a^2-a^2-b*a+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )
          (
            λ hb : x=b ↦  
              calc
                x^2 -(a+b)*x+a*b = b^2 -(a+b)*b+a*b  := by rw[hb]
                _                = b^2-a*b-b^2+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )

      )



-- Exercice 4.7

example :  ∀ x:ℝ , (x-3)^2 = 2 ↔ x=3-√2 ∨ x=3+√2  := 
  λ x:ℝ ↦  
    Iff.intro
    (
      λ h1: (x-3)^2 = 2 ↦ 
        have h2 : (x-(3-√2))*(x-(3+√2)) = 0 :=
          calc
            (x-(3-√2))*(x-(3+√2)) = (x-3)^2 - (√2)^2  := by ring_nf
            _                     = (x-3)^2 - 2       := by norm_num  -- by rw[Real.sq_sqrt (by norm_num)]
            _                     = 2 -2              := by rw[h1]
            _                     = 0                 := by norm_num

        Or.imp eq_of_sub_eq_zero  eq_of_sub_eq_zero  (eq_zero_or_eq_zero_of_mul_eq_zero h2)
    )
    (
      λ  h:x=3-√2 ∨ x=3+√2   ↦
        Or.elim h
        (
          λ hm : x=3-√2 ↦  
            calc
              (x-3)^2 = (3-√2-3)^2 := by rw[hm]
              _           = 2      := by norm_num
        )
        (
          λ hp : x=3+√2 ↦  
            calc
              (x-3)^2 = (3+√2-3)^2  := by rw[hp]
              _       = 2           := by norm_num
        )

    )

example :  ∀ x:ℝ , (x-3)^2 = 2 ↔ x=3-√2 ∨ x=3+√2  := 
  λ x:ℝ ↦  
    calc
       (x-3)^2 = 2 ↔  (x-3)^2 + (-2)   = 2 + (-2) := add_right_cancel_iff.symm 
       _           ↔  (x-3)^2 - 2      = 0        := by ring_nf
       _           ↔  (x-3)^2 - (√2)^2 = 0        := by norm_num
       _           ↔  (x-(3-√2))*(x-(3+√2)) = 0   := by ring_nf
       _           ↔  x-(3-√2) = 0 ∨ x-(3+√2) =0  := mul_eq_zero 
       _           ↔  x = 3-√2 ∨  x = 3+√2        := Iff.or sub_eq_zero sub_eq_zero

example :  ∀ x:ℝ , (x-3)^2 = 2 ↔ x=3-√2 ∨ x=3+√2  := 
  λ x:ℝ ↦  
    calc
       (x-3)^2 = 2 ↔  (x-3)^2 + (-2)   = 2 + (-2) := add_right_cancel_iff.symm 
       _           ↔  (x-3)^2 - 2      = 0        := by ring_nf
       _           ↔  (x-3)^2 - (√2)^2 = 0        := by norm_num
       _           ↔  (x-(3-√2))*(x-(3+√2)) = 0   := by ring_nf
       _           ↔  x = 3-√2 ∨  x = 3+√2        := eq_or_eq_iff_mul_eq_zero


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
example : ∀x:ℝ , 5*x +2 = 0 → x=-2/5 := λ x:ℝ ↦  (equation_premier_degre 5 2 (by norm_num: 5 ≠ (0:ℝ)) x).mp

-- Exercice 5.2
-- De meme que dans les exemples :
-- Utilisez le théorème précédent pour donner une CS pour que -4+x=0
-- (meme si ça aurait semblé + court sans utiliser le théorème...)
example : ∀x:ℝ ,  x=4 → -4+x = 0 := 
  λ x:ℝ  ↦ 
    λ h: x=4 ↦ 
      have h1 : x= -(-4) /1 :=
        calc
          x = 4         := h
          _ = -(-4) /1  := by norm_num

      calc
        -4+x = 1*x+(-4) := by ring_nf
        _    = 0        := (equation_premier_degre 1 (-4) (by norm_num : 1 ≠ (0:ℝ )) x).mpr h1


-- Exercice 5.3
-- Réécrivez l'exercice 4.5 pour a,b,x dans ℤ, 
-- faites en un lemme, nommé, et utilisez le pour prouver :

lemma Int.eq_sum_product :  ∀ a:ℤ ,∀ b:ℤ, ∀ x:ℤ, x^2 -(a+b)*x+a*b = 0 ↔  x = a ∨ x = b := 
  λ a b:ℤ ↦  
    λ x:ℤ ↦  
      Iff.intro
      (
        λ h1: x^2 -(a+b)*x+a*b = 0 ↦ 
          have h2 : (x-a)*(x-b) = 0 :=
            calc
              (x-a)*(x-b) = x^2 -(a+b)*x+a*b  := by ring_nf
              _           = 0                 := h1
          have h3 : x-a=0 ∨ x-b=0 := eq_zero_or_eq_zero_of_mul_eq_zero h2
          Or.elim h3
            (
              λ h4 : x-a=0 ↦
                Or.inl (eq_of_sub_eq_zero h4 : x=a)
            )
            (
              λ h5 : x-b=0 ↦
                Or.inr (eq_of_sub_eq_zero h5 : x=b)
            )
      )
      (
        λ  h: (x=a ∨ x=b) ↦
          Or.elim h
          (
            λ ha : x=a ↦  
              calc
                x^2 -(a+b)*x+a*b = a^2 -(a+b)*a+a*b  := by rw[ha]
                _                = a^2-a^2-b*a+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )
          (
            λ hb : x=b ↦  
              calc
                x^2 -(a+b)*x+a*b = b^2 -(a+b)*b+a*b  := by rw[hb]
                _                = b^2-a*b-b^2+a*b   := by ring_nf
                _                = 0                 := by ring_nf
          )

      )


lemma Int.eq_or_eq_of_mul_eq_zero {x a b :ℤ } (h: (x-a)*(x-b)=0 ) : x=a ∨ x=b := 
  Or.imp eq_of_sub_eq_zero eq_of_sub_eq_zero  (eq_zero_or_eq_zero_of_mul_eq_zero h)

lemma Int.eq_sum_product' :  ∀ a:ℤ ,∀ b:ℤ, ∀ x:ℤ, x^2 -(a+b)*x+a*b = 0 ↔  x = a ∨ x = b := 
  λ a b:ℤ ↦  
    λ x:ℤ ↦  
      Iff.intro
      (
        λ h1: x^2 -(a+b)*x+a*b = 0 ↦ 
          Int.eq_or_eq_of_mul_eq_zero (
            calc
              (x-a)*(x-b) = x^2 -(a+b)*x+a*b  := by ring_nf
              _           = 0                 := h1
          )
      )
      (
        λ  h: (x=a ∨ x=b) ↦
          Or.elim h
          (
            λ ha : x=a ↦  
              calc
                x^2 -(a+b)*x+a*b = a^2 -(a+b)*a+a*b  := by rw[ha]
                _                = 0                 := by ring_nf
          )
          (
            λ hb : x=b ↦  
              calc
                x^2 -(a+b)*x+a*b = b^2 -(a+b)*b+a*b  := by rw[hb]
                _                = 0                 := by ring_nf
          )

      )


def pair (n:ℤ) : Prop := ∃ k:ℤ, n=2*k
example : ∀ n:ℤ,  n^2-10*n+24=0 → pair n := 
  λ n:ℤ ↦ 
    λ h:  n^2-10*n+24=0 ↦ 
      have h_eq : n^2 -(4+6)*n+4*6 = 0 :=
        calc 
          n^2 -(4+6)*n+4*6 = n^2-10*n+24 := by ring_nf
          _                = 0           := h
      have h46 : n= 4 ∨ n=6 := (Int.eq_sum_product  4 6 n).mp h_eq

      Or.elim h46
      (
        λ h4 : n=4 ↦ 
          Exists.intro 2 (
            calc
              n = 4   := h4
              _ = 2*2 := by norm_num
          )
      )
      (
        λ h6 : n=6 ↦ 
          Exists.intro 3 (
            calc
              n = 6   := h6
              _ = 2*3 := by norm_num
          )
      )



