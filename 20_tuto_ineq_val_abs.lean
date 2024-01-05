import Mathlib.Data.Real.Basic

-- Le but de ce tuto est la résolution d'inéquations du 1er degré comportant des valeurs absolues

------------------------------------------------------------------------------------------------------------
-- Partie 0 - Préliminaire :  lemme de substitution utile dans les résolutions d'équations/inéquations par équivalence
------------------------------------------------------------------------------------------------------------

-- Le lemme iff_arg vous permettra de substituer dans une équivalence.

-- Par exemple si h:a=b  
-- alors (iff_arg (fun z ↦ z+1 ≤ 4 ) h )   sera une preuve de   (  a+1 ≤ 4  ↔  b+1 ≤ 4  )

lemma subst.{v}  {α : Sort v} (motive : α → Prop) {a b : α} (h₁ : a = b) (h₂ : motive a) : motive b
  := @Eq.subst α motive a b h₁ h₂ 

theorem iff_arg.{u}   {α : Sort u}  {a₁ a₂ : α} (f : α → Prop) :  a₁ = a₂ → (f a₁ ↔ f a₂) := 
    λ h => 
      subst  (fun z ↦ (f a₁ ↔ f z)  ) h (Iff.refl _)

example (a b :ℝ) (h: a=b):   a+1 ≤ 4  ↔  b+1 ≤ 4    := iff_arg (fun z ↦ z+1 ≤ 4 ) h
example (a b :ℝ) (h: a=b):   a+1 ≤ 4  ↔  b+1 ≤ 4    := iff_arg (· + 1 ≤ 4 ) h        --   ·  s'obtient avec \.


-- Exercice 0.1

example   : ∀ (x :ℝ),  x-(x-1) ≤ 2  ↔ True := 
  λ (x :ℝ) ↦ 
    calc
      x-(x-1) ≤ 2  ↔ 1 ≤ 2 := sorry 
      _            ↔ True  := by norm_num

-- Exercice 0.2

example  : ∀ (x :ℝ), -x-(-(x-1)) > -1   ↔ False := sorry
  
 

---------------------------------------------------------------------------------
-- Partie 1 -  Additions et soustractions
---------------------------------------------------------------------------------

-- Le lemme    add_le_add_iff_right    de la bibliothèque permet de justifier qu'on conserve l'équivalence en ajoutant
-- un même nombre à droite à chaque membre d'une inégalité large :

  example (a b c :ℝ ) : a ≤ b ↔ a+c ≤ b+c := (add_le_add_iff_right c).symm

-- De même on trouve : add_le_add_iff_left   (addition à gauche) 
   example (a b c :ℝ ) : a ≤ b ↔ c+a ≤ c+b := (add_le_add_iff_left c).symm


-- et add_lt_add_iff_right  et add_lt_add_iff_left  (avec des inégalités strictes)
  example (a b c :ℝ ) : a < b ↔ a+c < b+c := (add_lt_add_iff_right c).symm
  example (a b c :ℝ ) : a < b ↔ c+a < c+b := (add_lt_add_iff_left c).symm

-- Exemples d'utilisation

  example : ∀ x:ℝ , x-1 ≥ 4  ↔  x ≥ 5 :=
    λ x:ℝ ↦  
      calc
        x-1 ≥ 4  ↔  x-1+1 ≥ 4+1  := (add_le_add_iff_right 1).symm
        _        ↔ x ≥ 5         := by ring_nf 
      

  example : ∀ x:ℝ , x+1 > 0  ↔  x > -1 :=
    λ x:ℝ ↦  
      calc
        x+1 > 0  ↔  x+1-1 > 0-1  := (add_lt_add_iff_right (-1)).symm
        _        ↔  x > -1       := by ring_nf 


  example : ∀ x:ℝ , -x+2 ≤ -4  ↔  x ≥ 6 :=
    λ x:ℝ ↦  
      calc
        -x+2 ≤-4   ↔  -x+2+(x+4) ≤ -4+(x+4)   := (add_le_add_iff_right (x+4)).symm
        _          ↔  x ≥ 6                   := by ring_nf

  example : ∀ x:ℝ , 1+x < 0  ↔  x < -1 :=
    λ x:ℝ ↦  
      calc
        1+x < 0  ↔  -1+(1+x) < -1+0  := (add_lt_add_iff_left (-1)).symm
        _        ↔  x < -1           := by ring_nf 
      


-- Exercice 1.1
  example : ∀ x:ℝ , x+2 ≥ -3  ↔  sorry := sorry
      

-- Exercice 1.2
  example : ∀ x:ℝ , x-3 < -1   ↔  sorry := sorry

-- Exercice 1.3
  example : ∀ x:ℝ , -(x-1) ≥ 12  ↔  sorry := sorry


-- Exercice 1.4
  example : ∀ x:ℝ , 1+x/3+1+2*x/3+1 < -1/3  ↔  sorry := sorry
      


---------------------------------------------------------------------------------
-- Partie 2 -  Multiplications et divisons
---------------------------------------------------------------------------------
  
  -- On peut produire une inégalité équivalente en multipliant ou divisant chaque membre par un même nombre 
  --   *** à condition que ce dernier soit strictement positif
  -- Les lemmes ci-dessous en rendent compte :


    example (a b c :ℝ ) (hc:c>0) : a ≤ b ↔ a*c ≤ b*c := (mul_le_mul_right hc).symm
    example (a b c :ℝ ) (hc:c>0) : a < b ↔ a*c < b*c := (mul_lt_mul_right hc).symm
    example (a b c :ℝ ) (hc:c>0) : a ≤ b ↔ c*a ≤ c*b := (mul_le_mul_left hc).symm
    example (a b c :ℝ ) (hc:c>0) : a < b ↔ c*a < c*b := (mul_lt_mul_left hc).symm

    example (a b c :ℝ ) (hc:c>0) : a ≤ b ↔ a/c ≤ b/c := (div_le_div_right hc).symm
    example (a b c :ℝ ) (hc:c>0) : a < b ↔ a/c < b/c := (div_lt_div_right hc).symm

    -- pour les inégalités du premier ordre on devrait pouvoir se passer des deux suivants...
    example  (a b c :ℝ )  (ha : a>0) (hb : b>0) (hc:c>0) : c ≤ b ↔ a/b ≤ a/c  := (div_le_div_left ha hb hc).symm
    example  (a b c :ℝ )  (ha : a>0) (hb : b>0) (hc:c>0) : c < b ↔ a/b < a/c  := (div_lt_div_left ha hb hc).symm

    -- on peut aussi citer les lemmes de la famille  de   : mul_le_mul_right_of_neg   
    -- mais en utilisant le paragraphe sur les additions et les 6 premiers lemmes de ce paragraphe, 
    -- vous devriez avoir assez...
    example (a b c :ℝ ) (hc:c<0) : a ≤ b ↔ a*c ≥ b*c := (mul_le_mul_right_of_neg hc).symm

-- Exemple

  example : ∀ x:ℝ , 2*x-1 ≥ 4  ↔  x ≥ 5/2 :=
    λ x:ℝ ↦  
      calc
        2*x-1 ≥ 4  ↔  2*x-1+1 ≥ 4+1  := (add_le_add_iff_right 1).symm
        _          ↔ 2*x ≥ 5         := by ring_nf 
        _          ↔ 2*x/2 ≥ 5/2     := (div_le_div_right (by norm_num : 2>(0:ℝ))).symm
        _          ↔ x ≥ 5/2         := by ring_nf



  example : ∀ x:ℝ , x - (-(x/2-1))  > 0  ↔  x > 2/3 :=
    λ x:ℝ ↦  
      calc
        x - (-(x/2-1))  > 0  ↔  3*x/2-1     > 0       := by ring_nf
        _                    ↔  3*x/2-1 +1  > 0+1     := (add_lt_add_iff_right 1).symm
        _                    ↔  3*x/2       > 1       := by ring_nf 
        _                    ↔  3*x/2*(2/3) > 1*(2/3) := (mul_lt_mul_right (by norm_num : 2/3>(0:ℝ))).symm
        _                    ↔ x > 2/3                := by ring_nf


-- Exercice 2.1 
  example : ∀ x:ℝ , x - (x/2-1) > 0  ↔  sorry := sorry

-- Exercice 2.2 
  example : ∀ x:ℝ , -3*x+4 ≤ 1  ↔  sorry  := sorry


---------------------------------------------------------------------------------
-- Partie 3 -  Définition de la valeur absolue + quelques lemmes utiles
---------------------------------------------------------------------------------

-- Cette partie  définit la valeur absolue  et en donne quelques propriétés

-- Cette notion existe déjà dans la Mathlib de Lean mais on donne ici une version 'maison' qui permet d'en observer
-- le processus de définition et l'établissement des premières propriétés, suivant un cheminement parallèle au cours.

-- Seules ont été conservés ici les lemmes directement utiles pour les résolutions d'inéquations
-- Un document plus complet sera proposé contenant une preuve de toutes les propriétés vue en  et la résolution des exercices du cours




namespace ineq_val_abs  -- création d'un espace de noms pour ne pas entrer en conflit avec  le   abs   de la Mathib

  -- Définition

  noncomputable def abs (x:ℝ  ) : ℝ := if (x ≥ 0)  then  x   else  (-x)       


  --  Les lemmes   abs_of_nonneg  et  abs_of_nonpos   servent à simplifier  (abs x)  lorsqu'on sait que x≥0  ou que x≤0 

  lemma abs_of_neg  {x:ℝ} (h:x<0) : abs x = -x := if_neg (not_le_of_lt h)
  lemma abs_zero                  : abs 0 = 0  := if_pos (le_refl 0)
  lemma abs_of_pos  {x:ℝ} (h:x>0) : abs x = x  := if_pos (le_of_lt h)

  lemma abs_of_nonneg  {x:ℝ} (h:x≥0) : abs x = x  := if_pos h

  lemma abs_of_nonpos  {x:ℝ} (h:x≤0) : abs x = -x :=
   Or.elim3 (lt_trichotomy x 0   :    ( x <  0) ∨ (x=0) ∨ (x > 0) )
   (
     λ hn : x<0 ↦ abs_of_neg hn
   )
   (
     λ hz : x=0  ↦ 
       calc
         abs x = abs 0 := by rw[hz]
         _     = 0     := abs_zero
         _     = -0    := zero_eq_neg.mpr rfl  -- by norm_num
         _     = -x    := by rw[hz]
   )
   (
     λ hp : x>0 ↦ absurd h (not_le_of_lt hp) 
   )


  -- Exemples
  example : abs 3 = 3        := abs_of_nonneg (by norm_num : 3   ≥ (0:ℝ))
  example : abs (-5/2) = 5/2 := 
    calc
       abs (-5/2) = -(-5/2) :=  abs_of_nonpos (by norm_num : -5/2 ≤ (0:ℝ))
      _           = 5/2     := by norm_num


  -- Exercice 3.1

  example : abs 0 = 0        := sorry
  example : abs (3-1) = 2    := sorry
  example : abs (1-3) = 2    := sorry



  --  Le lemme   abs_neg_eq_abs  (P_3_1_1_3_iii  du cours)   stipule que pour tout x ,  abs (-x) = abs (x)
  -- Sera en particulier utile pour écrire par exempple que  abs (1-x)  =  abs (x+1)

  lemma P_3_1_1_3_iii (x:ℝ) : abs (-x) = abs x :=  
   Or.elim3 (lt_trichotomy x 0   :    ( x <  0) ∨ (x=0) ∨ (x > 0) )
   (
     λ hn : x<0 ↦ 
       have hmp : -x > 0 := neg_pos.mpr hn
       calc
         abs (-x) = -x     := abs_of_pos hmp
         _        = abs x  := (abs_of_neg hn).symm
   )
   (
     λ hz : x=0  ↦ 
       have hmxx : -x=x := hz ▸ (by norm_num:-0=(0:ℝ ))  
       congr_arg abs hmxx
   )
   (
     λ hp : x>0 ↦ 
       have hmn : -x < 0 := neg_lt_zero.mpr hp
       calc 
         abs (-x) = -(-x)  := abs_of_neg hmn
         _        = x      := by ring_nf
         _        = abs x  := (abs_of_pos hp).symm
     
   )
    
  lemma abs_neg_eq_abs (x:ℝ) : abs (-x) = abs x := P_3_1_1_3_iii x

  -- Exemple

  example : ∀ x:ℝ , abs (-x+1) = abs (x-1) := 
    λ x:ℝ ↦ 
      calc
        abs (-x+1) = abs (-(-x+1)) := (abs_neg_eq_abs (-x+1)).symm
        _          = abs (x-1)     := by ring_nf

  -- Exercice 3.2

  example : ∀ x:ℝ , abs (3-x/2) = abs (x/2-3) := sorry




end ineq_val_abs


---------------------------------------------------------------------------------
-- Partie 4 - inéquations avec valeurs absolues
---------------------------------------------------------------------------------

-- Dans  cette partie, le but est de résoudre des inéquations avec des valeurs absolues

namespace ineq_val_abs


  -- Le petit lemme ci-dessous est utile  pour  mettre en place de disjonctions de 3 cas 

    lemma left_or_center_or_right  (x a b : ℝ) : x < a ∨ (x ≥  a ∧ x <  b) ∨ x ≥ b := 
      Or.elim  (lt_or_le x a ) Or.inl
      (
        λ hxa ↦ 
          Or.elim  (lt_or_le x b ) 
          (
             Or.inr  ∘  Or.inl ∘  And.intro hxa 
          )
          (
            Or.inr  ∘  Or.inr
          )
      )

    -- exemple d'utilisation
    example  : ∀ x:ℝ , abs x + abs (x+1) ≥ 1 :=
      λx:ℝ ↦ 
        Or.elim3 (left_or_center_or_right x (-1) 0)  
        (
           λ h : x < -1 ↦ 
             have h0 : x   ≤ 0 :=  
               calc
                 x ≤ -1 := le_of_lt h
                 _ ≤ 0  := by norm_num


             have h1 : x+1 ≤ 0 := 
               calc
                 x+1 ≤ -1+1 := by rel[h]
                 _   = 0    := by norm_num

       -- les deux calculs précedents auraient pu  etre abrégés avec la tactique linarith
             have h0' : x   ≤ 0 :=  by  linarith
             have h1' : x+1 ≤ 0 :=  by  linarith

             calc  
               abs x + abs (x+1) = (-x) + (-(x+1))  := by rw[abs_of_nonpos h0,  abs_of_nonpos h1]
               _                 = (-2)*x-1         := by ring_nf
               _                 ≥ (-2)*(-1)-1      := (add_le_add_iff_right ((-1):ℝ )).mpr ( (mul_le_mul_left_of_neg (by norm_num)).mpr (le_of_lt h))
               _                 = 1                := by norm_num
        )
        (
           λ h : x ≥ -1  ∧ x < 0  ↦ 
             have h0 : x   ≤ 0 :=  le_of_lt h.right
             have h1 : x+1 ≥ 0 :=  
               calc
                 x+1 ≥ -1+1 := by rel[h.left]
                 _   = 0    := by norm_num 

             -- idem
             have h0' : x   ≤ 0 :=  by  linarith
             have h1' : x+1 ≥ 0 :=  by  linarith

             calc  
               abs x + abs (x+1) = (-x) + (x+1)  := by rw[abs_of_nonpos h0,  abs_of_nonneg h1]
               _                 = 1             := by ring_nf
               _                 ≥ 1             := by norm_num
        )
        (
           λ h : x ≥ 0 ↦ 
             have h0 : x   ≥ 0 := h
             have h1 : x+1 ≥ 0 :=  
               calc
                 x+1 ≥ 0+1 := by rel[h]
                 _   ≥  0  := by norm_num 

             -- idem
             have h0' : x   ≥ 0 :=  by  linarith
             have h1' : x+1 ≥ 0 :=  by  linarith

             calc  
               abs x + abs (x+1) = x + (x+1)  := by rw[abs_of_nonneg h0,  abs_of_nonneg h1]
               _                 = 2*x+1      := by ring_nf
               _                 ≥ 2*0+1      := by rel[h]
               _                 = 1          := by norm_num
        )


    -- Exercice 4.1
    example  : ∀ x:ℝ , abs (x+1) + abs (2-x) ≥ 3 := sorry





    --  Maintenant, voici trois  exemples de résolutions d'inéquations proprement dites, ensuite c'est à vous !

    -- Exemple 1

    example (x:ℝ ) : abs (2*x+1) - abs (1-x) ≥ 3 ↔ x ≤ -5 ∨ x ≥ 1  :=
      Or.elim3 (left_or_center_or_right x (-1/2) 1)
      (
        λ h ↦ 
          have h1 : 2*x+1 ≤ 0 := by linarith  -- by rel[h] : ne trouve pas
          have h2 : 1-x   ≥ 0 := by linarith
          calc
             abs (2*x+1) - abs (1-x) ≥ 3 ↔ -(2*x+1) -  (1-x) ≥3 := by rw[abs_of_nonpos h1, abs_of_nonneg h2 ]
             _                           ↔ -x-2 ≥3              := by ring_nf 
             _                           ↔ -x-2+(x-3) ≥3+(x-3)  := (add_le_add_iff_right _).symm 
             _                           ↔ x ≤ -5               := by ring_nf 
             _                           ↔ x ≤ -5 ∨ x ≥ 1       := Iff.intro (Or.inl) (λ o: x≤-5 ∨ x≥1 ↦ Or.elim o id
                                                                     (λ o':x≥1 ↦ absurd o' (not_le_of_gt (lt_trans h (by norm_num))) ))
      )
      (
        λ h ↦ 
          have h1 : 2*x+1 ≥ 0 := by linarith  
          have h2 : 1-x   ≥ 0 := by linarith
          calc
             abs (2*x+1) - abs (1-x) ≥ 3 ↔ (2*x+1) -  (1-x) ≥3 := by rw[abs_of_nonneg h1, abs_of_nonneg h2 ]
             _                           ↔ 3*x ≥3              := by ring_nf 
             _                           ↔ 3*x/3 ≥ 3/3         := (div_le_div_right (by norm_num)).symm
             _                           ↔ x ≥ 1               := by ring_nf 
             _                           ↔ False               := Iff.intro (λ o ↦ absurd (trans h.right o) (by norm_num)) False.elim
             _                           ↔ x ≤ -5 ∨ x ≥ 1      := Iff.intro False.elim (λ o:x≤-5 ∨ x≥1 ↦ Or.elim o 
                                                                       (λ o1: x≤-5 ↦ absurd (le_trans h.left o1)        (by norm_num)) 
                                                                       (λ o2: x≥1  ↦ absurd (lt_of_lt_of_le h.right o2) (by norm_num) ) )
      )
      (
        λ h ↦ 
          have h1 : 2*x+1 ≥ 0 := by linarith  
          have h2 : 1-x   ≤ 0 := by linarith
          calc
             abs (2*x+1) - abs (1-x) ≥ 3 ↔ (2*x+1) - ( -(1-x)) ≥3 := by rw[abs_of_nonneg h1, abs_of_nonpos h2 ]
             _                           ↔ x+2 ≥3                 := by ring_nf 
             _                           ↔ x+2-2 ≥ 3-2            := (add_le_add_iff_right _).symm 
             _                           ↔ x ≥ 1                  := by ring_nf 
             _                           ↔ True                   := Iff.intro (λ _ ↦ trivial) (λ_ ↦ h )       
             _                           ↔ x ≤ -5 ∨ x ≥ 1         := Iff.intro (λ _ ↦ Or.inr h) (λ _ ↦ trivial)
      )

    
    -- Exemple 2

    example (x:ℝ ) : abs (x) - abs (1-x/2) > 0 ↔ x < -2 ∨ x > 2/3  :=
      have h0 : abs (x) - abs (1-x/2) > 0  ↔  (abs x) - (abs (x/2-1)) > 0 :=
        calc
          (abs x) - (abs (1-x/2)) > 0 ↔ (abs x) - (abs (-(1-x/2))) > 0  := by rw[abs_neg_eq_abs]
          _                           ↔ (abs x) - (abs (x/2-1))    > 0  := by ring_nf

      Or.elim3 (left_or_center_or_right x 0 2)
      (
        λ h ↦ 
          have h1 : x     ≤  0  := le_of_lt h                                                                                        -- by linarith
          have h2 : x/2-1 ≤  0  := le_trans (add_le_add_right ((div_le_div_right (by norm_num)).mpr (le_of_lt  h)) _) (by norm_num ) -- by linarith
          calc
             (abs x) - (abs (1-x/2)) > 0 ↔ (abs x) - (abs (x/2-1))    > 0  := h0
             _                           ↔ -x - (-(x/2-1))            > 0  := by rw[abs_of_nonpos h1, abs_of_nonpos h2 ]
             _                           ↔ -x/2-1                     > 0  := by ring_nf 
             _                           ↔ -x/2-1+x/2   > 0+x/2            := (add_lt_add_iff_right _).symm 
             _                           ↔ x/2   < -1                      := by ring_nf
             _                           ↔ x/2*2   < (-1)*2                := (mul_lt_mul_right (by norm_num)).symm
             _                           ↔ x       < -2                    := by ring_nf 
             _                           ↔ x < (-2) ∨ x > 2/3              := Iff.intro (Or.inl) ( λ o: x<(-2) ∨ x>2/3 ↦ Or.elim o id 
                                                                                ( λ o':x>2/3 ↦ absurd (lt_trans o' h)  (by norm_num)) )
      )
      (
        λ h ↦ 
          have h1 : x     ≥ 0 := h.left                                                                                                   -- by linarith  
          have h2 : x/2-1 ≤ 0 := le_trans (add_le_add_right ((div_le_div_right (by norm_num)).mpr (le_of_lt  h.right)) _) (by norm_num )  -- by linarith
          calc
             (abs x) - (abs (1-x/2)) > 0 ↔ (abs x) - (abs (x/2-1))    > 0  := h0
             _                           ↔  x - (-(x/2-1))            > 0  := by rw[abs_of_nonneg h1, abs_of_nonpos h2 ]
             _                           ↔ 3*x/2-1                    > 0  := by ring_nf 
             _                           ↔ 3*x/2-1+1   > 0+1               := (add_lt_add_iff_right _).symm 
             _                           ↔ 3*x/2   > 1                     := by ring_nf
             _                           ↔ 3*x/2*(2/3)   > 1*(2/3)         := (mul_lt_mul_right (by norm_num)).symm
             _                           ↔ x       > 2/3                   := by ring_nf 
             _                           ↔ x < (-2) ∨ x > 2/3              := Iff.intro (Or.inr) (λ o : x<(-2) ∨ x>2/3 ↦ Or.elim o 
                                                       (λ o':x<(-2) ↦ absurd o' (not_lt_of_le (le_of_lt (lt_of_lt_of_le (by norm_num) h.left))) ) 
                                                       id )
      )
      (
        λ h ↦ 
          have h1 : x     ≥ 0 := le_trans (by norm_num) h                                                               -- by linarith  
          have h2 : x/2-1 ≥ 0 := le_trans (by norm_num ) (add_le_add_right ((div_le_div_right (by norm_num)).mpr h) _)  -- by linarith
          calc
             (abs x) - (abs (1-x/2)) > 0 ↔ (abs x) - (abs (x/2-1))   > 0  := h0
             _                           ↔ x - (x/2-1)               > 0  := by rw[abs_of_nonneg h1, abs_of_nonneg h2 ]
             _                           ↔ x/2+1                     > 0  := by ring_nf 
             _                           ↔ x/2+1-1 > 0-1                  := (add_lt_add_iff_right _).symm 
             _                           ↔ x/2     > -1                   := by ring_nf
             _                           ↔ x/2*2   > (-1)*2               := (mul_lt_mul_right (by norm_num)).symm
             _                           ↔ x       > -2                   := by ring_nf 
             _                           ↔ x < (-2) ∨ x > 2/3             := Iff.intro (λ _ ↦ Or.inr (lt_of_lt_of_le (by norm_num) h))
                                                                                       (λ _ ↦  lt_of_lt_of_le (by norm_num) h )
      )


    -- Exemple 3
    example (x:ℝ ) : abs (x) - abs (1-x) ≤ 1 ↔ True  :=
      have h0 : _ :=
        calc
          (abs x) - (abs (1-x)) ≤ 1 ↔ (abs x) - (abs (-(1-x))) ≤ 1  := by rw[abs_neg_eq_abs]
          _                         ↔ (abs x) - (abs (x-1))  ≤ 1    := by ring_nf

      Or.elim3 (left_or_center_or_right x 0 1)
      (
        λ h : x < 0 ↦ 
          have h1 : x    ≤  0  := le_of_lt h                                                -- by linarith
          have h2 : x-1  ≤  0  := le_trans (add_le_add_right (le_of_lt h) _) (by norm_num ) -- by linarith
          calc
             (abs x) - (abs (1-x)) ≤ 1 ↔ (abs x) - (abs (x-1))  ≤ 1  := h0
             _                         ↔ -x - (-(x-1))          ≤ 1  := by rw[abs_of_nonpos h1, abs_of_nonpos h2 ]
             _                         ↔ -1                 ≤ 1      := iff_arg ( · ≤ 1) (by ring_nf) 
             _                         ↔ True                        := by norm_num
      )
      (
        λ h : x ≥ 0 ∧ x < 1 ↦
          have h1 : x    ≥  0  := h.left                                                          -- by linarith
          have h2 : x-1  ≤  0  := le_trans (add_le_add_right (le_of_lt h.right) _) (by norm_num ) -- by linarith
          calc
             (abs x) - (abs (1-x)) ≤ 1 ↔ (abs x) - (abs (x-1))  ≤ 1  := h0
             _                         ↔  x - (-(x-1))          ≤ 1  := by rw[abs_of_nonneg h1, abs_of_nonpos h2 ]
             _                         ↔ 2*x-1                  ≤ 1  := by ring_nf
             _                         ↔ True                        := Iff.intro 
                                                                         (λ _ ↦ trivial)
                                                                         (λ _ ↦ le_trans (by rel[h.right]) (by norm_num : 2*1-1 ≤ (1:ℝ)))
      )
      (
        λ h : x ≥ 1  ↦ 
          have h1 : x    ≥   0  := le_trans (by norm_num) h                       -- by linarith
          have h2 : x-1  ≥   0  := le_trans (by norm_num) (add_le_add_right h _)  -- by linarith
          calc
             (abs x) - (abs (1-x)) ≤ 1 ↔ (abs x) - (abs (x-1))  ≤ 1  := h0
             _                         ↔  x - (x-1)             ≤ 1  := by rw[abs_of_nonneg h1, abs_of_nonneg h2 ]
             _                         ↔ 1                      ≤ 1  := iff_arg ( · ≤ 1) (by ring_nf) 
             _                         ↔ True                        := by norm_num
      )


    -- Exercice 4.2
    example (x:ℝ ) : abs (3-2*x) - abs (2*x) < 4 ↔ sorry  := sorry

    -- Exercice 4.3
    example (x:ℝ ) : abs (x) + abs (x+1) ≤ 2 ↔ sorry  := sorry

    -- Exercice 4.4
    example (x:ℝ ) : abs (2*x)-abs (1-x/2) ≥ 2 ↔ sorry  := sorry

    -- Exercice 4.5
    example (x:ℝ ) : abs (2*x)-abs (1-x/2) > 6 ↔ sorry  := sorry

    -- Exercice 4.6
    example (x:ℝ ) : abs (2*x)-abs (1-x/2) ≤ -2 ↔ sorry  := sorry



end ineq_val_abs
