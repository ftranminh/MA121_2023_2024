import Mathlib.Data.Nat.Basic 
import Mathlib.Data.Int.Basic 
import Mathlib.Data.Real.Basic 


--- Treize solutions pour prouver une condition nécessaire à une équation du premier degré dans Lean

-- Différentes solutions à l'exercice 1.1du 10_tuto.lean

---Solution 1 (recommandée)
example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      calc
        x = (2*x+11-11)/2 := by ring_nf
        _ = (6  -11)/2    := by rw[h]
        _ = -5/2          := by norm_num



---Solution 2 (les tactiques sont remplacées par l'appel à des lemmes précis)
example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      calc
        x = (x*2)/2       := (mul_div_cancel x (by norm_num : (2:ℝ) ≠ 0)).symm
        _ = (2*x)/2       := congr_arg (fun z ↦ z/2)      (mul_comm x 2)
        _ = (2*x+11-11)/2 := congr_arg (fun z ↦ z/2)      (add_sub_cancel (2*x) 11).symm
        _ = (6  -11)/2    := congr_arg (fun z ↦ (z-11)/2) h
        _ = -5/2          := by norm_num




-- Lemmes intermédiaires pour la suite

lemma subst.{v}  {α : Sort v} (motive : α → Prop) {a b : α} (h₁ : a = b) (h₂ : motive a) : motive b
  := @Eq.subst α motive a b h₁ h₂ 

theorem imp_arg  {α : Sort u}  {a₁ a₂ : α} (f : α → Prop) :  a₁ = a₂ → (f a₁ → f a₂) := 
    λ h => 
      subst  (fun z ↦ (f a₁ → f z)  )  h (id)

example (a b c :ℝ ): a +b-c = a+(b -c) := by exact?
example (a :ℝ ): a -a = 0 := by exact?


-- Solution 3 :  sans calc, comme vous avez l'habitude , par transformation de l'équation initiale, avec "have" ("on a"), très détaillé

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := congr_arg (fun z ↦ z-11)  h
      have h2:  2*x +(11 -11) = 6 -11    := Eq.trans (add_sub_assoc (2*x) 11 11).symm h1
      have h3:  2*x + 0       = 6 -11    := subst (fun z ↦ 2*x+z=6-11 ) (sub_self 11     : (11:ℝ)-11=0    )  h2
      have h4:  2*x           = 6 -11    := subst (fun z ↦ z=6-11 )     (add_zero (2*x)  : 2*x+0=2*x      )  h3
      have h5:  2*x           = -5       := subst (fun z ↦ 2*x=z )      (by norm_num     : (6:ℝ)-11=-5    )  h4
      have h6:  2*x/2         = -5/2     := congr_arg (fun z => z/2) h5
      have h7:  x*2/2         = -5/2     := subst (fun z => z/2 = -5/2) (mul_comm 2 x)                       h6
      have h8:  x             = -5/2     := subst (fun z => z = -5/2)   (mul_div_cancel x (by norm_num: (2:ℝ) ≠ 0 )) h7
      h8      


-- Solution 4 : variante utilisant subst a chaque ligne


example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := subst (fun z ↦ 2*x+11-11 = z-11) (h:2*x+11 = 6)                 (rfl:2*x+11-11=2*x+11-11 )
      have h2 : 2*x +(11 -11) = 6 -11    := subst (fun z ↦ z = 6-11)    (add_sub_assoc (2*x) 11 11 : 2*x+11-11 = 2*x+(11-11))    h1
      have h3:  2*x + 0       = 6 -11    := subst (fun z ↦ 2*x+z=6-11 ) (sub_self 11     : (11:ℝ)-11=0    )  h2
      have h4:  2*x           = 6 -11    := subst (fun z ↦ z=6-11 )     (add_zero (2*x)  : 2*x+0=2*x      )  h3
      have h5:  2*x           = -5       := subst (fun z ↦ 2*x=z )      (by norm_num     : (6:ℝ)-11=-5    )  h4
      have h6:  2*x/2         = -5/2     := subst (fun z => 2*x/2 = z/2) (h5: 2*x = -5)                     (rfl: 2*x/2=2*x/2)
      have h7:  x*2/2         = -5/2     := subst (fun z => z/2 = -5/2) (mul_comm 2 x)                       h6
      have h8:  x             = -5/2     := subst (fun z => z = -5/2)   (mul_div_cancel x (by norm_num: (2:ℝ) ≠ 0 )) h7
      h8      


-- Solution 5 : variante utilisant ▸ qui est une version allegee de subst

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := (h                                            : 2*x+11 = 6             )  ▸ (rfl:2*x+11-11=2*x+11-11 )
      have h2 : 2*x +(11 -11) = 6 -11    := (add_sub_assoc (2*x) 11 11                    : 2*x+11-11 = 2*x+(11-11))  ▸  h1
      have h3:  2*x + 0       = 6 -11    := (sub_self 11                                  : (11:ℝ)-11=0            )  ▸  h2
      have h4:  2*x           = 6 -11    := (add_zero (2*x)                               : 2*x+0=2*x              )  ▸  h3
      have h5:  2*x           = -5       := (by norm_num                                  : (6:ℝ)-11=-5            )  ▸  h4
      have h6:  2*x/2         = -5/2     := (h5                                           : 2*x = -5               )  ▸ (rfl: 2*x/2=2*x/2)
      have h7:  x*2/2         = -5/2     := (mul_comm 2 x                                 : 2*x = x*2              )  ▸  h6
      have h8:  x             = -5/2     := (mul_div_cancel x (by norm_num: (2:ℝ) ≠ 0 )   : x*2/2 = x              )  ▸  h7
      h8      

-- Solution 6 : variante utilisant ▸ sans les annotations de typage

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := h                                            ▸  rfl
      have h2 : 2*x +(11 -11) = 6 -11    := (add_sub_assoc (2*x) _ _ )                   ▸  h1
      have h3:  2*x + 0       = 6 -11    := (sub_self (11:ℝ )     )                      ▸  h2
      have h4:  2*x           = 6 -11    := (add_zero (2*x)       )                      ▸  h3
      have h5:  2*x           = -5       := (by norm_num : (6:ℝ)-11=-5)                  ▸  h4
      have h6:  2*x/2         = -5/2     := (h5)                                         ▸  rfl
      have h7:  x*2/2         = -5/2     := (mul_comm 2 x)                               ▸  h6
      have h8:  x             = -5/2     := (mul_div_cancel x (by norm_num: (2:ℝ) ≠ 0 )) ▸  h7
      h8      

-- Solution 7 : variante utilisant des tactques au lieu des lemmes

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := (h           : 2*x+11 = 6              )  ▸  rfl
      have h2 : 2*x +(11 -11) = 6 -11    := (by ring_nf  : 2*x+11-11 = 2*x+(11-11) )  ▸  h1
      have h3:  2*x + 0       = 6 -11    := (by norm_num : (11:ℝ )-11=0            )  ▸  h2
      have h4:  2*x           = 6 -11    := (by ring_nf  : 2*x+0=2*x               )  ▸  h3
      have h5:  2*x           = -5       := (by norm_num : (6:ℝ)-11=-5             )  ▸  h4
      have h6:  2*x/2         = -5/2     := (h5          : 2*x = -5                )  ▸  rfl
      have h7:  x*2/2         = -5/2     := (by ring_nf  : 2*x=x*2                 )  ▸  h6
      have h8:  x             = -5/2     := (by ring_nf  : x*2/2=x                 )  ▸  h7
      h8      

-- Solution 8 : variante avec moins d'étapes

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := h                       ▸  rfl
      have h5 : 2*x           = -5       := (by norm_num : (6:ℝ)-11=-5) ▸ (by ring_nf : 2*x+11-11 = 2*x)  ▸  h1
      have h6:  2*x/2         = -5/2     := h5                      ▸  rfl
      have h8:  x             = -5/2     := (by ring_nf  : 2*x/2=x) ▸  h6
      h8      

-- Solution 9 : presque la meme chose que la solution 8, la ligne h5 a été raccourcie

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := h                                                ▸  rfl
      have h5 : 2*x           = -5       := (by ring_nf : (2*x+11-11 = 6-11 ) = (2*x = -5))  ▸  h1
      have h6:  2*x/2         = -5/2     := h5                                               ▸  rfl
      have h8:  x             = -5/2     := (by ring_nf  : 2*x/2=x)                          ▸  h6
      h8      

-- Solution 10 : dans la solution 3 peu de lignes se laissent remplacer par des tactiques simples (sans subst ni ▸ )

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := by rw[h]
      have h2:  2*x +(11 -11) = 6 -11    := Eq.trans (add_sub_assoc (2*x) 11 11).symm h1
      have h3:  2*x + 0       = 6 -11    := subst (fun z ↦ 2*x+z=6-11 ) (sub_self 11     : (11:ℝ)-11=0    )  h2
      have h4:  2*x           = 6 -11    := subst (fun z ↦ z=6-11 )     (add_zero (2*x)  : 2*x+0=2*x      )  h3
      have h5:  2*x           = -5       := subst (fun z ↦ 2*x=z )      (by norm_num     : (6:ℝ)-11=-5    )  h4
      have h6:  2*x/2         = -5/2     := by rw[h5]
      have h7:  x*2/2         = -5/2     := subst (fun z => z/2 = -5/2) (mul_comm 2 x)                       h6
      have h8:  x             = -5/2     := subst (fun z => z = -5/2)   (mul_div_cancel x (by norm_num: (2:ℝ) ≠ 0 )) h7
      h8      

-- Solution 11 : seule la tactique linarith vient à bout de tout...

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := by linarith
      have h2:  2*x +(11 -11) = 6 -11    := by linarith
      have h3:  2*x + 0       = 6 -11    := by linarith
      have h4:  2*x           = 6 -11    := by linarith
      have h5:  2*x           = -5       := by linarith
      have h6:  2*x/2         = -5/2     := by linarith
      have h7:  x*2/2         = -5/2     := by linarith
      have h8:  x             = -5/2     := by linarith
      h8      

-- Solution 12 : mais elle ne vous sera pas forcément autorisée...


example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := by linarith
      have h5 : 2*x           = -5       := by linarith
      have h6:  2*x/2         = -5/2     := by linarith
      have h8:  x             = -5/2     := by linarith
      h8      

-- Solution 13 : parce que finalement elle ne laisse parfois pas grand chose à faire !

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      calc  
        x  = -5/2     := by linarith




