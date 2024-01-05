import Mathlib.Data.Nat.Basic 
import Mathlib.Data.Int.Basic 
import Mathlib.Data.Real.Basic 



example : ∀ x:ℝ, ∃ y:ℝ , y>x := 
  λ x:ℝ ↦ 
      Exists.intro (x+1)
        (
          calc 
            x+1 > x   := lt_add_one x
        )

-- Exercice 4.1
example : ∀ u:ℝ, ∃ t:ℝ , t + 1 < u  := 
  λ u:ℝ ↦ 
      Exists.intro (u-2)
        (
          calc 
            (u-2)+1 = u-1  := by ring
            _        < u   := sub_one_lt u
        )



def even (n:ℕ ) : Prop := ∃ k:ℕ, n=2*k

example (n:ℕ) :  n=0 ∨ n > 0 := Or.imp (Eq.symm ) id (eq_or_lt_of_le (zero_le n))

example (p q p' q':Prop) (h:p ∨ q) (hp : p → p') (hq: q→ q') : p' ∨ q' := Or.imp hp hq h

lemma even_zero_or_ge_two : ∀ n:ℕ , even n → (n=0 ∨ n ≥ 2 ) :=
   λ n:ℕ ↦  
     λ h1:even n ↦ 
       have h2 : n ≤ 0 ∨ n ≥ 1   := le_or_gt n 0
       Or.elim h2
       (
         λ h3: n ≤ 0  ↦
           have h4 : n=0 := le_antisymm h3 (zero_le n)

           Or.inl h4
       )
       (
         λ h5  ↦ 
           Exists.elim h1 
           (
             λ (k:ℕ) (h6: n = 2*k) ↦
               have h7 : n ≠ 0 := Nat.pos_iff_ne_zero.mp h5
               have h8 : k ≠ 0 := λ h9 ↦ absurd (calc n = 2*0 := by rw[h6,h9]
                                                      _ = 0 := by  norm_num) h7 
               have h9 : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr h8 
               have h10 : n ≥ 2 := calc
                 n = 2*k := h6
                 _ ≥ 2*1 := Nat.mul_le_mul_left 2 h9
                 _  ≥ 2  := by norm_num 

               Or.inr h10
           )

       )

example : ¬(even 1)  := λ h ↦  absurd (even_zero_or_ge_two 1 h) (by norm_num)







example :  ∀n:ℕ , n^2 ≠ 2  := 
  
  λ n ↦ 
    have : _ := le_or_gt n 1
    Or.elim this
    (
      λ h ↦ 
        have : _ :=     
          calc  
            n^2 ≤ 1^2 := Nat.pow_le_pow_of_le_left h 2 
            _   < 2   := by norm_num

        ne_of_lt this
      
    )
    (
      λ h ↦ 
        have : _ :=     
          calc  
            n^2 ≥ 2^2 := Nat.pow_le_pow_of_le_left h 2 
            _   > 2   := by norm_num

        ne_of_gt this
    ) 





example : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) :=
  λ P Q : Prop ↦ 
    λ h1 : ¬ (P ∨ Q) ↦ 
      And.intro  
        (λ hP :P ↦ absurd (Or.inl hP) h1)
        (λ hQ :Q ↦ absurd (Or.inr hQ) h1)
   


example : ∀ P Q : Prop,  (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
  λ P Q : Prop ↦ 
    λ h1 :  (¬ P) ∧ (¬ Q) ↦ 
      λ h2 : P ∨ Q ↦ 
        Or.elim h2
        (
          λ hP:P ↦ 
            absurd (hP:P) (h1.left: ¬ P)
        )
        (
          λ hQ:Q ↦ 
            absurd (hQ:Q) (h1.right: ¬ Q)
        )





-----------------------------------------------------


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

-- .. on peut justifier

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
example (f:ℝ → ℝ ): ¬ (majoree f ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by unfold majoree ; push_neg ; rfl


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





example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by push_neg ; rfl
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ):= by push_neg ; rfl


example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by 
  constructor
  
  intro h
  push_neg at h
  assumption

  intro h
  push_neg
  assumption


example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ):= by 
  constructor
  
  intro h
  push_neg at h
  assumption

  intro h
  push_neg
  assumption




-- https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/push_neg.20of.20.5Cand.html
set_option push_neg.use_distrib true

example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x ≤ M ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by push_neg ; rfl

-- ou encore:
--def majoree (f:ℝ → ℝ) := ∃ M:ℝ, ∀ x:ℝ , f x ≤ M
example (f:ℝ → ℝ ): ¬ (majoree f ) ↔ (∀ M:ℝ,∃ x:ℝ, f x > M) := by unfold majoree ; push_neg ; rfl



-- Exercice 5.1
-- Complétez en remplaçant sorry par la négation de l'assertion (∃ ... )
-- Tip : en déplaçant le curseur sur 'push_neg', vous verrez apparaitre la solution dans LeanInfoView, mais essayez de ne pas regarder!!
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x > M ) ↔ sorry := by push_neg ; rfl  -- f n'est pas minorée
example (f:ℝ → ℝ ): ¬ (∃ M:ℝ, ∀ x:ℝ , f x > M ) ↔ ∀ M:ℝ, ∃ x:ℝ , f x ≤  M := by push_neg ; rfl  -- f n'est pas minorée

-- Exercice 5.2
-- Complétez en remplaçant sorry par la négation de l'assertion (∃ ... )
example : ¬ (∃ y:ℝ, ∀ x:ℕ  , y > x ) ↔ sorry := by push_neg ; rfl   -- il n'existe pas de réel strictement supérieur à n'importe quel entier naturel
example : ¬ (∃ y:ℝ, ∀ x:ℕ  , y > x ) ↔ ∀ y:ℝ, ∃ x:ℕ  , y ≤ x := by push_neg ; rfl   -- il n'existe pas de réel strictement supérieur à n'importe quel entier naturel

-- Exercice 5.2
-- Complétez en remplaçant sorry par la négation de l'assertion (∃ ... )
example (f:ℝ → ℝ ): ¬ (∃ m:ℝ,∃ M:ℝ, ∀ x:ℝ , (f x ≥ m) ∧ (f x ≤ M)  ) ↔ sorry := by push_neg ; rfl  -- f n'est pas bornée
example (f:ℝ → ℝ ): ¬ (∃ m:ℝ,∃ M:ℝ, ∀ x:ℝ , (f x ≥ m) ∧ (f x ≤ M)  ) ↔ ∀ (m M : ℝ), ∃ x, ((f x < m) ∨  (M < f x) ):= by push_neg ; rfl  -- f n'est pas bornée

example (P Q : Prop) : (P → ¬ Q) ↔   (¬ P ∨ ¬ Q) := imp_iff_not_or  -- by library_search  -- by tauto
example (P Q : Prop) : ¬ (P ∧ Q ) ↔   (¬ P ∨ ¬ Q) := by push_neg ;rfl




-- 12_tuto.lean
-- Exercice 1.4
-- (a) Montrez le lemme suivant
lemma and_iff_of_imp : ∀ P Q :Prop,  (P → Q) → ((P ∧ Q) ↔ P) := 
  λ P Q : Prop ↦ 
    λ h : P → Q ↦
      Iff.intro
      (
        λ h1 : P ∧ Q ↦
          h1.left
      )
      (
        λ h2: P ↦  
          have h3 : Q := h h2
          And.intro h2 h3
      )  

-- (b) Montrez le lemme suivant
example : ∀ a b :ℝ ,(a ≤ b) → (∀ x:ℝ,  x ≥ b → x ≥ a ) :=
  λ _ _ h _ i ↦ le_trans h i

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
    and_iff_of_imp (s ≥ 3) (s ≥ 2) (imp_of_le 2 3 (by norm_num) s)

example : ∀ s:ℝ,  (s ≥ 3 ∧ s ≥ 2) ↔ (s ≥ 3)  := 
  λ s:ℝ ↦ 
    have h : s ≥ 3 → s ≥ 2 := imp_of_le 2 3 (by norm_num) s
    and_iff_of_imp (s ≥ 3) (s ≥ 2) h











theorem not_forall_not_esisar (α : Type) (P : α → Prop) : ¬ (∀ x:α, ¬ P x) ↔ ∃ x:α, P x := 
  Iff.intro
    (
      λ hnf : ¬ (∀ x:α, ¬ P x) ↦ 
        have hnne : ¬¬  (∃ x:α, P x) :=
                      λ hne : ¬ (∃ x:α, P x) ↦
                      have hf : ∀ x:α, ¬ P x := λ x:α  ↦ (( λ hPx : P x ↦  absurd (Exists.intro x hPx) hne) : ¬(P x) )
                      absurd hf hnf
        of_not_not hnne
    )
    (
      λ hePx : ∃ x:α, P x   ↦  
        λ hf : ∀ x:α, ¬ P x    ↦ 
          Exists.elim hePx (
            λ (x:α)   (hPx : P x )  ↦ 
              have hnPx : ¬ P x  := hf x 
              absurd hPx hnPx 
          )
    )



theorem not_forall_esisar (α : Type) (P : α → Prop) : ¬ (∀ x:α, P x) ↔ ∃ x:α, ¬ P x := 
  Iff.intro
    (
      λ hnf : ¬ (∀ x:α, P x) ↦ 
        of_not_not (
          λ hne : ¬ (∃ x:α, ¬ P x) ↦
          have hf : ∀ x:α, P x := λ x:α  ↦  of_not_not (λ hnPx : ¬ (P x) ↦  absurd (Exists.intro x hnPx) hne )
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



theorem not_exists_not_esisar (α : Type) (P : α → Prop) : ¬ (∃ x:α, ¬ P x) ↔ ∀ x:α, P x := 
  Iff.intro
    (
      λ hne : ¬ (∃ x:α, ¬ P x) ↦ 
        λ x : α              ↦ 
          have hnnPx : ¬¬(P x)  :=
                λ hnPx : ¬ (P x)   ↦
                  have he : ∃ x:α, ¬ P x := Exists.intro x hnPx  
                  absurd he hne
          of_not_not hnnPx
    )
    (
      λ hfx : ∀ x:α, P x   ↦  
        λ he : ∃ x:α, ¬ P x    ↦ 
          Exists.elim he (
            λ (x:α)   (hnPx : ¬( P x) )  ↦ 
              have hPx : P x  := hfx x 
              absurd hPx hnPx 
          )
    )







-- 12_tuto.lean
-- ex 5



-- Exercice 5.3
-- Vrai ou faux :une et une seule des deux assertions suivantes à prouver :

example :    ∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2 := sorry 

example : ¬ (∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2) :=  
   -- si vous choisissez cette assertion à prouver, 
   -- l'utilisation du lemme not_forall permet de ramener une preuve de ¬ ∀ ... à une preuve de ∃ ...
  not_forall.mpr (  
    Exists.intro sorry (
      sorry
   )
  )

example : ¬ (∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2) :=  
   -- si vous choisissez cette assertion à prouver, 
   -- l'utilisation du lemme not_forall permet de ramener une preuve de ¬ ∀ ... à une preuve de ∃ ...
  not_forall.mpr (  
    Exists.intro sorry (
      not_forall.mpr (
        Exists.intro sorry (
          sorry
        )
      )
   )
  )

example : ¬ (∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2) := 
  not_forall.mpr (  
    Exists.intro 2 (
      not_forall.mpr (
        Exists.intro 1 (
          by norm_num
        )
      )
   )
  )

example : ¬ (∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2) := by
  push_neg
  use 1
  use 2
  norm_num

example : ¬ (∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2) := by
  push_neg
  exact (
    Exists.intro 1 (
      Exists.intro 2 (
        by norm_num
      )
    )

  )


-- Exercice 5.3

-- (a) Vrai ou faux :une et une seule des deux assertions suivantes à prouver :

def P : Prop := ∀ u:ℝ, ∀ b:ℝ, (u+b)^2 = u^2 + b^2

example :    P := 
  λ u:ℝ  ↦  
    λ b:ℝ  ↦  
      sorry 

example : ¬ P :=  
   -- si vous choisissez cette assertion à prouver, 
   -- l'utilisation du lemme not_forall permet de ramener une preuve de ¬ ∀ ... à une preuve de ∃ ...
  not_forall.mpr (  
    Exists.intro 1 ( 
      not_forall.mpr (  
        Exists.intro 2 ( 
          by norm_num
        )
      )
    )
  )

-- (b) Vrai ou faux :une et une seule des deux assertions suivantes à prouver :
def Q : Prop := ∀ u:ℝ, ∀ b:ℝ, (u+b)^2 ≠ u^2 + b^2

example :    Q := sorry 
example : ¬ Q  :=  
  not_forall.mpr (  
    Exists.intro 1 ( 
      not_forall.mpr (  
        Exists.intro 0 ( 
          by norm_num
        )
      )
    )
  )

-- (c)  : commentaire : P et Q sont-elles contraires  ? expliquez















inductive EtatAmpoule where
  | saine   : EtatAmpoule
  | grillee : EtatAmpoule

inductive EtatLumiere where
  | allumee   : EtatLumiere
  | eteinte   : EtatLumiere

inductive EtatInterrupteur where
  | on    : EtatInterrupteur
  | off   : EtatInterrupteur

structure Systeme where
  amp : EtatAmpoule
  lum : EtatLumiere 
  int : EtatInterrupteur

axiom A1 : ∀ s:Systeme, s.int = EtatInterrupteur.off →  s.lum = EtatLumiere.eteinte
axiom A2 : ∀ s:Systeme, s.int = EtatInterrupteur.on → s.amp = EtatAmpoule.saine  →  s.lum = EtatLumiere.allumee

lemma test3 (s:Systeme) : s.lum = EtatLumiere.allumee ∨ s.lum = EtatLumiere.eteinte  :=
      match s.lum with
      | EtatLumiere.eteinte   =>  Or.inr (by aesop)
      | EtatLumiere.allumee   =>  Or.inl (by aesop)
#print test3
#check eq_self
lemma test3' (s:Systeme) : s.lum = EtatLumiere.allumee ∨ s.lum = EtatLumiere.eteinte  :=
      match s.lum with
      | EtatLumiere.eteinte   =>  Or.inr (rfl)
      | EtatLumiere.allumee   =>  Or.inl (rfl)
#print test3'


lemma test3'' (s:Systeme) : s.lum = EtatLumiere.allumee ∨ s.lum = EtatLumiere.eteinte  :=
      match s.lum with
      | EtatLumiere.eteinte   =>  Or.inr (rfl)
      | EtatLumiere.allumee   =>  Or.inl (rfl)

lemma test3''' (s:Systeme) : s.lum = EtatLumiere.allumee ∨ s.lum = EtatLumiere.eteinte  :=
      match s.lum with
      | EtatLumiere.eteinte   =>  
           have hr1 : s.lum = EtatLumiere.eteinte := rfl
           Or.inr (hr1)
      | EtatLumiere.allumee   =>  Or.inl (rfl)

#check @EtatLumiere.rec

--lemma test3'''' (s:Systeme) : s.lum = EtatLumiere.allumee ∨ s.lum = EtatLumiere.eteinte  := by aesop

lemma test4 : EtatLumiere.allumee ≠  EtatLumiere.eteinte := by aesop
#print test4
#check EtatLumiere.noConfusion
#print EtatLumiere.noConfusionType
#print noConfusionTypeEnum
#check EtatLumiere.toCtorIdx
lemma test4' : EtatLumiere.allumee ≠  EtatLumiere.eteinte := by norm_num
#print test4' 
#check eq_false'
theorem test4'' : EtatLumiere.allumee ≠ EtatLumiere.eteinte :=
    of_eq_true
      (Eq.trans (congrArg Not (eq_false' fun h => EtatLumiere.noConfusion h))
        (Eq.trans not_false_eq_true (eq_true True.intro)))

theorem test4''' : (EtatLumiere.allumee ≠ EtatLumiere.eteinte) = True :=
   calc
     _ = ¬ False := congrArg Not (eq_false' fun h => EtatLumiere.noConfusion h)
     _ = True    := not_false_eq_true

theorem test4'''' : (EtatLumiere.allumee = EtatLumiere.eteinte) →  False :=
    fun h => EtatLumiere.noConfusion h

theorem test4''''' : (EtatLumiere.allumee = EtatLumiere.allumee) →  (False → False) :=
    fun h => EtatLumiere.noConfusion h



lemma L1 : ∀ s:Systeme, s.lum = EtatLumiere.allumee  →  s.int = EtatInterrupteur.on :=      -- L1 est vraie
  λ s : Systeme ↦ 
    λ h : s.lum = EtatLumiere.allumee ↦ 
      match s.int with
      | EtatInterrupteur.off  =>
                                 absurd
                                    (((A1 s rfl ) :  s.lum = EtatLumiere.eteinte)   ) 
                                    (fun h1 => EtatLumiere.noConfusion (Eq.trans h.symm h1) )
      | EtatInterrupteur.on   =>  rfl

lemma L2 : ∀ s:Systeme,   ¬ s.int = EtatInterrupteur.on → ¬ s.lum = EtatLumiere.allumee :=  -- contraposee de L1 : vraie (car L1 est vraie)
  sorry

lemma L3 : ∀ s:Systeme,  ¬ (s.int = EtatInterrupteur.on → s.lum = EtatLumiere.allumee) :=   -- la réciproque de L1 est fausse (pourtant L1 est vraie)
  sorry







lemma not_imp_not_esisar' :  ∀ P Q : Prop,  (¬Q → ¬P) ↔(P→ Q)  := 
   λ P Q : Prop ↦ 
     Iff.intro
     (
       λ hc:  ¬Q → ¬P ↦ 
         λ hP: P ↦
           of_not_not ( 
             λ hnQ : ¬ Q ↦   
               have hnP : ¬ P := hc hnQ 
               absurd hP hnP
            )  
     )
     (
       λ hd:  P → Q ↦ 
         λ hnQ : ¬ Q ↦ 
           λ hP : P ↦
             have hQ : Q := hd hP
             absurd hQ hnQ
     )






def P82' : Prop := (-2)=2
def Q82' : Prop := (-2)^2=4
def A82' : Prop := P82' → Q82'
def R82' : Prop := Q82' → P82' 
example : A82' := λ h : (-2) = 2 ↦ (by norm_num : (-2)^2 =4)
example : ¬ R82' := λ (h: R82') ↦ absurd (h (by norm_num : (-2)^2 = 4)) (by norm_num : (-2)≠ 2)










------------------------------------------------------------------
--- Exemple 9
------------------------------------------------------------------
-- Nouvelles notions
--   formulation de l'implication avec ¬ et ∨ 
--   négation d'une implication

example : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := λ _ _ ↦ not_imp  

lemma imp_of_not : ∀ P Q : Prop,  (¬ P) →  (P → Q) := 
  λ P Q : Prop ↦
   λ hnP : ¬ P  ↦ 
     λ hP: P ↦  
       absurd hP hnP

lemma imp_of_ccl : ∀ P Q : Prop,  Q →  (P → Q) := 
  λ P Q:Prop ↦
   λ hQ : Q  ↦ 
     λ hP: P ↦  
       hQ


example : ∀ P Q : Prop,   (P → Q)→ (¬ P ∨ Q)  := λ _ _ ↦ not_or_of_imp 

#check not_or_of_imp

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
  
#check imp_iff_not_or
example : ∀ P Q : Prop,   (P → Q) ↔ (¬ P ∨ Q)  := λ _ _ ↦ imp_iff_not_or

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
    





--Exercice 9.3
-- Les lois de De Morgan précedemment vues donnent que ¬ (¬ P ∨ Q ) équivaut à .... (complétez sans regarder l'exercice 9.4 !!)
example (P Q: Prop) : ¬ (¬ P ∨ Q ) ↔ (P ∧ ¬ Q  ) := by push_neg ; rfl


--Exercice 9.5

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



-- Exercice 8.3
-- Exemple : prouvez par la contraposée que : pour tout entier naturel n, si n^2 est pair alors n est pair

--def pair   (n:ℕ) : Prop := ∃ k:ℕ , n=2*k
--def impair (n:ℕ) : Prop := ∃ k:ℕ , n=2*k+1
def pair   (n:ℕ) : Prop := Even n
def impair (n:ℕ) : Prop := Odd n

example (n:ℕ) : pair n ↔   (∃ k:ℕ , n=k+k)   := Iff.rfl
example (n:ℕ) : impair n ↔ (∃ k:ℕ , n=2*k+1) := Iff.rfl

example : ∀ n:ℕ,  pair (n^2) → pair n :=
  λ n:ℕ  ↦ 
    not_imp_not.mp 
    (
      λ hne : ¬ pair n ↦
        have hi : impair n := Nat.odd_iff_not_even.mpr hne
        Exists.elim hi 
        (
          λ (k:ℕ) (h: n = 2*k+1) ↦ 
            have h_n2 : n^2 = 2*(2*k^2+2*k)+1 :=
              calc 
                n^2 = (2*k+1)^2        := by rw[h]
                _   = 2*(2*k^2+2*k)+1  := by ring_nf

            have h_n2i : impair (n^2) :=
              Exists.intro (2*k^2+2*k) h_n2
            
            Nat.odd_iff_not_even.mp h_n2i
        )
    )
    



-- Exercice 9.6
-- Donnons d'abord la définition (que nous reverrons plus tard) d'une suite réelle tendant vers +infini

def tend_vers_plus_infini (u: ℕ → ℝ) : Prop := ∀ A:ℝ, ∃ n0:ℕ, ∀ n:ℕ , n ≥ n0 → (u n) ≥ A  

-- L'objectif n'est pas de comprendre maintenant la signification d'une telle assertion, mais 
-- d'exprimer mécaniquement sa négation.

example (u:ℕ → ℝ) : ¬ (tend_vers_plus_infini u) ↔ ( ∃ A:ℝ, ∀ n0:ℕ, ∃ n:ℕ , n ≥ n0 ∧  (u n) < A ) := by unfold tend_vers_plus_infini; push_neg ; rfl






-- Exercice 9.5
-- Donnez la négation de ∀ x :ℝ , P x → Q x
example (P Q: ℝ →  Prop) : ¬(∀ x:ℝ , P x → Q x) ↔ (sorry) := by push_neg ; rfl
example (P Q: ℝ → Prop) : ¬(∀ x:ℝ , P x → Q x) ↔ (∃x:ℝ, P x ∧ (¬ Q x )   ) := by push_neg ; rfl







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



-- Exercice 10.1

-- On reprend ici l'exercice : TD1.1 ex8
--   Peut-on trouver deux réels a et b tels que
--     ∀x ∈ R, a sin(x) + b cos(x) = sin(2x)
-- Conjecture: on ne peut pas, on le prouve par l'absurde
-- Pour utliser sin et cos, on a besoin d'importer en début de fichier :
--    import Mathlib.Data.Complex.Exponential
--    import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- puis :
open Real

-- les lemmes suivants sont utiles :
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



-- Exemple

-- On reprend ici l'exercice : TD1.1 ex8
--   Peut-on trouver deux réels a et b tels que
--     ∀x ∈ R, a sin(x) + b cos(x) = sin(2x)
-- Conjecture: on ne peut pas, on le prouve par l'absurde
-- Pour utliser sin et cos, on a besoin d'importer en début de fichier :
--    import Mathlib.Data.Complex.Exponential
--    import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- puis :
open Real

-- les lemmes suivants sont utiles :
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

-- Exercice 10.1
#check exp_zero
#check exp_neg

#check neg_eq_of_add_eq_zero_right
example (a b:ℝ ) (h:b≠ 0) : a*b⁻¹ = a/b := by exact rfl


-- Montrez qu'on ne peut pas trouver deux réels a et b tels que 
--    ∀x:ℝ, a * (exp x) + b*(exp (-x)) = x^2)
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
                        = a*(exp (-1))+b*e             := by rw [exp_neg 1]
                _       = a*(exp (-1))+b*(exp (-(-1))) := by norm_num
                _       = (-1)^2                       := h'' (-1)
                _       = 1                            := by norm_num
            have h0' : b =-a :=  (neg_eq_of_add_eq_zero_right h0).symm
            have he' : a*(e-1/e) = 1 :=
              calc
                a*(e-1/e) = a*e+(-a)/e := by ring
                _         = a*e+b/e    := by rw[h0']
                _         = 1          := by rw[he]
            have h1e' : a*(e-1/e) = -1 :=
              calc
                a*(e-1/e) = -(a/e -a*e) := by ring
                _         = -(a/e +b*e) := by rw[h0']
                _         = -1          := by rw[h1e]
            have ha : 1 = -1 :=
              calc 
                1 = a*(e-1/e)  := he'.symm
                _ = -1         := h1e'
              
            absurd ha (by norm_num)
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
example (a b c:ℝ  ) (h1 : a≤b  ) (h2 : c≥ 0) : a*c ≤ b*c :=  mul_le_mul_of_nonneg_right h1 h2 
example (a b c:ℝ  ) (h1 : a≤b  ) (h2 : c≥ 0) : a+c ≤ b+c :=  add_le_add_right h1 c
example (a b:ℝ  ) (h1 : 1≤b  ) (k:ℕ ) : 1 ≤ b^k          :=  one_le_pow_of_one_le h1 k
example (a b:ℝ  ) (h1 : 0≤b  ) (k:ℕ ) : 0 ≤ b^k          :=  pow_nonneg h1 k



-- Exemple

example (P : ℕ → ℝ → Prop ) : (∀ n:ℕ , ∀ x:ℝ, P n x) ↔ (∀ x:ℝ, ∀ n:ℕ ,  P n x) :=  forall_swap
example (a b c:ℝ  ) (h1 : a≤b  ) (h2 : c≥ 0) : a*c ≤ b*c :=  mul_le_mul_of_nonneg_right h1 h2 
example (a b c:ℝ  ) (h1 : a≤b  ) (h2 : c≥ 0) : a+c ≤ b+c :=  add_le_add_right h1 c
example (a b:ℝ  ) (h1 : 1≤b  ) (k:ℕ ) : 1 ≤ b^k          :=  one_le_pow_of_one_le h1 k
example (a b:ℝ  ) (h1 : 0≤b  ) (k:ℕ ) : 0 ≤ b^k          :=  pow_nonneg h1 k



-- Montrons par récurrence que :   ∀ x:ℝ , x≥-1 →  ∀ n:ℕ, (1+x)^n ≥ n*x


example : ∀ x:ℝ , x≥-1 →  ∀ n:ℕ, (1+x)^n ≥ n*x :=
  λ x:ℝ ↦ 
    λ h: x ≥ -1 ↦ 
      Or.elim (le_or_gt 0 x)
      (
        λ h1 : x ≥  0 ↦ 
          have h' : 1+x ≥ 1 := 
            calc 
              1+x ≥ 1+0 := add_le_add_left h1 1
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
      (
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

example (k:ℕ ) : 2*2^k = 2^(k+1) := by exact Eq.symm Nat.pow_succ'

-- Conjecturez un rang n0 pour lequel : ∀ n:ℕ , n≥ n0 → P n
-- La récurrence à partir d'un certain rang n0 se prouve avec Nat.le_induction  (au lieu de Nat.rec)
-- On lui fournit:
--   * une preuve de P n0
--   * une preuve de ∀ k:ℕ , k ≥ n0 → P k → P (k+1)

-- et elle renvoie :
--   une preuve de ∀ n:ℕ , n ≥ n0 → P n

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


-- Exercice 11.x
example : ∀ n:ℕ , n ≥ 5 → 2^n > 5*(n+1) :=
  sorry











-- Différentes solutions à l'exercice 1.1

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

example (a b c :ℝ ): a +b-c = a+(b -c) := by library_search
example (a b c :ℝ ): a -a = 0 := by library_search


-- Solution 3 :  sans calc, comme vous avez l'habitude , avec "have" ("on a"), très détaillé

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
      have h1:  2*x +11 -11   = 6 -11    := (h:2*x+11 = 6)                                         ▸  (rfl:2*x+11-11=2*x+11-11 )
      have h2 : 2*x +(11 -11) = 6 -11    := (add_sub_assoc (2*x) 11 11 : 2*x+11-11 = 2*x+(11-11))  ▸  h1
      have h3:  2*x + 0       = 6 -11    := (sub_self 11     : (11:ℝ)-11=0    )                    ▸  h2
      have h4:  2*x           = 6 -11    := (add_zero (2*x)  : 2*x+0=2*x      )                    ▸  h3
      have h5:  2*x           = -5       := (by norm_num     : (6:ℝ)-11=-5    )                    ▸  h4
      have h6:  2*x/2         = -5/2     := (h5: 2*x = -5)                                         ▸  (rfl: 2*x/2=2*x/2)
      have h7:  x*2/2         = -5/2     := (mul_comm 2 x)                                         ▸  h6
      have h8:  x             = -5/2     := (mul_div_cancel x (by norm_num: (2:ℝ) ≠ 0 ))           ▸  h7
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
      have h1:  2*x +11 -11   = 6 -11    := h                                         ▸  rfl
      have h2 : 2*x +(11 -11) = 6 -11    := (by ring_nf  :  2*x+11-11 = 2*x+(11-11) ) ▸  h1
      have h3:  2*x + 0       = 6 -11    := (by norm_num : (11:ℝ )-11=0    )          ▸  h2
      have h4:  2*x           = 6 -11    := (by ring_nf  : 2*x+0=2*x )                ▸  h3
      have h5:  2*x           = -5       := (by norm_num : (6:ℝ)-11=-5)               ▸  h4
      have h6:  2*x/2         = -5/2     := h5                                        ▸  rfl
      have h7:  x*2/2         = -5/2     := (by ring_nf  : 2*x=x*2)                   ▸  h6
      have h8:  x             = -5/2     := (by ring_nf  : x*2/2=x)                   ▸  h7
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

-- Solution 10 : dans la solution 3 peu de lignes se laissent remplacer par des tactiques simples

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





-- Mixte Draft
example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      have h1:  2*x +11 -11   = 6 -11    := congr_arg (fun z ↦ z-11)  h
      have h1': 2*x +11 -11   = 6 -11    := subst (fun z ↦ 2*x+11-11 = z-11) (h:2*x+11 = 6)                 (rfl:2*x+11-11=2*x+11-11 )
      have h2:  2*x +(11 -11) = 6 -11    := Eq.trans (add_sub_assoc (2*x) 11 11).symm h1
      have h2': 2*x +(11 -11) = 6 -11    := subst (fun z ↦ z = 6-11)    (add_sub_assoc (2*x) 11 11 : 2*x+11-11 = 2*x+(11-11))    h1
      have h3:  2*x + 0       = 6 -11    := subst (fun z ↦ 2*x+z=6-11 ) (sub_self 11     : (11:ℝ)-11=0    )  h2
      have h4:  2*x           = 6 -11    := subst (fun z ↦ z=6-11 )     (add_zero (2*x)  : 2*x+0=2*x      )  h3
      have h5:  2*x           = -5       := subst (fun z ↦ 2*x=z )      (by norm_num     : (6:ℝ)-11=-5    )  h4
      have h6:  2*x/2         = -5/2     := subst (fun z => 2*x/2 = z/2) (h5: 2*x = -5)                     (rfl: 2*x/2=2*x/2)
      have h6': 2*x/2         = -5/2     := congr_arg (fun z => z/2) h5
      have h7:  x*2/2         = -5/2     := subst (fun z => z/2 = -5/2) (mul_comm 2 x)                       h6
      have h8:  x             = -5/2     := subst (fun z => z = -5/2)   (mul_div_cancel x (by norm_num: (2:ℝ) ≠ 0 )) h7
      h8      


