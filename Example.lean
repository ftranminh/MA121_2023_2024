import Esisar.Basic
--import Mathlib.Data.Real.Basic

#check (4:ℝ) 
--#check (x↦x+1 )
#check (fun x↦x+1 )
#check Real.sin
--#check XX

lemma L : a+1=1+a := sorry



example : ∀ x:ℝ, 3*x+4=2 → x=-2/3   :=    

  soit x:ℝ , 
    supposons h:3*x+4=2 ,
    
      calc
        x = (3*x+4-4)/3 := by ring_nf     
        _ = (2  -4)/3   := by rw[h]       
        _ = -2/3        := by norm_num    


set_option push_neg.use_distrib true
--example (f:ℝ → ℝ ): ¬ (∃ m:ℝ,∃ M:ℝ, ∀ x:ℝ , (f x ≥ m) ∧ (f x ≤ M)  ) ↔ sorry := by push_neg ; rfl  -- f n'est pas bornée
example (f:ℝ → ℝ ): ¬ (∃ m:ℝ,∃ M:ℝ, ∀ x:ℝ , (f x ≥ m) ∧ (f x ≤ M)  ) ↔ ∀ (m M : ℝ), ∃ x, ((f x < m) ∨  (M < f x) ):= by push_neg ; rfl  -- f n'est pas bornée
