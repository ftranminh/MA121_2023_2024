import Mathlib.Data.Real.Basic

/-
import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic 
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic 
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-/

lemma subst.{v}  {α : Sort v} (motive : α → Prop) {a b : α} (h₁ : a = b) (h₂ : motive a) : motive b
  := @Eq.subst α motive a b h₁ h₂ 

theorem iff_arg.{u}   {α : Sort u}  {a₁ a₂ : α} (f : α → Prop) :  a₁ = a₂ → (f a₁ ↔ f a₂) := 
    λ h => 
      subst  (fun z ↦ (f a₁ ↔ f z)  ) h (Iff.refl _)


namespace chap3

  def absQ (x:ℚ  ) : ℚ  := ite (x ≥ 0)  x (-x)
  def maxQ (a b:ℚ) : ℚ  := ite (a ≥ b)  a b
  def minQ (a b:ℚ) : ℚ  := ite (a ≤ b)  a b
  noncomputable def abs (x:ℝ  ) : ℝ := ite (x ≥ 0)  x (-x)
  noncomputable def max (a b:ℝ) : ℝ := ite (a ≥ b)  a b
  noncomputable def min (a b:ℝ) : ℝ := ite (a ≤ b)  a b

  lemma abs_of_neg  {x:ℝ} (h:x<0) : abs x = -x := if_neg (not_le_of_lt h)
  lemma abs_zero                 : abs 0 = 0  := if_pos (le_refl 0)
  lemma abs_of_pos  {x:ℝ} (h:x>0) : abs x = x  := if_pos (le_of_lt h)

  lemma max_of_lt       {a b:ℝ} (h:a<b) : max a b = b := if_neg (not_le_of_lt h)
  lemma max_self        {a :ℝ}          : max a a = a := if_pos (le_refl a)
  lemma max_of_eq_left  {a b:ℝ} (h:a=b) : max a b = a := h ▸ max_self
  lemma max_of_eq_right {a b:ℝ} (h:a=b) : max a b = b := h ▸ max_self
  lemma max_of_gt       {a b:ℝ} (h:a>b) : max a b = a := if_pos (le_of_lt h)

  lemma min_of_gt       {a b:ℝ} (h:a>b) : min a b = b := if_neg (not_le_of_lt h)
  lemma min_self        {a :ℝ}          : min a a = a := if_pos (le_refl a)
  lemma min_of_eq_left  {a b:ℝ} (h:a=b) : min a b = a := h ▸ min_self
  lemma min_of_eq_right {a b:ℝ} (h:a=b) : min a b = b := h ▸ min_self
  lemma min_of_lt       {a b:ℝ} (h:a<b) : min a b = a := if_pos (le_of_lt h)

  lemma abs_of_nonneg  {x:ℝ} (h:x≥0) : abs x = x  := if_pos h

--lemma Z : (0:ℝ )=-(0:ℝ ) := by exact Iff.mpr zero_eq_neg rfl
--#check zero_eq_neg


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
    

  lemma max_of_le  {a b:ℝ} (h:a≤b) : max a b = b := 
    Or.elim (lt_or_eq_of_le h)
    (
      λ h_lt  : a< b ↦ 
       max_of_lt h_lt
    )
    (
      λ h_eq  : a = b ↦ 
        max_of_eq_right h_eq
    )
  lemma max_of_ge  {a b:ℝ} (h:a≥b) : max a b = a := if_pos h

  lemma max_ge_left {a b:ℝ} : max a b ≥ a :=
    dite (a ≥ b)
    (
      λ h ↦ 
       (max_of_ge h).symm ▸  le_refl a
    )
    (  
      λ h ↦ 
       (max_of_lt (lt_of_not_ge h)).symm ▸  (le_of_lt (lt_of_not_ge h))
    )

  lemma max_ge_right {a b:ℝ} : max a b ≥ b :=
    dite (a ≥ b)
    (  
      λ h ↦ 
       (max_of_ge h).symm ▸  h
    )
    (
      λ h ↦ 
       (max_of_lt (lt_of_not_ge h)).symm ▸  le_refl b
    )

  lemma min_of_ge  {a b:ℝ} (h:a≥b) : min a b = b := 
    Or.elim (gt_or_eq_of_le h)
    (
      λ h_gt  : a > b ↦ 
       min_of_gt h_gt
    )
    (
      λ h_eq  : a = b ↦ 
        min_of_eq_right h_eq
    )
  lemma min_of_le  {a b:ℝ} (h:a ≤ b) : min a b = a := if_pos h

  lemma min_le_left {a b:ℝ} : min a b ≤ a :=
    dite (a ≤ b)
    (
      λ h ↦ 
       (min_of_le h).symm ▸  le_refl a
    )
    (  
      λ h ↦ 
       (min_of_gt (lt_of_not_ge h)).symm ▸  (le_of_lt (lt_of_not_ge h))
    )

  lemma min_le_right {a b:ℝ} : min a b ≤ b :=
    dite (a ≤ b)
    (  
      λ h ↦ 
       (min_of_le h).symm ▸  h
    )
    (
      λ h ↦ 
       (min_of_gt (lt_of_not_ge h)).symm ▸  le_refl b
    )


  lemma max_comm  { a b: ℝ } : max a b = max b a := 
    dite (a ≥ b)
    (
      λ h ↦
        calc
          max a b = a       := max_of_ge h
          _       = max b a := (max_of_le h).symm
    )
    (
      λ h ↦
        have h' : a<b := lt_of_not_ge h
        calc
          max a b = b       := max_of_lt h'
          _       = max b a := (max_of_gt h').symm
    )

  lemma min_comm  { a b: ℝ } : min a b = min b a := 
    dite (a ≤ b)
    (
      λ h ↦
        calc
          min a b = a       := min_of_le h
          _       = min b a := (min_of_ge h).symm
    )
    (
      λ h ↦
        have h' : a>b := lt_of_not_ge h
        calc
          min a b = b       := min_of_gt h'
          _       = min b a := (min_of_lt h').symm
    )

  lemma max_le_iff { a b c :ℝ } : max a b ≤ c ↔ (a ≤ c ∧ b ≤ c ) :=
     Iff.intro
     (
      λ h ↦
        And.intro
          (
            calc 
              a ≤ max a b := max_ge_left
              _ ≤ c       := h
          )
          (
            calc 
              b ≤ max a b := max_ge_right
              _ ≤ c       := h
          )
     )
     (
      λ h ↦
        dite (a ≥ b)
        (
          λ hab ↦ 
            (max_of_ge hab).symm ▸ h.left
        )
        (
          λ hab' ↦ 
            (max_of_lt (lt_of_not_ge hab')).symm ▸ h.right
        )
     )

  lemma max_lt_iff { a b c :ℝ } : max a b < c ↔ (a < c ∧ b < c ) :=
     Iff.intro
     (
      λ h ↦
        And.intro
          (
            calc 
              a ≤ max a b := max_ge_left
              _ < c       := h
          )
          (
            calc 
              b ≤ max a b := max_ge_right
              _ < c       := h
          )
     )
     (
      λ h ↦
        dite (a ≥ b)
        (
          λ hab ↦ 
            (max_of_ge hab).symm ▸ h.left
        )
        (
          λ hab' ↦ 
            (max_of_lt (lt_of_not_ge hab')).symm ▸ h.right
        )
     )

  lemma min_ge_iff { a b c :ℝ } : min a b ≥ c ↔ (a ≥ c ∧ b ≥ c ) :=
     Iff.intro
     (
      λ h ↦
        And.intro
          (
            calc 
              a ≥  min a b := min_le_left
              _ ≥ c       := h
          )
          (
            calc 
              b ≥ min a b := min_le_right
              _ ≥ c       := h
          )
     )
     (
      λ h ↦
        dite (a ≤ b)
        (
          λ hab ↦ 
            (min_of_le hab).symm ▸ h.left
        )
        (
          λ hab' ↦ 
            (min_of_gt (lt_of_not_ge hab')).symm ▸ h.right
        )
     )

  lemma min_gt_iff { a b c :ℝ } : min a b > c ↔ (a > c ∧ b > c ) :=
     Iff.intro
     (
      λ h ↦
        And.intro
          (
            calc 
              a ≥  min a b := min_le_left
              _ > c       := h
          )
          (
            calc 
              b ≥ min a b := min_le_right
              _ > c       := h
          )
     )
     (
      λ h ↦
        dite (a ≤ b)
        (
          λ hab ↦ 
            (min_of_le hab).symm ▸ h.left
        )
        (
          λ hab' ↦ 
            (min_of_gt (lt_of_not_ge hab')).symm ▸ h.right
        )
     )

  lemma max_assoc { a b c: ℝ } : max a (max b c) = max (max a b) c:= 
    dite (a ≥ b )
    (
      λ hab ↦ 
        dite (a ≥ c )
        (
          λ hac ↦ 
            have h1 : max b c ≤ a         := max_le_iff.mpr ⟨ hab, hac⟩ 
            have h2 : max a (max b c) = a := max_of_ge h1
            have h3 : max (max a b) c = a := (max_of_ge hab).symm ▸ (max_of_ge hac)
            Eq.trans h2 h3.symm
        )
        (
          λ hac' ↦ 
            have hca : c ≥ a := le_of_lt (lt_of_not_ge hac')
            have h1 : c ≥ b := le_trans hab hca
            have h2 : max a (max b c) = c := (max_of_le h1).symm  ▸ (max_of_le hca) 
            have h3 : max (max a b) c = c := (max_of_ge hab).symm ▸ (max_of_le hca)
            Eq.trans h2 h3.symm
        )
    )
    (
      λ hab' ↦ 
        have hba : b ≥ a := le_of_lt (lt_of_not_ge hab')
        dite (b ≥ c )
        (
          λ hbc ↦ 
            have h2 : max a (max b c) = b := (max_of_ge hbc).symm ▸ (max_of_le hba) 
            have h3 : max (max a b) c = b := (max_of_le hba).symm ▸ (max_of_ge hbc)
            Eq.trans h2 h3.symm
        )
        (
          λ hbc' ↦ 
            have hcb : c ≥ b := le_of_lt (lt_of_not_ge hbc')
            have h1 : c ≥ a := le_trans hba hcb
            have h2 : max a (max b c) = c := (max_of_le hcb).symm ▸ (max_of_le h1) 
            have h3 : max (max a b) c = c := (max_of_le hba).symm ▸ (max_of_le hcb)
            Eq.trans h2 h3.symm
        )
    )

  lemma min_assoc { a b c: ℝ } : min a (min b c) = min (min a b) c:= 
    dite (a ≤ b )
    (
      λ hab ↦ 
        dite (a ≤ c )
        (
          λ hac ↦ 
            have h1 : min b c ≥  a        := min_ge_iff.mpr ⟨ hab, hac⟩ 
            have h2 : min a (min b c) = a := min_of_le h1
            have h3 : min (min a b) c = a := (min_of_le hab).symm ▸ (min_of_le hac)
            Eq.trans h2 h3.symm
        )
        (
          λ hac' ↦ 
            have hca : c ≤ a := le_of_lt (lt_of_not_ge hac')
            have h1  : c ≤ b := le_trans hca hab
            have h2  : min a (min b c) = c := (min_of_ge h1).symm  ▸ (min_of_ge hca) 
            have h3  : min (min a b) c = c := (min_of_le hab).symm ▸ (min_of_ge hca)
            Eq.trans h2 h3.symm
        )
    )
    (
      λ hab' ↦ 
        have hba : b ≤ a := le_of_lt (lt_of_not_ge hab')
        dite (b ≤ c )
        (
          λ hbc ↦ 
            have h2 : min a (min b c) = b := (min_of_le hbc).symm ▸ (min_of_ge hba) 
            have h3 : min (min a b) c = b := (min_of_ge hba).symm ▸ (min_of_le hbc)
            Eq.trans h2 h3.symm
        )
        (
          λ hbc' ↦ 
            have hcb : c ≤ b := le_of_lt (lt_of_not_ge hbc')
            have h1 : c ≤ a := le_trans hcb hba
            have h2 : min a (min b c) = c := (min_of_ge hcb).symm ▸ (min_of_ge h1) 
            have h3 : min (min a b) c = c := (min_of_ge hba).symm ▸ (min_of_ge hcb)
            Eq.trans h2 h3.symm
        )
    )



  lemma P_3_1_1_3_i (x:ℝ) : abs x ≥ 0 :=  
   --Or.elim (Classical.em (x≥ 0))
   dite (x ≥ 0)
   (
     λ hp ↦ 
       calc 
         abs x = x  := if_pos hp
         _     ≥ 0  := hp
     
   )
   (
     λ hn ↦ 
       calc
         abs x = -x  := if_neg hn
         _     ≥  0  := neg_nonneg.mpr (le_of_lt (lt_of_not_le hn)) -- by linarith --
   )

  lemma abs_nonneg (x:ℝ) : abs x ≥ 0 := P_3_1_1_3_i x

  lemma P_3_1_1_3_ii (x:ℝ) : abs (abs x) = abs x :=  
    if_pos (P_3_1_1_3_i x)

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
    

  example (x y:ℝ ) (hx : x≥ 0)(hy : y ≤  0) : x*y ≤  0 := by exact mul_nonpos_of_nonneg_of_nonpos hx hy

  lemma P_3_1_1_3_v (x:ℝ)(y:ℝ) : abs (x*y) = (abs x)*(abs y) :=   
    dite (x≥0)
    (
      λ hxp : x≥ 0 ↦ 
        have hax  :  abs x = x  := if_pos hxp
        dite (y≥0)
        (
          λ hyp : y≥ 0 ↦ 
            have hxyp : x*y ≥0 := mul_nonneg hxp hyp
            have hay  :  abs y = y := if_pos hyp
            calc 
              abs (x*y) = x*y             := if_pos hxyp
              _         = (abs x)*(abs y) := by rw[hax,hay]
        )
        (
          λ hyn' : ¬ (y≥ 0) ↦ 
            have hyn : y ≤ 0 := le_of_lt (lt_of_not_le hyn')
            have hxyn : x*y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hxp hyn
            have hay  :  abs y = -y := abs_of_nonpos hyn
            calc 
              abs (x*y) = -(x*y)             := abs_of_nonpos hxyn
              _         = x*(-y)             := by ring_nf
              _         = (abs x)*(abs y) := by rw[hax,hay]
        )
    )
    (
      λ hxn' : ¬ (x≥ 0) ↦ 
        have hxn : x ≤ 0 := le_of_lt (lt_of_not_le hxn')
        have hax  :  abs x = -x := abs_of_nonpos hxn
        dite (y≥0)
          (
            λ hyp : y≥ 0 ↦ 
              have hxyn : x*y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hxn hyp
              have hay  :  abs y = y := if_pos hyp
              calc 
                abs (x*y) = -(x*y)          := abs_of_nonpos hxyn
                _         = (-x)*y          := by ring_nf
                _         = (abs x)*(abs y) := by rw[hax,hay]
          )
          (
            λ hyn' : ¬ (y≥ 0) ↦ 
              have hyn : y ≤ 0        := le_of_lt (lt_of_not_le hyn')
              have hxyp : x*y ≥0      := mul_nonneg_of_nonpos_of_nonpos hxn hyn
              have hay  :  abs y = -y := abs_of_nonpos hyn
              calc 
                abs (x*y) = x*y             := abs_of_nonneg hxyp
                _         = (-x)*(-y)       := by ring_nf
                _         = (abs x)*(abs y) := by rw[hax,hay]
          )
    )

  lemma abs_mul (x:ℝ)(y:ℝ) : abs (x*y) = (abs x)*(abs y) :=   P_3_1_1_3_v x y

/-
  lemma P_3_1_1_3_iv (x:ℝ) : (abs (x^2)) = (abs x)^2 :=   
    calc 
      abs (x^2)  = abs (x*x)       := by ring_nf
      _          = (abs x)*(abs x) := P_3_1_1_3_v x x
      _          = (abs x)^2       := by ring_nf
  
  lemma abs_sq (x:ℝ) : (abs (x^2)) = (abs x)^2 :=   P_3_1_1_3_iv x
-/

  lemma P_3_1_1_3_iv (x:ℝ) : x^2 = (abs x)^2 :=   
    calc 
      x^2        = abs (x^2)       := (abs_of_nonneg (sq_nonneg x)).symm
      _          = abs (x*x)       := by ring_nf
      _          = (abs x)*(abs x) := P_3_1_1_3_v x x
      _          = (abs x)^2       := by ring_nf
  
  lemma abs_sq (x:ℝ) : x^2 = (abs x)^2 :=   P_3_1_1_3_iv x

  -- Proposition 3.1.1.5

  lemma abs_eq_max (x:ℝ ) : abs x = max x (-x) :=
    dite (x≥ 0)
    (
      λ hp : x ≥ 0  ↦ 
        have hxmx :  x ≥ -x :=
          calc 
            x ≥  0  := hp
            _ ≥ -x  := neg_nonpos.mpr hp
        calc
          abs x = x          := if_pos hp
          _     = max x (-x) := (if_pos hxmx).symm
    )
    (
      λ hn' : ¬ (x ≥ 0)  ↦ 
        have hn : x ≤ 0 := le_of_lt (lt_of_not_le hn')
        have hxmx :  x ≤ -x :=
          calc 
            x ≤  0  := hn
            _ ≤  -x := neg_nonneg.mpr hn
        calc
          abs x = -x          := abs_of_nonpos hn
          _     = max x (-x) := (max_of_le hxmx).symm
    )

  lemma P_3_1_1_5 :  ∀ x:ℝ , abs x = max x (-x) := abs_eq_max


  lemma abs_pos_of_non_zero  {x:ℝ} (h:x ≠ 0) : abs x > 0 :=
    Or.elim3 (lt_trichotomy x 0   :    ( x <  0) ∨ (x=0) ∨ (x > 0) )
    (
      λ hn : x<0 ↦ 
        calc
          abs x = -x := abs_of_neg hn
          _     > -0  := by rel[hn]
          _     = 0   := by norm_num
    )
    (
      λ hz : x=0  ↦ absurd hz h
    )
    (
      λ hp : x>0 ↦ 
        calc
          abs x = x := abs_of_pos hp
          _     > 0 := hp
    )

  lemma zero_of_abs_zero {x:ℝ} : abs x = 0 → x = 0 :=
    λ h ↦  
      of_not_not
      (
        λ h0 : x ≠ 0 ↦
          absurd h (ne_of_gt (abs_pos_of_non_zero h0))
      )

  
  lemma zero_of_abs_zero' {x:ℝ} : abs x = 0 → x = 0 :=
    λ h ↦  
      have h0 : 0 = max x (-x) := 
        calc
          0 = abs x := h.symm
          _ = max x (-x) := abs_eq_max x

      have h1 : x ≤ 0 := 
        calc
          0 = max x (-x) := h0
          _ ≥ x          := max_ge_left 

      have h2 : -x ≤ 0 := 
        calc
          0 = max x (-x) := h0
          _ ≥ -x         := max_ge_right
          
      have h3 : x ≥  0 := 
        calc 
          x = -(-x) := by ring_nf
          _ ≥ -0    := by rel[h2]
          _ = 0     := by norm_num

      le_antisymm h1 h3 

  lemma abs_zero_iff  (x:ℝ) : abs x = 0 ↔  x = 0 := ⟨zero_of_abs_zero , λ h ↦ h ▸ abs_zero  ⟩  

  lemma ex_3_1_1_6_2 : {x:ℝ | abs (-x) = - abs x} = {0} :=
    Set.ext 
    (
      λ x:ℝ ↦ Iff.intro
      (
        λ h: abs (-x) = - abs x ↦
          have h1 : abs (-x) ≥ 0 := P_3_1_1_3_i (-x)
          have h2 : abs x    ≥ 0 := P_3_1_1_3_i x
          have h3 : abs x    ≤ 0 :=
            calc
              abs x = -(- abs x)   := by ring_nf
              _      = -(abs (-x)) := by rw[h]
              _     ≤ -0           := by rel[h1] 
              _     = 0            := by norm_num
          
          have h5 : abs x = 0 := le_antisymm  h3 h2
          zero_of_abs_zero h5
      )
      (
        λ h: x=0 ↦
          calc
             abs (-x) = abs (-0)   := by rw[h]
             _        = abs (0)    := by ring_nf
             _        = 0          := abs_zero
             _        = -0         := by norm_num
             _        =- abs 0     := by rw[abs_zero]
             _        = - abs x    := by rw[h]
      )
      
    )

/-
  example (p q : Prop) (h:¬ q) : p ∨ q ↔ p := by exact? 
  example (p  : Prop) : p ↔ p ∨ p := by exact Iff.symm (or_self_iff p) 
  example (a:ℝ) (ha : a ≥ 0) :  a>0 ∨ a=0 := gt_or_eq_of_le ha
  example (p q p': Prop) (h:p ↔  p') : p ∨ q ↔ p' ∨ q := by exact or_congr_left h 
  example (a:ℝ) (ha : -a ≥ 0) (ha' : a>0) : False := by exact?
  example (a:ℝ) (ha : -a ≥ 0)  : ¬ (a>0) := by exact?
  example (a:ℝ)  (ha' : a>0) : ¬ (-a ≥ 0) := by exact?
  example (a:ℝ) (ha : -a ≥ 0)  : a ≤ 0 := by exact Iff.mp neg_nonneg ha
  example (a:ℝ) (ha : -a ≥ 0) (ha' : a>0) : False := absurd ha' (not_lt_of_le (neg_nonneg.mp ha))
  example (a:ℝ) (b:ℝ ) : a=-b ↔ -a =b := by exact Iff.symm neg_eq_iff_eq_neg
#check or_iff_right
-/


  lemma abs_eq_iff (x:ℝ) (a:ℝ) (ha : a ≥ 0) : abs x = a ↔ x = a ∨ x = -a :=
    Or.elim (gt_or_eq_of_le ha)
    (
      λ ha_gt_0 : a>0 ↦ 
        dite (x ≥ 0)
        (
          λ h ↦
            calc
              abs x = a ↔ x = a          := iff_arg (· = a) (abs_of_nonneg h) 
              _         ↔ x = a ∨ x = -a := (or_iff_left (λ hxma ↦ absurd ha_gt_0 (not_lt_of_le (neg_nonneg.mp (subst _ hxma h))))).symm
        ) 
        (
          λ h ↦
            calc
              abs x = a ↔ -x = a         := iff_arg (· = a) (abs_of_neg (lt_of_not_le h)) 
              _         ↔ x = a ∨ -x = a := (or_iff_right (λ hxa ↦ absurd (lt_trans ha_gt_0 (subst (·<0) hxa (lt_of_not_le h))) (by norm_num) )).symm
              _         ↔ x = a ∨ x = -a := or_congr_right neg_eq_iff_eq_neg
        ) 
    )
    (
      λ ha0 : a=0 ↦ 
        calc
         abs x = a ↔ abs x = 0  := by rw[ha0]
         _         ↔ x=0        := abs_zero_iff x 
         _         ↔ x=0 ∨ x=0  := (or_self_iff (x=0)).symm
         _         ↔ x=0 ∨ x=-0 := by ring_nf
         _         ↔ x=a ∨ x=-a := by rw[ha0]
    )



--  notation:50 " [ " a:50  " ; " b:50  " ] " => {x:ℝ | x ≥ a ∧ x ≤ b }
  macro " [ " a:term  " ; " b:term  " ] "  : term => do
    `({x:ℝ | x ≥ ($a) ∧ x ≤ ($b) })

  #check [1;3]

  
  example (P Q : Prop) : P →  Q → (P ↔ Q) := by exact? 
  example (P Q : Prop) : ¬ P →  ¬ Q → (P ↔ Q) := by exact? 
  example (a:ℝ ) (ha: a<0) : -a > 0 := by exact Iff.mpr neg_pos ha
  example (P Q : Prop) : P →  (Q ↔ P ∧ Q) := by exact fun a => Iff.symm (and_iff_right a) 
  example (a:ℝ ) (ha: a ≥ 0) : -a ≤ 0 := by exact Iff.mpr neg_nonpos ha

  lemma abs_le_iff (a:ℝ) (x:ℝ) : abs x ≤ a ↔ x ∈ [-a;a]:=
    Or.elim (lt_or_le a 0)
    (
      λ ha ↦
        have h1 : ¬ (abs x ≤ a) := λ h ↦  absurd (lt_of_le_of_lt (le_trans (P_3_1_1_3_i x)  h) ha) (by norm_num)
        have h2 : ¬ (x ∈ [-a;a]):= λ h ↦  absurd (lt_trans (lt_of_lt_of_le (lt_of_lt_of_le  (neg_pos.mpr ha)  h.left) h.right) ha)  (by norm_num)
        iff_of_false h1 h2  
    )
    (
      λ ha ↦
        dite (x ≥ 0)
        (
          λ h ↦
            calc
              abs x ≤  a ↔ x ≤  a           := iff_arg (· ≤ a) (abs_of_nonneg h) 
              _         ↔  x ≥ -a  ∧  x ≤ a := (and_iff_right (le_trans (neg_nonpos.mpr ha) h)).symm
        ) 
        (
          λ h ↦
            calc
              abs x ≤ a ↔ -x ≤  a           := iff_arg (· ≤  a) (abs_of_neg (lt_of_not_le h)) 
              _         ↔ x ≥ -a            := neg_le 
              _         ↔ x ≥ -a  ∧  x ≤ a  := (and_iff_left (le_trans (le_of_lt (lt_of_not_le h)) ha)).symm
        ) 
    )

  lemma dist_le_iff (a b:ℝ) (x:ℝ)  : abs (x-b) ≤ a ↔ x ∈ [b-a;b+a]:=
    calc
      abs (x-b) ≤ a ↔ x-b ∈ [-a; a]  := abs_le_iff  a  (x-b)
      _             ↔  x ∈ [b-a;b+a] := Iff.and (Iff.trans (add_le_add_iff_right b).symm (by ring_nf)) (Iff.trans (add_le_add_iff_right b).symm (by ring_nf))

  def limit (f:ℝ → ℝ ) (a:ℝ ) (ℓ:ℝ ) : Prop:=
     ∀ ε:ℝ , ε>0 → ∃ η :ℝ , η >0 ∧ ∀ x:ℝ, x ∈ [a-η;a+η] → (f x)∈ [ℓ-ε;ℓ+ε]

  def continuous_at (f:ℝ → ℝ) (a:ℝ )  : Prop := ∃ ℓ:ℝ , limit f a ℓ
  def continuous_on (f:ℝ → ℝ) (a b:ℝ) : Prop := ∀ x∈[a;b], continuous_at f x 

--  example (x:ℝ) (hx: x≠ 0) : x/x=1 := by exact div_self hx
--  example (a b c:ℝ) (h:a≤ b) (hc: c < 0) : a/c ≥ b/c := by exact Iff.mpr (div_le_div_right_of_neg hc) h
--  example (a b c:ℝ) (h:a≤ b) (hc: c > 0) : a/c ≤  b/c := by exact Iff.mpr (div_le_div_right hc) h

  lemma sep (x:ℝ ) (h:∀ε:ℝ, ε >0 → x ∈  [-ε;ε] ) : x = 0 :=
    Or.elim3 (lt_trichotomy x 0)
    (
      λ hx : x < 0 ↦
        let ε := -x/2
        have hε : ε > 0 :=
          calc
            ε = -x/2 := rfl
            _ > -0/2 := by rel[hx]
            _ = 0    := by norm_num
        have ha0 : x ≥ -(-x/2) := (h ε hε).left
        have ha : _ := 
          calc
            1 = x/x       := (div_self (ne_of_lt hx)).symm
            _ ≤ -(-x/2)/x := (div_le_div_right_of_neg hx).mpr ha0
            _ = (x/x)/2    := by ring_nf
            _ = 1/2       := by rw[(div_self (ne_of_lt hx))]
        absurd ha (by norm_num)
    )
    id
    (
      λ hx : x > 0 ↦
        let ε := x/2
        have hε : ε > 0 :=
          calc
            ε = x/2 := rfl
            _ > 0/2 := by rel[hx]
            _ = 0   := by norm_num
        have ha0 : x ≤ x/2 := (h ε hε).right
        have ha : _ := 
          calc
            1 = x/x       := (div_self (ne_of_gt hx)).symm
            _ ≤ (x/2)/x   := (div_le_div_right hx).mpr ha0
            _ = (x/x)/2   := by ring_nf
            _ = 1/2       := by rw[(div_self (ne_of_gt hx))]
        absurd ha (by norm_num)
    )

  lemma sep' (x a:ℝ ) (h:∀ε:ℝ, ε >0 → x ∈  [a-ε;a+ε] ) : x = a :=
    have h'  : ∀ε:ℝ, ε >0 → x-a ∈  [-ε; ε] :=
      λ ε hε ↦ And.intro
      (
        calc
          x-a ≥ a-ε -a := by rel[(h ε hε).left] 
          _   = - ε    := by ring_nf 
      )
      (
        calc
          x-a ≤ a+ε -a := by rel[(h ε hε).right] 
          _   =  ε     := by ring_nf 
      ) 
    have hxa : _ := sep (x-a) h'
    eq_of_sub_eq_zero hxa

  
  lemma lim_of_cont (f:ℝ → ℝ) (a:ℝ ) (h :continuous_at f a)  :  limit f a (f a)  :=
    Exists.elim h 
    (
      λ ℓ hℓ ↦ 
        have h_fa : ∀ ε:ℝ , ε >0 → (f a)  ∈[ℓ-ε;ℓ+ε]   := λ ε hε ↦ 
          Exists.elim (hℓ ε hε)
            (
              λ η ⟨ hη, hx ⟩  ↦ 
                hx a ⟨ by linarith, by linarith⟩ 
            )
        (sep' (f a)  ℓ h_fa ).symm ▸ hℓ
    )

  def Relation.{u} (E F: Type u) : Type u := E → F → Prop 
  def RelationBinaire.{u} (E : Type u) : Type u:= Relation E E

  def reflexive.{u}       {E : Type u} (r: RelationBinaire E) : Prop := ∀ x:E, r x x
  def symetrique.{u}      {E : Type u} (r: RelationBinaire E) : Prop := ∀ x:E, ∀ y:E, r x y → r y x
  def transitive.{u}      {E : Type u} (r: RelationBinaire E) : Prop := ∀ x:E, ∀ y:E,∀ z:E, r x y → r y z → r x z
  def antisymetrique.{u}  {E : Type u} (r: RelationBinaire E) : Prop := ∀ x:E, ∀ y:E, r x y → r y x → x = y

  def relation_equivalence.{u}  {E : Type u} (r: RelationBinaire E) : Prop := (reflexive r) ∧ (symetrique r) ∧ (transitive r)
  def relation_ordre.{u}        {E : Type u} (r: RelationBinaire E) : Prop := (reflexive r) ∧ (antisymetrique r) ∧ (transitive r)

/-
  structure TypeOrdonne
    :=
    (type : Type) (ordre : RelationBinaire type) (property : relation_ordre ordre) 
-/

  class Ordonne.{u} (E : Type u) extends LE E, LT E where
--    le          : RelationBinaire E
    le_ordre    : relation_ordre le

--    lt          : RelationBinaire E := λ x y ↦ (le x y) ∧ (x ≠ y)  
--    lt          := λ x y ↦ (le x y) ∧ (x ≠ y)  
    lt          := λ x y ↦ (le x y) ∧ ( ¬ ( le y x))  
    le_refl     : reflexive      le := le_ordre.left
    le_trans    : transitive     le := (le_ordre.right).right
    le_antisymm : antisymetrique le := (le_ordre.right).left

-- notation:50 lhs:51 " ≤  " rhs:51 => Ordonne.le lhs rhs
-- notation:50 lhs:51 " <  " rhs:51 => Ordonne.lt lhs rhs

  instance instPartialOrderIsOrdonne.{u} (E : Type u) [i: PartialOrder E] : Ordonne E :=
    {
      le       := i.le,
      le_ordre := And.intro (i.le_refl) (And.intro i.le_antisymm i.le_trans)
    }

/-
  instance instOrdonneIsPartialOrder.{u} (E : Type u) [i: Ordonne E] : PartialOrder E :=
    {
      le       := i.le,
      le_refl  := i.le_refl
      le_trans := i.le_trans
      le_antisymm := i.le_antisymm
--      lt := i.lt
--      lt_iff_le_not_le := λ _ _ ↦ ⟨ λ h ↦ And.intro h.left sorry, λ _ ↦  sorry ⟩ 
--      lt_iff_le_not_le := by intros ; rfl
      lt_iff_le_not_le := sorry
    }
-/

  instance instROrdonne : Ordonne ℝ := instPartialOrderIsOrdonne ℝ 

  def majorant  {E:Type} [Ordonne E] (A: Set E) (m: E) : Prop  :=  ∀ x∈ A,  x ≤ m
  def minorant  {E:Type} [Ordonne E] (A: Set E) (m: E) : Prop  :=  ∀ x∈ A,  m ≤ x
  def majore    {E:Type} [Ordonne E] (A: Set E)        : Prop  :=  ∃ m:E, majorant A m
  def minore    {E:Type} [Ordonne E] (A: Set E)        : Prop  :=  ∃ m:E, minorant A m
  def pge       {E:Type} [Ordonne E] (A: Set E) (m: E) : Prop  :=  (m ∈ A) ∧ (majorant A m)
  def ppe       {E:Type} [Ordonne E] (A: Set E) (m: E) : Prop  :=  (m ∈ A) ∧ (minorant A m)
  def borne_sup {E:Type} [Ordonne E] (A: Set E) (m: E) : Prop :=   ppe (majorant A) m
  def borne_inf {E:Type} [Ordonne E] (A: Set E) (m: E) : Prop :=   pge (minorant A) m

  theorem borne_sup_R (S: Set ℝ) (hne : S.Nonempty) (hmaj : majore S) : ∃ s:ℝ, borne_sup S s :=
    Real.exists_isLUB S hne hmaj
/-
noncomputable instance : SupSet ℝ :=
  ⟨fun S => if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB S h.1 h.2) else 0⟩

theorem sSup_def (S : Set ℝ) :
    sSup S = if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB S h.1 h.2) else 0 :=
  rfl
-/
--  example (s e : ℝ ) (h : e ≥ 0 ) : s - e ≤ s := by exact sub_le_self s h 
--  example (s b : ℝ ) (h : s<b ) : b-s > 0 := by exact Iff.mpr sub_pos h
--  example (s b : ℝ ) (h : b ≥ 0 ) : s ≤ s+b := by exact le_add_of_nonneg_right h

  theorem tvi (a b:ℝ) (hab : a ≤ b) (f:ℝ → ℝ)  (hc : continuous_on f a b) (y:ℝ) (hy: y∈ [f a; f b]) : ∃ c∈ [a;b] , f c = y :=

    let E:= {x:ℝ | x∈[a;b] ∧ f x ≤ y }

    Exists.elim (borne_sup_R E ⟨a, ⟨ ⟨le_refl a, hab⟩  ,hy.1⟩⟩ ⟨b, λ x hxE ↦ hxE.1.2 ⟩ )
    (
      λ s hssup ↦  

      have h_sab : s ∈ [a;b] := 
        And.intro
        (
          hssup.left a ((And.intro ⟨le_refl a, hab⟩  hy.left): a ∈ E )
        )
        (
          hssup.right b ((λ _ hx ↦ hx.1.2 ) : majorant E b)
        )

      Or.elim3 (lt_trichotomy (f s) y )
        (
          λ h :  f s < y ↦  

            have h_s_lt_b : s < b := Or.elim (lt_or_eq_of_le h_sab.right) id (
              λ hsb ↦ absurd (lt_of_lt_of_le (Trans.trans (congrArg f hsb).symm h) hy.right) (lt_irrefl (f b))
            )

            let ε := (y -  (f s))/ 2
            have hε : ε > 0 := 
              calc 
                ε = (y -  (f s))/ 2   := rfl
                _ > ((f s) - (f s))/2 := by rel[h]
                _ = 0                 := by ring_nf

            Exists.elim ((lim_of_cont f s (hc s h_sab)) ε hε )
              (
                λ η ⟨ hη, hx⟩  ↦

                  let d := b-s
                  have hd : d > 0 := sub_pos.mpr h_s_lt_b
                  let η' := min η d

                  have hη' : η'>0 := min_gt_iff.mpr (And.intro hη hd)
                  have hx' :  ∀ x:ℝ, x∈[s-η';s+η'] → f x ∈ [(f s)-ε;(f s)+ε] := 
                    λ x hxi ↦
                      hx x  (
                              And.intro 
                                (
                                  calc 
                                    x ≥ s - η' := hxi.left
                                    _ ≥ s - η  := by rel [min_le_left] 
                                )
                                (
                                  calc 
                                    x ≤ s + η' := hxi.right
                                    _ ≤ s + η  := by rel [min_le_left] 
                                )
                            )
                     

                  let t := s + η'/2

                  have ht  : t ∈ [s-η';s+η']                := 
                    And.intro
                    (
                      calc
                        t = s + η'/2 := rfl
                        _ ≥ s + 0/2  := by rel[hη']
                        _ = s        := by ring_nf
                        _ ≥ s - η'   := sub_le_self s (le_of_lt hη')
                    )
                    (
                      calc
                        t = s + η'/2 + 0/2   := by ring_nf
                        _ ≤ s + η'/2 + η'/2  := by rel[hη']
                        _ = s + η'           := by ring_nf
                    )

                  have hft : f t ∈ [(f s)-ε ; (f s) + ε ] := hx' t ht
                  have hfs : (f s) + ε ≤ y                := 
                    calc
                      (f s) + ε = (f s)/2 + y/2  := by ring_nf
                      _         ≤  y/2+y/2       := by rel[h] 
                      _         =  y             := by ring_nf

                  have hfty: f t ≤ y                      :=
                    calc
                      f t ≤ (f s) + ε := hft.right
                      _   ≤ y         := hfs

                  have hts': t > s      :=
                    calc
                      t =  s + η'/2 := rfl
                      _ >  s + 0/2  := by rel[hη']
                      _ = s         := by ring_nf

                  have htE : t ∈ E      := 
                    And.intro 
                      (
                        And.intro
                          (le_trans h_sab.left (le_of_lt hts'))
                          (
                            calc
                              t = s + η'/2 + 0/2   := by ring_nf
                              _ ≤ s + η'/2 + η'/2  := by rel[hη']
                              _ = s + η'           := by ring_nf
                              _ ≤ s + d            := by rel[min_le_right]
                              _ = b                := by ring_nf
                          )
                      )
                      hfty
                  have hts : t ≤ s      := hssup.left t htE

                  absurd hts (not_le_of_gt hts')
                
              )
        )
        (
          λ h :  f s = y ↦  
            Exists.intro s 
            (
              And.intro
                h_sab 
                h
            )
        )
        (
          λ h :  f s > y ↦  
            have h_s_gt_a : s > a := Or.elim (lt_or_eq_of_le h_sab.left) id (
              λ hsa ↦ absurd (lt_of_le_of_lt hy.left (Trans.trans h (congrArg f hsa).symm ) ) (lt_irrefl (f a))
            )

            let ε := ((f s) - y)/ 2
            have hε : ε > 0 := 
              calc 
                ε = ((f s)- y )/ 2    := rfl
                _ > ((f s) - (f s))/2 := by rel[h]
                _ = 0                 := by ring_nf

            Exists.elim ((lim_of_cont f s (hc s h_sab)) ε hε )
              (
                λ η ⟨ hη, hx⟩  ↦

                  let d := s-a
                  have hd : d > 0 := sub_pos.mpr h_s_gt_a
                  let η' := min η d

                  have hη' : η'>0 := min_gt_iff.mpr (And.intro hη hd)
                  have hx' :  ∀ x:ℝ, x∈[s-η';s+η'] → f x ∈ [(f s)-ε;(f s)+ε] := 
                    λ x hxi ↦
                      hx x  (
                              And.intro 
                                (
                                  calc 
                                    x ≥ s - η' := hxi.left
                                    _ ≥ s - η  := by rel [min_le_left] 
                                )
                                (
                                  calc 
                                    x ≤ s + η' := hxi.right
                                    _ ≤ s + η  := by rel [min_le_left] 
                                )
                            )
                  have hx'' :  ∀ x:ℝ, x∈[s-η';s+η'] → f x > y := 
                    λ x hxi ↦ 
                      calc
                        f x ≥ (f s) - ε     := (hx' x hxi).left
                        _   = (f s)/2 + y/2 := by ring_nf
                        _   > y/2+y/2       := by rel[h]
                        _   = y             := by ring_nf

                  have hEmaj : ∀x∈E, x ≤ s - η' :=
                    λ x hxE ↦ 
                      have hxs   : x ≤ s := hssup.left x hxE
                      have hxnge : ¬ (x ≥ s-η') :=
                        λ hxge ↦
                          absurd
                            (hx'' x ⟨hxge,le_trans hxs (le_add_of_nonneg_right (le_of_lt hη'))⟩ : f x > y    )
                            (not_lt_of_ge hxE.right                                             : ¬ (f x > y))
                           
                      le_of_lt (lt_of_not_ge hxnge) 
                  
                  have hsle : s ≤ s - η' :=
                    hssup.right (s-η') (hEmaj)

                  absurd
                    (
                      calc
                        s ≤ s - η' := hsle
                        _ < s-0    := by rel[hη']
                        _ = s      := sub_zero s
                    )
                    (lt_irrefl s)
            )
        )
    )

  lemma sq_increasing (x:ℝ) (y:ℝ) (hx : x≥ 0) (hxy: x ≤ y)  : x^2 ≤ y^2 :=
    calc
      x^2 = x*x := by ring_nf
      _   ≤ y*x := mul_le_mul_of_nonneg_right hxy hx
      _   ≤ y*y := mul_le_mul_of_nonneg_left hxy (le_trans hx hxy)
      _   = y^2 := by ring_nf

  lemma sq_strictly_increasing (x:ℝ) (y:ℝ) (hx : x≥ 0)  (hxy: x < y)  : x^2 < y^2 :=
    have hy' : y>0 := lt_of_le_of_lt hx hxy
    calc
      x^2 = x*x := by ring_nf
      _   ≤ y*x := mul_le_mul_of_nonneg_right (le_of_lt hxy) hx
      _   < y*y := mul_lt_mul_of_pos_left hxy hy'
      _   = y^2 := by ring_nf

  lemma lt_of_sq_lt (x:ℝ) (y:ℝ)  (hy : y ≥ 0) (hx2y2: x^2 < y^2) : x < y :=
    lt_of_not_le (
      λ hyx ↦ 
        absurd (sq_increasing y x hy hyx) (not_le_of_gt hx2y2)
    )

  lemma le_of_sq_le (x:ℝ) (y:ℝ)  (hy : y ≥ 0) (hx2y2: x^2 ≤ y^2) : x ≤ y :=
    le_of_not_lt (
      λ hyx ↦ 
        absurd (sq_strictly_increasing y x hy hyx) (not_lt_of_ge hx2y2)
    )

  lemma sq_decreasing (x:ℝ) (y:ℝ) (hy : y ≤ 0) (hxy: x ≤ y)  : x^2 ≥ y^2 :=
    calc
      y^2 = (-y)^2 := by ring_nf
      _   ≤ (-x)^2 := sq_increasing (-y) (-x) (neg_nonneg.mpr hy) (neg_le_neg hxy)
      _   = x^2    := by ring_nf

  lemma sq_strictly_decreasing (x:ℝ) (y:ℝ) (hy : y ≤ 0) (hxy: x < y)  : x^2 > y^2 :=
    calc
      y^2 = (-y)^2 := by ring_nf
      _   < (-x)^2 := sq_strictly_increasing (-y) (-x) (neg_nonneg.mpr hy) (neg_lt_neg hxy)
      _   = x^2    := by ring_nf



  lemma inegalite_triangulaire_R (x y : ℝ ) : abs (x+y) ≤  (abs x) + (abs y) := 
    have h_sq : (abs (x+y)) ^2 ≤  ( (abs x) + (abs y)) ^2 :=
      calc
/-        (abs (x+y)) ^2 = abs ((x+y)^2)                 := (abs_sq (x+y)).symm
        _              = (x+y)^2                       := abs_of_nonneg (sq_nonneg  (x+y))-/
        (abs (x+y)) ^2 =  (x+y)^2                      := (abs_sq (x+y)).symm
        _              = x^2+y^2 + 2*(x*y)             := by ring_nf
        _              ≤ x^2+y^2 + 2*(abs (x*y))       := by rel[Trans.trans (abs_eq_max (x*y)) ( max_ge_left ) ]
        _              = x^2+y^2 + 2*((abs x)*(abs y))                  := by rw[abs_mul x y]
--        _              = (abs (x^2))+(abs (y^2)) + 2*((abs x)*(abs y))  := by rw[abs_of_nonneg (sq_nonneg  x), abs_of_nonneg (sq_nonneg  y)]
        _              = (abs x)^2 + (abs y)^2 + 2*((abs x)*(abs y))    := by rw[abs_sq x, abs_sq y]
        _              = ((abs x) + (abs y))^2                          := by ring_nf
    
    have haxay : (abs x) + (abs y) ≥ 0 :=  add_nonneg (abs_nonneg x) (abs_nonneg y)

    le_of_sq_le (abs (x+y)) ((abs x) + (abs y)) haxay h_sq



  def square (x:ℝ ) : ℝ := x^2 

--  example (a b :ℝ ) (ha :a>0) (hb : b>0) : a/b >0 := by exact div_pos ha hb
  --example (a b :ℝ ) (ha :a≥ 0)  : a+b ≥ b := by exact le_add_of_nonneg_left ha
  -- example (a b :ℝ ) (ha :a≥ 0) (hb : b≥ 0) : a*b ≥ 0 := by exact mul_nonneg ha hb
--  example (a b :ℝ )  (hb : b≠ 0) : a/b*b=a := by exact div_mul_cancel a hb
--   example (a b c:ℝ ) (hab :a≥ b) (hc : c≥ 0) : a*c ≥ b*c := by exact mul_le_mul_of_nonneg_right hab hc

  lemma sq_continuous (a:ℝ):  continuous_at square a := Exists.intro (a^2) (
    λ ε hε  ↦ 
      let k := 2 * (abs a) + 1
      have hk : k>0 :=
        calc
          2 * (abs a) + 1  ≥ 1  := le_add_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg a))
          _                > 0  := by norm_num

      let η' := ε / k
      have hη' : η' > 0 :=  div_pos hε hk

      let η := min 1 η'
      have hη : η > 0   := min_gt_iff.mpr  (And.intro  (by norm_num) hη' )

      Exists.intro η (
        And.intro hη 
        (
          λ x hx ↦  
            have : _ := 
              (dist_le_iff η a x  ).mpr hx

            have : _ := 
              calc 
                abs (x^2-a^2)  = abs ((x-a)*(x+a))                           := by ring_nf
                _              = (abs (x-a)) * (abs (x+a))                   := abs_mul (x-a) (x+a)
                _              ≤ η * (abs (x+a))                             := mul_le_mul_of_nonneg_right this (abs_nonneg (x+a))
                _              = η * (abs ((x-a)+2*a))                       := by ring_nf 
                _              ≤ η * ((abs (x-a)) + (abs (2*a)))             := by rel[inegalite_triangulaire_R (x-a) (2*a)]
                _              = η * ((abs (x-a)) + (abs 2)*(abs a))         := by rw[abs_mul 2 a]
                _              = η * ((abs (x-a) )+ 2*(abs a))               := by rw[abs_of_nonneg (by norm_num : (2:ℝ ) ≥ 0)]
                _              ≤ η * (η  + 2*(abs a))                        := by rel[this]
                _              ≤ η * (1  + 2*(abs a))                        := by rel[min_le_left]
                _              = η * k                                       := by ring_nf
                _              ≤ (ε / k) *  k                                := by rel[min_le_right]
                _              = ε                                           := div_mul_cancel ε (ne_of_gt hk) 


            (dist_le_iff ε (a^2) (x^2) ).mp this
        )
      )
  ) 


  lemma sqrt_exists (a:ℝ) (ha:a≥0) : ∃ r ≥ 0, r^2=a :=
    let b := max 1 a 
    have hb2 : b^2 ≥ a := 
      dite (1 ≥ a)
      (
        λ h ↦ 
          le_trans h (Trans.trans (by norm_num : (1:ℝ)=1^2) (sq_increasing 1 b (by norm_num) max_ge_left))
      )
      (
        λ h ↦ 
          have h' : a ≥ 1 := le_of_lt (lt_of_not_le h)
          calc
            b^2 ≥ a^2 := sq_increasing a b ha max_ge_right
            _   = a*a := by ring_nf
            _   ≥ a*1 := mul_le_mul_of_nonneg_left h' ha
            _   = a   := mul_one a
      )
    have : _ := tvi 0 b (le_trans (by norm_num) (max_ge_left)) square (λ x _ ↦ sq_continuous x ) a 
                    ⟨ trans ha (by norm_num : (0:ℝ )=0^2) ,hb2⟩ 
    Exists.elim  this (
      λ c hc ↦ 
        Exists.intro c (And.intro hc.left.left hc.right)
      
    )


    
    /-
      -- mathlib4/Mathlib/Data/Real/Sqrt.lean

        /-- The square root of a real number. This returns 0 for negative inputs. -/
        noncomputable def Real.sqrt (x : ℝ) : ℝ :=   NNReal.sqrt (Real.toNNReal x)

        /-- Square root of a nonnegative real number. -/
        noncomputable def NNReal.sqrt : ℝ≥0 ≃o ℝ≥0 :=  OrderIso.symm <| powOrderIso 2 two_ne_zero
    
      -- mathlib4/Mathlib/Topology/Instances/NNReal.lean

      /-- `x ↦ x ^ n` as an order isomorphism of `ℝ≥0`. -/
      def powOrderIso (n : ℕ) (hn : n ≠ 0) : ℝ≥0 ≃o ℝ≥0 :=
        StrictMono.orderIsoOfSurjective (fun x ↦ x ^ n) (fun x y h =>
            strictMonoOn_pow hn.bot_lt (zero_le x) (zero_le y) h) <|
          (continuous_id.pow _).surjective (tendsto_pow_atTop hn) <| by
            simpa [OrderBot.atBot_eq, pos_iff_ne_zero]      

      --     mathlib4/Mathlib/Order/Hom/Basic.lean

      /-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
      This definition is an abbreviation of `RelIso (≤) (≤)`. -/
      abbrev OrderIso (α β : Type*) [LE α] [LE β] :=
        @RelIso α β (· ≤ ·) (· ≤ ·)

      /-- Notation for an `OrderIso`. -/
      infixl:25 " ≃o " => OrderIso

      /-- Inverse of an order isomorphism. -/
      def symm (e : α ≃o β) : β ≃o α := RelIso.symm e
      
     --     mathlib4/Mathlib/Order/RelIso/Basic.lean

      /-- A relation isomorphism is an equivalence that is also a relation embedding. -/
      structure RelIso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β where
        /-- Elements are related iff they are related after apply a `RelIso` -/
        map_rel_iff' : ∀ {a b}, s (toEquiv a) (toEquiv b) ↔ r a b      


        /-- Inverse map of a relation isomorphism is a relation isomorphism. -/
        protected def symm (f : r ≃r s) : s ≃r r :=
          ⟨f.toEquiv.symm, @fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩

     --     mathlib4/Mathlib/Logic/Equiv/Defs.lean

        /-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
        structure Equiv (α : Sort*) (β : Sort _) where
          protected toFun : α → β
          protected invFun : β → α
          protected left_inv : LeftInverse invFun toFun
          protected right_inv : RightInverse invFun toFun

        infixl:25 " ≃ " => Equiv

        /-- Inverse of an equivalence `e : α ≃ β`. -/
        @[symm, pp_dot]
        protected def symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩


     --  mathlib4/Mathlib/Init/Function.lean

        /-- `LeftInverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
        def LeftInverse (g : β → α) (f : α → β) : Prop :=
          ∀ x, g (f x) = x

        /-- `RightInverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
        def RightInverse (g : β → α) (f : α → β) : Prop :=
          LeftInverse f g

     --     https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FunLike/Equiv.html#EquivLike
     --     mathlib4/Mathlib/Data/FunLike/Equiv.lean
     --     https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FunLike/Basic.html#FunLike
     --     mathlib4/Mathlib/Data/FunLike/Basic.lean

     --     lean4/src/Init/Coe.lean

      /--
      `CoeFun α (γ : α → Sort v)` is a coercion to a function. `γ a` should be a
      (coercion-to-)function type, and this is triggered whenever an element
      `f : α` appears in an application like `f x`, which would not make sense since
      `f` does not have a function type.
      `CoeFun` instances apply to `CoeOut` as well.
      -/
      class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
        /-- Coerces a value `f : α` to type `γ f`, which should be either be a
        function type or another `CoeFun` type, in order to resolve a mistyped
        application `f x`. -/
        coe : (f : α) → γ f
      attribute [coe_decl] CoeFun.coe


     --     mathlib4/Mathlib/Order/Hom/Set.lean

    variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

    /-- A strictly monotone function from a linear order is an order isomorphism between its domain and its range. -/
    @[simps! apply]
    protected noncomputable def orderIso :
        α ≃o Set.range f where
      toEquiv := Equiv.ofInjective f h_mono.injective
      map_rel_iff' := h_mono.le_iff_le

    /-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
    noncomputable def orderIsoOfSurjective : α ≃o β :=
      (h_mono.orderIso f).trans <|
        (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ

     --     mathlib4/Mathlib/Logic/Equiv/Set.lean

    /-- If `f : α → β` is an injective function, then domain `α` is equivalent to the range of `f`. -/
    @[simps! apply]
    noncomputable def ofInjective {α β} (f : α → β) (hf : Injective f) : α ≃ range f :=
      Equiv.ofLeftInverse f (fun _ => Function.invFun f) fun _ => Function.leftInverse_invFun hf

    /-- If `f : α → β` has a left-inverse when `α` is nonempty, then `α` is computably equivalent to the
    range of `f`.

    While awkward, the `Nonempty α` hypothesis on `f_inv` and `hf` allows this to be used when `α` is
    empty too. This hypothesis is absent on analogous definitions on stronger `Equiv`s like
    `LinearEquiv.ofLeftInverse` and `RingEquiv.ofLeftInverse` as their typeclass assumptions
    are already sufficient to ensure non-emptiness. -/
    @[simps]
    def ofLeftInverse {α β : Sort _} (f : α → β) (f_inv : Nonempty α → β → α)
        (hf : ∀ h : Nonempty α, LeftInverse (f_inv h) f) :
        α ≃ range f where
      toFun a := ⟨f a, a, rfl⟩
      invFun b := f_inv (nonempty_of_exists b.2) b
      left_inv a := hf ⟨a⟩ a
      right_inv := fun ⟨b, a, ha⟩ =>
        Subtype.eq <| show f (f_inv ⟨a⟩ b) = b from Eq.trans (congr_arg f <| ha ▸ hf _ a) ha



    --     mathlib4/Mathlib/Logic/Function/Basic.lean

    attribute [local instance] Classical.propDecidable

    /-- The inverse of a function (which is a left inverse if `f` is injective
      and a right inverse if `f` is surjective). -/
    -- Explicit Sort so that `α` isn't inferred to be Prop via `exists_prop_decidable`
    noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=
      fun y ↦ if h : (∃ x, f x = y) then h.choose else Classical.arbitrary α

     --    lean4/src/Init/Prelude.lean


      /--
      `Nonempty α` is a typeclass that says that `α` is not an empty type,
      that is, there exists an element in the type. It differs from `Inhabited α`
      in that `Nonempty α` is a `Prop`, which means that it does not actually carry
      an element of `α`, only a proof that *there exists* such an element.
      Given `Nonempty α`, you can construct an element of `α` *nonconstructively*
      using `Classical.choice`.
      -/
      class inductive Nonempty (α : Sort u) : Prop where
        /-- If `val : α`, then `α` is nonempty. -/
        | intro (val : α) : Nonempty α

      /--
      **The axiom of choice**. `Nonempty α` is a proof that `α` has an element,
      but the element itself is erased. The axiom `choice` supplies a particular
      element of `α` given only this proof.

      The textbook axiom of choice normally makes a family of choices all at once,
      but that is implied from this formulation, because if `α : ι → Type` is a
      family of types and `h : ∀ i, Nonempty (α i)` is a proof that they are all
      nonempty, then `fun i => Classical.choice (h i) : ∀ i, α i` is a family of
      chosen elements. This is actually a bit stronger than the ZFC choice axiom;
      this is sometimes called "[global choice](https://en.wikipedia.org/wiki/Axiom_of_global_choice)".

      In lean, we use the axiom of choice to derive the law of excluded middle
      (see `Classical.em`), so it will often show up in axiom listings where you
      may not expect. You can use `#print axioms my_thm` to find out if a given
      theorem depends on this or other axioms.

      This axiom can be used to construct "data", but obviously there is no algorithm
      to compute it, so lean will require you to mark any definition that would
      involve executing `Classical.choice` or other axioms as `noncomputable`, and
      will not produce any executable code for such definitions.
      -/
      axiom Classical.choice {α : Sort u} : Nonempty α → α

      /--
      The elimination principle for `Nonempty α`. If `Nonempty α`, and we can
      prove `p` given any element `x : α`, then `p` holds. Note that it is essential
      that `p` is a `Prop` here; the version with `p` being a `Sort u` is equivalent
      to `Classical.choice`.
      -/
      protected def Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
        match h₁ with
        | intro a => h₂ a



     --     lean4/src/Init/Classical.lean

      noncomputable def Classical.indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
        choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

      noncomputable def Classical.choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
        (indefiniteDescription p h).val

      theorem Classical.choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
        (indefiniteDescription p h).property

     --     std4/Std/Logic.lean

      /-- Extract an element from a existential statement, using `Classical.choose`. -/
      -- This enables projection notation.
      @[reducible] noncomputable def Exists.choose (P : ∃ a, p a) : α := Classical.choose P

      /-- Show that an element extracted from `P : ∃ a, p a` using `P.choose` satisfies `p`. -/
      theorem Exists.choose_spec {p : α → Prop} (P : ∃ a, p a) : p P.choose := Classical.choose_spec P

      -/

      
   /-
    noncomputable def sqrt0 (x:ℝ) (hx : x≥ 0 ) : { y // y≥0 ∧ y^2=x }  :=
      Classical.choice (
        Exists.elim (sqrt_exists x hx) (λ x px ↦ Nonempty.intro ⟨x,px⟩  ) 
      )

    lemma sqrt0_nonneg (x:ℝ) (hx : x≥ 0 ) : (sqrt0 x hx).val ≥ 0 := (sqrt0 x hx).property.left



    noncomputable def sqrt1 (x:ℝ) (hx : x≥ 0 ) : { y // y≥0 ∧ y^2=x }  := 
      Classical.indefiniteDescription 
          _ -- (λ y ↦ (y≥0 ∧ y^2=x) )
          (sqrt_exists x hx) 

    lemma sqrt1_nonneg (x:ℝ) (hx : x≥ 0 ) : (sqrt1 x hx).val ≥ 0 := (sqrt0 x hx).property.left

    
    noncomputable def sqrt2 (x:ℝ) (hx : x≥ 0 ) : ℝ  := 
      Classical.choose
          (sqrt_exists x hx) 

    lemma sqrt2_nonneg (x:ℝ) (hx : x≥ 0 ) : (sqrt2 x hx) ≥ 0 := 
      (Classical.indefiniteDescription  _  (sqrt_exists x hx) ).property.left

    -/


    noncomputable def sqrt_st (x:ℝ) (hx : x≥ 0 ) : { y // y≥0 ∧ y^2=x }  := 
      Classical.indefiniteDescription  _  (sqrt_exists x hx) 

    noncomputable def sqrt (x:ℝ) (hx : x≥ 0 ) : ℝ  := (sqrt_st x hx).val 
    lemma sqrt_nonneg (x:ℝ) (hx : x≥ 0 ) : (sqrt x hx) ≥ 0   := (sqrt_st x hx).property.left
    lemma sq_sqrt     (x:ℝ) (hx : x≥ 0 ) : (sqrt x hx)^2 = x := (sqrt_st x hx).property.right

    noncomputable def sqrt! (x:ℝ) : ℝ  :=
      if  hx: x≥ 0 then
        sqrt x hx
      else
         (0:ℝ)

    noncomputable def sqrt? (x:ℝ) : Option ℝ  :=
      if  hx: x≥ 0 then
        some (sqrt x hx)
      else
        none

    class Nonneg (x:ℝ) where
      nonneg : x ≥ 0 

    example (m n :ℕ ) (h: m≤n ) : (m:ℝ ) ≤(n:ℝ )  := by exact Iff.mpr Nat.cast_le h

--    noncomputable def sqrt' (x:ℝ) [ix : Nonneg x] : ℝ  := (sqrt_st x ix.nonneg).val 
    noncomputable def sqrt' (x:ℝ) [ix : Nonneg x] : ℝ  := sqrt x ix.nonneg
    lemma sq_sqrt'     (x:ℝ) [ix : Nonneg x] : (sqrt' x )^2 = x := (sqrt_st x ix.nonneg).property.right
    lemma sqrt_nonneg' (x:ℝ) [ix : Nonneg x] : (sqrt' x ) ≥ 0   := (sqrt_st x ix.nonneg).property.left

--    instance instNatNonneg (n:ℕ) : Nonneg (n.cast) := ⟨  Nat.cast_le.mpr (zero_le n)   ⟩ 
    #print Nat.cast_le
    
    --@[default_instance 100] 
--    instance instNatNonneg (n:ℕ) : Nonneg n := ⟨  by aesop  ⟩ 
--    instance (priority := 1000) instNatNonneg (n:ℕ) : Nonneg (n.cast) := ⟨  by aesop  ⟩ 
    instance instNatNonneg (n:ℕ) : Nonneg (n.cast) := ⟨  by aesop  ⟩ 
    #print instNatNonneg

    #check (inferInstance : Nonneg 2) 
    #check (inferInstanceAs (Nonneg 2): Nonneg 2) 
    #check (inferInstance : Nonneg (2:ℝ)) 
    #synth (Nonneg 2)

    instance instNatNonneg2 : Nonneg 2 := instNatNonneg 2
    #synth (Nonneg 2)
    #synth (OfNat ℝ 2)

    #check (inferInstance : Nonneg 2) 

    example : (sqrt' (2:ℝ))^2 = 2 := sorry
    example : (@sqrt'  (2:ℝ) (instNatNonneg 2) )^2 = 2 := sq_sqrt 2 _
    example : (@sqrt'  (2:ℝ) (inferInstance) )^2 = 2 := sq_sqrt 2 _
    example : (@sqrt'  2 (instNatNonneg 2) )^2 = 2 := sq_sqrt 2 _
    example : (@sqrt'  2 (instNatNonneg 2) )^2 = 2 := sq_sqrt' 2
    example : (@sqrt'  2 (instNatNonneg 2) )^2 = 2 := @sq_sqrt' 2 (instNatNonneg 2)


example (x a  :ℝ ) (h: x-a=0 ) : x=a  := eq_of_sub_eq_zero h -- by exact?
--example (x a b :ℝ ) (h: (x-a)*(x-b)=0 ) : x=a ∨ x=b := by exact?
example (a  :ℝ ) (h: -a ≥ 0  ) : a≤ 0  := by exact Iff.mp neg_nonneg h


lemma eq_or_eq_of_mul_eq_zero {x a b :ℝ } (h: (x-a)*(x-b)=0 ) : x=a ∨ x=b := 
  Or.imp eq_of_sub_eq_zero eq_of_sub_eq_zero  (eq_zero_or_eq_zero_of_mul_eq_zero h)

lemma eq_or_eq_iff_mul_eq_zero {x a b :ℝ } : (x-a)*(x-b)=0 ↔ x=a ∨ x=b := 
   Iff.trans  mul_eq_zero (Iff.or sub_eq_zero sub_eq_zero)


    noncomputable def sqrt_sq (x:ℝ) : ℝ := (sqrt (x^2) (sq_nonneg x) ) 

    lemma sqrt_sq_eq_abs (x:ℝ)  : sqrt_sq x = abs x := 
      let s := sqrt_sq x
      have hsn : s ≥ 0     := sqrt_nonneg _ _ 
      have hs2 : s^2 = x^2 := sq_sqrt     _ _
      have hsxx1: _ :=
        calc
          (s-x)*(s- (-x)) = s^2 - x^2 := by ring_nf
          _               = x^2 - x^2 := by rw[hs2]
          _               = 0         := by ring_nf
      Or.elim  (eq_or_eq_of_mul_eq_zero hsxx1)
        (
          λ hs1 : s=x ↦ 
            calc
             s= x      := hs1
             _= abs x  := (abs_of_nonneg (Trans.trans hs1.symm hsn) ).symm
        )
        (
          λ hs2 : s=-x ↦ 
            calc
             s= -x      := hs2
             _= abs x  :=
--                 (abs_of_nonpos (neg_nonneg.mp (Trans.trans hs2.symm hsn) )).symm
                 have : _ := Trans.trans hs2.symm hsn
                 (abs_of_nonpos (neg_nonneg.mp this )).symm
        )



--  lemma sqrt_unique (a:ℝ) (_:a≥0) (r s : ℝ )  (hr : r≥0 )(hs : s≥0) (hr2a :  r^2=a) (hs2a :  s^2=a):  r=s  :=
  lemma sqrt_unique  { a r s : ℝ }  (hr : r≥0 )(hs : s≥0) (hr2a :  r^2=a) (hs2a :  s^2=a):  r=s  :=
        have : _ := calc
          (s-r)*(s- (-r)) = s^2 - r^2 := by ring_nf
          _               = a - a     := by rw[hr2a,hs2a]
          _               = 0         := by ring_nf
      Or.elim  (eq_or_eq_of_mul_eq_zero this)
        Eq.symm
        (
          λ hsmr : s=-r ↦ 
            have : _ := nonpos_of_neg_nonneg (trans hs hsmr)
            have : _ := le_antisymm hr this
            calc 
              r =  0  := this.symm
              _ = -0  := by norm_num
              _ = -r  := by rw[this]
              _ = s   := hsmr.symm
        )

  lemma sqrt_exists_unique (a:ℝ) (ha:a≥0) : ∃! r:ℝ ,  r ≥ 0 ∧ r^2=a := 
    Exists.elim (sqrt_exists a ha)
    (
       λ r ⟨ hr,hr2a⟩  ↦ 
         Exists.intro r 
         (
           And.intro
             ⟨ hr, hr2a⟩ 
             (
              λ _ hs ↦
--                sqrt_unique a ha s r hs.left hr hs.right hr2a 
                sqrt_unique  hs.left hr hs.right hr2a 
            )
         ) 
    )

--    lemma sqrt_unique'  (a:ℝ) (ha:a≥0) (r : ℝ )  (hr : r≥0 ) (hr2a :  r^2=a) : r = sqrt a ha :=
--    lemma sqrt_unique'  {a:ℝ}  {r : ℝ } (hr:r≥0)  (hr2a :  r^2=a) : r = sqrt a (trans hr2a.symm (sq_nonneg r)) :=
    lemma sqrt_unique'  {a:ℝ}  {r : ℝ } (hr:r≥0)  (hr2a :  r^2=a)  (ha : a≥ 0 := (trans hr2a.symm (sq_nonneg r))) :
         r = sqrt a ha :=
--      let s := sqrt a ha
--      sqrt_unique a ha r s hr (sqrt_nonneg _ _) hr2a (sq_sqrt _ _)
      sqrt_unique  hr (sqrt_nonneg _ _) hr2a (sq_sqrt _ _)

    lemma sqrt_sq_eq_abs' (x:ℝ)  : sqrt_sq x = abs x := 
--      (sqrt_unique' (x^2)  (sq_nonneg x)  (abs x)  (abs_nonneg x) (abs_sq x).symm ).symm
--      (sqrt_unique'   (sq_nonneg x)    (abs_nonneg x) (abs_sq x).symm ).symm
      (sqrt_unique'      (abs_nonneg x) (abs_sq x).symm ).symm


    lemma sqrt_sq_eq_self_of_nonneg (x:ℝ)  (hx : x≥ 0 ) : sqrt_sq x = x := 
      calc
        sqrt_sq x = abs x  := sqrt_sq_eq_abs x
        _         = x      := abs_of_nonneg hx



                           
  lemma sqrt_increasing (x:ℝ) (y:ℝ) (hx : 0 ≤ x) (hxy: x ≤ y) (hy : y ≥ 0 := le_trans hx hxy ) : sqrt x hx ≤ sqrt y hy :=
    let sx :=  sqrt x hx
    let sy :=  sqrt y hy
    le_of_sq_le sx sy (sqrt_nonneg y hy) (calc
       sx^2 = x    := sq_sqrt x hx
      _     ≤ y    := hxy
      _     = sy^2 := (sq_sqrt y hy).symm
    )

                           
  lemma sqrt_strictly_increasing (x:ℝ) (y:ℝ) (hx : 0 ≤ x) (hxy: x < y) (hy : y ≥ 0 := le_of_lt (lt_of_le_of_lt hx hxy) ) : sqrt x hx < sqrt y hy :=
    let sx :=  sqrt x hx
    let sy :=  sqrt y hy
    lt_of_sq_lt sx sy (sqrt_nonneg y hy) (calc
       sx^2 = x    := sq_sqrt x hx
      _     < y    := hxy
      _     = sy^2 := (sq_sqrt y hy).symm
    )



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

  example (a:ℝ) (h:a>0) : -a<0 := by exact Iff.mpr neg_lt_zero h
  example (a:ℝ) (h:a≥ 0) : -a≤ 0 := by exact Iff.mpr neg_nonpos h
  example (a x:ℝ) :  -x ≥  a  ↔ x ≤ -a  := by exact le_neg
  example (a :ℝ) :  a <  0  ↔ 0 < -a  := by exact Iff.symm neg_pos

  lemma abs_lt_iff  (a:ℝ) (x:ℝ) : abs x < a ↔ x ∈ (-a;a):=
    Or.elim (lt_or_le 0 a)
    (
      λ ha ↦
        dite (x ≥ 0)
        (
          λ h ↦
            calc
              abs x <  a ↔ x <  a           := iff_arg (· < a) (abs_of_nonneg h) 
              _          ↔ x > -a  ∧ x < a := (and_iff_right (lt_of_lt_of_le (neg_lt_zero.mpr ha) h)).symm
        ) 
        (
          λ h ↦
            have h' : x<0 := lt_of_not_le h
            calc
              abs x < a ↔ -x < a            := iff_arg (· <  a) (abs_of_neg h') 
              _         ↔  x > -a           := neg_lt
              _         ↔ x > -a  ∧  x < a  := (and_iff_left (lt_trans h' ha)).symm
        ) 
    )
    (
      λ ha ↦
        have h1 : ¬ (abs x < a) := λ h ↦ absurd (lt_of_lt_of_le (lt_of_le_of_lt (P_3_1_1_3_i x)  h) ha) (by norm_num)
        have h2 : ¬ (x ∈ (-a;a)):= λ h ↦ absurd (lt_of_lt_of_le (lt_trans (lt_of_le_of_lt  (neg_nonneg.mpr ha)  h.left) h.right) ha) (by norm_num)
        iff_of_false h1 h2  
    )

  example (P Q:Prop) : ¬ Q → ((P ∨ Q) ↔ P) := by exact fun a => or_iff_left a

  lemma abs_ge_iff  (a:ℝ) (x:ℝ) : abs x ≥ a ↔ x ≤ -a ∨ x ≥ a:= 
    dite (x ≥ 0)
    (
      λ h ↦ 

        calc
          abs x ≥  a ↔ x ≥  a         := iff_arg (· ≥  a) (abs_of_nonneg h) 
          _          ↔ x ≤ -a ∨ x ≥ a := Iff.intro
            (Or.inr)
            (
              Or.elim (lt_or_le 0 a)
              (
                λ ha ↦ 
                  (or_iff_right (λ o ↦ absurd (lt_of_lt_of_le (lt_of_lt_of_le  (neg_lt_zero.mpr ha) h) o) (lt_irrefl (-a)))).mp
              )
              (
                λ ha _ ↦ 
                  le_trans ha h
              )
            )
    )
    (
      λ h ↦ 
        have h' : x<0 := lt_of_not_le h
        calc
          abs x ≥  a ↔ -x ≥  a         := iff_arg (· ≥  a) (abs_of_neg h') 
          _          ↔  x ≤ -a         := le_neg
          _          ↔  x ≤ -a ∨ x ≥ a := Iff.intro
            (Or.inl)
            (
              Or.elim (lt_or_le a 0)
                (
                  λ ha _ ↦ 
                    le_of_lt (lt_trans h' (neg_pos.mpr ha))
                )
                (
                  λ ha ↦ 
                    (or_iff_left (λ o ↦ absurd (lt_of_le_of_lt  (le_trans ha o ) h') (lt_irrefl 0))).mp
                )
            )
    )



  lemma abs_gt_iff  (a:ℝ) (x:ℝ) : abs x > a ↔ x < -a ∨ x > a:= 
    dite (x ≥ 0)
    (
      λ h ↦ 

        calc
          abs x >  a ↔ x >  a         := iff_arg (· >  a) (abs_of_nonneg h) 
          _          ↔ x < -a ∨ x > a := Iff.intro
            (Or.inr)
            (
              Or.elim (lt_or_le a 0)
              (
                λ ha _ ↦ 
                  lt_of_lt_of_le ha h
              )
              (
                λ ha ↦ 
                  (or_iff_right (λ o ↦ absurd (lt_of_lt_of_le o (le_trans  (neg_nonpos.mpr ha) h) ) (lt_irrefl x))).mp
              )
            )
    )
    (
      λ h ↦ 
        have h' : x<0 := lt_of_not_le h
        calc
          abs x >  a ↔ -x >  a         := iff_arg (· >  a) (abs_of_neg h') 
          _          ↔  x < -a         := lt_neg
          _          ↔  x < -a ∨ x > a := Iff.intro
            (Or.inl)
            (
              Or.elim (lt_or_le 0 a)
                (
                  λ ha ↦ 
                    (or_iff_left (λ o ↦ absurd (lt_trans  (lt_trans ha o ) h') (lt_irrefl 0))).mp
                )
                (
                  λ ha _ ↦ 
                    lt_of_lt_of_le h' (neg_nonneg.mpr ha)
                )
            )
    )



  example  (a b:ℝ) (x:ℝ) : abs (x-b) ≤ a ↔  x ∈ [b-a;b+a] :=
     dist_le_iff a b x
  /-
    calc
      abs (x-b) ≤ a ↔  x-b ∈ [-a; a]  := abs_le_iff  a (x-b)
      _             ↔  x ∈ [b-a;b+a] := Iff.and (Iff.trans (add_le_add_iff_right b).symm (by ring_nf)) (Iff.trans (add_le_add_iff_right b).symm (by ring_nf))
-/

  lemma dist_ge_iff  (a b:ℝ) (x:ℝ) : abs (x-b) ≥ a ↔  x ≤  b-a ∨ x ≥  b+a:=
    calc
      abs (x-b) ≥ a ↔  x-b ≤ -a ∨ x-b ≥ a  := abs_ge_iff  a  (x-b)
      _             ↔  x ≤  b-a ∨  x ≥  b+a   := Iff.or (Iff.trans (add_le_add_iff_right b).symm (by ring_nf)) (Iff.trans (add_le_add_iff_right b).symm (by ring_nf))


  lemma dist_lt_iff   (a b:ℝ) (x:ℝ) : abs (x-b) < a ↔  x ∈ (b-a;b+a) :=
    calc
      abs (x-b) < a ↔  x-b ∈ (-a; a)  := abs_lt_iff  a (x-b)
      _             ↔  x ∈ (b-a;b+a) := Iff.and (Iff.trans (add_lt_add_iff_right b).symm (by ring_nf)) (Iff.trans (add_lt_add_iff_right b).symm (by ring_nf))


  lemma dist_gt_iff   (a b:ℝ) (x:ℝ) : abs (x-b) > a ↔  x < b-a ∨ x > b+a:=
    calc
      abs (x-b) > a ↔  x-b < -a ∨ x-b > a  := abs_gt_iff  a  (x-b)
      _             ↔  x < b-a ∨  x> b+a   := Iff.or (Iff.trans (add_lt_add_iff_right b).symm (by ring_nf)) (Iff.trans (add_lt_add_iff_right b).symm (by ring_nf))


    example  (a b : ℝ ) : a ≤ b ∨ a > b := by exact le_or_gt a b 
    example  (a b : ℝ ) : a < b ∨ a ≥ b := by exact lt_or_le a b 

    lemma left_or_center_or_right  (x a b : ℝ ) : x < a ∨ (x ≥  a ∧ x<  b) ∨ x ≥ b := 
      Or.elim  (lt_or_le x a ) Or.inl
      (
        λ hxa ↦ 
          Or.elim  (lt_or_le x b ) 
          (
--            λ hxb'  ↦ Or.inr (Or.inl (And.intro hxa hxb'))
--            λ hxb'  ↦ Or.inr  <| Or.inl <| And.intro hxa hxb'
--             Or.inr  <| Or.inl <| And.intro hxa 
             Or.inr  ∘  Or.inl ∘  And.intro hxa 
          )
          (
            Or.inr  ∘  Or.inr
          )
      )

    example (a b c :ℝ ) : a ≤ b ↔ a+c ≤ b+c := by exact Iff.symm (add_le_add_iff_right c)  
    example (a b c :ℝ ) (hc:c>0) : a ≤ b ↔ a/c ≤ b/c := by exact Iff.symm (div_le_div_right hc)

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
             _                           ↔  _                   := Iff.intro (by tauto ) (λ o ↦ Or.elim o id (λ o' ↦ absurd o' (by linarith) ))
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
--             _                           ↔ x ≤ -5 ∨ _          := Iff.intro  False.elim (λ o ↦ Or.elim o (λ o1 ↦ by linarith) (λ o2 ↦ by linarith) )
             _                           ↔ _                   := Iff.intro  False.elim (λ o ↦ Or.elim o (λ o1 ↦ absurd (le_trans h.left o1) (by norm_num)) (λ o2 ↦ absurd (lt_of_lt_of_le h.right o2) (by norm_num) ) )
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
             _                           ↔ True                   := Iff.intro (λ _ ↦ trivial) (λ_ ↦ h )        -- by tauto
             _                           ↔ _                      := Iff.intro (λ _ ↦ Or.inr h) (λ _ ↦ trivial) --by tauto
      )




  lemma P_3_2_1_3 : {m | majorant (0;1) m } = [1;+∞) := 
    Set.ext (
      λ m ↦
        Iff.intro
        (
          λ h ↦ 
            le_of_not_lt (
              λ hm1: m<1 ↦
                Or.elim (lt_or_le m 0)
                  (
                    λ hm0 ↦ 
                      absurd 
                      (
                        calc
                          1/2 ≤ m := h (1/2) (by norm_num)
                          _   < 0 := hm0
                      )
                      (by norm_num)

                  ) 
                  (
                    λ hm0 ↦ 
                      let u:= (m+1)/2
                      have hum: u ≤ m := h u 
                       (
                        And.intro
                          (
                            calc
                              u = (m+1)/2 := rfl
                              _ ≥ (0+1)/2 := by rel[hm0]
                              _ > 0       := by norm_num

                          )
                          (
                            calc
                              u = (m+1)/2 := rfl
                              _ < (1+1)/2 := by rel[hm1]
                              _ = 1       := by norm_num

                          )
                       )
                      absurd 
                      (
                        calc
                          m  = (m+m)/2   := by ring_nf
                          _  < (m+1)/2   := by rel [hm1]
                          _  ≤ m         := hum
                      )
                      (lt_irrefl m)
                      
                  ) 
            )
        )
        (
          λ h ↦ 
            λ x hx ↦
--              le_of_lt (lt_of_lt_of_le hx.right h) 
                calc
                  x ≤ 1 := le_of_lt hx.right
                  _ ≤ m := h

        )
    )


--  def pge       {E:Type} [Ordonne E] (A: Set E) (m: E) : Prop  :=  (m ∈ A) ∧ (majorant A m)

lemma P_3_2_2_2  {E:Type} [Ordonne E] {A: Set E} {p q: E}  (hp : pge A p) (hq : pge A q) : p=q  :=
  Ordonne.le_antisymm p q
  (
     hq.right p hp.left
  )
  (
     hp.right q hq.left
  )



end chap3
