import Mathlib.Data.Set.Basic   -- librairie à importer pour utiliser les ensembles (Set)
import Mathlib.Data.Finset.Basic
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
-- 14_tuto.lean
-- Nouvelles notions
-----------------------

--  Exemple 1 -----------------------
--    Notion d'ensemble
--    Notation d'un ensemble en compréhension
--    Appartenance (et non-appartenance) à un ensemble

--  Exemple 2 -----------------------
--     Inclusion

--  Exemple 3 -----------------------

--  Exemple 4 -----------------------

--  Exemple 5 -----------------------

--  Exemple 6 -----------------------

--  Exemple 7 -----------------------

--  Exemple 8 -----------------------

--  Exemple 9 -----------------------

--  Exemple 10 -----------------------

--  Exemple 11 -----------------------



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

#check ({(1:ℕ) ,2}:Set ℕ )

example : 1 ∈ ( {1,2 } : Set ℕ  ):=  Or.inl rfl

def A : Set ℕ := {1,2}
example : 1 ∈ A :=  Or.inl rfl
example : 1 ∈ A :=  by tauto



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


#print Set.union

example (α : Type) (A B : Set α ) : Set.union A B = A ∪ B := rfl
def incls  (α : Type) (A B : Set α ) : Prop := A ⊂ B
def incll  (α : Type) (A B : Set α ) : Prop := A ⊆ B

def s  (α : Type) : Set α → Set α → Prop := (· ⊂ · )
#check s
#print s
#reduce s

#print Set
variable (α : Type)
#reduce ((· ⊂ · ) : Set α → Set α → Prop)
#reduce ((· ⊆ · ) : Set α → Set α → Prop)
#reduce ((· ∪ · ) : Set α → Set α → Set α)


lemma dblincs  (α : Type) (A B : Set α )  ( h1  : A ⊂ B) (h2 : B ⊂ A ) : False :=
  absurd h1.left h2.right

#reduce ((· ⊂ · ) : Set α → Set α → Prop)


lemma dblincs'  (α : Type) (A B : Set α )  ( h1  : A ⊂ B) (h2 : B ⊂ A ) : False :=
  absurd h2.left h1.right

#print Set.Subset

def Subset' (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

-- Exercice 1.1



------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------
-- Nouvelles notions
--   Inclusion


example :  {x:ℤ | ∃ k:ℤ, x = 6*k } ⊆ {x:ℤ | ∃ k:ℤ, x = 3*k }  :=  sorry

example  (E:Type):  ∀ A:Set E, A ⊆ A  :=  sorry











-- Exercice 3.2
-- Redémontrez ce lemme de la bibliothèque :
example (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  := Set.Subset.antisymm_iff

--vous pouvez utiliser  subset_refl_esisar  démontré à l'exercice 2.2
lemma set_eq_iff_esisar (E : Type) (A B : Set E ) : A = B ↔ A ⊆ B ∧ B ⊆ A  :=
  Iff.intro
  (
    λ h: A = B ↦
      And.intro
        (h ▸  (subset_refl_esisar E B))
        (h ▸  (subset_refl_esisar E A))
  )
  (
    λ h : A ⊆ B ∧ B ⊆ A  ↦
      Set.ext
        (
          λ x: E ↦
            Iff.intro
            (
              λ hA : x ∈ A ↦
                (h.left hA : x ∈ B)
            )
            (
              λ hB : x ∈ B ↦
                (h.right hB : x ∈ A)
            )
        )
  )

lemma subst.{v}  {α : Sort v} (motive : α → Prop) {a b : α} (h₁ : a = b) (h₂ : motive a) : motive b
  := @Eq.subst α motive a b h₁ h₂


example :  {x:ℤ | ∃ k:ℤ, x = 4*k } ≠ {x:ℤ | ∃ k:ℤ, x = 2*k }  :=
  λ h ↦
    have : 2 ∈  {x:ℤ | ∃ k:ℤ, x = 2*k } := Exists.intro 1 (by norm_num)
--    have : 2 ∈  {x:ℤ | ∃ k:ℤ, x = 4*k } := h ▸ this
--    have : 2 ∈  {x:ℤ | ∃ k:ℤ, x = 4*k } := subst _ h.symm this
--    have : 2 ∈  {x:ℤ | ∃ k:ℤ, x = 4*k } := subst (fun Z ↦ (2 ∈ Z)) h.symm this
    have : 2 ∈  {x:ℤ | ∃ k:ℤ, x = 4*k } := subst (2 ∈ ·) h.symm this
    Exists.elim this
      (
        λ k hk ↦
          Or.elim (le_or_gt k 0)
            (
              λ h0 : k ≤ 0 ↦
                absurd
                (
                  calc
                    2 = 4*k := hk
                    _ ≤ 4*0 := by rel[h0]
                )
                (by norm_num)
            )
            (
              λ h1 : k ≥ 1 ↦
                absurd
                (
                  calc
                    2 = 4*k := hk
                    _ ≥ 4*1 := by rel[h1]
                )
                (by norm_num)
            )
      )


example (E : Type) (A B : Set E ) : A = B →  (∀ x:E , x ∈ A ↔ x ∈ B )  := λ a x ↦ Iff.of_eq (congrArg (Membership.mem x) a)

example (E : Type) (A B : Set E ) : A = B →  (∀ x:E , x ∈ A ↔ x ∈ B )  := λ h _ ↦ h ▸ Iff.rfl

example (E : Type) (A B : Set E ) :  ¬(∀ x:E , x ∈ A ↔ x ∈ B ) → A ≠  B := λ n h ↦ absurd (λ _ ↦ h ▸ Iff.rfl) n
example (E : Type) (A B : Set E ) :  (∃ x:E , ¬ (x ∈ A ↔ x ∈ B))  → A ≠  B := λ e h ↦ absurd (λ _ ↦ h ▸ Iff.rfl) (not_forall.mpr e)
example (E : Type) (A B : Set E ) (x:E ) :  (x ∈ A ∧  x ∉  B) ∨ (x ∈ B ∧  x ∉  A) → ¬ (x ∈ A ↔ x ∈ B) :=
  λ  a ↦ (fun P Q ↦ (xor_iff_not_iff P Q).mp) (x ∈ A) (x ∈ B) a

example  (E : Type)  (P Q : E → Prop) (h: ∀ x:E, P x → Q x):  (∃ x:E, P x) → (∃ x:E, Q x) :=
  λ a ↦ Exists.imp h a

example (E : Type) (A B : Set E ) :  (∃ x:E , (x ∈ A ∧  x ∉  B) ∨ (x ∈ B ∧  x ∉  A) )  → A ≠  B :=
  λ e' h ↦
    absurd (λ _ ↦ h ▸ Iff.rfl) (not_forall.mpr (
      Exists.imp (λ x h' ↦(fun P Q ↦ (xor_iff_not_iff P Q).mp) (x ∈ A) (x ∈ B) h' ) e'
    ))

example (E : Type) (A B : Set E ) :  (∃ x:E , (x ∈ A ∧  x ∉  B) ∨ (x ∈ B ∧  x ∉  A) )  → A ≠  B :=
  λ h n ↦
    Exists.elim h (
      λ x hx ↦
        Or.elim hx
        (
          λ hx1 ↦
            absurd hx1.left (n ▸ hx1.right)
        )
        (
          λ hx2 ↦
            absurd hx2.left (n.symm ▸ hx2.right)
        )
    )


theorem iff_arg.{u}   {α : Sort u}  {a₁ a₂ : α} (f : α → Prop) :  a₁ = a₂ → (f a₁ ↔ f a₂) :=
    λ h =>
      subst  (fun z ↦ (f a₁ ↔ f z)  ) h (Iff.refl _)



example (E : Type) (A B : Set E ) : A = B →  (∀ x:E , x ∈ A ↔ x ∈ B )  := λ h x ↦ iff_arg (fun Z ↦ x ∈ Z) h
example (E : Type) (A B : Set E ) : A = B →  (∀ x:E , x ∈ A ↔ x ∈ B )  := λ h x ↦ subst  (fun Z ↦ ((x ∈ A) ↔ (x ∈ Z))) h Iff.rfl





-- Exercice 4.1

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






-- Exercice 4.3

-- 4.x (a) un résultat préliminaire utile :
--def impair   (n:ℤ) : Prop := ∃ k:ℤ, n=2*k+1
--def pair   (n:ℤ) : Prop := ∃ k:ℤ, n=2*k
lemma int_not_odd_even : ∀ n:ℤ, ¬ (pairZ n ∧ impairZ n) :=
  λ n:ℤ ↦
    λ h :  (pairZ n ∧ impairZ n) ↦
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

example (b:ℕ ) :  ¬ (Int.NonNeg (Int.negSucc b)) := λ h ↦ nomatch h

example (n:ℤ) (h: n≥ 0) : ℕ  := match (n) with
  | Int.ofNat   a => a
  | Int.negSucc _ => nomatch h

example (n:ℤ) (h: n≥ 0) : ℕ  :=  Int.toNat n

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

example (a b : ℕ ) : - Int.ofNat (a+b) = - (Int.ofNat a) - (Int.ofNat b) :=
  calc
    - Int.ofNat (a+b)  = - ((Int.ofNat a) + (Int.ofNat b)) := by simp
    _                  = - (Int.ofNat a) - (Int.ofNat b)   := by ring_nf

lemma int_odd_or_even : ∀ n:ℤ, pairZ n ∨ impairZ n :=
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
example : Set.compl {n:ℤ | pairZ n} = {n:ℤ | impairZ n} :=
  Set.ext
    λ n:ℤ ↦
      Iff.intro
      (
        λ h : ¬ (pairZ n) ↦
         Or.elim (int_odd_or_even n)
         (
           λ hnpair: pairZ n ↦
             absurd hnpair h
         )
         (
           λ hnimpair: impairZ n ↦
             hnimpair
         )
      )
      (
        λ h : impairZ n ↦
          λ hnpair : pairZ n ↦
            absurd (And.intro hnpair h)  (int_not_odd_even n)
      )

-- ( vous pouvez admettre les deux lemmes précédents...)







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

instance : HDiff := ⟨ (λ E A ↦ (Set.univ ) \ A)  ⟩


#check ℝ \ {0}

-------------------------------------------------------------------------------
