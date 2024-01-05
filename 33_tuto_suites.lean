import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity


-- L'objectif de cette séance est de redémontrer dans Lean laplupart des résultats établis dans les chapitre 10 sur les suites
-- Par souci de simplicité, on se cantonnera
--     * aux suites de nombres réels
--     * aux suites définies ℕ → ℝ  c'est-à-dire commençant à l'indice 0


------------------------------------------------------------
--- Partie I :  Résultat utile pour les suites extraites
------------------------------------------------------------

-- Proposition 10.1.2.1, Exercice 10.1.2.2, Définition 10.1.2.3

def strictly_increasing_NN (φ: ℕ → ℕ ) : Prop := ∀ m n:ℕ , m<n → φ m < φ n

-- [Exercice I-1] Démontrez le résultat ci-dessous par récurrence (pour d'autres exemples sur la récurrence, voir 12_tuto )
-- Le lemme suivant pourrait être utile :
#check Nat.lt.base
example (n:ℕ): n < n+1 := Nat.lt.base n

-- et celui-ci
#check Nat.zero_le
example (n:ℕ): n ≥ 0 := zero_le n

theorem gt_id_of_strictly_increasing_NN (φ: ℕ → ℕ) (h: strictly_increasing_NN φ) : ∀ n:ℕ, φ n ≥ n :=
  -- introduit le raisonnement par récurrence
  Nat.rec
    -- initialisation
    (sorry: φ 0 ≥ 0)

    -- hérédité
    (
      λ (n:ℕ) (ih: φ n ≥ n) ↦
        (sorry : (φ (n+1) > n  ))
    )


------------------------------------------------------------
--- Partie II :  Premières définitions et propriétés
------------------------------------------------------------

 -- Définition Définition 10.1.1.1.
def suite := ℕ → ℝ

-- On définit ici par commoditié les notations
--     (u+v) (somme de deux suites)
--     (u*v) (produit de deux suites)
--     (γ•u) (produit d'une suite par un scalaire ; le point • s'obtient avec \smul)

def suite_add (u:suite) (v:suite) : suite := fun n:ℕ ↦  ((u n) + (v n) )
instance suite_has_add : Add suite :=⟨suite_add⟩

def suite_mul (u:suite) (v:suite) : suite := fun n:ℕ ↦  ((u n) * (v n) )
instance suite_has_mul : Mul suite :=⟨suite_mul⟩

def suite_smul (γ:ℝ) (u:suite) : suite := fun n:ℕ ↦  (γ * (u n) )
instance suite_has_smul : SMul ℝ suite :=⟨suite_smul⟩


-- Définition 10.1.4.2.

--  [Exercice II-1] Donnez la définition d'une suite constante :
def constante    (u: suite) : Prop := sorry

--  [Exercice II-2] Donnez la définition d'une suite stationnaire :
def stationnaire (u: suite) : Prop := sorry

-- Voici la définition d'une suite bornée :
-- Définition 10.1.5.1.
def bornee       (u: suite) : Prop := ∃A:ℝ , ∀ n:ℕ ,  |u n| ≤ A

--  [Exercice II-3] Donnez la définition d'une suite bornée à partir d'un certain rang:
def bornee_a_partir_d_un_certain_rang (u: suite): Prop := sorry


--  [Exercice II-4] Enoncez puis prouvez que toute suite constante est stationnaire


-- Proposition 10.1.5.3.
-- A titre d'exemple, voici des preuves que le produit de deux suites bornées est une suite bornée....
theorem mul_bornee
   (u v: ℕ → ℝ)
   (hu : bornee u) (hv : bornee v)
  : bornee (u*v)
  :=
  Exists.elim (hu)
  (
    λ (A:ℝ) (hA : ∀ n:ℕ, |u n|≤A) ↦
      Exists.elim (hv)
      (
        λ (B:ℝ) (hB : ∀ n:ℕ, |v n|≤B) ↦
          Exists.intro (A*B)
            λ n:ℕ  ↦
              calc
                |(u*v) n| = |(u n) * (v n)|   := rfl
                _         = |u n| * |v n| := abs_mul _ _
                _         ≤ A * B         := mul_le_mul (hA n) (hB n) (abs_nonneg _) (le_trans (abs_nonneg _) (hA 0))

      )
  )

-- et que et le produit d'une suite bornée par un scalaire est une suite bornée....
theorem smul_bornee
   (γ:ℝ )  (u : ℕ → ℝ)
   (hu : bornee u)
  : bornee (γ • u)
  :=
  Exists.elim (hu)
  (
    λ (A:ℝ) (hA : ∀ n:ℕ, |u n|≤A) ↦
      Exists.intro (|γ| * A)
        λ n:ℕ  ↦
          calc
            |(γ • u) n| = |γ * (u n)|   := rfl
            _           = |γ| * |u n| := abs_mul _ _
            _           ≤ |γ| * A          := mul_le_mul (le_refl _) (hA n) (abs_nonneg _) (abs_nonneg _)

  )

-- [Exercice II-5] Maintenant prouvez que la somme de deux suites bornées est une suite bornée :
-- Vous pourrez avoir besoin de
#check abs_add    -- inégalité triangulaire
example (a b:ℝ ) : |a+b| ≤ |a| + |b| := abs_add a b

#check add_le_add    -- addition de deux inégalités
example (a b c d :ℝ)  (h1 : a≤c) (h2:b≤d ): a+b ≤ c+d := add_le_add h1 h2

theorem somme_bornee
   (u v: ℕ → ℝ)
   (hu : bornee u) (hv : bornee v)
  : bornee (u+v)
  :=
 sorry

-- [Exercice II-6] Montrez que toute suite extraite d'une suite bornée est une suite bornée
theorem extraite_bornee
   (u : ℕ → ℝ) (φ : ℕ → ℕ )
   (hu : bornee u) (hφ : strictly_increasing_NN φ )
  : bornee (u ∘ φ)
  :=
  sorry



-- Nous allons prouver ci-dessus que toute suite bornée à partir d'un certain rang est bornée
-- Pour cela, nous établissons par récurrence un premier résultat énonçant que toute suite finie est bornée :

#check Nat.of_le_succ
example (n m:ℕ ) (h: n≤ m+1) : n≤ m ∨ n=m+1 :=  Nat.of_le_succ h

-- notez bien ci-dessous l'utilisation des lemmes le_max_left et le_max_right qui nous seront très utiles par la suite :
#check le_max_left
#check le_max_right

example (a b : ℝ) : a ≤ max a b := le_max_left a b
example (a b : ℝ) : a ≤ max a b := le_max_left _ _
example (a b : ℝ) : b ≤ max a b := le_max_right a b
example (a b : ℝ) : b ≤ max a b := le_max_right _ _

theorem finie_bornee
   (u : ℕ → ℝ)
   : ∀ (n0 : ℕ), ∃ A:ℝ, ∀n:ℕ , n≤ n0 → |u n|≤ A
   :=
    Nat.rec
    (
      Exists.intro (|u 0|)
      (
        λ (n:ℕ) (hn : n ≤ 0) ↦
          have hn0 : n=0 := le_antisymm  hn (zero_le n)
          calc
            |u n| = |u 0| := by rw[hn0]
            _     ≤ |u 0| := le_refl _
      )
    )
    (
      λ (n0:ℕ) (ih : ∃ A:ℝ, ∀ (n : ℕ), n ≤ n0 → |u n| ≤ A) ↦
        Exists.elim (ih)
        (
          λ (A:ℝ) (hA : ∀ (n : ℕ), n ≤ n0 → |u n| ≤ A) ↦

            let B:= max A  (|u (n0+1)|)
            Exists.intro B
            (
              λ (n:ℕ) (hn : n ≤ n0+1) ↦
                Or.elim (Nat.of_le_succ hn)
                (
                  λ hn1 : n ≤ n0 ↦
                    calc
                      |u n| ≤ A := hA n hn1
                      _     ≤ B := le_max_left A _
                )
                (
                  λ hn2 : n = n0+1 ↦
                    calc
                      |u n| = |u (n0+1)| := by rw[hn2]
                      _     ≤ B          := le_max_right _ _
                )
            )
        )
    )

-- [Exercice II-7] Ensuite on prouve le résultat voulu :  complétez la preuve ci-dessous
-- (remarque : la définitin que vous avez donnée de bornee_a_partir_d_un_certain_rang doit etre correcte pour aborder cet exercice)
theorem bornee_rang_bornee
   (u : ℕ → ℝ)
   (hu : bornee_a_partir_d_un_certain_rang u)
   : bornee u

   :=

  Exists.elim (hu)
  (
    λ (n0:ℕ ) hn0 ↦
      Exists.elim (hn0)
      (
        λ (A:ℝ) (hA: ∀ n≥n0, |u n| ≤ A) ↦
          Exists.elim (finie_bornee u n0)
          (
            λ (B:ℝ) (hB:∀ n≤ n0, |u n| ≤ B) ↦
              let C:= max A B
              sorry
          )
      )

  )

-- [Exercice II-8] Utilisez le résultat précédent (bornee_rang_bornee) pour prouver que toute suite stationnaire est bornée
theorem stationnaire_bornee
   (u : ℕ → ℝ)
   (hu : stationnaire u)
  : bornee u
  :=
  sorry


------------------------------------------------------------
--- Partie III :  Monotonie
------------------------------------------------------------


-- Voici les définitions concernant la monotonie des suites
-- Définition 10.1.5.8.


def strictement_croissante (u: ℕ → ℝ ) : Prop := ∀ m n:ℕ , m<n → u m < u n
def croissante             (u: ℕ → ℝ ) : Prop := ∀ m n:ℕ , m≤n → u m ≤ u n

-- [Exercice III-1] Complétez les définitions ci-dessous
def strictement_decroissante (u: ℕ → ℝ ) : Prop := sorry
def decroissante             (u: ℕ → ℝ ) : Prop := sorry

def strictement_monotone     (u: ℕ → ℝ ) : Prop := sorry
def monotone                 (u: ℕ → ℝ ) : Prop := sorry


-- On peut prouver, par récurrence, que les définitions ci-dessus sont équivalentes aux caractérisations ci-dessous:

theorem rec_croissante (u: ℕ → ℝ ) : (croissante u) ↔ (∀ n:ℕ , u n ≤ u (n+1) ) :=
  Iff.intro
  (
    λ h: croissante u ↦
      λ n:ℕ ↦
        have : n ≤ n+1 := Nat.le_succ n
        h _ _ this
  )
  (
    λ h: ∀ n:ℕ , u n ≤ u (n+1) ↦
      λ m:ℕ ↦
        Nat.le_induction
        (le_refl _ : u m ≤ u m)
        (
          λ (n:ℕ) (_: m ≤ n) (hu : u m ≤ u n) ↦
            calc
              u m ≤ u n     := hu
              _   ≤ u (n+1) := h n
        )

  )

theorem rec_strictement_croissante (u: ℕ → ℝ ) : (strictement_croissante u) ↔ (∀ n:ℕ , u n < u (n+1) ) :=
  Iff.intro
  (
    λ h: strictement_croissante u ↦
      λ n:ℕ ↦
        have : n < Nat.succ n := Nat.lt.base n
        h _ _ this
  )
  (
    λ h: ∀ n:ℕ , u n < u (n+1) ↦
      λ m:ℕ ↦
        Nat.le_induction
        (h m)
        (
          λ (n:ℕ) (_: m+1 ≤ n) (hu : u m < u n) ↦
            calc
              u m < u n     := hu
              _   < u (n+1) := h n
        )

  )

-- [Exercice III-2] Complétez les preuves ci-dessous

theorem rec_decroissante (u: ℕ → ℝ ) : (decroissante u) ↔ (∀ n:ℕ , u n ≥ u (n+1) ) :=
  sorry

theorem rec_strictement_decroissante (u: ℕ → ℝ ) : (strictement_decroissante u) ↔ (∀ n:ℕ , u n > u (n+1) ) :=
  sorry

------------------------------------------------------------
--- Partie IV :  Convergence, limites
------------------------------------------------------------


  -- [Exercice IV-1] Complétez la définition de convergence d'une suite:

  def converge_vers (u:suite) (ℓ : ℝ) : Prop := ∀ ε:ℝ, ε >0 → sorry
  def converge (u:suite)              : Prop := ∃  ℓ : ℝ, converge_vers u ℓ


  -- Proposition 10.2.1.3

  -- 10.2.1.3(i) Un premier résultat important est l'unicité de la limite d'une suite
  -- On donne ici la preuve, mais vous pouvez la comparer à celle du cours, et observer l'utilisation des lemmes
  -- (pour beaucoup, déjà utilisés plus haut) :
  #check abs_nonneg
  #check lt_or_eq_of_le
  #check abs_add       -- inegalité triangulaire
  #check abs_sub_comm
  #check add_le_add
  #check le_max_right
  #check le_max_left
  #check abs_eq_zero

  theorem unicite_limite
   (u : ℕ → ℝ) (ℓ ℓ' : ℝ)
   (h : converge_vers u ℓ) (h': converge_vers u ℓ')
  : ℓ = ℓ'
  :=
    let ε := |ℓ' - ℓ| /3
    have hε0: 0 ≤ |ℓ' - ℓ|/3  :=  have : _ := abs_nonneg (ℓ' - ℓ ) ; by linarith

    Or.elim (lt_or_eq_of_le hε0)
    (λ hε0': ε > 0 ↦

      Exists.elim (h ε hε0') (
        λ (n0:ℕ ) (h_n0: ∀ n:ℕ, n ≥ n0 → |u n - ℓ| ≤ ε) ↦

        Exists.elim (h' ε hε0') (
          λ (n1:ℕ ) (h_n1: ∀ n:ℕ, n ≥ n1 → |u n - ℓ'| ≤ ε) ↦
          let n2:=max n0 n1
          have h3ε: ε*3 ≤ ε*2 :=
            calc
              ε*3   = |ℓ' - ℓ|                          := by ring_nf
              _     = |(ℓ' - (u n2))  +  ((u n2) - ℓ)|  := by ring_nf
              _     ≤ |(ℓ' - (u n2))| + |((u n2) - ℓ)|  := abs_add _ _
              _     = |((u n2) - ℓ')| + |((u n2) - ℓ)|  := by rw [abs_sub_comm]
              _     ≤  ε + ε                           := add_le_add
                                                            (h_n1 n2 (le_max_right n0 n1))
                                                            (h_n0 n2 (le_max_left  n0 n1))
              _     = ε * 2                             := by ring_nf

            have h32 : (3:ℝ) ≤ 2 :=
              calc
                3 = ε*3/ε := by linarith
                _ ≤ ε*2/ε := by rel[h3ε]
                _ = 2     := by linarith

            absurd h32 (by norm_cast)
        )
      )
    )
    (λ hε0'': 0 =ε ↦
      have h_dℓℓ' : |ℓ' - ℓ|=0 :=
        calc
          |ℓ' - ℓ|= ε*3  := by ring_nf
          _       = 0*3  := by rw[hε0'']
          _       = 0    := by norm_cast

      have h_ℓℓ': ℓ' - ℓ = 0 := abs_eq_zero.mp h_dℓℓ'
      (by linarith : ℓ = ℓ')
    )


-- [Exercice IV-2] Montrez que toute suite convergente est bornée ( 10.2.1.3(ii))
-- Vous pourrez commencer par prouver que toute suite convergente est bornée à partir d'un certain rang
-- puis utiliser  bornee_rang_bornee
  theorem bornee_of_converge
    (u:ℕ  →  ℝ )
    (hu : converge u)
    : bornee u

    :=
    sorry



  -- Je donne ci-dessous pour information les preuves des ( 10.2.1.3(iii),(iv), (v))

  theorem converge_lim_iff_sub_lim_converge_zero
    (u:ℕ → ℝ) (ℓ:ℝ)
   : (converge_vers u ℓ) ↔ (converge_vers (fun n:ℕ ↦ (u n - ℓ))  0 )

   :=
     let v:=fun n:ℕ ↦ (u n - ℓ)

     Iff.intro
     (
      λ h:converge_vers u ℓ ↦
        λ (ε:ℝ) (hε:ε>0) ↦
          Exists.elim (h ε hε)
          (
            λ (n0:ℕ) (hn0:∀ n≥ n0, |u n - ℓ| ≤ ε) ↦
              Exists.intro n0
                λ (n:ℕ) (hn:n≥n0) ↦
                  calc
                    |v n - 0| = |u n - ℓ| := by ring_nf
                    _         ≤ ε         := hn0 n hn
          )
     )
     (
      λ h:converge_vers v 0 ↦
        λ (ε:ℝ) (hε:ε>0) ↦
          Exists.elim (h ε hε)
          (
            λ (n0:ℕ) (hn0:∀ n≥ n0, |v n - 0| ≤ ε) ↦
              Exists.intro n0
                λ (n:ℕ) (hn:n≥n0) ↦
                  calc
                    |u n - ℓ| = |v n - 0|  := by ring_nf
                    _         ≤ ε          := hn0 n hn
          )
     )

  theorem converge_zero_iff_abs_converge_zero
    (u:ℕ → ℝ)
   : (converge_vers u 0) ↔ (converge_vers (fun n:ℕ ↦ |u n|)  0 )

   :=
     let v:=fun n:ℕ ↦ |u n|

     Iff.intro
     (
      λ h:converge_vers u 0 ↦
        λ (ε:ℝ) (hε:ε>0) ↦
          Exists.elim (h ε hε)
          (
            λ (n0:ℕ) (hn0: ∀ n≥ n0, |u n - 0| ≤ ε ) ↦
              Exists.intro n0
                λ (n:ℕ) (hn:n≥n0) ↦
                  calc
                    |v n - 0| = |v n|     := by ring_nf
                    _         = v n       := abs_of_nonneg (abs_nonneg _)
                    _         = |u n - 0| := by ring_nf
                    _         ≤ ε         := hn0 n hn
          )
     )
     (
      λ h:converge_vers v 0 ↦
        λ (ε:ℝ) (hε:ε>0) ↦
          Exists.elim (h ε hε)
          (
            λ (n0:ℕ) (hn0:∀ n≥ n0, |v n - 0| ≤ ε) ↦
              Exists.intro n0
                λ (n:ℕ) (hn:n≥n0) ↦
                  calc
                    |u n - 0| = v n       := by ring_nf
                    _         = |v n|     := (abs_of_nonneg (abs_nonneg _)).symm
                    _         = |v n - 0| := by ring_nf
                    _         ≤ ε         := hn0 n hn
          )
     )

  theorem converge_lim_iff_dist_lim_converge_zero
    (u:ℕ → ℝ) (ℓ:ℝ)
   : (converge_vers u ℓ) ↔ (converge_vers (fun n:ℕ ↦ |u n - ℓ|)  0 )

   :=
      calc
        (converge_vers u ℓ) ↔ (converge_vers (fun n:ℕ ↦ (u n - ℓ))  0 ) :=  converge_lim_iff_sub_lim_converge_zero u ℓ
        _                   ↔ (converge_vers (fun n:ℕ ↦ |u n - ℓ|)  0 ) :=  converge_zero_iff_abs_converge_zero (fun n:ℕ ↦ (u n - ℓ))


  theorem gendarmes_faible
    (u:ℕ → ℝ) (ℓ:ℝ)
    (v:ℕ → ℝ) (hv: converge_vers v 0)
    (hu: ∃n1:ℕ, ∀ n≥ n1, |u n - ℓ|≤ v n )
    : converge_vers u ℓ
    :=

    λ (ε:ℝ) (hε:ε>0) ↦
      Exists.elim (hv ε hε)
      (
        λ (n0:ℕ) (hn0: ∀ n≥ n0, |v n - 0| ≤ ε ) ↦

          Exists.elim (hu)
          (
            λ (n1:ℕ) (hn1: ∀ n≥ n1, |u n - ℓ| ≤ v n ) ↦
              let n2 := max n0 n1

              Exists.intro n2
                λ (n:ℕ) (hn:n≥n2) ↦
                  have huv : |u n - ℓ| ≤ v n  := hn1 n (ge_trans hn (le_max_right _ _))
                  calc
                    |u n - ℓ| ≤ v n       := huv
                    _         = |v n|     := (abs_of_nonneg (le_trans (abs_nonneg _) huv)).symm
                    _         = |v n - 0| := by ring_nf
                    _         ≤ ε         := hn0 n (ge_trans hn (le_max_left _ _))
          )
      )


  example (a b:ℝ) : |( |a| - |b| )| ≤ |a-b| := by exact abs_abs_sub_abs_le_abs_sub a b

  theorem abs_cv_of_cv   -- reciproque fausse !!
    (u:ℕ → ℝ) (ℓ:ℝ)
    (hu: converge_vers u ℓ)
    : converge_vers (fun n ↦ |u n| ) (|ℓ|)
    :=

    let v:=fun n:ℕ ↦ |u n - ℓ|
    let w:=fun n:ℕ ↦ |u n|
    have h0 : converge_vers v 0                    := (converge_lim_iff_dist_lim_converge_zero u ℓ).mp hu
    have h1 : ∃n1:ℕ, ∀ n≥ n1, |(w n - |ℓ|)|≤ v n   := Exists.intro 0 (λ (n:ℕ) _ ↦ abs_abs_sub_abs_le_abs_sub (u n) ℓ)

    gendarmes_faible w (|ℓ|) v h0 h1


-- [Exercice IV-3]    ( 10.2.1.3(vi) ) Montrez que si (u_n) converge alors toute suite qui en est extraite converge vers la meme limite
-- Vous pouvez utiliser le théorème  gt_id_of_strictly_increasing_NN   démontré en début de document
  theorem extraite_cv
    (u:ℕ → ℝ) (ℓ:ℝ)
    (hu: converge_vers u ℓ)
    (φ : ℕ → ℕ )
    (hφ : strictly_increasing_NN φ )
  : converge_vers (u ∘ φ) ℓ
  :=
   sorry

  -- La proposition  ( 10.2.1.3(vii) ) est un peu plus difficile, je vous l'offre...
  -- Exercice : la retranscrire sur papier

  example (p :ℕ )  : p+p = 2*p := by exact Eq.symm (Nat.two_mul p)
  example (p q:ℕ ) (h: p+p ≥  q+q) : p ≥ q := by exact Iff.mp bit0_le_bit0 h
  example (p q:ℕ ) (h: p+p+1 ≥  q+q+1) : p ≥ q := by exact Iff.mp Nat.bit0_lt_bit1_iff h

  theorem cv_of_odd_even_cv
    (u:ℕ → ℝ) (ℓ:ℝ)
    (hue: converge_vers (fun p ↦ u (2*p)) ℓ)
    (huo: converge_vers (fun p ↦ u (2*p+1)) ℓ)
  : converge_vers u ℓ
  :=
    λ (ε:ℝ) (hε:ε>0) ↦
      Exists.elim (hue ε hε)
      (
        λ (p0:ℕ) (hp0: ∀ p≥ p0, |u (2*p) - ℓ| ≤ ε ) ↦

          Exists.elim (huo ε hε)
          (
            λ (p1:ℕ) (hp1: ∀ p≥ p1, |u (2*p+1) - ℓ| ≤ ε ) ↦

              let n0 := max (p0+p0) (p1+p1+1)

              Exists.intro n0
                λ (n:ℕ) (hn:n≥ n0) ↦

                  Or.elim (Nat.even_or_odd n)
                  (
                    λ hne : Even n ↦
                      Exists.elim hne
                      (
                        λ (p:ℕ) (hp : n = p+p) ↦
                         have h2p2p0 : p+p ≥ p0+p0 := hp ▸ (ge_trans hn (le_max_left _ _))
                         calc
                           |u n - ℓ| = |u (2*p) - ℓ| := by rw[hp,two_mul p]
                           _         ≤ ε             := hp0 p (bit0_le_bit0.mp h2p2p0)
                      )
                  )
                  (
                    λ hno : Odd n ↦
                      Exists.elim hno
                      (
                        λ (p:ℕ) (hp : n = 2*p+1) ↦
                         have hp' : n = p+p+1 := by linarith
                         have h2p12p01 : p+p+1 ≥ p1+p1+1 := hp' ▸ (ge_trans hn (le_max_right _ _))
                         calc
                           |u n - ℓ| = |u (2*p+1) - ℓ| := by rw[hp,two_mul p]
                           _         ≤ ε             := hp1 p (Nat.bit0_lt_bit1_iff.mp h2p12p01)
                      )
                  )
          )
      )



 -- Proposition 10.2.2.1.

 -- Voici la preuve de  10.2.2.1. (i)
  theorem cv_to_nonzero_limit
    (u:ℕ → ℝ) (ℓ:ℝ) (hℓ : ℓ ≠ 0  )
    (hu: converge_vers u ℓ)
    : ∃ n0:ℕ, ∀ n≥ n0, |u n| ≥ |ℓ|/2

    :=

    have haℓ_pos  : |ℓ|   > 0 := abs_pos.mpr hℓ
    have haℓ2_pos : |ℓ|/2 > 0 := by linarith
    Exists.elim (hu (|ℓ|/2) haℓ2_pos)
    (
      λ (n0:ℕ) (hn0 : ∀ n≥n0, |u n - ℓ| ≤ |ℓ|/2  )  ↦
        Exists.intro n0
        (
          λ (n:ℕ) (hn:n≥n0) ↦
            calc
              |ℓ|/2 = |ℓ| - |ℓ|/2                  := by ring_nf
              _     = |ℓ- (u n) + (u n)| - |ℓ|/2   := by ring_nf
              _     ≤  |ℓ- (u n)| + |u n| - |ℓ|/2  := by rel[abs_add _ (u n)]
              _     =  |(u n) - ℓ| + |u n| - |ℓ|/2 := by rw[abs_sub_comm]
              _     ≤  |ℓ|/2 + |u n|  - |ℓ|/2      := by rel[add_le_add (hn0 n hn) (le_refl _)]
              _     =  |u n|                       := by ring_nf

        )
    )


-- [Exercice IV-4] Maintenant, à vous de jouer : prouvez  10.2.2.1. (iii)
-- Pour cela vous pourrez utiliser le lemme ci-dessous qui caractérise  une inégalité du type   |x-b| ≤ a
  lemma dist_le {a b:ℝ} {x:ℝ} : |x-b| ≤ a ↔ x ≥ b-a ∧ x ≤ b+a :=
    calc
      abs (x-b) ≤ a ↔ x-b ≥ -a ∧  x-b ≤ a  := abs_le
      _             ↔ x ≥ b-a ∧ x ≤ b+a    := Iff.and (Iff.trans (add_le_add_iff_right b).symm (by ring_nf)) (Iff.trans (add_le_add_iff_right b).symm (by ring_nf))


  theorem cv_to_pos_limit
    (u:ℕ → ℝ) (ℓ:ℝ) (hℓ : ℓ > 0  )
    (hu: converge_vers u ℓ)
    : ∃ n0:ℕ, ∀ n≥ n0, u n ≥ ℓ/2

    :=

    sorry


------------------------------------------------------------
--- Partie V :  Opérations sur les limites
------------------------------------------------------------


-- Dans cette partie, on prouve la Proposition 10.2.2.4.

-- Je propose de donner à titre d'exemple la preuve de 10.2.2.4. (iii) (produit de limites) qui est un peu technique ....

lemma L1 (A:ℝ ) : A ≤ A+1 :=  by norm_num -- by linarith--
#print L1

example (a b:ℝ ) (h:b≠0  ) : (a/b)*b = a := by exact div_mul_cancel a h
example (a b:ℝ ) (h:b≠0  ) : b*(a/b) = a := by exact?
example (a b c:ℝ ) (hb:b≠0  ) (hc: c ≠ 0) : (a/(b*c)) =  (a/b)/c  := by exact div_mul_eq_div_div a b c



  theorem prodlim
    (u:suite) (v:suite)  (ℓ : ℝ ) (ℓ' : ℝ )
    (hu: converge_vers u ℓ)
    (hv: converge_vers v ℓ')
  : (converge_vers (u*v) (ℓ*ℓ'))
  :=

      have hbv : bornee v := bornee_of_converge v (Exists.intro ℓ' hv)

      Exists.elim hbv
      (
        λ (A:ℝ) (hA : ∀n:ℕ , |v n|≤A ) ↦

          λ (ε:ℝ)   (hε : ε >0)  ↦

            let εA := ε / (2*(A+1))
            let εℓ := ε / (2*(|ℓ|+1))

            have h1A : A+1 > 0 :=
              calc
                A+1  ≥ |v 0|+1  := by rel[hA 0]
                _    ≥  0 + 1   := by rel[abs_nonneg (v 0)]
                _    > 0        := by norm_cast


            have h2A : 2*(A+1) > 0 := by linarith

            have h1ℓ : |ℓ|+1 > 0 :=
              calc
                |ℓ|+1  ≥  0 + 1   := by rel[abs_nonneg ℓ]
                _    > 0          := by norm_cast

            have h2ℓ : 2*(|ℓ|+1) > 0 := by linarith

            have hεA : εA > 0 := div_pos hε h2A
            have hεℓ : εℓ > 0 := div_pos hε h2ℓ

            have hεAmA : εA * (A+1) = ε/2 :=   -- by linarith (échoue)  -- by ring_nf (échoue) -- by aesop (échoue)
              calc
                εA * (A+1) =  (ε / 2)/(A+1) * (A+1)  := congr_arg (· * (A+1) ) (div_mul_eq_div_div ε  2 (A+1))
                _          =  ε/2                    := div_mul_cancel _ (ne_of_gt h1A)

            have hεℓmℓ : (|ℓ|+1) * εℓ  = ε/2 :=   -- by linarith (échoue)  -- by ring_nf (échoue) -- by aesop (échoue)
              calc
                (|ℓ|+1) *εℓ  =  (|ℓ|+1)*( (ε / 2)/(|ℓ|+1) )  := congr_arg ( (|ℓ|+1) * ·  ) (div_mul_eq_div_div ε 2 (|ℓ|+1))
                _            =  ε/2                         := mul_div_cancel' _ (ne_of_gt h1ℓ)


          Exists.elim (hu  εA  hεA   )
          (λ (n0:ℕ) ↦ λ  (hu' : ∀ (n:ℕ ), n ≥ n0 → |u n - ℓ| ≤ εA ) ↦
            Exists.elim (hv  εℓ  hεℓ )
            (
              λ (n1:ℕ)  (hv' :  ∀ (n:ℕ ), n ≥ n1 → |v n - ℓ'| ≤ εℓ )   ↦
              let n2:=(max n0 n1) ; Exists.intro n2 (
                λ (n:ℕ ) (h4: n ≥ n2) ↦
                calc
                  |(u*v) n - (ℓ * ℓ')| = |(u n * v n ) - (ℓ * ℓ')|                       := rfl
                  _                   = |u n * v n - ℓ * (v n) + ℓ * (v n) - (ℓ * ℓ')|   := by ring_nf
                  _                   = |(u n - ℓ) * v n  + ℓ * (v n - ℓ')|              := by ring_nf
                  _                   ≤ |(u n - ℓ) * v n| + |ℓ * (v n - ℓ')|             := abs_add _ _
                  _                   = |u n - ℓ| * |v n| + |ℓ| * |v n - ℓ'|             := by rw[abs_mul,abs_mul]
                  _                   ≤ εA * |v n|  + |ℓ| * εℓ                           := add_le_add
                                                              (mul_le_mul ((hu' n ( ge_trans h4 ( le_max_left  _ _) ))) (le_refl _) (abs_nonneg _) (le_of_lt hεA)  )
                                                              (mul_le_mul (le_refl _) ((hv' n ( ge_trans h4 ( le_max_right  _ _) ))) (abs_nonneg _) (abs_nonneg _)  )
                  _                   ≤ εA * (A+1)  + (|ℓ|+1) * εℓ                           := add_le_add
                                                              (mul_le_mul (le_refl _) (le_trans (hA n) (by norm_num) ) (abs_nonneg _) (le_of_lt hεA)  )
                                                              (mul_le_mul (by norm_num) (le_refl _) (le_of_lt hεℓ) (le_trans (abs_nonneg _) (by norm_num : |ℓ| ≤ |ℓ|+1)))

                  _                   = ε/2 + ε/2 := by rw[hεAmA,hεℓmℓ]

                  _                   = ε := by ring_nf
              )
            )

          )
      )



-- [Exercice V-1]   ... et de vous laisser la preuve de 10.2.2.4. (i) (somme de limites) qui est plus simple

  theorem sumlim
    (u:suite) (v:suite)  (ℓ : ℝ ) (ℓ' : ℝ )
    (hu: converge_vers u ℓ)
    (hv: converge_vers v ℓ')
  : (converge_vers (u+v) (ℓ+ℓ'))
  :=
   sorry


------------------------------------------------------------
--- Partie VI :  Limites infinies
------------------------------------------------------------



------------------------------------------------------------
--- Partie VII :  Suites de réels et ordre
------------------------------------------------------------






-- [Exercice VII-1]  Démontrez le Théorème des gendarmes
theorem gendarmes
   (u v w : ℕ → ℝ) (ℓ : ℝ)
   (hu : converge_vers u ℓ) (hw : converge_vers w ℓ)
   (h : ∀ n:ℕ , u n ≤ v n)
   (h' : ∀ n:ℕ , v n ≤ w n)
  : converge_vers v ℓ
  :=
  sorry

-- [Exercice VII-2]  Démontrez le Théorème de la limite d'une suite monotone
def supremum (u:ℕ→ ℝ ) (M:ℝ ) : Prop := (∀n:ℕ , u n ≤ M ) ∧ (∀ ε>0, ∃n:ℕ, u n > M - ε )

theorem theoreme_de_la_limite_d_une_suite_monotone
  (u : ℕ → ℝ) (M : ℝ)
  (h : supremum  u M) (h' : croissante u)
  : converge_vers u M

  :=

  sorry




------------------------------------------------------------
--- Partie VIII :  Suites adjacentes
------------------------------------------------------------


----------------------------------------------------------------
--- Partie IX :  Suites définies par une relation de récurrence
----------------------------------------------------------------
