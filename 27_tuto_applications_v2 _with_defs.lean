import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

-----------------------
-- 27_tuto.lean
-- Nouvelles notions
-----------------------

--  Exemple 1 -----------------------
--   Application
--   Paramètres implicites

--  Exemple 2 -----------------------
--   injectivité, surjectivité, bijectivité
--   variable

--  Exemple 3 -----------------------
--   let
--   Dans cet exemple on traite l'ex18 du TD7
--  P → Q → R

--  Exemple 4 -----------------------
--   Applications et ensembles
--   Image directe, image réciproque
--   Set.univ

--  Exemple 5 -----------------------
--    Banque d'exercices


------------------------------------------------------------------
--- Exemple 1
------------------------------------------------------------------
-- Nouvelles notions
--   Application
--   Paramètres implicites

-- En Lean, si E et F sont deux types, il existe un type application de E dans F,
-- noté E → F  qui est le type des applications qui à un objet de type E associent un objet de type F

-- Si  x:E   et f : E → F   alors   f x  est de type F ; c'est l'image de x par f
-- Pour définir une application, on pourra utiliser le mot clé  fun

-- Par exemple : si E est un type, définissons l'identité de E :

def identite (E:Type) : E → E := fun x ↦ x

#check identite ℝ
#reduce identite ℝ

#check  identite ℕ
#check (identite ℕ) 2
#eval (identite ℕ) 2

-- on pourrait aussi écrire:
def identite_bis (E:Type) := fun x:E ↦ x


-- on souhaite définir la notion de fonction constante . Voici une définition possible:
namespace premier_essai

  def constante (E:Type) (F:Type) (f:E → F) : Prop := ∃k:F, ∀x:E, f x = k

  -- Il est obligatoire de préciser E et F comme paramètres de la définition,
  -- parce que sinon (f:E→F ) n'aurait pas de sens.

  -- on peut définir la fonction constante à k ...
  def fonction_constante (E:Type) (F:Type) (k:F) : E→ F := fun x ↦ k

  -- ... et prouver qu'elle est constante...
  example : ∀ (E:Type), ∀ (F:Type), ∀(k:F) , constante E F (fonction_constante E F k) :=
    λ E:Type ↦
      λ F:Type ↦
        λ k:F ↦
          Exists.intro k
            λ x:E ↦
              (rfl :  (fonction_constante E F k) x = k)

end premier_essai

-- Ce qui est correct, mais un peu lourd, parce qu'on doit répéter les paramètres E et F
-- En fait, dans essai_constante, si on donne f, Lean peut deviner E et F puisque f est de type E→F
-- Certains paramètres peuvent être implicites : ils sont donnés entre accolades {} au lieu des parenthèses

def constante {E:Type} {F:Type} (f:E → F) : Prop := ∃k:F, ∀x:E, f x = k

-- de même pour définir la fonction constante à k :  Lean pourra deviner F puisque k:F
def fonction_constante (E:Type) {F:Type} (k:F) : E→ F := fun x ↦ k

-- ... et le petit théorème :
example : ∀ (E:Type), ∀ (F:Type), ∀(k:F) , constante  (fonction_constante E k) :=
  λ E:Type ↦
    λ F:Type ↦
      λ k:F ↦
        Exists.intro k
          λ x:E ↦
            (rfl :  (fonction_constante E k) x = k)


-- Exercice 1.1

-- Enoncez puis Montrez que si E comporte deux éléments distincts alors l'identité de E n'est pas constante:
example : ∀ (E:Type), (∃x:E, ∃y:E, x≠ y) → sorry :=
  sorry


-- Exercice 1.2

-- Enoncez puis Montrez que la somme de deux applications constantes de E dans ℝ est une application constante
example : ∀ (E:Type), ∀  (f g : E→ℝ  ) , sorry :=
  sorry


------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------
-- Nouvelles notions
--   injectivité, surjectivité, bijectivité
--   variable

-- Exercice 2.1

-- Donnez les définition d'une application injective surjective, bijective de E dans F
-- Les paramètres E et F   devront être implicites

  def injective  {E:Type} {F:Type} (f: E → F) : Prop  := ∀ (u:E), ∀ (v:E), ( f u = f v → u = v )
  def surjective {E:Type} {F:Type} (f: E → F) : Prop  := ∀ (y:F), ∃ (x:E), y = f x
  def bijective  {E:Type} {F:Type} (f: E → F) : Prop  := (injective f) ∧ (surjective f)

-- Exercice 2.2
-- Montrez que l'identité est injective
  theorem identite_injective {E:Type}  : injective  (identite E)  :=
    sorry

-- Exercice 2.2
-- Montrez que l'identité est surjective
  theorem identite_surjective  : sorry  :=
    sorry

-- Exercice 2.3
-- Montrez que l'identité est bijective
  theorem identite_bijective  : sorry  :=
    sorry




  -- On remarque que dans les théorèmes et définitions précédentes, on a du
  -- systématiquement préciser  {E:Type} et  parfois {F:Type} en paramètres (implicites)

  -- Comme cette situation va se reproduire de nombreuses fois jusqu'à la fin du document,
  -- on peut les déclarer comme 'variables' c'est-à-dire que E, F, et parfois G seront
  -- systématiquement considérés comme des paramètres implicites de toutes les définitions
  -- et les théorèmes qui vont suivre, dès lors que les symboles E,F,G apparaissent dans leur énoncé :

  variable {E F G : Type}



  -- Exercice 2.4
  -- Montrez que la composée de deux applications injectives est injective

  theorem composee_injections : ∀ f: E → F, ∀ g : F → G, ((injective f)∧ (injective  g)) → (injective (g ∘ f)) :=
    sorry

  -- Exercice 2.5
  -- Enoncez puis Montrez que la composée de deux applications surjectives est surjective

  theorem composee_surjections : ∀ f: E → F, ∀ g : F → G, ((surjective f)∧ (surjective g)) → (surjective (g ∘ f)) :=
    sorry

  -- Exercice 2.6
  -- Enoncez puis Montrez que la composée de deux applications bijectives est bijective

  theorem composee_bijections  : ∀ f: E → F, ∀ g : F → G, ((bijective f)∧ (bijective g)) → (bijective (g ∘ f)) :=
    sorry



------------------------------------------------------------------
--- Exemple 3
------------------------------------------------------------------
-- Nouvelles notions
--   let
--   Dans cet exemple on traite l'ex18 du TD7
--  P → Q → R

-- La construction let permet d'introduire un symbole désignant un terme intermédiaire,
-- utile en général pour simplifier l'écriture de la fin du terme de preuve

  theorem exemple_let :  ∀ u:E → F,  ∀ v:F → G, surjective (v ∘  u) → (surjective v) :=
  λ (u:E → F) (v:F → G) ↦
    λ h : surjective (v ∘  u)   ↦
      λ (z:G) ↦
        Exists.elim (h z) (
          λ (x:E) (hx : z = (v ∘  u) x) ↦
            let y: F := u x
            Exists.intro y (
              (hx : z = v y)
            )
        )

-- Exercice 3.1   (cf TD7 ex 18)
  theorem TD7ex18q1 : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (injective u) :=
    sorry


-- L'énoncé   P → Q → R  (si P alors (si Q alors R))  est équivalent à (P∧Q) → R  (si P et Q alors R)
-- ça a l'air plus alambiqué mais c'est en général plus facile à manipuler.
example (P Q:Prop): P → Q → P :=
  λ hP : P ↦
    λ hQ : Q ↦
      (hP : P)

-- au lieu de :

example (P Q:Prop): P ∧ Q → P :=
  λ hPQ : P ∧ Q ↦
      (hPQ.left : P)



-- Exercice 3.2   (cf TD7 ex 18)

  theorem TD7ex18q2 : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (surjective u)→ (injective v)  :=
    sorry

-- Exercice 3.3   (cf TD7 ex 18)
  theorem TD7ex18q4 : ∀  (u: E → F) (v: F → G), surjective (v ∘  u) → (injective v) → (surjective u) :=
    sorry



------------------------------------------------------------------
--- Exemple 4
------------------------------------------------------------------
-- Nouvelles notions
--   Applications et ensembles
--   Image directe, image réciproque
--   Set.univ


-- Exercice 4.1
-- Donnez une definition de Imf.
def ensemble_image  (f: E → F) : Set F := {y:F | ∃ x:E, y = f x }

-- Exercice 4.2
-- Donnez la définition d'image directe, image réciproque

def image_directe    (f: E → F) (A: Set E) : Set F := {y:F | ∃ x:E, (x ∈ A) ∧ (y = f x) }
def image_reciproque (f: E → F) (B: Set F) : Set E := {x:E | (f x)∈ B }

-- Exercice 4.3
-- Montrez que Im f = f< E >
-- Attention : dans l'assertion ci-dessus E désigne un ensemble (l'ensemble des éléments de type E)
--   et non le type E ; en Lean il faudra donc écrire (@Set.univ E)
--   ou bien simplement, s'il n'y a pas d'ambiguité, Set.univ

theorem ensemble_image_egale_image_depart:
  ∀ f: E → F, ensemble_image f = image_directe f (@Set.univ E) :=
    sorry



-- Exercice 4.4
-- Montrez que (f surjective) <=> Im f = F   (idem F est ici @Set.univ F)

theorem reformulation_surjectivite :
    ∀  (f: E → F), (surjective f) ↔ (ensemble_image f = @Set.univ F)
  :=
    sorry



-- Exercice 4.5
theorem image_directe_intersection :
  ∀ (f: E→ F) (A: Set E) (B: Set E), image_directe f (A ∩ B) ⊆ (image_directe f A) ∩ (image_directe f B)
:=
  sorry



-- Exercice 4.6
  theorem image_directe_union :
    ∀ (f: E→ F) (A: Set E) (B: Set E), image_directe f (A ∪ B) = (image_directe f A) ∪ (image_directe f B) :=
    sorry


-- Exercice 4.7
  theorem image_reciproque_intersection :
    ∀ (f: E→ F) (H: Set F) (K: Set F), image_reciproque f (H ∩ K) = (image_reciproque f H) ∩ (image_reciproque f K) :=
    sorry

-- Exercice 4.8
  theorem image_reciproque_union :
    ∀ (f: E→ F) (H: Set F) (K: Set F), image_reciproque f (H ∪ K) = (image_reciproque f H) ∪ (image_reciproque f K) :=
    sorry



------------------------------------------------------------------
--- Exemple 5
------------------------------------------------------------------
-- Plein d'exercices pour s'entrainer !

-- Exercice 5.1
  example : ∀ (f: E→ F) (g:F→ G) (A: Set E), image_directe g (image_directe f A) = image_directe (g ∘ f) A := sorry

-- Exercice 5.2
  example : ∀ (f: E→ F) (g:F→ G) (C: Set G), image_reciproque f (image_reciproque g C) = image_reciproque (g ∘ f) C := sorry

-- Exercice 5.3
  lemma ex_5_3 :  ∀  (f: E → F), ∀ (B:Set F), ( (image_directe f (image_reciproque f B)) ⊆ B) := sorry

-- Exercice 5.4
  example : ∀ (f: E → F), ∀ (B:Set F),  (image_directe f (image_reciproque f B)) = B ∩ (ensemble_image f) := sorry

-- Exercice 5.5
  lemma ex_5_5 : ∀ (f: E → F),  ∀ (A:Set E), (A ⊆  (image_reciproque f (image_directe f A))) := sorry

-- Exercice 5.6
  lemma ex_5_6 : ∀  (f: E → F),  (surjective f) → ∀ (H:Set F), (H ⊆  (image_directe f (image_reciproque f H))) := sorry

-- Exercice 5.7
  example :  ∀  f: E → F, ∀ A: Set E, Set.Nonempty A → Set.Nonempty (image_directe f A) := sorry

-- Exercice 5.8
  lemma ex_5_8 :  ∀  f: E → F, ∀ A: Set E,  Set.Nonempty (image_directe f A) → Set.Nonempty A := sorry

-- Exercice 5.9
#check Set.not_nonempty_iff_eq_empty
#check Set.singleton_nonempty
#check Set.subset_eq_empty
#check Set.not_nonempty_iff_eq_empty.not_right.mpr
#check Set.eq_of_mem_singleton
#check ex_5_8

 lemma ex_5_9 : ∀  (f: E → F), (∀ (H:Set F), H ⊆  (image_directe f (image_reciproque f H)) ) →  (surjective f)   := sorry


-- Exercice 5.10
  #check subset_antisymm
  #check Eq.subset
  #check ex_5_3
  #check ex_5_6
  #check ex_5_9

  example :  ∀  (f: E → F), (surjective f) ↔  (∀ (H:Set F), H =  (image_directe f (image_reciproque f H)) )  := sorry


-- Exercice 5.11
  lemma ex_5_11 : ∀  (f: E → F), (injective f) → (∀ (A:Set E), ((image_reciproque f (image_directe f A)) ⊆ A)) := sorry

-- Exercice 5.12
  #check Set.eq_of_mem_singleton
  #check Set.mem_singleton

  lemma ex_5_12 : ∀  (f: E → F), ∀ (x:E), (image_directe  f {x}) = {f x} := sorry

-- Exercice 5.13
  #check ex_5_12
  lemma ex_5_13 :  ∀  (f: E → F), (∀ (A:Set E), ((image_reciproque f (image_directe f A)) ⊆ A))   → (injective f) := sorry

-- Exercice 5.14
#check subset_antisymm
#check subset_refl
#check ex_5_11
#check ex_5_5
#check ex_5_13
example : ∀  (f: E → F), (injective f) ↔  (∀ (A:Set E), ((image_reciproque f (image_directe f A)) = A)) := sorry

-- Exercice 5.15
#check Set.not_subset
#check Set.Nonempty.not_subset_empty
#check Set.singleton_nonempty
#check Set.mem_singleton_iff
#check Set.mem_of_mem_of_subset

  example :  ∀ (f: E → F), (surjective f) ↔ (∀ B₁:Set F, ∀ B₂:Set F, ( ( (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) → ( B₁ ⊆ B₂) )  ) := sorry

-- Exercice 5.16
  #check subset_antisymm
  #check Set.mem_singleton
  #check ex_5_8

  example : ∀ (f:E → F), (injective f)  ↔ (∀ A: Set E, ∀ B: Set E, image_directe f (A∩B) = (image_directe f A)∩ (image_directe f B)) := sorry

-- Exercice 5.17
  #check Set.subset_empty_iff
  lemma ex_5_17 : ∀ f:E→ F, image_directe f ∅ = ∅   := sorry

-- Exercice 5.18
  #check @mt
  #check @not_imp_not
  #check Set.compl_empty
  #check @Set.eq_of_mem_singleton
  #check Set.mem_singleton
  #check ensemble_image_egale_image_depart
  #check ex_5_17

  example :  ∀ f:E→ F, (bijective f) ↔ (∀ A:Set E, image_directe f (Aᶜ) = (image_directe f A)ᶜ  ) := sorry
