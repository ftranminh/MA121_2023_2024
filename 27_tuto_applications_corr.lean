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

namespace solution
  example : ∀ (E:Type), (∃x:E, ∃y:E, x≠ y) → ¬(constante (identite E)) :=
    λ E:Type ↦
      λ h : (∃x:E, ∃y:E, x≠ y) ↦
        λ ha : constante (identite E) ↦
          Exists.elim h
          (
            λ (x:E) (hx: ∃y:E, x≠ y) ↦
              Exists.elim hx
              (
                λ (y:E) (hxny : x≠ y) ↦
                  Exists.elim ha
                  (
                    λ (k:E) (hk:∀x:E, (identite E) x=k) ↦
                      have hxy : x=y :=
                        calc
                          x = k := hk x
                          _ = y := (hk y).symm
                      absurd hxy hxny
                  )
              )
          )
end solution

-- Exercice 1.2

-- Enoncez puis Montrez que la somme de deux applications constantes de E dans ℝ est une application constante
example : ∀ (E:Type), ∀  (f g : E→ℝ  ) , sorry :=
  sorry

namespace solution
  example : ∀ (E:Type), ∀  (f g : E→ℝ  ) , constante f → constante g → constante (f+g) :=
    λ E:Type ↦
      λ f g : E → ℝ  ↦
        λ hf : constante f ↦ λ hg : constante g ↦
          Exists.elim (hf)
          (
            λ (kf:ℝ) (hkf : ∀x:E, f x =kf) ↦
              Exists.elim (hg)
              (
                λ (kg:ℝ) (hkg : ∀x:E, g x =kg) ↦
                  Exists.intro (kf+kg)
                  (
                    λ x: E ↦
                      calc
                        (f+g) x = f x + g x := rfl
                        _       = kf+kg     := by rw[hkf x,hkg x]
                  )
              )
          )
end solution


------------------------------------------------------------------
--- Exemple 2
------------------------------------------------------------------
-- Nouvelles notions
--   injectivité, surjectivité, bijectivité
--   variable

-- Exercice 2.1

-- Donnez les définition d'une application injective surjective, bijective de E dans F
-- Les paramètres E et F   devront être implicites

  def injective  {E:Type} {F:Type} (f: E → F) : Prop  := ∀ (u:E), ∀ (v:E), sorry
  def surjective  : sorry  := sorry
  def bijective   : sorry  := sorry

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



  namespace solution
    def injective  {E:Type} {F:Type} (f: E → F) : Prop  := ∀ (u:E), ∀ (v:E), ( f u = f v → u = v )
    def surjective {E:Type} {F:Type} (f: E → F) : Prop  := ∀ (y:F), ∃ (x:E), y = f x
    def bijective  {E:Type} {F:Type} (f: E → F) : Prop  := (injective f) ∧ (surjective f)

    theorem identite_injective {E:Type}  : injective  (identite E)  :=
        λ u:E ↦
            λ v:E ↦
              λ h:(identite E) u = (identite E) v ↦
                (h: u=v)

    theorem identite_surjective {E:Type} : surjective (identite E)  :=
      λ y:E ↦
        Exists.intro y (
          show y = identite y from Eq.refl y
        )

    theorem identite_bijective {E:Type} : bijective (identite E) :=
      And.intro identite_injective identite_surjective
  end solution

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

  namespace solution
    theorem composee_injections : ∀ f: E → F, ∀ g : F → G,  ((injective   f)∧ (injective  g)) → (injective (g ∘ f)) :=
      λ f: E → F ↦
        λ  g : F → G ↦
          λ (h1: (injective f)∧ (injective  g)) ↦
              λ (u v : E ) ↦
                λ (h2 : (g ∘ f) u = (g ∘ f) v) ↦
                  have h3 : f u = f v :=   h1.right (f u) (f v) h2
                  show        u = v   from  h1.left   u     v    h3


    theorem composee_surjections : ∀ f: E → F, ∀ g : F → G,  ((surjective f)∧ (surjective g)) → (surjective (g ∘ f)) :=
      λ f: E → F ↦
        λ  g : F → G ↦
          λ (h1: (surjective  f)∧ (surjective   g)) ↦
              λ (z : G  ) ↦
                have  h2: (∃ y:F , z = g y) :=  h1.right z
                Exists.elim h2 (
                  λ (y:F ) ↦  λ (h3: z = g y) ↦
                    have h4: ∃ x:E , y = f x :=  h1.left y
                    Exists.elim h4 (
                      λ (x:E )  ↦ λ (h5: y = f x) ↦
                        Exists.intro x (
                            calc
                              z   = g y   := h3
                              _ = g (f x) := congr_arg g h5
                          )
                    )
                )

    theorem composee_bijections  :  ∀ f: E → F, ∀ g : F → G, ((bijective f)∧ (bijective g)) → (bijective (g ∘ f)) :=
      λ f: E → F ↦
        λ  g : F → G ↦
          λ (h1: (bijective f)∧ (bijective g)) ↦
            have h2: bijective  f :=  h1.left
            have h3: bijective  g :=  h1.right
            have h4: injective  f :=  h2.left
            have h5: surjective f :=  h2.right
            have h6: injective  g :=  h3.left
            have h7: surjective g :=  h3.right
            have h8: injective  (g ∘ f) :=  composee_injections  f g (And.intro h4 h6)
            have h9: surjective (g ∘ f) :=  composee_surjections f g (And.intro h5 h7)
            show bijective  (g ∘ f) from And.intro h8 h9

  end solution


------------------------------------------------------------------
--- Exemple 3
------------------------------------------------------------------
-- Nouvelles notions
--   let
--   Dans cet exemple on traite l'ex18 du TD7

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

-- Exercice 3.2   (cf TD7 ex 18)
  theorem TD7ex18q2 : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (surjective u)→ (injective v)  :=
    sorry

-- Exercice 3.3   (cf TD7 ex 18)
  theorem TD7ex18q4 : ∀  (u: E → F) (v: F → G), surjective (v ∘  u) → (injective v) → (surjective u) :=
    sorry


namespace solution

  theorem TD7ex18q1 : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (injective u) :=
  λ  (u: E → F) (v: F → G) ↦
    λ (h: injective (v ∘  u)) ↦
      λ (x x':E) ↦
        λ  (hu:u x = u  x') ↦
          have hvu : v ( u x) = v (u x') := by rw[hu]
          h x x' hvu

  theorem TD7ex18q1' : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (injective u) :=
  λ  (u: E → F) (v: F → G) ↦
    λ (h: injective (v ∘  u)) ↦
      λ (x x':E) ↦
        λ  (hu:u x = u  x') ↦
          have hvu : v ( u x) = v (u x') :=  hu ▸ rfl
          h x x' hvu

  theorem TD7ex18q1'' : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (injective u) :=
  λ  (u: E → F) (v: F → G) ↦
    λ (h: injective (v ∘  u)) ↦
      λ (x x':E) ↦
        λ  (hu:u x = u  x') ↦
          have hvu : v ( u x) = v (u x') :=  congrArg v hu
          h x x' hvu

  theorem TD7ex18q2 : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (surjective u)→ (injective v)  :=
  λ  (u: E → F) (v: F → G) ↦
    λ (h1: injective (v ∘  u) )↦
      λ (h2 : surjective u)↦
        λ (y y':F)↦
          λ  (hv:v y = v y')↦
            Exists.elim (h2 y) (
              λ (x:E) (hx : y = u x)↦
                Exists.elim (h2 y') (
                  λ (x':E) (hx' : y' = u x') ↦
                    have hvu : v (u x)  = v (u x') :=   hx' ▸ hx ▸ hv
                    have hxx'     : x=x'           :=   h1 x x' hvu
                    calc
                      y = u x  := hx
                      _ = u x' := by rw[hxx']
                      _ = y'   := hx'.symm
                )
            )

  theorem TD7ex18q2' : ∀  (u: E → F) (v: F → G), (injective (v ∘  u) )→ (surjective u)→ (injective v)  :=
  λ  (u: E → F) (v: F → G) ↦
    λ (h1: injective (v ∘  u) )↦
      λ (h2 : surjective u)↦
        λ (y y':F)↦
          λ  (hv:v y = v y')↦
            Exists.elim (h2 y) (
              λ (x:E) (hx : y = u x)↦
                Exists.elim (h2 y') (
                  λ (x':E) (hx' : y' = u x') ↦
                    have hvu : v (u x)  = v (u x') :=   hx' ▸ hx ▸ hv
                    have hxx'     : x=x'           :=   h1 x x' hvu
                    show y =y'                     from  hx.symm ▸ hx'.symm ▸ (congrArg u hxx')
                )
            )

  theorem TD7ex18q3 : ∀  (u: E → F) (v: F → G), surjective (v ∘  u) → (surjective v) :=
  λ  (u: E → F) (v: F → G) ↦
    λ h : surjective (v ∘  u)   ↦
      λ (z:G) ↦
        Exists.elim (h z) (
          λ (x:E) (hx : z = (v ∘  u) x) ↦
            Exists.intro (u x) (
              show z = v (u x) from hx
            )
        )

  theorem TD7ex18q4 : ∀  (u: E → F) (v: F → G), surjective (v ∘  u) → (injective v) → (surjective u) :=
  λ  (u: E → F) (v: F → G) ↦
    λ h1 : surjective (v ∘  u) ↦
      λ h2: injective v ↦
        λ (y:F) ↦
          let z:= v y
          Exists.elim (h1 z)
          (
            λ (x:E) (hx: z = v (u x))  ↦
              Exists.intro x (
                show y = u x from h2 y (u x) hx
              )
          )
end solution


------------------------------------------------------------------
--- Exemple 4
------------------------------------------------------------------
-- Nouvelles notions
--   Applications et ensembles
--   Image directe, image réciproque
--   Set.univ


-- Exercice 4.1
-- Donnez une definition de Imf.
def ensemble_image  (f: E → F) : Set F := sorry

namespace solution
  def ensemble_image  (f: E → F) : Set F := {y:F | ∃ x:E, y = f x }
end solution

-- Exercice 4.2
-- Donnez la définition d'image directe, image réciproque

  def image_directe    (f: sorry) (A: Set E) : sorry := sorry
  def image_reciproque (f: sorry) (B: sorry) : sorry := sorry

namespace solution
  def image_directe    (f: E → F) (A: Set E) : Set F := {y:F | ∃ x:E, (x ∈ A) ∧ (y = f x) }
  def image_reciproque (f: E → F) (B: Set F) : Set E := {x:E | (f x)∈ B }
end solution

-- Exercice 4.3
-- Montrez que Im f = f< E >
-- Attention : dans l'assertion ci-dessus E désigne un ensemble (l'ensemble des éléments de type E)
--   et non le type E ; en Lean il faudra donc écrire (@Set.univ E)
--   ou bien simplement, s'il n'y a pas d'ambiguité, Set.univ

theorem ensemble_image_egale_image_depart:
  ∀ f: E → F, ensemble_image f = image_directe f (@Set.univ E) :=
    sorry

namespace solution
  theorem ensemble_image_egale_image_depart:
    ∀ f: E → F, ensemble_image f = image_directe f (@Set.univ E)
  :=
      λ f: E → F ↦
        Set.ext
          λ y:F ↦
            Iff.intro
            (
              λ h : y ∈ ensemble_image f ↦
                Exists.elim h
                (
                  λ (x:E) (hx: y = f x) ↦
                    Exists.intro x
                      (And.intro trivial hx : x ∈ Set.univ  ∧  y = f x  )
                )
            )
            (
              λ h : y ∈ image_directe f Set.univ ↦
                Exists.elim h
                (
                  λ (x:E) (hx: x ∈ Set.univ  ∧ y = f x) ↦
                    Exists.intro x
                      hx.right
                )
            )

  example :  ∀ f:E→ F, ensemble_image f = image_directe f (@Set.univ E) :=
    λ (f: E→ F) ↦  Set.ext (λ (y:F) ↦  Iff.intro
      (λ (h:y ∈ ensemble_image f ) ↦  Exists.elim h (λ (x:E) (h_yfx:y=f x) ↦  Exists.intro x (And.intro trivial h_yfx) ) )
      (λ (h:y ∈ image_directe f (@Set.univ E) ) ↦  Exists.elim h (λ (x:E) (h_y_and: x ∈ Set.univ ∧ y = f x) ↦  Exists.intro x h_y_and.right ) ))

end solution


-- Exercice 4.4
-- Montrez que (f surjective) <=> Im f = F   (idem F est ici @Set.univ F)

theorem reformulation_surjectivite :
    ∀  (f: E → F), (surjective f) ↔ (ensemble_image f = @Set.univ F)
  :=
    sorry


namespace solution

  theorem reformulation_surjectivite : ∀  (f: E → F), (surjective f) ↔ (ensemble_image f = @Set.univ F) :=
    λ  f: E → F ↦
      Iff.intro
        (λ  h_f_surjective : surjective f ↦
          Set.ext  (
            λ  y:F ↦
              Iff.intro
                (λ h_y_in_im: y ∈ ensemble_image f ↦
                  (trivial: y ∈ (@Set.univ F))
                )
                (λ h_y_in_set_univ: y ∈ (@Set.univ F) ↦
                  show ∃ x:E, y = f x  from h_f_surjective y
                )
          )
        )
        (λ h_im_eq_F: ensemble_image f = @Set.univ F ↦ λ y:F ↦
          (
            have h_y_in_F : y ∈ @Set.univ F :=  trivial
            show y ∈ (ensemble_image f)  from h_im_eq_F.symm ▸ h_y_in_F
          )

        )
end solution

-- Exercice 4.5
theorem image_directe_intersection :
  ∀ (f: E→ F) (A: Set E) (B: Set E), image_directe f (A ∩ B) ⊆ (image_directe f A) ∩ (image_directe f B)
:=
  sorry



namespace solution

  theorem image_directe_intersection : ∀ (f: E→ F) (A: Set E) (B: Set E), image_directe f (A ∩ B) ⊆ (image_directe f A) ∩ (image_directe f B) :=
     λ  (f: E→ F) (A: Set E) (B: Set E) ↦
       λ (y:F) (h_yfAB : y ∈ image_directe f (A ∩ B))  ↦
         Exists.elim h_yfAB (
           λ (x:E) (h_x_and : x ∈ A ∩ B ∧ y = f x ) ↦
            And.intro
              (Exists.intro (x:E) ( And.intro (h_x_and.left.left :x∈ A) (h_x_and.right : y = f x)))
              (Exists.intro (x:E) ( And.intro (h_x_and.left.right:x∈ B) (h_x_and.right : y = f x)))
          )

--  example : ∀ (f: E→ F), ∀ A: Set E, ∀ B: Set E, image_directe f (A∩B) = (image_directe f A)∩ (image_directe f B) := by slim_check

end solution

-- Exercice 4.6
  theorem image_directe_union :
    ∀ (f: E→ F) (A: Set E) (B: Set E), image_directe f (A ∪ B) = (image_directe f A) ∪ (image_directe f B) :=
    sorry

namespace solution

  theorem image_directe_union :  ∀ (f: E→ F) (A: Set E) (B: Set E), image_directe f (A ∪ B) = (image_directe f A) ∪ (image_directe f B) :=
     λ  (f: E→ F) (A: Set E) (B: Set E) ↦
      Set.ext (λ (y:F) ↦ Iff.intro
        (λ (h_yfAB : y ∈ image_directe f (A ∪ B))  ↦
          Exists.elim h_yfAB (
            λ (x:E) (h_x_and : x ∈ A ∪ B ∧ y = f x ) ↦
              Or.elim h_x_and.left
                (λ (h_xA:x∈ A) ↦ Or.inl  (Exists.intro (x:E) (And.intro (h_xA:x∈ A) (h_x_and.right:y =f x))) )
                (λ (h_xB:x∈ B) ↦ Or.inr  (Exists.intro (x:E) (And.intro (h_xB:x∈ B) (h_x_and.right:y =f x))) )
            )
        )
        (
           λ h_yfAfB : y ∈ (image_directe f A) ∪ (image_directe f B) ↦
            Or.elim h_yfAfB
              (λ h_yfA: y ∈ (image_directe f A) ↦
                Exists.elim h_yfA (
                  λ (x:E) (h_x_and: x∈ A ∧ y = f x) ↦
                    Exists.intro (x:E) (And.intro ((Or.inl h_x_and.left):x ∈ A ∪ B ) (h_x_and.right:y=f x))
                )
              )
              (λ h_yfB: y ∈ (image_directe f B) ↦
                Exists.elim h_yfB (
                  λ (x:E) (h_x_and: x∈ B ∧ y = f x) ↦
                    Exists.intro (x:E) (And.intro ((Or.inr h_x_and.left):x ∈ A ∪ B ) (h_x_and.right:y=f x))
                )
              )
        )
      )
end solution

-- Exercice 4.7
  theorem image_reciproque_intersection :
    ∀ (f: E→ F) (H: Set F) (K: Set F), image_reciproque f (H ∩ K) = (image_reciproque f H) ∩ (image_reciproque f K) :=
    sorry

namespace solution

  theorem image_reciproque_intersection : ∀ (f: E→ F) (H: Set F) (K: Set F), image_reciproque f (H ∩ K) = (image_reciproque f H) ∩ (image_reciproque f K) :=
     λ  (f: E→ F) (H: Set F) (K: Set F) ↦
      Set.ext (λ x:E ↦ Iff.intro
        (
          λ h_xfm1HK : x ∈ image_reciproque f (H ∩ K)  ↦
            have h_fx : f x ∈ H ∩ K :=  h_xfm1HK
            show  x ∈ (image_reciproque f H) ∩ (image_reciproque f K)
              from And.intro (h_fx.left : f x ∈ H) (h_fx.right : f x ∈ K)
        )
        (
          λ h_xfm1Hfm1K : x ∈ (image_reciproque f H) ∩ (image_reciproque f K)  ↦
            have h_fxH : f x ∈ H :=  h_xfm1Hfm1K.left
            have h_fxK : f x ∈ K :=  h_xfm1Hfm1K.right
            show x ∈ (image_reciproque f (H ∩ K) )  from And.intro h_fxH h_fxK
        )
      )
end solution

-- Exercice 4.8
  theorem image_reciproque_union :
    ∀ (f: E→ F) (H: Set F) (K: Set F), image_reciproque f (H ∪ K) = (image_reciproque f H) ∪ (image_reciproque f K) :=
    sorry

namespace solution

  theorem image_reciproque_union : ∀ (f: E→ F) (H: Set F) (K: Set F), image_reciproque f (H ∪ K) = (image_reciproque f H) ∪ (image_reciproque f K) :=
     λ  (f: E→ F) (H: Set F) (K: Set F) ↦
      Set.ext (λ x:E ↦ Iff.intro
        (
          λ (h_xfm1HK : x ∈ image_reciproque f (H ∪ K))  ↦
            have h_fx : f x ∈ H ∪ K :=  h_xfm1HK
            Or.elim h_fx
              (λ h_fxH : f x ∈ H ↦ Or.inl h_fxH)
              (λ h_fxK : f x ∈ K ↦ Or.inr h_fxK)
        )
        (
          λ h_xfm1Hfm1K : x ∈ (image_reciproque f H) ∪ (image_reciproque f K)  ↦
            Or.elim h_xfm1Hfm1K
              (λ h_fxH: f x ∈ H ↦ Or.inl h_fxH)
              (λ h_fxK: f x ∈ K ↦ Or.inr h_fxK)
        )
      )

end solution












------------------------------------------------------------------
--- Exemple 5
------------------------------------------------------------------
-- Plein d'exercices pour s'entrainer !

-- Exercice 5.1
example : ∀ (f: E→ F) (g:F→ G) (A: Set E), image_directe g (image_directe f A) = image_directe (g ∘ f) A := sorry

namespace solution
  example : ∀ (f: E→ F) (g:F→ G) (A: Set E), image_directe g (image_directe f A) = image_directe (g ∘ f) A :=
    λ (f: E→ F) (g:F→ G) (A: Set E) ↦
      Set.ext (λ (z:G) ↦ Iff.intro
        (
          λ (h_z_in_im_im : z ∈ image_directe g (image_directe f A) ) ↦
            Exists.elim h_z_in_im_im (
              λ (y:F) (h_y_and : (y ∈ image_directe f A)∧ (z = g y) ) ↦
                Exists.elim h_y_and.left (
                  λ (x:E) (h_x_and : (x∈ A)∧ (y = f x)) ↦
                  (
                    Exists.intro (x:E) (
                      And.intro
                        (h_x_and.left : x∈ A)
                        (show z = (g∘ f) x from (h_x_and.right ▸ h_y_and.right : z = g (f x) ))
                    )
                  )
                )
            )
        )
        (
          λ (h_z_in_im_o  : z ∈ image_directe (g ∘ f) A ) ↦
            Exists.elim h_z_in_im_o (
              λ (x:E) (h_x_and: (x∈ A) ∧ (z = g (f x))) ↦
              Exists.intro (f x : F) (
                And.intro
                  (show f x ∈ image_directe f A from Exists.intro (x:E) (And.intro (h_x_and.left:x∈ A) (Eq.refl (f x)) ) )
                  (show z = g (f x)             from h_x_and.right                                                       )
              )
            )
        )
      )
end solution

-- Exercice 5.2
example : ∀ (f: E→ F) (g:F→ G) (C: Set G), image_reciproque f (image_reciproque g C) = image_reciproque (g ∘ f) C := sorry

namespace solution
  example : ∀ (f: E→ F) (g:F→ G) (C: Set G), image_reciproque f (image_reciproque g C) = image_reciproque (g ∘ f) C := 
    λ (f: E→ F) (g:F→ G) (C: Set G) ↦
      Set.ext (λ x:E ↦ Iff.intro
        (
          λ (h_x_in_imr_imr : x ∈ image_reciproque f (image_reciproque g C)) ↦
            have h_fx : f x ∈ (image_reciproque g C) :=   h_x_in_imr_imr
            have h_gfx: g (f x) ∈ C :=   h_fx
            show (g ∘ f) x ∈ C from h_gfx
        )
        (
          λ h_z_in_imr_o  : x ∈ image_reciproque (g ∘ f) C  ↦
            have h_gfx : g (f x) ∈ C :=  h_z_in_imr_o
            have h_fx  : f x ∈ (image_reciproque g C) :=  h_gfx
            show x ∈ image_reciproque f (image_reciproque g C) from h_fx
        )
      )
end solution


-- Exercice 5.3
lemma ex_5_3 :  ∀  (f: E → F), ∀ (B:Set F), ( (image_directe f (image_reciproque f B)) ⊆ B) := sorry

namespace solution
  -- Construction eq.subst
  example : ∀ A:Set E, ∀ B:Set E, ∀ x:E, x ∈ A ∧ A=B → x ∈ B :=
    λ (A:Set E) (B:Set E) ↦ λ x:E ↦
      λ (h: x ∈ A ∧ A=B) ↦
        show x∈ B from (h.right: A=B) ▸ (h.left: x∈ A )

  -- Caractérisations de l’injectivité et de la surjectivité

  -- Image directe de l'image reciproque

  lemma ex_5_3 :  ∀  (f: E → F), ∀ (B:Set F), ( (image_directe f (image_reciproque f B)) ⊆ B) :=
    λ (f: E → F) ↦
      λ (B:Set F) ↦
        λ (y:F) ↦ λ (h_yB: y ∈ (image_directe f (image_reciproque f B))) ↦
            Exists.elim h_yB (
              λ x:E ↦
                λ (h_and : (x ∈ (image_reciproque f B)) ∧ (y = f x)) ↦
                  (Eq.symm h_and.right) ▸ (h_and.left: f x ∈ B)
            )

end solution


-- Exercice 5.4
example : ∀ (f: E → F), ∀ (B:Set F),  (image_directe f (image_reciproque f B)) = B ∩ (ensemble_image f) := sorry

namespace solution

  example : ∀ (f: E → F), ∀ (B:Set F),  (image_directe f (image_reciproque f B)) = B ∩ (ensemble_image f) :=
    λ (f: E → F) ↦
      λ (B:Set F) ↦
        Set.ext (
          λ (y:F) ↦
            Iff.intro
              (
                λ (h_yffm1B: y ∈ (image_directe f (image_reciproque f B))) ↦
                  Exists.elim h_yffm1B (
                    λ (x:E) (h_x_and : x∈ image_reciproque f B ∧ y = f x) ↦
                      And.intro
                        (show y ∈ B                from h_x_and.right.symm ▸ (h_x_and.left: f x ∈ B) )
                        (show y ∈ ensemble_image f from Exists.intro x h_x_and.right)
                  )
              )
              (
                λ h_yBimF: y ∈ B ∩ (ensemble_image f)  ↦
                  Exists.elim h_yBimF.right
                  (
                    λ (x:E) (h_yfx : y= f x) ↦
                      Exists.intro x (
                        And.intro
                          (
                            have h_fxB :  f x ∈ B :=          h_yfx ▸ h_yBimF.left
                            show x ∈ image_reciproque f B from h_fxB
                          )
                          (show y = f x from h_yfx)
                      )
                  )
              )
        )

end solution


-- Exercice 5.5
lemma ex_5_5 : ∀ (f: E → F),  ∀ (A:Set E), (A ⊆  (image_reciproque f (image_directe f A))) := sorry

namespace solution

  -- Image réciproque de l'image directe

  lemma ex_5_5 : ∀ (f: E → F),  ∀ (A:Set E), (A ⊆  (image_reciproque f (image_directe f A))) :=
    λ (f: E → F) ↦
        λ (A:Set E) ↦
          λ x:E ↦ λ (h_xA: x ∈ A) ↦
          have h0: f x ∈ {y:F | ∃t :E,  t ∈ A ∧ y= f t }         := Exists.intro x ⟨ h_xA,  (Eq.refl (f x)) ⟩
          have h1: f x ∈ (image_directe f A)                     := h0
          have h2: x   ∈ {t : E | f t ∈ (image_directe f A) }    := h1
          show x ∈(image_reciproque f (image_directe f A))       from
            h2

  example : ∀ (f: E → F),  ∀ (A:Set E), (A ⊆  (image_reciproque f (image_directe f A))) :=
    λ (f: E → F) ↦
        λ (A:Set E) ↦
          λ x:E ↦ λ (h_xA: x ∈ A) ↦
          show f x ∈ (image_directe f A) from Exists.intro x ⟨ h_xA,  (Eq.refl (f x)) ⟩

end solution


-- Caracterisations de la surjectivité, de l'injectivité

-- Exercice 5.6
lemma ex_5_6 : ∀  (f: E → F),  (surjective f) → ∀ (H:Set F), (H ⊆  (image_directe f (image_reciproque f H))) := sorry

namespace solution

  lemma ex_5_6 : ∀  (f: E → F),  (surjective f) → ∀ (H:Set F), (H ⊆  (image_directe f (image_reciproque f H))) :=
    λ (f: E → F) ↦
      λ (h: surjective f) ↦
        λ (H:Set F) ↦
          λ (y:F) ↦ λ (h_yH: y ∈ H) ↦
            Exists.elim (h y)  (
              λ(x:E) ↦ λ (h_yfx:y= f x) ↦
              have h_fxH: f x ∈ H :=  h_yfx ▸ h_yH
              have h_xiH: x ∈ (image_reciproque f H) :=  h_fxH
              Exists.intro x  ( And.intro  h_xiH h_yfx)
            )
end solution


-- Exercice 5.7
example :  ∀  f: E → F, ∀ A: Set E, Set.Nonempty A → Set.Nonempty (image_directe f A) := sorry

namespace solution
  example :  ∀  f: E → F, ∀ A: Set E, Set.Nonempty A → Set.Nonempty (image_directe f A) :=
    λ  (f: E → F) (A: Set E) ↦
      λ (hnA : Set.Nonempty A) ↦
       Exists.elim hnA (
         λ (v:E) (p:v ∈ A) ↦
           Exists.intro  (f v) (Exists.intro v (And.intro p (Eq.refl (f v))))
       )

  example : ∀  f: E → F, ∀ A: Set E, Nonempty A → Nonempty (image_directe f A) :=
    λ  (f: E → F) (A: Set E) ↦
      λ (hnA : Nonempty A) ↦
       Nonempty.elim hnA (
         λ (u: (Subtype A)) ↦
           Nonempty.intro (Subtype.mk (f u.val) (Exists.intro u.val (And.intro u.property (Eq.refl (f u.val)))))
       )

end solution


-- Exercice 5.8
lemma ex_5_8 :  ∀  f: E → F, ∀ A: Set E,  Set.Nonempty (image_directe f A) → Set.Nonempty A := sorry

namespace solution
  lemma ex_5_8 :  ∀  f: E → F, ∀ A: Set E,  Set.Nonempty (image_directe f A) → Set.Nonempty A :=
    λ  (f: E → F) (A: Set E) ↦
      λ (hnfA : Set.Nonempty (image_directe f A)) ↦
       Exists.elim hnfA (
         λ (y:F) (h_y_in_fA: y ∈  (image_directe f A) ) ↦
           Exists.elim h_y_in_fA (
             λ (x:E) (h_x_and : x∈ A ∧ y = f x) ↦
               Exists.intro  x h_x_and.left
           )
       )

end solution


-- Exercice 5.9
#check Set.not_nonempty_iff_eq_empty
#check Set.singleton_nonempty
#check Set.subset_eq_empty
#check Set.not_nonempty_iff_eq_empty.not_right.mpr
#check Set.eq_of_mem_singleton
#check ex_5_8

example : ∀  (f: E → F), (∀ (H:Set F), H ⊆  (image_directe f (image_reciproque f H)) ) →  (surjective f)   := sorry

namespace solution
  #check ex_5_8

  lemma ex_5_9 : ∀  (f: E → F), (∀ (H:Set F), H ⊆  (image_directe f (image_reciproque f H)) ) →  (surjective f)   :=
    λ (f: E → F) ↦
      λ (h_forall: ∀ (H:Set F), H ⊆  (image_directe f (image_reciproque f H))) ↦
        λ (y:F) ↦
          let H:=({y}: Set F)
          have h_im_nonempty: Set.Nonempty (image_directe f (image_reciproque f H) ) :=
            Set.not_nonempty_iff_eq_empty.not_right.mpr (λ h_im_empty:image_directe f (image_reciproque f H) = ∅  ↦
              absurd
                   (Set.singleton_nonempty y)
                   (Set.not_nonempty_iff_eq_empty.mpr (Set.subset_eq_empty (h_forall H) h_im_empty)))
          have h_imrec_nonempty : Set.Nonempty (image_reciproque f H) :=  ex_5_8 f  (image_reciproque f H) h_im_nonempty
          Exists.elim h_imrec_nonempty (
            λ (x:E) (h_x: x ∈ (image_reciproque f H)) ↦
              Exists.intro x (show y=f x from (Set.eq_of_mem_singleton h_x).symm)
          )

end solution



-- Exercice 5.10
#check subset_antisymm
#check Eq.subset
#check ex_5_3
#check ex_5_6
#check ex_5_9

example :  ∀  (f: E → F), (surjective f) ↔  (∀ (H:Set F), H =  (image_directe f (image_reciproque f H)) )  := sorry

namespace solution
  theorem ex_6_3_20_1 :  ∀  (f: E → F), (surjective f) ↔  (∀ (H:Set F), H =  (image_directe f (image_reciproque f H)) )  :=
    λ (f: E → F) ↦
      Iff.intro
      (λ h_fsurj: surjective f ↦
        λ H:Set F ↦
          subset_antisymm
            (ex_5_6   f h_fsurj H)
            (ex_5_3   f H )
      )
      (
        λ (h_forall :   ∀ (H:Set F), H =  (image_directe f (image_reciproque f H)) )↦
         ex_5_9 f (
           λ (H:Set F) ↦
             Eq.subset (h_forall H)
         )
      )
end solution


-- Exercice 5.11
lemma ex_5_11 : ∀  (f: E → F), (injective f) → (∀ (A:Set E), ((image_reciproque f (image_directe f A)) ⊆ A)) := sorry

namespace solution
  lemma ex_5_11 : ∀  (f: E → F), (injective f) → (∀ (A:Set E), ((image_reciproque f (image_directe f A)) ⊆ A)) :=
    λ (f: E → F) ↦
      λ (h_inj: injective f) ↦
        λ (A:Set E) ↦
          λ x:E ↦ λ (h_xfm1fA: x ∈ (image_reciproque f (image_directe f A))) ↦
          have h_fxfA:f x ∈ (image_directe f A) :=  h_xfm1fA
          Exists.elim h_fxfA (
            λ(x':E)↦
              λ ( h_x'A_and_fxfx' : (x'∈ A) ∧( f x = f x')) ↦
                have h_xx': x=x' :=  h_inj x x' h_x'A_and_fxfx'.right
                (h_xx') ▸ h_x'A_and_fxfx'.left
          )


  example (f: E → F) :  (injective f) → (∀ (A:Set E), ((image_reciproque f (image_directe f A)) ⊆ A)) :=
    λ  h1 _ x ⟨ x',⟨ h4,h5⟩ ⟩ ↦  (h1 x x' h5)  ▸ h4

end solution


-- Exercice 5.12
#check Set.eq_of_mem_singleton
#check Set.mem_singleton

lemma ex_5_12 : ∀  (f: E → F), ∀ (x:E), (image_directe  f {x}) = {f x} := sorry

namespace solution
  lemma ex_5_12 : ∀  (f: E → F), ∀ (x:E), (image_directe  f {x}) = {f x} :=
    λ (f: E → F) ↦
      λ (x: E) ↦
        Set.ext (
          λ (y:F) ↦
            Iff.intro
              (λ (h:y ∈ image_directe  f {x}) ↦
                  Exists.elim h (
                    λ (t:E) ↦ λ (h_t:t ∈ {x} ∧ y= f t) ↦
                      have htx : _ := Set.eq_of_mem_singleton h_t.left ;
                      (((Set.eq_of_mem_singleton h_t.left ) ▸ h_t.right) : y = f x)
                  )
              )
              (λ (h:y ∈ {f x}) ↦ Exists.intro x (And.intro ((Set.mem_singleton x) : (x∈ {x})) (h: y = f x)  ))
        )

end solution


-- Exercice 5.13
#check ex_5_12
lemma ex_5_13 :  ∀  (f: E → F), (∀ (A:Set E), ((image_reciproque f (image_directe f A)) ⊆ A))   → (injective f) := sorry

namespace solution
  lemma ex_5_13 : ∀  (f: E → F), (∀ (A:Set E), ((image_reciproque f (image_directe f A)) ⊆ A))   → (injective f) :=
    λ (f: E → F) ↦
      λ (h_forallset: ∀ (A:Set E), (image_reciproque f (image_directe f A)) ⊆ A)  ↦
        λ (x:E) (x':E) (h_fx1x' : f x = f x') ↦
          let A := ({x}:Set E)
          have h_fm1fA : image_reciproque f {f x} ⊆ {x} :=   (ex_5_12 f x) ▸  (h_forallset A)
          have h_x'_in  : x' ∈ image_reciproque f {f x}  :=  h_fx1x'.symm
          show x=x' from (h_fm1fA h_x'_in).symm
end solution


-- Exercice 5.14
#check subset_antisymm
#check subset_refl
#check ex_5_11
#check ex_5_5
#check ex_5_13
example : ∀  (f: E → F), (injective f) ↔  (∀ (A:Set E), ((image_reciproque f (image_directe f A)) = A)) := sorry

namespace solution

  example : ∀  (f: E → F), (injective f) ↔  (∀ (A:Set E), ((image_reciproque f (image_directe f A)) = A)) :=
     λ (f: E → F) ↦
       Iff.intro
       (λ (h_inj: injective f) ↦ λ (A:Set E) ↦ subset_antisymm (ex_5_11 f h_inj A) (ex_5_5 f A))
       (λ (h_forallset: ∀ (A:Set E), (image_reciproque f (image_directe f A)) = A) ↦ ex_5_13 f (
           λ (A:Set E) ↦ (h_forallset A).symm ▸ (subset_refl A)
         )
       )end solution


-- Exercice 5.15
#check Set.not_subset
#check Set.Nonempty.not_subset_empty
#check Set.singleton_nonempty
#check Set.mem_singleton_iff
#check Set.mem_of_mem_of_subset

example :  ∀ (f: E → F), (surjective f) ↔ (∀ B₁:Set F, ∀ B₂:Set F, ( ( (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) → ( B₁ ⊆ B₂) )  ) := sorry

namespace solution
  example : ∀ (f: E → F),
       (surjective f) ↔
            (∀ B₁:Set F, ∀ B₂:Set F,
               ( ( (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) → ( B₁ ⊆ B₂) )
            )
        :=
        λ (f: E → F)  ↦
         Iff.intro
           (
              λ(h_surjective_f: surjective f) ↦
                λ (B₁:Set F)↦ λ( B₂:Set F )↦
                  λ(h_imrec_subset: (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) ↦
                    λ (y)↦ λ (h_yB1: y ∈ B₁)↦
                      show (y ∈ B₂) from
                        Exists.elim (h_surjective_f y) (
                           λ x:E ↦ λ (h_yfx: y = f x) ↦
                             have h_fxB1 : (f x)∈ B₁ :=  (h_yfx ▸  h_yB1)
                             have h_xirB1: x ∈ (image_reciproque f B₁) :=  h_fxB1
                             have h_xirB2: x ∈ (image_reciproque f B₂) :=  (Set.mem_of_mem_of_subset h_xirB1 h_imrec_subset)
                             have h_fxB2 : (f x)∈ B₂ :=  h_xirB2
                             have h_yB2  : y∈ B₂ :=  (( Eq.symm h_yfx) ▸ h_fxB2)
                             h_yB2
                        )

           )
           (
             λ(h_forall: ∀ B₁:Set F, ∀ B₂:Set F, ( ( (image_reciproque f B₁) ⊆  (image_reciproque f B₂)) → ( B₁ ⊆ B₂) )) ↦
               λ(y:F) ↦
                  have h_syne: (Set.Nonempty {y})  :=   Set.singleton_nonempty _
                  have h_incl: _ :=  (mt (h_forall {y} ∅ ) ) (Set.Nonempty.not_subset_empty h_syne)
                  Exists.elim ((Set.not_subset ).mp h_incl) (
                     λ x:E ↦ λ(h_existsH:_) ↦
--                     Exists.elim (h_existsH) (
                     (
                        have H:x ∈ (image_reciproque f {y} ) := h_existsH.left
                        have h_inutile: x ∉ (image_reciproque f ∅ ) := h_existsH.right
                        Exists.intro x (
                            have h_fxy: (f x)∈ {y} :=  by unfold image_reciproque at H; exact H
                            have h_fxy': (f x)=y :=  H
                            have h_iff:_ :=  @Set.mem_singleton_iff F (f x) y
                            show y=f x from Eq.symm (( h_iff.mp ) h_fxy)
                        )
                     )

                  )
           )

end solution


-- Exercice 5.16
#check subset_antisymm
#check Set.mem_singleton
#check ex_5_8

example : ∀ (f:E → F), (injective f)  ↔ (∀ A: Set E, ∀ B: Set E, image_directe f (A∩B) = (image_directe f A)∩ (image_directe f B)) := sorry

namespace solution
end solution


-- Exercice 5.17
#check Set.subset_empty_iff
lemma ex_5_17 : ∀ f:E→ F, image_directe f ∅ = ∅   := sorry

namespace solution
  lemma ex_5_17 : ∀ f:E→ F, image_directe f ∅ = ∅ := λ (f:E→ F) ↦  (Set.subset_empty_iff).mp (
      λ  (y:F) (h_y: y∈  image_directe f ∅) ↦
      Exists.elim h_y (
        λ (x:E) (h_x: x∈ ∅ ∧ y = f x) ↦
          show y∈ ∅  from False.elim h_x.left
      )
    )
end solution


-- Exercice 5.18
#check @mt
#check @not_imp_not
#check Set.compl_empty
#check @Set.eq_of_mem_singleton
#check Set.mem_singleton
#check ensemble_image_egale_image_depart
#check ex_5_17

example :  ∀ f:E→ F, (bijective f) ↔ (∀ A:Set E, image_directe f (Aᶜ) = (image_directe f A)ᶜ  ) := sorry

namespace solution

  theorem ex_6_3_20_5 : ∀ f:E→ F, (bijective f) ↔ (∀ A:Set E, image_directe f (Aᶜ) = (image_directe f A)ᶜ  ) :=
    λ f: E→ F ↦
      Iff.intro
        (λ h_f_bijective:bijective f ↦
          λ A:Set E ↦
            Set.ext ( λ (y:F) ↦
              Iff.intro
                (λ h_y_in_f_Ac : y ∈ image_directe f (Aᶜ) ↦
                  λ h_y_in_fA:y ∈ (image_directe f A) ↦
                    Exists.elim h_y_in_f_Ac (
                      λ (x:E) (h_x_and : x∈Aᶜ ∧ y = f x ) ↦
                        Exists.elim h_y_in_fA (
                          λ (x':E) (h_x'_and : x'∈A ∧ y = f x' ) ↦
                            have h_x_eq_x' : x=x' :=  (h_f_bijective.left : injective f) x x' (h_x_and.right ▸ h_x'_and.right)
                            absurd ((h_x_eq_x'.symm ▸ h_x'_and.left): x∈ A) (h_x_and.left : ¬ x∈ A)
                        )
                    )
                )
                (λ h_y_in_fA_c : y ∈ (image_directe f A)ᶜ ↦
                  Exists.elim ((h_f_bijective.right : surjective f) y) (
                    λ (x:E) (h_yfx: y = f x) ↦
                      have h_x_notin_A : x ∉ A :=  (
                         λ (h_x_in_A: x∈ A) ↦
                           absurd (Exists.intro x (And.intro h_x_in_A h_yfx)) h_y_in_fA_c
                        )
                      --have : ∃x:E, x∈Aᶜ∧ y=f x  := Exists.intro x (And.intro (h_x_notin_A : x∈ Aᶜ ) h_yfx)
                      Exists.intro x (And.intro (h_x_notin_A : x∈ Aᶜ ) h_yfx)
                  )
                )
            )
        )
        (λ h_forallset: (∀ A:Set E, image_directe f (Aᶜ) = (image_directe f A)ᶜ  ) ↦
          And.intro
            (λ (x x':E) ↦
              not_imp_not.mp
                 (λ  (h_x_ne_x' : x ≠  x') ↦
                   let A:Set E:={x}
                   have h_x'_notin_A: x' ∉ A :=  (mt (@Set.eq_of_mem_singleton _ x' x)) h_x_ne_x'.symm
                   have h_fx'_in_fA_c: f x' ∈  (image_directe f A)ᶜ   :=
                      (h_forallset A) ▸ (Exists.intro x' (And.intro h_x'_notin_A (Eq.refl (f x')) ))
                   show f x ≠ f x' from (
                     λ (h_fx_eq_fx': f x = f x') ↦
                      absurd (Exists.intro x (And.intro (Set.mem_singleton x) h_fx_eq_fx'.symm ) : ( f x' ∈  (image_directe f A))) h_fx'_in_fA_c
                   )
                 )
          )
            (
               (reformulation_surjectivite f).mpr (
                  calc
                    ensemble_image f = image_directe f (∅ᶜ)    := (@Set.compl_empty E).symm ▸ (ensemble_image_egale_image_depart f)
                    _                = (image_directe f ∅)ᶜ    := h_forallset ∅
                    _                = (∅: Set F)ᶜ             := congr_arg HasCompl.compl (ex_5_17 f)
                    _                = @Set.univ F             := @Set.compl_empty F

               )
            )
        )

end solution
