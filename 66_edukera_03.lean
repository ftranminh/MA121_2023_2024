import Mathlib.Tactic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
--import Mathlib.Tactic.Finish
import Init.Tactics

--import init.meta.simp_tactic 
--import init.meta.interactive
--import tactic.finish

--import data.real.basic
--import data.set.basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

import Lean

macro x:ident ":" t:term " ↦ " y:term : term => do
`(fun $x : $t => $y)
#eval (x : Nat ↦ x + 2) 2 -- 4
macro "lambda" x:ident ":" t:term "," y:term : term => do
`(fun $x : $t => $y)
#eval (lambda x : Nat, x + 2) 2 -- 4
macro "lambda" x:ident  "," y:term : term => do
`(fun $x  => $y)
#eval (lambda x, x + 2) 2 -- 4

macro x:ident " ↦ " y:term : term => do
`(fun $x => $y)
#eval (x ↦  x + 2) 2 -- 4

macro "assume" x:ident ":" t:term "," y:term : term => do
`(fun $x : (($t):Prop) => $y)
#eval (assume x : Nat, x + 2) 2 -- 4
#eval (assume h : (∀n:ℕ,n ≥ 0), h 2) 

example :  (∀n:ℕ,n ≥ 0) → 2 ≥ 0 :=
    (λ  h : (∀n:ℕ,n ≥ 0)  => h 2) 

example :  (∀n:ℕ,n ≥ 0) → 2 ≥ 0 :=
    (assume  h : (∀n:ℕ,n ≥ 0) , h 2) 

example :  (∀n:ℕ,n ≥ 0) → 2 ≥ 0 :=
    (assume  h  , h 2) 

-- Enoncé à importer

namespace Edukera

  axiom Chose : Type 

  namespace Formalisation
    namespace Logique
      namespace Lecture
          -- Anaïs
          axiom A    : Chose

          -- Victor Hugo
          axiom VH   : Chose

          -- Les Miserables    
          axiom LM   : Chose

          -- R x  signifie   x   est un roman
          axiom R    : Chose → Prop

          -- H x  signifie   x   est un être humain
          axiom H    : Chose → Prop

          -- Anaïs est un être humain 
          axiom H_A : H A

          -- Victor Hugo  est un être humain 
          axiom H_VH : H VH

          -- Les Misérables est un être roman
          axiom R_LM : R LM

          -- L x y  signifie   x   a lu   y
          axiom L    : Chose → Chose → Prop

          -- E x y  signifie   x   a écrit   y
          axiom E    : Chose → Chose → Prop


        namespace EX01
          -- "Anaïs a lu les Misérables"
        end EX01

        namespace EX02
          -- "Quelqu'un a lu les Misérables"
        end EX02

        namespace EX03
          -- "Tout le monde a lu les Misérables"
        end EX03

        namespace EX04
          -- "Tout le monde n'a pas lu les Misérables"
        end EX04

        namespace EX05
          -- "Quelqu'un n'a pas lu les Misérables"
        end EX05

        namespace EX06
          -- "Anaïs a lu un roman"
        end EX06

        namespace EX07
          -- "Les Misérables a été écrit par Victor Hugo"
        end EX07

        namespace EX08
          -- "Anaïs a lu tous les romans de Victor Hugo"
        end EX08

        namespace EX09
          -- "Anaïs n'a pas lu tous les romans"
        end EX09

        namespace EX10
          -- "Tout le monde a lu un roman de Victor Hugo"
        end EX10

        namespace EX11
          -- "Quelqu'un a lu tous les romans de Victor Hugo"
        end EX11

        namespace EX12
          -- "Tous ceux qui ont écrit un roman ont lu Les Misérables"
        end EX12

        namespace EX13
          -- "Tous les romans n'ont pas été écrits par une même personne"
        end EX13

        namespace EX14
          -- "Parmi les romans de Victor Hugo, Anaïs n'a lu que Les Misérables"
        end EX14

        namespace EX15
          -- "Anaïs a lu exactement 2 romans"
        end EX15

      end Lecture

      namespace Bucheron

          -- Paul
          axiom P    : Chose

          -- homme x  signifie   x   est un homme
--          axiom homme    : Chose → Prop
          axiom homme    : Set Chose

          -- bucheron x  signifie   x   est un bûcheron
--          axiom bucheron    : Chose → Prop
          axiom bucheron    : Set Chose

          -- riche x  signifie   x   est riche
          axiom riche    : Chose → Prop

          -- Paul est un être humain 
          axiom homme_P : homme P


        namespace EX16
          -- "Tous les bûcherons sont des hommes"
        end EX16

        namespace EX17
          -- "Paul est riche"
        end EX17

        namespace EX18
          -- "Si Paul est un bûcheron, Paul est riche"
        end EX18

        namespace EX19
          -- "Tous les hommes sont bûcherons ou riches"
        end EX19

        namespace EX20
          -- "Quelques bûcherons sont riches"                            -- attention ambiguité : >= 1 ou >= 2 ?    rep edukera  : rep1
        end EX20

        namespace EX21
          -- "Quelques bûcherons ne sont pas riches"
        end EX21

        namespace EX22
          -- "Aucun bûcheron n'est riche"
        end EX22

        namespace EX23
          -- "Tous les hommes sont bûcherons"
        end EX23

        namespace EX24
          -- "Aucun homme n'est bûcheron"
        end EX24

        namespace EX25
          -- "Tous les hommes ne sont pas bûcherons"
        end EX25

      end Bucheron

      namespace Grippe

          axiom Personne : Type

--          definition Temperature : Type := nat
          axiom Temperature : Type

          -- Pierre
          axiom Pierre    : Personne

          -- grippe x  signifie   x   a la grippe
          axiom grippe    : Personne → Prop

          -- travail x  signifie   x   doit aller au travail
          axiom travail    : Personne → Prop

          -- fievre x  signifie   x   a de la fievre
          axiom fievre    : Personne → Prop

          -- tousse x  signifie   x   tousse
          axiom tousse    : Personne → Prop

          -- temp x y  signifie   x   a une température de y
          axiom temp    : Personne → Temperature → Prop

          -- sup x y  signifie   x   est supérieur à y
          axiom sup    : Temperature → Temperature → Prop

          -- TrenteHuit signifie 38
--          def TrenteHuit : Temperature := (38:ℕ )
          axiom TrenteHuit : Temperature


        namespace EX26
          -- "Les personnes qui ont la grippe ne doivent pas aller au travail"         -- attention ambiguité : ne dovent pas  = ne sont pas obligés ou doivent ne pas ?  -- contexte : rep1
        end EX26

        namespace EX27
          -- "Les personnes qui ont de la fièvre et qui toussent ont la grippe"
        end EX27

        namespace EX28
          -- "Ceux qui ont une température supérieure à 38°C ont de la fièvre"
        end EX28

        namespace EX29
          -- "Pierre tousse et a une température supérieure à 38°C"
        end EX29

      end Grippe

      namespace Bonheur

          axiom Personne : Type

          -- Raphaël
          axiom Raphael    : Personne

          -- estAperitif x  signifie   x   est apéritif
          axiom estAperitif    : Chose → Prop

          -- apprecie x y  signifie   x:Personne   aime y:Chose
          axiom apprecie    : Personne → Chose → Prop

          -- aime x y  signifie   x:Personne   aime y:Personne 
          axiom aime    : Personne → Personne → Prop

          -- heureux x  signifie   x   est heureux
          axiom heureux    : Personne → Prop



        namespace EX30
          -- "Raphaël est heureux"
        end EX30

        namespace EX31
          -- "Raphaël aime les apéritifs"
        end EX31

        namespace EX32
          -- "Quelqu'un n'aime que les apéritifs"
        end EX32

        namespace EX33
          -- "Tous ceux qui sont aimés sont heureux"
        end EX33

        namespace EX34
          -- "Ceux qui aiment sans être aimés en retour sont malheureux"
        end EX34

      end Bonheur


      namespace Tournoi

          axiom Personne : Type

          -- Alain
          axiom A    : Personne

          -- Bernard
          axiom B    : Personne

          -- j x y  signifie   x a joué contre y     ou : x et y ont joué ensemble
          axiom j    : Personne → Personne → Prop

          axiom j_commute : ∀ x y, j x y → j y x 

          -- b x y  signifie   x a battu y
          axiom b    : Personne → Personne → Prop

          -- i x  signifie   x   est inscrit au tournoi
          axiom i    : Personne → Prop

          -- e x  signifie   x   est éliminé du tournoi
          axiom e    : Personne → Prop


        namespace EX35
          -- "Alain et Bernard ont joué ensemble"
        end EX35

        namespace EX36
          -- "Alain et Bernard sont inscrits au tournoi"
        end EX36

        namespace EX37
          -- "Un joueur doit être inscrit pour pouvoir jouer et tout joueur battu est éliminé"
        end EX37

        namespace EX38
          -- "Bernard a battu tous les joueurs inscrits qui ont joué contre Alain"
        end EX38

        namespace EX39
          -- "Aucun joueur inscrit ayant battu Bernard n'a joué contre un joueur inscrit battu par Alain"
        end EX39

      end Tournoi



      namespace Connaissance

          axiom Personne : Type

          -- Thomas
          axiom T    : Personne

          -- Jeanne
          axiom J    : Personne

          -- connait x y  signifie   x connaît y
          axiom connait    : Personne → Personne → Prop


        namespace EX40
          -- "Quelqu'un connaît Jeanne"
        end EX40

        namespace EX41
          -- "Personne ne connaît tout le monde"
        end EX41

        namespace EX42
          -- "Thomas connaît tous ceux qui connaissent Jeanne"
        end EX42

        namespace EX43
          -- "Jeanne connaît quelqu'un qui connaît tout le monde"
        end EX43

      end Connaissance



      namespace Nature

          -- mange x y  signifie   x mange y
          axiom mange    : Chose → Chose → Prop

          -- herbivore x  signifie   x   est un herbivore
          axiom herbivore    : Chose → Prop

          -- vegetal x  signifie   x   est un végétal
          axiom vegetal    : Chose → Prop

          -- bambou x  signifie   x   est un bambou
          axiom bambou    : Chose → Prop

          -- panda x  signifie   x   est un panda
          axiom panda    : Chose → Prop



        namespace EX44
          -- "Les herbivores mangent des végétaux"
        end EX44

        namespace EX45
          -- "Les herbivores ne mangent que des végétaux"    -- ambiguité : en mangent ils?   -- rep eduk : pas forcément
        end EX45

        namespace EX46
          -- "Aucun herbivore ne mange tout type de végétal"     -- ?? confusion végétal/type de végétal ?
        end EX46

        namespace EX47
          -- "Il y a des végétaux que ne mange aucun herbivore"
        end EX47

        namespace EX48
          -- "Certains herbivores ne mangent pas de bambou"
        end EX48

        namespace EX49
          -- "Les pandas sont des herbivores qui ne consomment que des bambous"
        end EX49

      end Nature



      namespace SystemeSolaire

          -- Soleil
          axiom So    : Chose

          -- Mercure
          axiom Me    : Chose

          -- Vénus
          axiom V     : Chose

          -- Terre
          axiom T     : Chose

          -- Mars
          axiom Ma    : Chose

          -- Lune
          axiom L     : Chose

          -- Jupiter
          axiom J     : Chose

          -- Saturne
          axiom Sa    : Chose

          -- Uranus
          axiom U     : Chose

          -- Neptune
          axiom N     : Chose

          -- planete x  signifie   x   est une planète
          axiom planete    : Chose → Prop

          -- tourneTerre x  signifie   x   tourne autour de la Terre
          axiom tourneTerre    : Chose → Prop

          -- plusPetit x y  signifie   x   est plus petit (ou aussi grand) que y
          axiom plusPetit    : Chose → Chose → Prop

          -- plusProcheSoleil x y  signifie   x   est plus proche (ou à égale distance) du Soleil que y
          axiom plusProcheSoleil    : Chose → Chose → Prop



        namespace EX50
          -- "Vénus est une planète"
        end EX50

        namespace EX51
          -- "Le Soleil n'est pas une planète"
        end EX51

        namespace EX52
          -- "Le Soleil tourne autour de la Terre"
        end EX52

        namespace EX53
          -- "Certaines planètes sont plus petites que la Terre"
        end EX53

        namespace EX54
          -- "Toutes les planètes sont plus petites que Saturne"     -- faux !! ;-)
        end EX54

        namespace EX55
          -- "Rien n'est plus petit que la Lune"
        end EX55

        namespace EX56
          -- "Mercure est la planète la plus proche du Soleil"
        end EX56

        namespace EX57
          -- "Mars est plus loin du Soleil que Neptune"          -- impossible !!... 
        end EX57

        namespace EX58
          -- "Si quelquechose est plus éloigné du Soleil que Neptune, alors ce n'est pas une planète"
        end EX58

        namespace EX59
          -- "Si le Soleil tourne autour de la Terre, alors il est plus petit que celle-ci"            -- vrai
        end EX59

        namespace EX60
          -- "S'il n'y a pas de planète plus grande que la Terre, alors la Terre est plus grande que Jupiter"       -- vrai     --- ambiguités ? égalité ?
        end EX60

        namespace EX61
          -- "La Lune est une planète mais certaines choses ne sont pas des planètes"        -- faux...
        end EX61

        namespace EX62
          -- "Toutes les planètes ne tournent pas autour de la Terre"
        end EX62

        namespace EX63
          -- "Aucune planète n'est plus petite que Mercure"      --- ambiguité : rep edukera : ∀ x, planete x  → (plusPetit x Me)    : alors que l'énoncé sous entend strict...
        end EX63

        namespace EX64
          -- "Il n'y a pas de planète qui soit plus grande que la Terre tout en étant plus proche du Soleil qu'elle"
        end EX64

        namespace EX65
          -- "Il existe une planète telle que tout objet plus proche du Soleil qu'elle, est plus petit qu'elle"
        end EX65

        namespace EX66
          -- "Aucune planète n'est à la fois plus petite qu'Uranus et plus éloignée du Soleil qu'elle"
        end EX66

        namespace EX67
          -- "Si toutes les planètes tournent autour de la Terre, alors Neptune aussi"          -- vrai
        end EX67

      end SystemeSolaire

    end Logique


    namespace Math 


       namespace Arithmetique0
        
        -- Le type entier nature
        def Entier: Type := Nat

        -- 0
        def Zero : Entier := (0:ℕ)

        -- 1
        def Un : Entier :=  (1: Nat)

        -- InferieurOuEgal x y  signifie   x ≤  y
        def InferieurOuEgal    : Entier → Entier → Prop := Nat.le 

        -- Plus x y  signifie   x + y
        def Plus    : Entier → Entier → Entier := Nat.add

        -- Mult x y  signifie   x * y
        def Mult    : Entier → Entier → Entier := Nat.mul

        -- Pair x  signifie   x   est pair
        def Pair    : Entier → Prop   :=   λ n => (∃k:Entier, n = Plus k k  )

        -- Div x y  signifie   x divise y
        def Div    : Entier → Entier → Prop := Nat.instDvdNat.dvd

        -- Prem x  signifie   x   est premier
        def Prem    : Entier → Prop := λ p => p ≠ Zero ∧  p ≠ Un ∧  (∀ d:Entier, (Div d p) → (d = Un) ∨ (d = p))



        --notations
        infix:50 " ≤ "  => InferieurOuEgal
        infixl:65 " + " => Plus
        notation:65 lhs:65 " * " rhs:66 => Mult lhs rhs
--        notation:50 lhs:50 " ∣ " rhs:50 => Div lhs rhs

        macro lhs:term " ∣ " rhs:term : term => `(Div $lhs $rhs)

        syntax term " * " term : term 
--        macro_rules (kind := atom)
--         | `($lhs * $rhs)  => `(Mult $lhs $rhs)

        namespace EX01
          -- "Il existe un entier plus petit ou égal à tous les autres"
        end EX01

        namespace EX02
          -- "Il n'existe pas d'entier plus grand ou égal à tous les autres, mais pour tout entier, il en existe un qui est strictement plus grand"
        end EX02

        namespace EX03
          -- "Tout nombre entier pair est égal à la somme de deux nombres entiers premiers"
        end EX03

        namespace EX04
          -- "L'ensemble des entiers premiers est non borné"    -- pas si evident : edukera accepte ∀x, ∃y, x ≤ y ∧ x ≠ y ∧ (Prem y)  
                                                                -- mais n'accepte pas               ∀x, ∃y, x ≤ y ∧ (Prem y)  
                                                                -- ni                               ∀x, ∃y, x +1 ≤ y ∧ (Prem y)      pourtant corrects

          -- il y a aussi la signification de 'borné' qui dans ℕ signifie 'majoré'                                                                 
        end EX04


       end Arithmetique0


       namespace Arithmetique
        
        -- Le type entier nature
        axiom Entier: Type
--        class Entier extends has_zero, has_one := () 

        -- InferieurOuEgal x y  signifie   x ≤  y
        axiom InferieurOuEgal    : Entier → Entier → Prop

        -- Pair x  signifie   x   est pair
        axiom Pair    : Entier → Prop

        -- Prem x  signifie   x   est premier
        axiom Prem    : Entier → Prop


        -- Plus x y  signifie   x + y
        axiom Plus    : Entier → Entier → Entier

        -- Mult x y  signifie   x * y
        axiom Mult    : Entier → Entier → Entier

        -- Div x y  signifie   x divise y
        axiom Div    : Entier → Entier → Prop

        -- 0
        axiom Zero : Entier

        -- 1
        axiom Un : Entier

        --notations
        notation:50 lhs:50 " ≤ " rhs:50 => InferieurOuEgal lhs rhs
        notation:65 lhs:65 " + " rhs:66 => Plus lhs rhs
        infixl:65 " * " => Mult
        infix:50 " ∣ "  => Div



        namespace EX01
          -- "Il existe un entier plus petit ou égal à tous les autres"
        end EX01

        namespace EX02
          -- "Il n'existe pas d'entier plus grand ou égal à tous les autres, mais pour tout entier, il en existe un qui est strictement plus grand"
        end EX02

        namespace EX03
          -- "Tout nombre entier pair est égal à la somme de deux nombres entiers premiers"
        end EX03

        namespace EX04
          -- "L'ensemble des entiers premiers est non borné"    -- pas si evident : edukera accepte ∀x, ∃y, x ≤ y ∧ x ≠ y ∧ (Prem y)  
                                                                -- mais n'accepte pas               ∀x, ∃y, x ≤ y ∧ (Prem y)  
                                                                -- ni                               ∀x, ∃y, x +1 ≤ y ∧ (Prem y)      pourtant corrects
        end EX04


       end Arithmetique


       namespace Fonctions0

        def Nombre     : Type := Real        
        def Intervalle : Type := Set ℝ 

        def  InferieurOuEgal : Nombre → Nombre → Prop         := Real.instLEReal.le
        def  Appartient      : Nombre → Intervalle → Prop     := Set.Mem


        --notations
        infix:50 " ≤ " => InferieurOuEgal
        infix:50 " ∈ " => Appartient

        axiom f : Nombre → Nombre
        axiom I : Intervalle


        namespace EX05
          -- "La fonction f est croissante sur l'intervalle I"
        end EX05

        namespace EX06
          -- "La fonction f n'est pas croissante sur l'intervalle I"
        end EX06

       end Fonctions0


       namespace Fonctions

        axiom Nombre     : Type
        axiom Intervalle : Type

        axiom InferieurOuEgal : Nombre → Nombre → Prop  
        axiom Appartient      : Nombre → Intervalle → Prop  

        --notations
        infix:50 " ≤ " => InferieurOuEgal
        infix:50 " ∈ " => Appartient

        axiom f : Nombre → Nombre
        axiom I : Intervalle


        namespace EX05
          -- "La fonction f est croissante sur l'intervalle I"
        end EX05

        namespace EX06
          -- "La fonction f n'est pas croissante sur l'intervalle I"
        end EX06

        namespace EX07
          -- "La fonction f est strictement décroissante sur l'intervalle I"
        end EX07

        namespace EX08
          -- "La fonction f est majorée sur l'intervalle I"
        end EX08

        namespace EX09
          -- "La fonction f est bornée sur l'intervalle I"
        end EX09

       end Fonctions

       namespace Suites_A0
        def Entier     : Type := ℕ 
        def Nombre     : Type := ℝ 
        def Suite : Type := Entier → Nombre 
        def Zero : Nombre := (0:ℝ )

        -- convergente x signifie x est convergente
        axiom convergente : Suite → Prop

        -- bornee x signifie x est bornee
        axiom bornee : Suite → Prop

        namespace EX10
          -- "La contraposée de : si la fonction f converge alors f est bornée"     -- f: suite ?      
                                                                                    -- contraposée : équivalente? ou s'arrete l'automatisation ?
                                                                                    -- edukera accepte : ∀ f, convergente f → bornee f
        end EX10

        namespace EX11
          -- "La réciproque de : si la fonction f converge alors f est bornée"
        end EX11

        namespace EX11
          -- "La suite n'est pas la suite nulle"
        end EX11

       end Suites_A0

       namespace Suites_A
        axiom Entier     : Type
        axiom Nombre     : Type
        def Suite : Type := Entier → Nombre 
        axiom Zero:Nombre

        -- convergente x signifie x est convergente
        axiom convergente : Suite → Prop

        -- bornee x signifie x est bornee
        axiom bornee : Suite → Prop

        namespace EX10
          -- "La contraposée de : si la fonction f converge alors f est bornée"     -- f: suite ?      
                                                                                    -- contraposée : équivalente? ou s'arrete l'automatisation ?
                                                                                    -- edukera accepte : ∀ f, convergente f → bornee f
        end EX10

        namespace EX11
          -- "La réciproque de : si la fonction f converge alors f est bornée"
        end EX11

       end Suites_A


       namespace Suites_B0
--        #check real.has_neg
--        #check has_neg.to_has_abs  
--        #check real.has_neg.to_has_abs.abs
--        #check real.has_neg.to_has_abs.abs

        def I          : Type := Set ℕ 
        def Nombre     : Type := ℝ 
        def Suite : Type := I → Nombre 
        def Zero:Nombre := (0:ℝ)
--        noncomputable def absR : ℝ  → ℝ  := Real.instNegReal.toHasAbs.abs 
        noncomputable def absR : ℝ  → ℝ  := abs 
        #check Real.instNegReal.toHasAbs
--        noncomputable def absR   := Real.instNegReal.toHasAbs.abs 
--        #check real.has_sup
--         def absR2 : ℝ  → ℝ  := (@has_neg.to_has_abs ℝ real.has_neg real.has_sup).abs
        noncomputable def Abs : Nombre → Nombre := λ x => absR x

        def Plus : Nombre → Nombre → Nombre := Real.instAddReal.add
--        def Mult : Nombre → Nombre → Nombre := real.has_mul.mul
        def Sub : Nombre → Nombre → Nombre := Real.instSubReal.sub

        axiom s : Suite

        def  InferieurOuEgal : Nombre → Nombre → Prop   := Real.instLEReal.le 
--        def  Appartient      : Nombre → I → Prop        := set.has_mem.mem


        --notations
        infix:50 " ≤ " => InferieurOuEgal
        infix:50 " + " => Plus
        infix:50 " - " => Sub
--        infix ∈ :50 := Appartient
--        notation `|` a `|` :100 := abs a
        notation:67  "|" a:99 "|"  => Abs a

        namespace EX12
          -- "La suite s n'est pas la suite nulle"
        end EX12

        namespace EX13
          -- "La suite n'est pas majorée"
        end EX13

        namespace EX14
          -- "La suite s n'est pas décroissante"
        end EX14

        namespace EX15
          -- "La suite s est convergente"
        end EX15

       end Suites_B0



       namespace Suites_B
        axiom I     : Type
        axiom Nombre     : Type
        def Suite : Type := I → Nombre 
        axiom Zero:Nombre

        axiom Abs : Nombre → Nombre 
        axiom Plus : Nombre → Nombre → Nombre
        axiom Sub : Nombre → Nombre → Nombre

        axiom s : Suite

        axiom InferieurOuEgal : Nombre → Nombre → Prop  
--        axiom Appartient      : Nombre → I → Prop  

        axiom InferieurOuEgalIndices : I → I → Prop  

        --notations
        infix:50 " ≤ " => InferieurOuEgal
--        infix ∈ :50 := Appartient
        infix:50 " ≤ " => InferieurOuEgalIndices
        infix:50 " + " => Plus
        infix:50 " - " => Sub
--        infix ∈ :50 := Appartient
--        notation `|` a `|` :100 := abs a
        notation:67  "|" a:67 "|" => Abs a

        namespace EX12
          -- "La suite s n'est pas la suite nulle"
        end EX12

        namespace EX13
          -- "La suite s n'est pas majorée"
        end EX13

        namespace EX14
          -- "La suite s n'est pas décroissante"
        end EX14

        namespace EX15
          -- "La suite s est convergente"
        end EX15

       end Suites_B

       namespace Geometrie
         axiom Droite : Type
         axiom a : Droite
         axiom b : Droite

         -- paralleles x y   signifie   x et y sont parallelles
         axiom paralleles : Droite → Droite → Prop  

         -- point_commun x y   signifie   x et y ont un point en commun
         axiom point_commun : Droite → Droite → Prop  

        namespace EX16
          -- "Les droites a et b sont parallèles si elles n'ont aucun point en commun ou si elles sont confondues"
        end EX16

        namespace EX17
          -- "Les droites a et b ne sont ni parallèles ni confondues"
        end EX17

        namespace EX18
          -- "Si les droites a et b n'ont aucun point commun, elles sont parallèles"
        end EX18

        namespace EX19
          -- "Pour que les droites a et b soient parallèles, il faut qu'elles n'aient aucun point commun"
        end EX19

        namespace EX20
          -- "Si les droites a et b ont un point commun, elles ne sont pas parallèles, sauf si elles sont confondues"
        end EX20

        namespace EX21
          -- "Soit les droites a et b n'ont aucun point en commun, soit elles sont confondues"
        end EX21

        namespace EX22
          -- "Si les droites a et b ne sont pas confondues, pour qu'elles soient parallèles, il suffit qu'elles n'aient aucun point en commun"
        end EX22


       end Geometrie

    end Math


    namespace Echiquier
      namespace Echiquier01
        namespace EX01
          -- ""
        end EX01
        namespace EX02
          -- "
        end EX02
        namespace EX03
          -- ""
        end EX03
        namespace EX04
          -- ""
        end EX04
        namespace EX05
          -- ""
        end EX05
        namespace EX06
          -- ""
        end EX06
        namespace EX07
          -- ""
        end EX07
      end Echiquier01
      namespace Echiquier02
        namespace EX08
          -- ""
        end EX08
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX16
          -- ""
        end EX16
      end Echiquier02
      namespace Echiquier03
        namespace EX17
          -- ""
        end EX17
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX27
          -- ""
        end EX27
      end Echiquier03
      namespace Echiquier04
        namespace EX28
          -- ""
        end EX28
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX38
          -- ""
        end EX38
      end Echiquier04
      namespace Echiquier05
        namespace EX39
          -- ""
        end EX39
        namespace EX40
          -- ""
        end EX40
      end Echiquier05
      namespace Echiquier06
        namespace EX41
          -- ""
        end EX41
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX57
          -- ""
        end EX57
      end Echiquier06
      namespace Echiquier07
        namespace EX58
          -- ""
        end EX58
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX61
          -- ""
        end EX61
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX64
          -- ""
        end EX64
      end Echiquier07
      namespace Echiquier08
        namespace EX65
          -- ""
        end EX65
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX76
          -- ""
        end EX76
      end Echiquier08
      namespace Echiquier09
        namespace EX77
          -- ""
        end EX77
        namespace EX78
          -- ""
        end EX78
        namespace EX79
          -- ""
        end EX79
      end Echiquier09
      namespace Echiquier10
        namespace EX80
          -- ""
        end EX80
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX86
          -- ""
        end EX86
      end Echiquier10
      namespace Echiquier11
        namespace EX87
          -- ""
        end EX87
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX94
          -- ""
        end EX94
      end Echiquier11
      namespace Echiquier12
        namespace EX95
          -- ""
        end EX95
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX01
          -- ""
        end EX01
        namespace EX101
          -- ""
        end EX101
      end Echiquier12
      namespace BacASable
      end BacASable
        namespace EX102
          -- ""
        end EX102
        namespace EX103
          -- ""
        end EX103
    end Echiquier

  end Formalisation
end Edukera 


-- Fichier réponse étudiante  ( qui importe l'énoncé )
namespace Edukera
  namespace Formalisation
    namespace Logique
      namespace Lecture
        namespace EX00_test
          def reponse  : Prop := (E VH LM)  ∧ (L A LM) 
        end EX00_test

        namespace EX01
          def reponse  : Prop := L A LM
        end EX01

        namespace EX02
          def reponse  : Prop := ∃ x, (L x LM) ∧  (H x)
          def reponse_erronee  : Prop := ∃ x, (L x LM) 
        end EX02

        namespace EX03
          def reponse  : Prop := ∀ y,  (H y) → (L y LM)
        end EX03

        namespace EX04
          def reponse : Prop :=  ∃ z,   (¬ ( L z LM)) ∧ (H z)
        end EX04

        namespace EX05
          def reponse : Prop :=  ∃ t,   (¬ ( L t LM)) ∧ (H t)
        end EX05

        namespace EX06
          def reponse : Prop :=  ∃ x,   (L A x) ∧ (R x)
        end EX06

        namespace EX07
          def reponse : Prop := ( E VH LM ) ∧ (H VH)
        end EX07

        namespace EX08
          def reponse : Prop := ∀ t, R t → L A t
        end EX08

        namespace EX09
          def reponse : Prop := ∃ r, (¬ (L A r)) ∧ (R r)
        end EX09

        namespace EX10
          def reponse : Prop := ∀ y, ((H y) →  (∃ t, (  (E VH t) ∧ (L y t) ∧  (R t)  )))
        end EX10

        namespace EX11
          def reponse : Prop :=  ∃  y, ( (∀ t, ( ((E VH t) ∧ (R t) ) → (L y t)))  ∧ (H y) )
        end EX11

      end Lecture
    end Logique
  end Formalisation
end Edukera 



-- Fichier test prof ( qui importe l'énoncé et la réponse étudiante )

-- Solutions
namespace Edukera

  namespace Formalisation
    namespace Logique
      namespace Lecture
        namespace EX00_test
          def solution  : Prop := (L A LM) ∧ (E VH LM) 
        end EX00_test

        namespace EX01
          def solution : Prop := L A LM
        end EX01

        namespace EX02
          def solution : Prop :=  ∃ x, ((H x) ∧ (L x LM))
        end EX02

        namespace EX03
          def solution : Prop :=  ∀ x, ( (H x) → (L x LM))
        end EX03

        namespace EX04
          def solution : Prop :=  ∃ x, ( (H x) ∧ (¬ ( L x LM)))
        end EX04

        namespace EX05
          def solution : Prop :=  ∃ x, ( (H x) ∧ (¬ ( L x LM)))
        end EX05

        namespace EX06
          def solution : Prop :=  ∃ r, ( (R r) ∧  (L A r))
        end EX06
        
        namespace EX07
          def solution : Prop :=  E VH LM -- (H VH) ∧ (E VH LM)
        end EX07

        namespace EX08
          def solution : Prop :=  ∀ r, ((R r) → (L A r))
        end EX08

        namespace EX09
          def solution : Prop :=  ∃ r, (R r) ∧ (¬ (L A r))
        end EX09

        namespace EX10
          def solution : Prop :=  ∀ x, ((H x) →  (∃ r, ( (R r) ∧ (E VH r) ∧ (L x r))))
        end EX10

        namespace EX11
          def solution : Prop :=  ∃  x, ((H x) ∧  (∀ r, ( ((R r) ∧ (E VH r)) → (L x r))))
        end EX11

        namespace EX12
          -- "Tous ceux qui ont écrit un roman ont lu Les Misérables"
--          def solution : Prop := ∀ x, (∃ r, (R r) ∧ (E x r)) → L x LM    -- incorrect Edukera   --  preciser x humain  "ceux"
          def solution : Prop := ∀ x,( (H x) ∧  (∃ r, (R r) ∧ (E x r))) → (L x LM )
        end EX12

        namespace EX13
          -- "Tous les romans n'ont pas été écrits par une même personne"
          def solution  : Prop := ¬ ( ∃ x, (H x) ∧  (∀ r, R r  →  (E x r)) )
          def solution2 : Prop :=   ∀  x, (H x) →   (∃ r,( R r ) ∧  ( ¬ (E x r)))   -- equivalente
        end EX13

        namespace EX14
          -- "Parmi les romans de Victor Hugo, Anaïs n'a lu que Les Misérables"    -- attention ambiguité  :  Anais n'a pas forcément lu les Misérables
          def solution   : Prop := ∀ r, ((R r) ∧ (E VH r) ∧ (¬ (r = LM) ))  → (¬ (L A r) )   
          def solution2  : Prop := ∀ r, ((R r) ∧ (E VH r) ∧ (L A r))  → r=LM    -- equivalente
        end EX14

        namespace EX15
          -- "Anaïs a lu exactement 2 romans"
            def solution   : Prop := ∃ r, ∃ s, (R r) ∧ (R s) ∧ (¬(r=s) ) ∧ (L A r) ∧ (L A s)  ∧ (∀ t, ((R t)∧(L A t)) → ((t=r) ∨ (t=s))  ) 
        end EX15

      end Lecture


      namespace Bucheron

          -- Paul
          --axiom P    : Chose

          -- homme x  signifie   x   est un homme
          --axiom homme    : Chose → Prop
          --axiom homme    : set Chose

          -- bucheron x  signifie   x   est un bûcheron
          --axiom bucheron    : Chose → Prop
          --axiom bucheron    : set Chose

          -- riche x  signifie   x   est riche
          --axiom riche    : Chose → Prop

          -- Paul est un être humain 
          --axiom homme_P : homme P


        namespace EX16
          -- "Tous les bûcherons sont des hommes"
            def solution   : Prop := ∀ x, bucheron x → homme x
            def solution'  : Prop := ∀ x:Chose, bucheron x → homme x
            def solution'' : Prop := ∀ x ∈ bucheron, homme x
        end EX16

        namespace EX17
          -- "Paul est riche"
            def solution   : Prop := riche P
        end EX17

        namespace EX18
          -- "Si Paul est un bûcheron, Paul est riche"
            def solution   : Prop := bucheron P → riche P
        end EX18

        namespace EX19
          -- "Tous les hommes sont bûcherons ou riches"
            def solution   : Prop := ∀ x, (homme x) → (bucheron x) ∨ (riche x)
            def solution'  : Prop := ∀ x:Chose, (homme x) → (bucheron x) ∨ (riche x)
            def solution'' : Prop := ∀ x ∈ homme, (bucheron x) ∨ (riche x)
        end EX19

        namespace EX20
          -- "Quelques bûcherons sont riches"                            -- attention ambiguité : >= 1 ou >= 2 ?    rep edukera  : rep1
          def solution   : Prop := ∃ x,  (bucheron x) ∧ (riche x)
          --def solution   : Prop := ∃ x, ∃ y,  (bucheron x) ∧ (riche x) ∧ (bucheron y) ∧ (riche y) ∧ (¬ (x=y)) -- incorrect edukera
          def solution'  : Prop := ∃ x:Chose,  (bucheron x) ∧ (riche x)
          def solution'' : Prop := ∃ x ∈ bucheron, riche x
        end EX20

        namespace EX21
          -- "Quelques bûcherons ne sont pas riches"
          def solution   : Prop := ∃ x,  (bucheron x) ∧ (¬ (riche x))
          def solution'  : Prop := ∃ x:Chose,  (bucheron x) ∧ (¬ (riche x))
        end EX21

        namespace EX22
          -- "Aucun bûcheron n'est riche"
            def solution   : Prop := ∀ x, (bucheron x) → ( ¬  (riche x))
            def solution'  : Prop := ∀ x:Chose, (bucheron x) → ( ¬  (riche x))
            def solution'' : Prop := ∀ x:Chose, x ∈ bucheron  → ( ¬  (riche x))
            def solution''': Prop := ∀ x ∈ bucheron, ( ¬  (riche x))
        end EX22

        namespace EX23
          -- "Tous les hommes sont bûcherons"
            def solution    : Prop := ∀ x, (homme x) → (bucheron x) 
            def solution'   : Prop := ∀ x:Chose, (homme x) → (bucheron x) 
            def solution''  : Prop := ∀ x:Chose, x ∈ homme → (bucheron x) 
            def solution''' : Prop := ∀ x ∈ homme, (bucheron x) 
        end EX23

        namespace EX24
          -- "Aucun homme n'est bûcheron"
            def solution    : Prop := ∀ x, (homme x) → (¬ (bucheron x)) 
            def solution'   : Prop := ∀ x:Chose, (homme x) → (¬ (bucheron x)) 
            def solution''  : Prop := ∀ x:Chose, x ∈ homme → (¬ (bucheron x)) 
            def solution''' : Prop := ∀ x ∈ homme ,  (¬ (bucheron x)) 
        end EX24

        namespace EX25
          -- "Tous les hommes ne sont pas bûcherons"
            def solution   : Prop := ∃ x, (homme x) ∧ (¬ (bucheron x))  
            def solution'  : Prop := ∃ x:Chose, (homme x) ∧ (¬ (bucheron x))  
            def solution2  : Prop := ¬ (∀  x, (homme x) →   (bucheron x))   -- equivalente
        end EX25

      end Bucheron

      namespace Grippe

          --axiom Personne : Type

          --definition Temperature : Type := nat

          -- Pierre
          --axiom Pierre    : Personne

          -- grippe x  signifie   x   a la grippe
          --axiom grippe    : Personne → Prop

          -- travail x  signifie   x   doit aller au travail
          --axiom travail    : Personne → Prop

          -- fievre x  signifie   x   a de la fievre
          --axiom fievre    : Personne → Prop

          -- tousse x  signifie   x   tousse
          --axiom tousse    : Personne → Prop

          -- temp x y  signifie   x   a une température de y
          --axiom temp    : Personne → Temperature → Prop

          -- sup x y  signifie   x   est supérieur à y
          --axiom sup    : Temperature → Temperature → Prop


        namespace EX26
          -- "Les personnes qui ont la grippe ne doivent pas aller au travail"         -- attention ambiguité : ne dovent pas  = ne sont pas obligés ou doivent ne pas ?  -- contexte : rep1
          def solution   : Prop := ∀ x, grippe x → ¬ (travail x) 
        end EX26

        namespace EX27
          -- "Les personnes qui ont de la fièvre et qui toussent ont la grippe"
            def solution   : Prop := ∀ x, fievre x ∧ tousse x → grippe x
            def solution'  : Prop := ∀ x:Personne, fievre x ∧ tousse x → grippe x
        end EX27

        namespace EX28
          -- "Ceux qui ont une température supérieure à 38°C ont de la fièvre"
            def solution   : Prop := ∀ x, ∀ y, (temp x y) ∧ (sup y TrenteHuit) → (fievre x)
            def solution'  : Prop := ∀ x:Personne, ∀ y:Temperature, (temp x y) ∧ (sup y TrenteHuit) → (fievre x)
        end EX28

        namespace EX29
          -- "Pierre tousse et a une température supérieure à 38°C"
            def solution   : Prop := tousse Pierre ∧ (∃ t, (temp Pierre t) ∧ (sup t TrenteHuit) )
            def solution'  : Prop := tousse Pierre ∧ (∃ t:Temperature, (temp Pierre t) ∧ (sup t TrenteHuit) )
        end EX29

      end Grippe


      namespace Bonheur

          --axiom Personne : Type

          -- Raphaël
          --axiom Raphael    : Personne

          -- estAperitif x  signifie   x   est apéritif
          --axiom estAperitif    : Chose → Prop

          -- apprecie x y  signifie   x:Personne   aime y:Chose
--          axiom apprecie    : Personne → Chose → Prop

          -- aime x y  signifie   x:Personne   aime y:Personne 
--          axiom aime    : Personne → Personne → Prop

          -- heureux x  signifie   x   est heureux
          --axiom heureux    : Personne → Prop



        namespace EX30
          -- "Raphaël est heureux"
          def solution   : Prop := heureux Raphael  
        end EX30

        namespace EX31
          -- "Raphaël aime les apéritifs"
          def solution   : Prop := ∀x:Chose, estAperitif x → apprecie  Raphael x
        end EX31

        namespace EX32
          -- "Quelqu'un n'aime que les apéritifs"               -- ambiguité : ce quelqu'un pourrait ne pas aimer les apéritifs
          def solution   : Prop := ∃x:Personne, ∀y:Chose, apprecie x y → estAperitif y
          
        end EX32

        namespace EX33
          -- "Tous ceux qui sont aimés sont heureux"
          def solution   : Prop := ∀ x:Personne, (∃ y:Personne, aime y x ) → heureux x
        end EX33

        namespace EX34
          -- "Ceux qui aiment sans être aimés en retour sont malheureux"
          def solution   : Prop := ∀ x:Personne, ((∃ y:Personne, aime x y ) ∧ (∀ z:Personne, ¬ (aime z x))) →  ¬ (heureux x)
        end EX34

      end Bonheur


      namespace Tournoi

          --axiom Personne : Type

          -- Alain
          --axiom A    : Personne

          -- Bernard
          --axiom B    : Personne

          -- j x y  signifie   x a joué contre y
          --axiom j    : Personne → Personne → Prop

          --axiom j_commute : ∀ x y, j x y → j y x 

          -- b x y  signifie   x a battu y
          --axiom b    : Personne → Personne → Prop

          -- i x  signifie   x   est inscrit au tournoi
          --axiom i    : Personne → Prop

          -- e x  signifie   x   est éliminé du tournoi
          --axiom e    : Personne → Prop


        namespace EX35
          -- "Alain et Bernard ont joué ensemble"
          def solution   : Prop := j A B
          def solution2   : Prop := j B A   -- attention a priori pas equivalente, sauf a considerer automatiquement un axiome de commutativité
                                            -- edukera accepte cette 2e solution 
          lemma deux_solutions_equiv : solution ↔ solution2 := by
             constructor
             all_goals {
               intro
               apply j_commute
               assumption
             }             
          
          lemma deux_solutions_equiv' : solution ↔ solution2 := ⟨ λ h => j_commute _ _ h  , λ h => j_commute _ _ h ⟩ 
        end EX35

        namespace EX36
          -- "Alain et Bernard sont inscrits au tournoi"
           def solution   : Prop := (i A) ∧ (i B)
        end EX36

        namespace EX37
          -- "Un joueur doit être inscrit pour pouvoir jouer et tout joueur battu est éliminé"    
                -- attention : la phrase en français induit une dimension temporelle, (on est élmininé après avoir été battu)
                -- ce qui n'est pas le cas de la phrase math ( e x   est un attribut intemporel de x  )
          def solution   : Prop := (∀ x, (∃ y, j x y) → (i x) ) ∧ (∀ x, (∃ y, b y x) → (e x) )
        end EX37

        namespace EX38
          -- "Bernard a battu tous les joueurs inscrits qui ont joué contre Alain"      -- prendre en compte j_commute
          def solution   : Prop := ∀x, ((i x)∧ (j A x)) →  b B x
        end EX38

        namespace EX39
          -- "Aucun joueur inscrit ayant battu Bernard n'a joué contre un joueur inscrit battu par Alain"    -- prendre en compte j_commute
          def solution   : Prop := ∀ x , ((i x) ∧ (b x B)) → (¬ (∃ y, (i y ) ∧ (b A y) ∧ (j x y) ))
        end EX39

      end Tournoi


      namespace Connaissance

          --axiom Personne : Type

          -- Thomas
          --axiom T    : Personne

          -- Jeanne
          --axiom J    : Personne

          -- connait x y  signifie   x connaît y
          --axiom connait    : Personne → Personne → Prop


        namespace EX40
          -- "Quelqu'un connaît Jeanne"
          def solution   : Prop := ∃ x, connait x J            -- edukera ne presuppose par la commutativite de connait :  ∃ x, connait J x   n'est pas accepté 
        end EX40

        namespace EX41
          -- "Personne ne connaît tout le monde"
          def solution   : Prop := ¬ (∃x, ∀ y, connait x y )
          def solution2  : Prop := ∀ x, ∃ y, ¬ (connait x y)     -- equivalente
        end EX41

        namespace EX42
          -- "Thomas connaît tous ceux qui connaissent Jeanne"
          def solution   : Prop := ∀ x, connait x J → connait T x
        end EX42

        namespace EX43
          -- "Jeanne connaît quelqu'un qui connaît tout le monde"
          def solution   : Prop := ∃ x, (connait J x) ∧ (∀ y, connait x y )
        end EX43

      end Connaissance



      namespace Nature

          -- mange x y  signifie   x mange y
          --axiom mange    : Chose → Chose → Prop

          -- herbivore x  signifie   x   est un herbivore
          --axiom herbivore    : Chose → Prop

          -- vegetal x  signifie   x   est un végétal
          --axiom vegetal    : Chose → Prop

          -- bambou x  signifie   x   est un bambou
          --axiom bambou    : Chose → Prop

          -- panda x  signifie   x   est un panda
          --axiom panda    : Chose → Prop



        namespace EX44
          -- "Les herbivores mangent des végétaux"
          def solution   : Prop := ∀x, herbivore x  → ∃ y, vegetal y ∧ mange x y   
        end EX44

        namespace EX45
          -- "Les herbivores ne mangent que des végétaux"    -- ambiguité : en mangent ils?   -- rep eduk : pas forcément
          def solution   : Prop :=  ∀x, herbivore x  → (∀ y, mange x y → vegetal y)
        end EX45

        namespace EX46
          -- "Aucun herbivore ne mange tout type de végétal"     -- ?? confusion végétal/type de végétal ?
          def solution   : Prop := ∀ x, herbivore x → (∃y, (vegetal y) ∧ (¬ (mange x y))  )
        end EX46

        namespace EX47
          -- "Il y a des végétaux que ne mange aucun herbivore"    -- ambiguité : des?
          def solution   : Prop := ∃y, (vegetal y) ∧ (∀x , herbivore x → (¬ (mange x y))  ) 
        end EX47

        namespace EX48
          -- "Certains herbivores ne mangent pas de bambou"       -- ambiguité : pluriel
          def solution   : Prop := ∃ x, (herbivore x) ∧ ( ∀y, bambou y → (¬ (mange x y )))
        end EX48

        namespace EX49
          -- "Les pandas sont des herbivores qui ne consomment que des bambous"     -- ambiguité : en mangent-ils ? rep : pas forcément
          def solution   : Prop := ∀x, panda x → ((herbivore x) ∧  (∀ y, mange x y → bambou y )  ) 
        end EX49

      end Nature



      namespace SystemeSolaire

          -- Soleil
          --axiom So    : Chose

          -- Mercure
          --axiom Me    : Chose

          -- Vénus
          --axiom V     : Chose

          -- Terre
          --axiom T     : Chose

          -- Mars
          --axiom Ma    : Chose

          -- Lune
          --axiom L     : Chose

          -- Jupiter
          --axiom J     : Chose

          -- Saturne
          --axiom Sa    : Chose

          -- Uranus
          --axiom U     : Chose

          -- Neptune
          --axiom N     : Chose

          -- planete x  signifie   x   est une planète
          --axiom planete    : Chose → Prop

          -- tourneTerre x  signifie   x   tourne autour de la Terre
          --axiom tourneTerre    : Chose → Prop

          -- plusPetit x y  signifie   x   est plus petit (ou aussi grand) que y
          --axiom plusPetit    : Chose → Chose → Prop

          -- plusProcheSoleil x y  signifie   x   est plus proche (ou à égale distance) du Soleil que y
          --axiom plusProcheSoleil    : Chose → Chose → Prop



        namespace EX50
          -- "Vénus est une planète"
          def solution   : Prop := planete V
        end EX50

        namespace EX51
          -- "Le Soleil n'est pas une planète"
          def solution   : Prop := ¬ (planete So)
        end EX51

        namespace EX52
          -- "Le Soleil tourne autour de la Terre"
          def solution   : Prop := tourneTerre So
        end EX52

        namespace EX53
          -- "Certaines planètes sont plus petites que la Terre"     -- ambiguité : pluriel   -- ambiguité : ou égal
          def solution   : Prop := ∃p, (planete p) ∧  (plusPetit p T)
        end EX53

        namespace EX54
          -- "Toutes les planètes sont plus petites que Saturne"     -- faux !! ;-)
        end EX54
          def solution   : Prop := ∀ p, planete p → plusPetit p Sa 

        namespace EX55
          -- "Rien n'est plus petit que la Lune"           -- ambiguité :   phrase fausse en considérant que plusPetit signifie plusPetitOuEgal ... (plusPetit L L)
          def solution   : Prop := ∀ x, ¬ (plusPetit x L)
        end EX55

        namespace EX56
          -- "Mercure est la planète la plus proche du Soleil"                               --  ??? solution edukera introuvable ?? bug edukera
--          def solution   : Prop := ∀ p , planete p →  plusProcheSoleil Me p                -- incorrect, il faut preciser que Mercure est une planete
          def solution   : Prop := (planete Me) ∧  (∀ p , planete p →  plusProcheSoleil Me p)
        end EX56

        namespace EX57
          -- "Mars est plus loin du Soleil que Neptune"          -- impossible !!...     -- ambiguité : "à ou égale distance"
          def solution   : Prop := plusProcheSoleil N Ma
        end EX57

        namespace EX58
          -- "Si quelquechose est plus éloigné du Soleil que Neptune, alors ce n'est pas une planète"  
                -- ambiguité : "ou à égale distance..."    -- du coup Neptune n'est pas une planète ???
          def solution   : Prop := ∀ x, plusProcheSoleil N x → ¬ (planete x) 
        end EX58

        namespace EX59
          -- "Si le Soleil tourne autour de la Terre, alors il est plus petit que celle-ci"            -- vrai    -- "ou égal"
          def solution   : Prop := tourneTerre So → plusPetit So T  
        end EX59

        namespace EX60
          -- "S'il n'y a pas de planète plus grande que la Terre, alors la Terre est plus grande que Jupiter"       -- vrai     --- ambiguités ? égalité ?
          def solution   : Prop := (∀ p, planete p → plusPetit p T) → plusPetit J T
        end EX60

        namespace EX61
          -- "La Lune est une planète mais certaines choses ne sont pas des planètes"        -- faux...    -- ambiguité : pluriel
          def solution   : Prop := (planete L) ∧ (∃x, ¬ (planete x)  ) 
        end EX61

        namespace EX62
          -- "Toutes les planètes ne tournent pas autour de la Terre"
          def solution   : Prop := ∃ p, (planete p) ∧ (¬(tourneTerre p) )
          def solution2  : Prop := ∃ p, ¬ (planete p → tourneTerre p )     -- equivalente
        end EX62

        namespace EX63
          -- "Aucune planète n'est plus petite que Mercure"      --- ambiguité : rep edukera : ∀ x, planete x  → (plusPetit Me x)    : alors que l'énoncé sous entend strict...
          def solution   : Prop := ∀ p, planete p  → (plusPetit Me p) 
          def solution'  : Prop := ¬ (∃ p, (planete p)  ∧  (plusPetit p Me) )
            --- ?!  les deux solutions ci dessus sont acceptées par Edukera ce qui sous entend que (plusPetit Me p)   est  la négation de  (plusPetit p Me) ...
        end EX63

        namespace EX64
          -- "Il n'y a pas de planète qui soit plus grande que la Terre tout en étant plus proche du Soleil qu'elle"  -- tjrs ambiguité sur égalités
          def solution   : Prop := ¬ (∃ p, (planete p) ∧ (plusPetit T p) ∧ (plusProcheSoleil p T)  )
        end EX64

        namespace EX65
          -- "Il existe une planète telle que tout objet plus proche du Soleil qu'elle, est plus petit qu'elle"
          def solution   : Prop := ∃p,(planete p) ∧ (∀ x, (plusProcheSoleil x p) → (plusPetit x p) )
        end EX65

        namespace EX66
          -- "Aucune planète n'est à la fois plus petite qu'Uranus et plus éloignée du Soleil qu'elle"    -- idem egalité distance
          def solution   : Prop := ¬ (∃ p, (planete p) ∧  (plusPetit p U)  ∧ (plusProcheSoleil U p))
        end EX66

        namespace EX67
          -- "Si toutes les planètes tournent autour de la Terre, alors Neptune aussi"          -- vrai
          def solution   : Prop := (∀ p, planete p → tourneTerre p ) → tourneTerre N
        end EX67

      end SystemeSolaire

    end Logique

    namespace Math 
       namespace Arithmetique
        
        -- Le type entier nature
        --axiom Entier: Type

        -- InferieurOuEgal x y  signifie   x ≤  y
        --axiom InferieurOuEgal    : Entier → Entier → Prop

        -- Pair x  signifie   x   est pair
        --axiom Pair    : Entier → Prop

        -- Prem x  signifie   x   est premier
        --axiom Prem    : Entier → Prop


        -- Plus x y  signifie   x + y
        --axiom Plus    : Entier → Entier → Entier

        -- Mult x y  signifie   x * y
        --axiom Mult    : Entier → Entier → Entier

        -- Div x y  signifie   x divise y
        --axiom Div    : Entier → Entier → Prop

        -- 0
        --axiom Zero : Entier

        -- 1
        --axiom Un : Entier

        --notations
        --infix ≤:50 := InferieurOuEgal
        --infix +:65 := Plus
        --infix *:65 := Mult
        --infix |:50 := Div



        namespace EX01
          -- "Il existe un entier plus petit ou égal à tous les autres"
          def solution   : Prop :=  ∃n:Entier, ∀ m:Entier, n ≤ m
        end EX01

        namespace EX02
          -- "Il n'existe pas d'entier plus grand ou égal à tous les autres, mais pour tout entier, il en existe un qui est strictement plus grand"
            def solution   : Prop := (¬ (∃s:Entier, ∀n:Entier, n ≤ s )) ∧ (∀ m:Entier, ∃n:Entier, (m ≤ n ) ∧ (¬ (m=n)) ) 
        end EX02

        namespace EX03
          -- "Tout nombre entier pair est égal à la somme de deux nombres entiers premiers"              
              -- axiomatiser la commutativité de + ? ou la commutativité des ∃ et du ∧ suffisent ?
            def solution   : Prop := ∀ n:Entier, (Pair n) → (∃ p, ∃ q, (Prem p) ∧ (Prem q) ∧ (n = p+q) )
        end EX03

        namespace EX04
          -- "L'ensemble des entiers premiers est non borné"    -- pas si evident : edukera accepte ∀x, ∃y, x ≤ y ∧ x ≠ y ∧ (Prem y)  
                                                                -- mais n'accepte pas               ∀x, ∃y, x ≤ y ∧ (Prem y)  
                                                                -- ni                               ∀x, ∃y, x +1 ≤ y ∧ (Prem y)      pourtant corrects
          -- il y a aussi la signification de 'borné' qui dans ℕ signifie 'majoré'                                                                 
            def solution   : Prop := ∀ x:Entier, ∃ y:Entier, x ≤ y ∧ ¬ (x=y)   ∧ (Prem y)
          -- Remarque  : si on remplace (Prem y) par sa définition utilisant Div, edukera n'accepte plus...
            def solution2  : Prop := ∀ x:Entier, ∃ y:Entier, x ≤ y ∧ ¬ (x=y)   ∧ ( (¬(y=Zero)) ∧ (¬(y=Un)) ∧ (∀ d:Entier, (Div d y) → ((d=Un)∨ (d =y)))  )
          -- N'en parlons pas si on remplace (Div d y) par sa définition utilisant Mult ...   et prendre en compte la commutativité de Mult ....
            def solution3  : Prop := ∀ x:Entier, ∃ y:Entier, x ≤ y ∧ ¬ (x=y)   ∧ ( (¬(y=Zero)) ∧ (¬(y=Un)) ∧ (∀ d:Entier, (∃k:Entier, d= Mult k y ) → ((d=Un)∨ (d =y)))  )
        end EX04


       end Arithmetique


       namespace Fonctions

        --axiom Nombre     : Type
        --axiom Intervalle : Type

        --axiom InferieurOuEgal : Nombre → Nombre → Prop  
        --axiom Appartient      : Nombre → Intervalle → Prop  

        --notations
        --infix ≤ :50 := InferieurOuEgal
        --infix ∈ :50 := Appartient

        --axiom f : Nombre → Nombre
        --axiom I : Intervalle

        namespace EX05
          -- "La fonction f est croissante sur l'intervalle I"
            def solution   : Prop := ∀ x y, x∈ I ∧ y ∈ I ∧ x ≤ y → f x ≤ f y
              -- devrait etre encore accepté si on remplace x ≤ y par x < y ;  meme si < ne figure pas dans les predicats,
             --  un-e etudiant-e pourrait le remplacer par  ((x ≤ y) ∧ (¬(x=y) ))
        end EX05

        namespace EX06
          -- "La fonction f n'est pas croissante sur l'intervalle I"
            def solution   : Prop := ¬ (∀ x y, x∈ I ∧ y ∈ I ∧ x ≤ y → f x ≤ f y)
            def solution2  : Prop := ∃ x y, x∈ I ∧ y ∈ I ∧ x ≤ y ∧ (¬ ( f x ≤ f y))
            -- doit on accepter ceci ?   ce qui revient à axiomatiser la négation de ≤ , provenant de [ordre total, réflexivité de ≤ ,  antisymétrie de  ≤ ] 
            def solution3  : Prop := ∃ x y, x∈ I ∧ y ∈ I ∧ x ≤ y ∧ (( f y ≤ f x) ∧ ( ¬ (f x = f y)) )
        end EX06

        namespace EX07
          -- "La fonction f est strictement décroissante sur l'intervalle I"
            def solution   : Prop := ∀ x y, x∈ I ∧ y ∈ I ∧ ((x ≤ y) ∧ (¬(x=y) )) → ((f x ≤ f y) ∧ (¬ (f x = f y)))
        end EX07

        namespace EX08
          -- "La fonction f est majorée sur l'intervalle I"
            def solution   : Prop := ∃A:Nombre, ∀ x, x∈ I → f x ≤ A  
        end EX08

        namespace EX09
          -- "La fonction f est bornée sur l'intervalle I"
            def solution   : Prop := ∃A:Nombre,∃B:Nombre, ∀ x, x∈ I → (f x ≤ A) ∧ (B ≤ f x) 
        end EX09

       end Fonctions

       namespace Suites_A
        --axiom Entier     : Type
        --axiom Nombre     : Type
        --def Suite : Type := Entier → Nombre 
        --axiom Zero:Nombre

        -- convergente x signifie x est convergente
        --axiom convergente : Suite → Prop

        -- bornee x signifie x est bornee
        --axiom bornee : Suite → Prop

        namespace EX10
          -- "La contraposée de : si la fonction f converge alors f est bornée"     -- f: suite ?      
                                                                                    -- contraposée : équivalente? ou s'arrete l'automatisation ?
                                                                                    -- edukera accepte : ∀ f, convergente f → bornee f
            def solution   : Prop := ∀ f,  ¬( bornee f) → ¬( convergente f)
            def solution2  : Prop := ∀ f, convergente f → bornee f        -- discutable si cette automatisation doit etre appliquée...
        end EX10

        namespace EX11
          -- "La réciproque de : si la fonction f converge alors f est bornée"
            def solution   : Prop := ∀ f,  convergente f → bornee f
            def solution2  : Prop := ∀ f,  ¬( bornee f) → ¬( convergente f)   -- ...
        end EX11

       end Suites_A

       namespace Suites_B
        --axiom I     : Type
        --axiom Nombre     : Type
        --def Suite : Type := I → Nombre 
        --axiom Zero:Nombre

        --axiom Abs : Nombre → Nombre 
        --axiom Plus : Nombre → Nombre → Nombre
        --axiom Sub : Nombre → Nombre → Nombre

        --axiom s : Suite

        --axiom InferieurOuEgal : Nombre → Nombre → Prop  
--        axiom Appartient      : Nombre → I → Prop  


        --notations
        --infix ≤ :50 := InferieurOuEgal
--        infix ∈ :50 := Appartient
        --infix ≤ :50 := InferieurOuEgal
        --infix + :65 := Plus
        --infix - :65 := Sub
--        infix ∈ :50 := Appartient
--        notation `|` a `|` :100 := abs a
        --notation `|` a `|` :100 := abs a

        namespace EX12
          -- "La suite s n'est pas la suite nulle"
            def solution   : Prop := ¬ (∀ n , s n = Zero)
            def solution2  : Prop := ∃ n, ¬ (s n = Zero)  
        end EX12

        namespace EX13
          -- "La suite s n'est pas majorée"                    -- dans ces négations attend on que l'étudiant-e explicite la négation des quantificateurs ?
            def solution   : Prop := ¬( ∃ A, ∀ n, s n ≤ A ) 
            def solution2  : Prop := ∀  A, ∃ n, ¬( s n ≤ A )
            def solution3  : Prop := ∀  A, ∃ n, ( A ≤ s n ) ∧ ( ¬ (s n = A))      -- implementer la negation de ≤ 
            def solution4  : Prop := ∀  A, ∃ n, ( A ≤ s n )                       -- prouver equivalent !  auto ??   -- ajouter axiome R non majoré....
        end EX13

        namespace EX14
          -- "La suite s n'est pas décroissante"
            def solution    : Prop := ¬  (∀ n ,  s n ≤ s (succ n) )       -- definir succ
            --def solution2   : Prop := ¬  (∀ m n ,  m ≤ n → s n ≤ s m )  -- autoriser ≤ pour I ??  oui
        end EX14

        namespace EX15
          -- "La suite s est convergente"
--            def solution   : Prop := ∃ ℓ , ∀ ε , ((Zero ≤  ε ) ∧ ( ¬  (Zero = ε ) )) → (∃ N:I,  ∀ n, (N ≤ n) →   | Sub (s n) ℓ |  ≤ ε    )
            def solution   : Prop := ∃ ℓ , ∀ ε , ((Zero ≤  ε ) ∧ ( ¬  (Zero = ε ) )) → (∃ N:I,  ∀ n, (N ≤ n) →   Abs (Sub (s n) ℓ)   ≤ ε    )
        end EX15

       end Suites_B

       namespace Geometrie
         --axiom Droite : Type
         --axiom a : Droite
         --axiom b : Droite

         -- paralleles x y   signifie   x et y sont parallelles
         --axiom paralleles : Droite → Droite → Prop  

         -- point_commun x y   signifie   x et y ont un point en commun
         --axiom point_commun : Droite → Droite → Prop  

        namespace EX16
          -- "Les droites a et b sont parallèles si elles n'ont aucun point en commun ou si elles sont confondues"
            def solution   : Prop := ((¬(point_commun a b)  ) ∨    (a = b) ) → paralleles a b
        end EX16

        namespace EX17
          -- "Les droites a et b ne sont ni parallèles ni confondues"
            def solution   : Prop := (¬ (paralleles a b))∧(¬(a = b) ) 
            -- axiome : confondues => paralleles   ??    ( ∀ d , paralleles d d)     (*)
            -- EX16 implique cet axiome
            -- def solution2   : Prop := ¬ (paralleles a b) 
        end EX17

        namespace EX18
          -- "Si les droites a et b n'ont aucun point commun, elles sont parallèles"
            def solution   : Prop := (¬ (point_commun a b)) → (paralleles a b)
        end EX18

        namespace EX19
          -- "Pour que les droites a et b soient parallèles, il faut qu'elles n'aient aucun point commun"
            -- rq: si cette assertion est vraie, cela contredit l'axiome (*) donc aussi EX16
            -- ( sou l'hypothese de l'axiome   ( ∀ d , point_commun d d)   )
            def solution   : Prop := (paralleles a b) → (¬ (point_commun a b))
        end EX19

        namespace EX20
          -- "Si les droites a et b ont un point commun, elles ne sont pas parallèles, sauf si elles sont confondues"
            -- attention pour l'equivalence entre ces deux solutions la logique classique risque d'etre nécessaire
            def solution   : Prop :=  (point_commun a b) →  (( ¬  (paralleles a b)  )∨ ( a = b) )
            def solution2  : Prop :=  ((point_commun a b) ∧ (¬( a = b) ) )→  ( ¬  (paralleles a b))
        end EX20

        namespace EX21
          -- "Soit les droites a et b n'ont aucun point en commun, soit elles sont confondues"
            def solution   : Prop := (¬(point_commun a b))∨(a=b) 
        end EX21

        namespace EX22
          -- "Si les droites a et b ne sont pas confondues, pour qu'elles soient parallèles, il suffit qu'elles n'aient aucun point en commun"
            def solution   : Prop := ( ¬( a = b)  ) → ( ( ¬ (point_commun a b) ) → ( paralleles a b ) )
        end EX22


       end Geometrie



    end Math 



  end Formalisation
end Edukera 

#check and_comm

-- Verifications
namespace Edukera
  namespace Tactic
/-
   meta def try_exists_swap : tactic unit :=
   do
     `[fconstructor],
     tactic.all_goals
     (do `[intro r],
       `[cases r with x h],
       `[existsi x],
       `[tauto]
     ),
     return ()
-/
/-  open Lean Meta Elab Tactic Term in
  elab "try_exists_swap" : tactic => do
     evalTactic $ ← `(tactic|fconstructor)
-/
  syntax "try_exists_swap" : tactic
  macro_rules
| `(tactic| try_exists_swap) => `(tactic| 
          fconstructor <;> 
          all_goals (
                intro r  
            <;> cases r with 
            | intro x h =>  existsi x   <;> tauto
          )
     )

  theorem and_comm' : ∀ {a b : Prop}, a ∧ b ↔ b ∧ a := @And.comm

   /- meta def try_swaps : tactic unit :=
   do
      `[exact exists_swap] <|> `[exact forall_swap] <|>  `[exact tactic.and_comm'] <|>  try_exists_swap  <|> tactic.trace "zut"
   -/

  syntax "try_swaps" : tactic
  macro_rules
| `(tactic| try_swaps) => `(tactic| 
               exact exists_swap
          <|>  exact forall_swap 
          <|>  exact Tactic.and_comm'
          <|>  try_exists_swap
          <|>  trace "zut"
     )

  /-
   meta def try_verif : tactic unit :=
   do
     `[tauto! {closer:=try_swaps}] <|> `[finish] <|>  try_swaps
   -/

  syntax "try_verif" : tactic
  macro_rules
| `(tactic| try_verif) => `(tactic| 
               tauto 
--          <|>  finish
          <;>  try_swaps
     )


  /-
   meta def try_verif' : tactic unit :=
   do
     `[tauto! ] <|> `[finish] <|>  try_swaps
   -/


  end Tactic

  namespace Formalisation
    namespace Logique
      namespace Lecture

        namespace EX00_test
          theorem verification : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop

          theorem v : reponse ↔ solution := ⟨ (λ r, ⟨r.right,r.left ⟩  ) , (λ s, ⟨s.right,s.left ⟩  ) ⟩ 
          #print verification'
        end EX00_test

        namespace EX01
          theorem verification : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop

          #print verification
          #print verification'
        end EX01

        namespace EX02
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop   -- tauto

          theorem v0  : reponse ↔ solution := by try_swaps

          def reponse1  : Prop := ∃ x, (L x LM) ∧  (H x)
          def solution1 : Prop :=  ∃ x, ((H x) ∧ (L x LM))

          theorem v1  : (∃ x, (L x LM) ∧  (H x)) ↔ (∃ x, ((H x) ∧ (L x LM)) ):= by aesop
          theorem v2 x  :  (L x LM) ∧  (H x) ↔  ((H x) ∧ (L x LM)) := by aesop
          --theorem v3  : ∃ x, (L x LM) ∧  (H x) ↔ ∃ x, ((H x) ∧ (L x LM)) := by aesop
          --theorem v3'  : ∃ x, (L x LM) ∧  (H x) ↔ ∃ x, ((H x) ∧ (L x LM)) := by library_search


          theorem v4' {α:Type} {P: α→Prop}  {Q: α→Prop} : (∀x, (P x ↔ Q x)) → ( (∃ x, P x) ↔ (∃x, Q x )  )
              := by library_search

          #print v4' 

          theorem v4 {α:Type} {P: α→Prop}  {Q: α→Prop} : (∀x, (P x ↔ Q x)) → ( (∃ x, P x) ↔ (∃x, Q x )  )
              := by aesop

          #print v4 

          theorem v3'''  : (∃ x, (L x LM) ∧  (H x)) ↔ ∃ x, (((H x) ∧ (L x LM)) ):= by aesop

          theorem w0 : ¬ (reponse_erronee ↔ solution) := by 
            unfold reponse_erronee
            unfold solution
            aesop
           



        end EX02

        namespace EX03
          theorem verification  : reponse ↔ solution := by try_verif 
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop -- tauto

          #print verification
          #print verification'
        end EX03

        namespace EX04
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop -- tauto

        end EX04

        namespace EX05
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop -- tauto
        end EX05

        namespace EX06
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop -- tauto
        end EX06
        
        namespace EX07
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponseHH_VH
/-/
          class HVHClass : Prop where 
             hHVH : H VH

          instance iHVH: HVHClass :=  ⟨ H_VH ⟩ 

          theorem verification'' [HVHClass] : reponse  ↔ solution  := by 
            unfold reponse
            unfold solution
            aesop -- tauto
--            exact H_VH
            exact inst.hHVH
-/
          theorem verification'''  : reponse  ↔ solution  := by 
            unfold reponse
            unfold solution
            aesop(add safe H_VH) -- tauto

          theorem v : reponse ↔  solution := by
              fconstructor
              intro h
              exact h.left

              intro
              fconstructor
              assumption
              exact H_VH

        end EX07
        
        namespace EX08
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop

          #print verification
          #print verification'
        end EX08
        
        namespace EX09
          theorem verification  : reponse ↔ solution := by try_verif 
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop
        end EX09

        namespace EX10
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop

          theorem v : reponse ↔  solution := by
            unfold reponse
            unfold solution
            fconstructor

            intros r x hx
            exact (  let ⟨t,⟨ a,b,c⟩  ⟩ := r x hx 
                     ⟨ t, ⟨ c,a,b⟩  ⟩  )

            intros s x hx
            exact (  let ⟨t,⟨ a,b,c⟩  ⟩ := s x hx 
                     ⟨ t, ⟨ b,c,a⟩  ⟩  )

          example  (E:Type) (P Q : E → Prop) : (∀ x, (P x) → (Q x)) → (∀ x, P x) → (∀ x, Q x):= by exact?
          example  (E:Type) (P Q : E → Prop) : (∀ x, (P x) → (Q x)) → (∀ x, P x) → (∀ x, Q x):= λ h hp x ↦ h x (hp x)

          theorem v' : reponse ↔  solution := by
            unfold reponse
            unfold solution
            fconstructor

            intros r x hx
            exact (  let ⟨t,⟨ a,b,c⟩  ⟩ := r x hx 
                     ⟨ t, ⟨ c,a,b⟩  ⟩  )

            intros s x hx
            exact (  let ⟨t,⟨ a,b,c⟩  ⟩ := s x hx 
                     ⟨ t, ⟨ b,c,a⟩  ⟩  )

        end EX10

        namespace EX11
          theorem verification  : reponse ↔ solution := by try_verif
          theorem verification' : reponse ↔ solution := by 
            unfold reponse
            unfold solution
            aesop

          theorem v : reponse ↔  solution := by
            fconstructor

            intro rep
            exact (
              let ⟨ y, ⟨ rf , rh⟩  ⟩ := rep 
              ⟨y, ⟨ rh, by intros r rr_evhr ; exact (rf r ⟨rr_evhr.right, rr_evhr.left ⟩ )    ⟩  ⟩ 
            )

            intro sol
            exact (
              let ⟨ y, ⟨ rh, rf  ⟩  ⟩ := sol
              ⟨y, ⟨  by intros t evhr_rt ; exact (rf t ⟨ evhr_rt.right, evhr_rt.left ⟩ )    , rh ⟩  ⟩ 
            )

        end EX11

      end Lecture
    end Logique
  end Formalisation
end Edukera 

