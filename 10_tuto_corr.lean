import Esisar.Basic


-- Vous pouvez tester immédiatement ces exemples dans le Lean Web Editor :
-- https://lean.math.hhu.de/

-- Ou vous pouvez installer sur votre machine VS Code et l'extension Lean4 en suivant ces instructions :
-- https://leanprover.github.io/lean4/doc/quickstart.html
-- https://leanprover-community.github.io/install/project.html


-- Tout ce qui dans une ligne suit -- est un commentaire, et donc ignoré par Lean

-----------------------
-- 10_tuto.lean
-- Nouvelles notions
-----------------------

--   Exemple 1 -----------------------
--    introduction de ∀
--    introduction de → 
--    environnement calc
--    tactiques ring_nf, rw, norm_num

--  Exemple 2 -----------------------
--    le ET logique (∧)  : introduction et élimination

--  Exemple 3 -----------------------
--   écrire une définition
--   quantificateur ∃  : introduction

--  Exemple 4 -----------------------
--   utiliser un lemme ou un théorème de la bibliothèque

--  Exemple 5 -----------------------
--   quantificateur ∃ : élimination

--  Exemple 6 -----------------------
--   quantificateur ∀ : élimination

--  Exemple 7 -----------------------
--   Démontrer un résultat intermédiaire et le nommer avec  'have'

--  Exemple 8 -----------------------
--    utilisation de congr_arg
--    utilisation de lemmes de la bibliothèque pour prouver un calcul




------------------------------------------------------------------
--- Exemple 1
------------------------------------------------------------------

-- Nouvelles notions
--    introduction de ∀
--    introduction de → 
--    environnement calc
--    tactiques ring_nf, rw, norm_num



example : ∀ x:ℝ, 3*x+4=2 → x=-2/3     -- énoncé à démontrer
  -- ∀ : taper \forall 
  -- → : taper \imp ou \to ou \rightarrow  ou \r 
  -- ℝ : taper \R 
  -- le ∈ des maths se note  ici : (deux points)
  -- le ⇒ des maths se note  ici → (flèche simple) 

  :=    -- annonce la preuve

  λ x:ℝ ↦      -- pour montrer pour tout, on fait 'soit'. Ceci s'appelle l'introduction de ∀
               -- le mot 'soit' se note λ 
  -- λ : taper \lambda
  -- ↦ : taper \mapsto
    λ h:3*x+4=2 ↦  -- pour prouver P → Q  , on suppose P et on montre Q. Ceci s'appelle l'introduction de → 
                -- le mot 'supposons' se note encore λ 
                -- l'hypothèse 3*x+4=2 est nommée ; ici on a choisi de la nommer h
      calc
        x = (3*x+4-4)/3 := by ring_nf     -- à gauche du :=,  les calculs, 
        _ = (2  -4)/3   := by rw[h]       -- à droite du := , la preuve de chaque étape
        _ = -2/3        := by norm_num    -- ring_nf, rw, et norm_num sont des 'tactiques'

        -- elles sont censées trouver automatiquement des preuves de faits simples
        -- ring_nf : manipulations algébriques
        -- rw[h] : réécrire en utilisant une hypothèse h
        -- norm_num  : calculs numériques


-- en déplaçant le curseur dans le code source, remarquez que deux informations sont affichées
-- et sont actualisées lorsque le curseur se déplace : 
-- *  le  but (goal), commençant par le symbole bleu ⊢  : c'est ce qu'il faut prouver
-- *  la liste des symboles et hypothèses présents dans le contexte (en jaune)

-- Avec le curseur devant le λ de  λ x:ℝ ↦   , on voit que le contexte et vide et
-- le but est :  ⊢ ∀ (x : ℝ), 3 * x + 4 = 2 → x = -2 / 3
-- Avec le curseur devant le λ de λ h:3*x+4=2 ↦, on voit que 
-- le but est maintenant réduit à :  ⊢  3 * x + 4 = 2 → x = -2 / 3
-- mais le symbole x:ℝ  a été introduit dans le contexte 
-- et ainsi de suite. Amusez vous à faire varier la position du curseur 
-- et observez l'évolution du but et du contexte 


-- Exercice 1.1
example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      calc
        x = (2*x+11-11)/2 := by ring_nf
        _ = (6  -11)/2    := by rw[h]
        _ = -5/2          := by norm_num

example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  soit x:ℝ ,                       -- des macros 'maison' permettent d'écrire soit et supposons
    supposons h:2*x+11=6 ,         -- à la place de λ 
      calc
        x = (2*x+11-11)/2 := by ring_nf
        _ = (6  -11)/2    := by rw[h]
        _ = -5/2          := by norm_num



-- Exercice 1.2
example  : ∀ c:ℚ,  4*c+1 =3*c-2 →  c = -3 :=
  λ  c:ℚ ↦ 
    λ  h:  4*c+1 =3*c-2 ↦ 
      calc
        c =  (4*c+1)-(3*c-2)  - 3  := by ring_nf
        _ =  (3*c-2)-(3*c-2)  - 3 := by rw[h]
        _ = -3                    := by norm_num

example  : ∀ c:ℚ,  4*c+1 =3*c-2 →  c = -3 :=
  soit c:ℚ,
    supposons h:  4*c+1 =3*c-2,
      calc
        c =  (4*c+1)-(3*c-2)  - 3 := by ring_nf
        _ =  (3*c-2)-(3*c-2)  - 3 := by rw[h]
        _ = -3                    := by norm_num

-- Exercice 1.3
example : ∀ a b :ℝ ,(a ≤ b) → (∀ x:ℝ,  x ≥ b → x ≥ a ) :=
  λ a b :ℝ ↦ 
    λ h : a ≤ b ↦    
      λ x : ℝ ↦
        λ hxb : x ≥ b ↦ 
          calc 
            x ≥ b := hxb
            _ ≥ a := h


example : ∀ a b :ℝ ,(a ≤ b) → (∀ x:ℝ,  x ≥ b → x ≥ a ) := 
  soit a :ℝ,
  soit b :ℝ,
    supposons h : a ≤ b,
      soit x : ℝ,
        supposons hxb : x ≥ b,
          calc 
            x ≥ b := hxb
            _ ≥ a := h





------------------------------------------------------------------
-- Exemple 2
------------------------------------------------------------------

-- Nouvelles notions
--   le ET logique (∧)  : introduction et élimination

example : ∀ (P Q : Prop), P ∧ Q → Q ∧ P 
                         --  ∧ signifie "et" .  Il s'obtient en tapant \and  
:=
  λ P  Q : Prop ↦        -- soient P, Q... 
    λ  h: P ∧ Q ↦               -- supposons P et Q ; cette hypothèse sera nommée h
      And.intro         -- pour former une preuve de Q ∧ P, on fournit à And.intro une preuve de Q et une preuve de P
                        -- ceci s'appelle l'introduction du ET (∧)
        (h.right:Q)     -- comme h est une preuve de P ∧ Q,   h.right est une preuve de Q
        (h.left :P)     -- ... et h.left est une preuve de P  (.left et .right constituent les éliminations du ET (∧))



-- Exercice 2.1
example : ∀ (P : Prop), P → P ∧ P := 
  λ P : Prop ↦
    λ h:P ↦
      And.intro (h:P) (h:P)    

example : ∀ (P : Prop), P → P ∧ P := 
  soit P : Prop,
    supposons h:P,
      And.intro (h:P) (h:P)    

-- Exercice 2.2
example : ∀ (P Q : Prop), P ∧ Q → P :=
  λ P Q : Prop ↦ 
    λ h: P ∧ Q ↦ 
      (h.left:P) 

example : ∀ (P Q : Prop), P ∧ Q → P :=
  soit P : Prop,
    soit Q : Prop,
      supposons h: P ∧ Q,
        (h.left:P) 

-- Exercice 2.3
example : ∀ (P Q : Prop), P ∧ Q → Q :=
  λ P Q : Prop ↦ 
    λ h: P ∧ Q ↦ 
      (h.right:Q) 

example : ∀ (P Q : Prop), P ∧ Q → Q :=
  soit P : Prop,
    soit Q : Prop,
      supposons h: P ∧ Q,
        (h.right:Q) 

-- Exercice 2.4
example : ∀ (P Q R: Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := 
  λ P Q R : Prop ↦ 
    λ h : (P∧Q)∧ R ↦
      And.intro
        (h.left.left : P)
        (
          And.intro
            (h.left.right: Q)
            (h.right:      R)
        )  

example : ∀ (P Q R: Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := 
  soit P : Prop,
    soit Q : Prop,
      soit R : Prop,
        supposons h : (P∧Q)∧ R,
          And.intro
            (h.left.left : P)
            (
              And.intro
                (h.left.right: Q)
                (h.right:      R)
            )  

-- Exercice 2.5
example : ∀ (P Q R: Prop), (P → Q) ∧ (Q → R) → (P → R) := 
  λ P Q R : Prop ↦ 
    λ h : (P → Q) ∧ (Q → R) ↦
      λ hP:P ↦ 
        (h.right (h.left  hP : Q) : R)

example : ∀ (P Q R: Prop), (P → Q) ∧ (Q → R) → (P → R) := 
  λ P Q R : Prop ↦ 
    λ h : (P → Q) ∧ (Q → R) ↦
      λ hP:P ↦ 
        have hQ : Q := h.left  hP
        have hR : R := h.right hQ
        hR

example : ∀ (P Q R: Prop), (P → Q) ∧ (Q → R) → (P → R) := 
  soit P : Prop,
    soit Q : Prop,
      soit R : Prop,
        supposons h : (P → Q) ∧ (Q → R),
          supposons hP:P,
            have hQ : Q := h.left  hP
            have hR : R := h.right hQ
            hR

-- Exercice 2.6
-- Cet exercice est le meme que le précédent, sauf que l'assertion
-- (a ∧ b) → c   a été écrite  (a → b → c)   ce qui signifie : (a → ( b → c ))
-- au lie de  "si (a et b) alors c"    on a écrit : "si a alors (si b alors c)"
-- je vous laisse vous convaincre que cela signifie la meme chose (vous pouvez essayer de le prouver)
example : ∀ (P Q R: Prop), (P → Q) → (Q → R) → (P → R) :=
  λ P Q R : Prop ↦ 
    λ hPQ : P → Q ↦
      λ hQR : Q → R ↦
        λ hP:P ↦ 
          (hQR (hPQ  hP : Q) : R)

example : ∀ (P Q R: Prop), (P → Q) → (Q → R) → (P → R) :=
  soit P : Prop,
    soit Q : Prop,
      soit R : Prop,
        supposons hPQ : P → Q ,
          supposons hQR : Q → R ,
            supposons hP:P,
              have hQ : Q := hPQ  hP
              have hR : R := hQR  hQ
              hR







------------------------------------------------------------------
-- Exemple 3
------------------------------------------------------------------

-- Nouvelles notions
--   écrire une définition
--   quantificateur ∃  : introduction


def impair (n:ℤ) : Prop := ∃ k:ℤ, n=2*k+1     
    --  ∃ s'obtient avec \exists
    --  ℤ s'obtient avec \Z

example : impair 7 :=
  Exists.intro 3            -- Pour démontrer ∃k... il faut fournir à Exists.intro une valeur de k (ici 3)
  (                         -- Et donner une preuve que cette valeur convient (calcul ci-dessous)
    calc                    -- Cette opération s'appelle l'introduction de ∃ 
      (7:ℤ)  = 2*3+1  := by norm_num  -- petit point malcommode :
                                      -- pour que Lean considère bien 7 comme élément de ℤ et non de ℕ  on doit préciser (7:ℤ)
  )

-- Exercice 3.1

-- Donnez la définition de pair et prouvez que -10 est pair

def pair (n:ℤ) : Prop := ∃ k:ℤ, n=2*k

example : pair (-10) := 
  Exists.intro (-5)
  (
    calc (-10:ℤ) = 2*(-5) := by norm_num
  )

example : pair (-10) := 
  Exists.intro (-5)
  (
    by norm_num :  (-10:ℤ) = 2*(-5)
  )




------------------------------------------------------------------
-- Exemple 4
------------------------------------------------------------------
-- Nouvelles notions
--   utiliser un lemme ou un théorème de la bibliothèque


-- La bibliothèque Mathlib comporte une énorme collection de théorèmes.
-- Si on veut prouver que x < x+1 pour un réel x, on peut interroger la bibliothèque :
example (x:ℝ) : x < x+1 := by exact?
-- En déplaçant le curseur sur 'exact?', la vue Lean InfoView affiche :
-- Try this: exact lt_add_one x     -- on va oublier le 'exact'
-- lt_add_one est un de ces nombreux théorèmes. On peut afficher son énoncé :
#check lt_add_one
-- On obtient : 
-- lt_add_one.{u_1} {α : Type u_1} [inst✝ : One α] [inst✝¹ : AddZeroClass α] [inst✝² : PartialOrder α]
--  [inst✝³ : ZeroLEOneClass α] [inst✝⁴ : NeZero 1]
--  [inst✝⁵ : CovariantClass α α (fun x x_1 => x + x_1) fun x x_1 => x < x_1] (a : α) : a < a + 1
-- ça a l'air compliqué mais en enlevant ce qui est entre {} et entre [] il reste :
-- lt_add_one (a : α) : a < a + 1
-- Pour l'utiliser:
example (x:ℝ) : x < x+1 := lt_add_one x

example : ∀ x:ℝ, ∃ y:ℝ , y>x := 
  λ x:ℝ ↦ 
      Exists.intro (x+1)
        (
          calc 
            x+1 > x   := lt_add_one x
        )

-- Exercice 4.1
example (x:ℝ) : x-1 < x := by exact?
#check sub_one_lt
example : ∀ u:ℝ, ∃ t:ℝ , t + 1 < u  := 
  λ u:ℝ ↦ 
      Exists.intro (u-2)
        (
          calc 
            (u-2)+1 = u-1  := by ring
            _        < u   := sub_one_lt u
        )


------------------------------------------------------------------
-- Exemple 5
------------------------------------------------------------------
-- Nouvelles notions
--   quantificateur ∃ : élimination



-- Montrons que si n s'écrit 4k+3 alors n est impair

example : ∀n:ℤ,  (∃k:ℤ, n = 4*k+3) → (impair n) :=
  λ n:ℤ ↦                      -- introduction de ∀
    λ h1:(∃k:ℤ, n = 4*k+3) ↦    -- introduction de →
      -- on va utiliser l'hypothèse h1 en instanciant une valeur de k telle que n=4k+3
      -- ceci s'appelle l'élimination de ∃ et se fait à l'aide de Exists.elim
      Exists.elim h1 
      (
        λ (k:ℤ)  (h2:n=4*k+3) ↦ 
          Exists.intro (2*k+1)   -- 2k+1 devrait convenir...
          (
            calc
              n = 4*k+3       := h2
              _ = 2*(2*k+1)+1 := by ring_nf
          )
      )


-- Exercice 5.1
-- Montrez que si n s'écrit 6k alors n est pair
example : ∀n:ℤ,  (∃k:ℤ, n = 6*k) → (pair n) :=
  λ n:ℤ ↦
    λ h1:(∃k:ℤ, n = 6*k) ↦
      Exists.elim h1 
      (
        λ (k:ℤ)  (h2:n=6*k) ↦ 
          Exists.intro (3*k)
          (
            calc
              n = 6*k     := h2
              _ = 2*(3*k) := by ring_nf
          )
      )

example : ∀n:ℤ,  (∃k:ℤ, n = 6*k) → (pair n) :=
  λ  n:ℤ ↦ 
    λ  h1:(∃k:ℤ, n = 6*k) ↦ 
      Exists.elim h1 
      (
        λ  k:ℤ ↦ 
          supposons h2:(n=6*k),
          (
              Exists.intro (3*k)
              (
                calc
                  n = 6*k     := h2
                  _ = 2*(3*k) := by ring_nf
              )
            : pair n
          )
      )



------------------------------------------------------------------
-- Exemple 6
------------------------------------------------------------------
-- Nouvelles notions
--   quantificateur ∀ : élimination

example : ∀ a:ℝ, (∀x:ℝ,a ≤ x^2 -2*x) →  a ≤ -1 := 
  λ a:ℝ ↦                       -- introduction de ∀
    λ h:  (∀x:ℝ,a ≤ x^2 -2*x) ↦ -- introduction de → 
      calc                   -- si h commence par ∀x...
                              -- alors la l'assertion qui suit (a ≤ x^2 -2*x) est vraie pour toute valeur de x,
                              -- en particulier pour x=1.
                              -- Pour obtienir une preuve de ceci, on applique h à la valeur 1, 
                              -- comme si h était une fonction et qu'on calculait h(1)

                              -- ceci s'appelle l'élimination de ∀   :
        a ≤ 1^2-2*1 := h 1   -- on applique h à 1
        _ = -1      := by norm_num


-- Exercice 6.1
example : ∀ a:ℝ, (∀x:ℝ,a * x^2 = 0) →  a = 0 :=  
  λ a:ℝ ↦
    λ h:  (∀x:ℝ,a * x^2 = 0) ↦
      calc
        a = a*1^2   := by ring_nf
        _ = 0       := h 1          -- on applique h à 1

example : ∀ a:ℝ, (∀x:ℝ,a * x^2 = 0) →  a = 0 :=  
  soit a:ℝ,
    supposons h:  (∀x:ℝ,a * x^2 = 0),
      calc
        a = a*1^2   := by ring_nf
        _ = 0       := h 1          -- on applique h à 1


------------------------------------------------------------------
-- Exemple 7
------------------------------------------------------------------
-- Nouvelles notions
--   Démontrer un résultat intermédiaire et le nommer avec  'have'


example : ∀ a b:ℝ , (∀x:ℝ,a * x + b = 0) →  (a = 0 ∧ b = 0) :=  
  λ a b:ℝ ↦ 
    λ h:(∀x:ℝ,a * x + b = 0) ↦
      have hb0 :  b=0 :=                -- have permet d'introduire un résultat intermédiaire
        calc                            -- have nom : énoncé := preuve 
          b = a*0 + b  := by ring_nf    -- ici on nomme hb0 la preuve que b=0, preuve qui est donnée après :=
          _ = 0        := h 0

      have ha0 : a=0 :=                 -- autre résultat intermédiaire introduit par have
        calc
          a = a*1+0 := by ring_nf
          _ = a*1+b := by rw[hb0]
          _ = 0     := h 1

      And.intro ha0 hb0                 -- ici commence la preuve du but : a=0 ∧ b=0


-- Exercice 7.1 
example : ∀ a b:ℝ , (∀x:ℝ,a * x^2 - b*x = 0) →  (a = 0 ∧ b = 0) :=  
  λ a b:ℝ ↦ 
    λ h:(∀x:ℝ,a * x^2 - b*x = 0) ↦
      have h1  : a-b=0 :=
        calc
          a -b = a*1^2 -b*1 := by ring_nf
          _    = 0          := h 1

      have hm1  : a+b =0 :=
        calc
          a+b = a*(-1)^2 -b*(-1) := by ring_nf
          _   = 0                := h (-1)


      have ha0 : a=0 := 
        calc
          a = ((a+b)+(a-b))/2 := by ring_nf
          _ = (0+0)/2         := by rw[h1,hm1]
          _ = 0               := by norm_num

      have hb0 :  b=0 :=
        calc            
          b = ((a+b)-(a-b))/2 := by ring_nf
          _ = (0-0)/2         := by rw[h1,hm1]
          _ = 0               := by norm_num

      And.intro ha0 hb0 









------------------------------------------------------------------
--- Exemple 8
------------------------------------------------------------------
-- Nouvelles notions
--    utilisation de congr_arg
--    utilisation de lemmes de la bibliothèque pour prouver un calcul


-- Dans cet exemple, nous reprenons l'énoncé de l'exemple 1 
-- mais nous allons réaliser la preuve sans utiliser les tactiques, un peu opaques, ring_nf et rw
-- mais en utilisant des théorèmes précis de la bibliothèque


-- Théorèmes que nous allons utiliser :

#check mul_div_cancel    
-- si h est une preuve que  y≠0   ,
-- mul_div_cancel x h            est une preuve que (x*y)/y =  x
-- et (mul_div_cancel x h).symm  est une preuve que x = (x*y)/y
-- #check affiche le type d'un objet ; pour un théorème, il affiche son énoncé


#check mul_comm
-- mul_comm a b   est une preuve que a*b=b*a

#check add_sub_cancel
-- add_sub_cancel a b            est une preuve que a+b-b = a
-- et (add_sub_cancel a b).symm  est une preuve que a = a+b-b


#check congr_arg 
-- congr_arg permet  de faire ce que fait la tactique 'rw' en étant précis sur la partie de l'expression que l'on veut remplacer
-- si f est une fonction  et que h est une preuve de a=b
-- congr_arg f h  est une preuve que  f a = f b   (ie: f (a) = f (b))
-- exemple:  congr_arg (fun z ↦ (2* z-4)/3 ) h    est une preuve de  (2* a-4)/3=(2* b-4)/3


-- recherche de théorèmes:

example (a b:ℝ) : a+b-a = b := by exact?                          -- (i)    -- répond : exact add_sub_cancel' a b
#check add_sub_cancel'                                            -- (ii)
example : ∀ (a b:ℝ), a+b-a = b := λ a b:ℝ ↦  add_sub_cancel' a b  -- (iii)

-- quand on pense qu'un  théorème  devrait etre dans la bibliothèque, on peut
-- écrire son énoncé, puis 'by exact?' en guise de preuve
-- Lean fait une proposition. 
-- Si la réponse commence par exact, on enlève le exact et on récupère le nom du théorème qu'on peut vérifier avec #check

-- finalement voici la preuve:

example : ∀ x:ℝ, 3*x+4=2 → x=-2/3
  :=
  λ x:ℝ ↦ 
    λ h:3*x+4=2 ↦ 
      calc
        x = (x*3)/3      := (mul_div_cancel x (by norm_num : (3:ℝ) ≠ 0)).symm      -- ≠ s'obtient avec \ne
        _ = (3*x)/3      := congr_arg (fun z ↦ z/3)     (mul_comm x 3)  
        _ = (3*x+4-4)/3  := congr_arg (fun z ↦ z/3)     (add_sub_cancel (3*x) 4).symm
        _ = (2  -4)/3    := congr_arg (fun z ↦ (z-4)/3) h
        _ = -2/3         := by norm_num  -- on s'autorise quand meme norm_num





-- Exercice 8.1 à faire sans les tactiques ring_nf ni rw
example : ∀ x:ℝ, 2*x+11=6 → x = -5/2 := 
  λ x:ℝ ↦ 
    λ h:2*x+11=6 ↦ 
      calc
        x = (x*2)/2       := (mul_div_cancel x (by norm_num : (2:ℝ) ≠ 0)).symm
        _ = (2*x)/2       := congr_arg (fun z ↦ z/2)      (mul_comm x 2)
        _ = (2*x+11-11)/2 := congr_arg (fun z ↦ z/2)      (add_sub_cancel (2*x) 11).symm
        _ = (6  -11)/2    := congr_arg (fun z ↦ (z-11)/2) h
        _ = -5/2          := by norm_num


-- Exercice 8.2 à faire sans les tactiques ring_nf ni rw

-- Lemmes utilisés:
#check one_mul
#check sub_mul
#check add_zero
#check add_sub
#check sub_add_eq_add_sub
#check sub_add_eq_sub_sub
#check sub_eq_add_neg
#check sub_self

example  : ∀ c:ℚ,  4*c+1 =3*c-2 →  c = -3 :=
  λ  c:ℚ ↦ 
    λ  h:  4*c+1 =3*c-2 ↦ 
      calc
        c = 1*c                    := (one_mul c).symm
        _ = (4-3)*c                := congr_arg (fun z ↦ z*c) (by norm_num: ((1:ℚ)=4-3))
        _ = 4*c-3*c                := sub_mul 4 3 c
        _ = 4*c-3*c+0              := (add_zero _).symm
        _ = 4*c-3*c+(1-((-2)+3))   := congr_arg (fun z ↦ 4*c-3*c+z) (by norm_num: (0:ℚ) = 1-((-2)+3))
        _ = 4*c-3*c+1-((-2)+3)     := add_sub (4*c-3*c) 1 ((-2)+3)
        _ = 4*c+1-3*c-((-2)+3)     := congr_arg (fun z ↦ z-((-2)+3) ) (sub_add_eq_add_sub (4 * c) (3 * c) 1)
        _ = 4*c+1-3*c-(-2)-3       := sub_add_eq_sub_sub (4*c+1-3*c) (-2) 3
        _ = 4*c+1-(3*c+(-2))-3     := congr_arg (fun z ↦ z-3)   (sub_add_eq_sub_sub (4*c+1) (3*c) (-2)).symm
        _ = 4*c+1-(3*c-2)-3        := congr_arg (fun z ↦ 4*c+1-z-3)  (sub_eq_add_neg (3*c) 2).symm
        
        _ =  (3*c-2)-(3*c-2)  - 3  := congr_arg (fun z ↦ z - (3*c-2) -3)  h

        _ =  0  - 3                := congr_arg (fun z ↦ z -  3)  (sub_self (3*c-2))
        _ = -3                     := by norm_num


