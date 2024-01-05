import Mathlib.Data.Set.Basic
import Esisar.CM43

--open chap3

namespace chap7


  namespace funTypes
      section s1

        variable  {E:Type}  {F:Type}  (f : E → F )

        def im         : Set F  := {y:F| ∃x:E, y = f x}
        def injective  : Prop   := ∀ u v : E, (f u = f v )  → u = v
        def surjective : Prop   := ∀ y : F, ∃ x: E, f x = y

      end s1

      section s2
        open chap3
        variable  {E:Type}  {F:Type}  (f : E → F )
        variable [Ordonne E] [Ordonne F]

        def croissante  : Prop :=  ∀ u v :E , u ≤ v → f u ≤ f v
      end s2

  end funTypes

  namespace funCond
      section s1
        variable  {E:Type} {A:Set E}  {F:Type}  {B : Set F} (f : (x:E) → (x ∈ A )  → F )

        def im        : Set F := {y:F| ∃x:E, ∃ (hxA: x∈A),  y = f x hxA}
        def injective : Prop  := ∀ u v :E, (huA : u∈A ) → (hvA : v ∈A ) →  (f u huA = f v hvA )  → u = v
        def surjective: Prop  := ∀ y ∈ B,  ∃ x: E, ∃ (hxA : x∈ A), f x hxA = y

      end s1


end funCond

  namespace funSubTypes
      section s1

        variable {E:Type} {A:Set E}  {F:Type}  {B : Set F} (f : A  → B )

        def ofTotalFun (φ : E → F) : (@Set.univ E) →  (@Set.univ F) :=
          fun x ↦ ⟨φ ↑x , trivial⟩

        def ofPartialDomainFun (α :A → F) : A →  (@Set.univ F) :=
          fun x ↦ ⟨α x , trivial⟩

        def ofPartialCodomainFun  (β:E → B) : (@Set.univ E) →  B :=
          fun x ↦ β ↑x

        def cut (g:E → F ) (x:E) [ixA:Decidable (x∈ A)] [iyB:Decidable (g x ∈ B)] : Option B :=
           if (x ∈ A) then
             if hyB: (g x ∈ B)  then
              some ⟨g x ,hyB ⟩
            else
              none
           else
            none

        def cut' (g:E → F ) (x:E) [ixA:Decidable (x∈ A)] [iyB:Decidable (g x ∈ B)] : Option F :=
          Option.map (Subtype.val) ( @cut _ _ _ _ g x ixA iyB )

        theorem cut'_in_B (g:E → F )  [iA: (x:E) → Decidable (x∈ A)] [iB: (y:F) → Decidable (y ∈ B)] :
           ∀ x:E, (@cut' _ A _ B g x _ _ = none) ∨ ∃ y∈B,  (@cut' _ A _ B g x _ _) = (some y)
           :=
           λ x:E ↦
            if hxA:(x ∈ A) then
              if hyB: (g x ∈ B)  then
                have r : cut' g x = Option.map (Subtype.val) (cut g x) := rfl
                have : cut g x = some ⟨g x ,hyB ⟩ :=
                  calc
                    cut g x = _                := if_pos hxA
                    _       = some ⟨g x ,hyB ⟩ := dif_pos hyB
--                Or.inr (Exists.intro (g x) ⟨ hyB, by unfold cut' ; rw [this] ; rfl  ⟩ )  -- doesn't need r

                have s : cut' g x = Option.map (Subtype.val) (some ⟨g x ,hyB ⟩) := this ▸ r
                Or.inr (Exists.intro (g x) ⟨ hyB, s  ⟩ )

              else
--                Or.inl (by unfold cut' ; unfold cut ; rw [if_pos hxA] ; rw [if_neg hyB] ; rfl)
--                Or.inl (by unfold cut' ; unfold cut ; rw [if_pos hxA] ; aesop)
--                Or.inl (by unfold cut' ; unfold cut ; aesop)

/-
                have :  (if hyB': g x ∈ B then some (Subtype.mk (g x) hyB')   else none) = none :=
                  --if_neg hyB
--                  @if_neg _ _ hyB _ _ _
--                    @if_neg (g x ∈ B) (iB (g x)) hyB (Option (Subtype B)) _ _
--                    @dif_neg (g x ∈ B) (iB (g x)) hyB (Option (Subtype B)) _ _
                    dif_neg hyB


                have : @cut _ A _ B g x _ _ = none :=  --have : cut g x = none :=
                  calc
                    @cut _ A _ B g x _ _ = _    := if_pos hxA          -- cut g x = _    := if_pos hxA
                    _                    = none := this -- dif_neg hyB
                Or.inl ( congr_arg  (Option.map (Subtype.val)) this  )
-/

/-
                have : cut g x = none :=
                  calc
                    cut g x = _    := if_pos hxA
                    _       = none := dif_neg hyB
                Or.inl ( congr_arg  (Option.map (Subtype.val)) this  )
-/
                Or.inl (by unfold cut' ; unfold cut ; rw [if_pos hxA] ; rw [dif_neg hyB] ; rfl)

            else
              Or.inl ( congr_arg  (Option.map (Subtype.val)) (if_neg hxA)  )


        #print cut'_in_B

        def cutS (g:E → F ) (x:A) [iyB:Decidable (g x ∈ B)] : Option B :=
          @cut _ _ _  _ g  x.val (isTrue x.property) iyB

        def cutS' (g:E → F ) (x:A) [iyB:Decidable (g x ∈ B)] : Option F :=
          Option.map (Subtype.val) ( @cutS _ _ _ _ g x iyB )

        def ofFun (g:E→F) (h : ∀ x:E, x∈ A → g x ∈ B ) : A → B  :=
          fun x ↦ ⟨g x , h x.val x.property⟩


        def injective : Prop := funTypes.injective f    -- ∀ u v : ↑A , (f u = f v )  → u = v
        def surjective: Prop := funTypes.surjective f   --  ∀ y : ↑B, ∃ x: ↑A, f x = y

        def im : Set F := {y:F |  ∃ hyB:y∈ B ,  (Subtype.mk y hyB) ∈ (funTypes.im f) }
                         -- {y:F |  ∃ hyB :y∈ B ,  ∃x:↑A, ⟨y, hyB⟩  = f x }

        def restriction {A':Set E} (h: A' ⊆ A ) : A' → B := fun x ↦ f ⟨ x.val,  h x.property⟩

        lemma mem_im {f : A  → B }  {x:A} : ↑(f x) ∈ im f := ⟨ (f x).property, ⟨x ,rfl ⟩ ⟩

        def corestriction {B':Set F} (h: B' ⊆ B ) (h_im : im f ⊆ B') : A → B' := fun x ↦ ⟨ (f x).val, h_im mem_im ⟩

        lemma Subtype.trans {A':Set E} {x y : E} {hxA : x ∈A } {hyA : y ∈A }  {hxA':x∈ A' } {hyA':y∈ A' }
          (h: Subtype.mk x hxA = Subtype.mk y hyA )   :  Subtype.mk x hxA' = Subtype.mk y hyA'  :=
          Subtype.eq (congrArg Subtype.val  h : x=y)

        lemma injective_restr {A':Set E}  {h: A' ⊆ A} : injective f → injective (restriction f h) :=
          λ hfi  _ _ hreq ↦  Subtype.trans (hfi _ _ hreq)

        def coprolongement {B':Set F} (h: B ⊆ B' )  : A → B' :=
          λ x ↦ ⟨ (f x).val   , h (f x).property  ⟩

        def eval? (x:E) [ixA: Decidable (x∈A)] : Option B :=
          match (ixA) with
          | isTrue hxA => some (f ⟨ x, hxA⟩ )
          | _          => none


        def evalD (default:B) (x:E) [Decidable (x∈A)] : B :=
          match (eval? f x) with
          | some y =>  y
          | none   => default

        def evalI [iB:Inhabited B] (x:E) [Decidable (x∈A)] : B :=
           (evalD f iB.default x)

        noncomputable def evalN [nB:Nonempty B] (x:E) [Decidable (x∈A)] : B :=
           (evalD f (Classical.choice nB) x)


/-
        def eval'? (x:E) [ixA: Decidable (x∈A)] : Option F :=
          match (ixA) with
          | isTrue hxA => some (f ⟨ x, hxA⟩ )
          | _          => none
-/
/-
        def eval'? (x:E) [ixA: Decidable (x∈A)] : Option F :=
          match (eval? f x) with
          | some y => y.val
          | _      => none
-/
        def eval'? (x:E) [Decidable (x∈A)] : Option F :=
          Option.map (Subtype.val) ( eval? f x )


        def eval'D (default:F) (x:E) [Decidable (x∈A)] : F :=
          match (eval'? f x) with
          | some y =>  y
          | none   => default

        def eval'I [iF:Inhabited F] (x:E) [Decidable (x∈A)] : F :=
           (eval'D f iF.default x)

        noncomputable def eval'N [nF:Nonempty F] (x:E) [Decidable (x∈A)] : F :=
           (eval'D f (Classical.choice nF) x)

      end s1


      lemma sq_increasing' {a b:ℝ} (ha: a≥ 0) {x:ℝ} (hx : x ∈ [a;b] ) : x^2 ∈ [a^2;b^2] :=
        have hx0 : x ≥ 0 := le_trans ha hx.left
        ⟨chap3.sq_increasing _ _ ha hx.left , chap3.sq_increasing _ _ hx0           hx.right ⟩

      def g : [1;2] → [1;4]  := fun ⟨ x,hx⟩   ↦ ⟨ x^2, ((
        (by norm_num : 1^2 = (1:ℝ )) ▸ (by norm_num : 2^2 = (4:ℝ )) ▸ (sq_increasing' (by norm_num) hx)
      ) : (x^2 ∈ [1;4]))⟩

      def QPlus : Set ℚ := λ x ↦ x ≥ 0

      def gQ : QPlus → QPlus  := fun ⟨ x,hx⟩   ↦ ⟨ x^2, sq_nonneg x⟩

      #eval gQ ⟨ 2, (by norm_num : (2:ℚ ) ≥0  ) ⟩
      #eval gQ ⟨ 2, ((by decide ) :( (2:ℚ ) ≥0 ))⟩

      section s2

        variable {E:Type} [i:chap3.Ordonne E]  {A:Set E}  {F:Type}  [chap3.Ordonne F] {B : Set F} (f : A → B )

        #print Subtype.le

        instance Subtype.instOrdonne    : chap3.Ordonne A where
          le       := (Subtype.le).le
          le_ordre := ⟨ λ x ↦ i.le_ordre.1 ↑x , λ x y h1 h2 ↦ Subtype.eq (i.le_ordre.2.1 x y h1 h2), λ x y z ↦  i.le_ordre.2.2 x y z⟩

        #check Subtype.instOrdonne

--        def croissante : Prop :=  ∀ u v : A , u ≤ v → f u ≤ f v
        def croissante : Prop :=  funTypes.croissante f

      end s2

      noncomputable def g2 : [0;+∞) → [0;+∞)   := fun ⟨ x,_⟩   ↦ ⟨ x^2, sq_nonneg x⟩

      example : croissante g2 :=
        λ u v h ↦
          chap3.sq_increasing u v u.property h


      namespace ex_7_1_1_2

        instance instCoeTypeSetUniv.{u} (E:Type u) : CoeDep (Type u) E (Set E) where
          coe  := @Set.univ E

        --variable {E:Type} {B: Set E}
        axiom E : Type
        axiom B : Set E

        example (X: Set E) : X ⊆ Set.univ := by exact Set.subset_univ X
        example (X: Set E) : X ∩  Set.univ = X:= by exact Set.inter_univ X
        example (X: Set E) :   Set.univ ∩ X = X:= by exact Set.univ_inter X
        example (X: Set E) :  X ⊆  X:= by exact Eq.subset rfl
        example (X: Set E) : X ∩  ∅  = ∅:= by exact Set.inter_empty X
        example (X: Set E) : ∅ ⊆ X := by exact Set.empty_subset X
        example (X: Set E) : X ∩ X  = X:= by exact Set.inter_self X
        example (X: Set E) : X ∩ Xᶜ   = ∅ := by exact Set.inter_compl_self X
        example (X: Set E) : Xᶜ ∩ X   = ∅ := by exact Set.compl_inter_self X

        def h0 : Set E → Set E := fun X  ↦ X ∩ B

        def h1 : 𝒫 (@Set.univ E) → 𝒫 (@Set.univ E) := fun X ↦ ⟨ X ∩ B  , Set.subset_univ _ ⟩

        example : h0 (@Set.univ E) = B := Set.univ_inter B
        example : h1 ⟨ @Set.univ E, Eq.subset rfl⟩  = B := Set.univ_inter B

        example : h0 ∅ = ∅ := Set.empty_inter _
        example : h1 ⟨ ∅, Set.subset_univ _⟩  = (∅: Set E) := Set.empty_inter B

        example : h0 B = B := Set.inter_self _
        example : h1 ⟨ B, Set.subset_univ _⟩  = B := Set.inter_self B

        example : h0 (Bᶜ)  = ∅  := Set.compl_inter_self _
        example : h1 ⟨Bᶜ, Set.subset_univ _⟩  = (∅:Set E) := Set.compl_inter_self _

      end ex_7_1_1_2

  end funSubTypes

  namespace appSets

    abbrev DecidableSubset {α : Type} (a : Set α) :=
      (x : α) → Decidable (x ∈ a)

    instance instCoeTypeSetUniv.{u} (E:Type u) : CoeDep (Type u) E (Set E) where
      coe  := @Set.univ E


    structure Application  {E:Type} (A:Set E) [DecidableSubset A] {F:Type}  [i:Inhabited F]  (B : Set F) : Type where
      func : (x:E) → (x∈ A) → F
      coh  : ∀ x:E, (hx: x∈ A) → func x hx ∈ B
/-
      eval? : E → Option F :=
            fun (x:E) ↦  dite (x ∈ A)
              (fun h => Option.some (func x h)  )
              (fun _ => Option.none)
      evalD (default:F) :  E → F :=
            fun (x:E) ↦ match (eval? x) with
                          |  Option.some z =>  z
                          |  _             =>  default
      eval! :  E → F :=
            evalD i.default
-/

    section s1

      variable  {E:Type} {A:Set E} [DecidableSubset A] {F:Type}  [i:Inhabited F]  {B : Set F}
      variable  (f : Application A B)

      namespace Application

      def eval? :
                              E → Option F :=
        fun (x:E) ↦  dite (x ∈ A)
          (fun h => Option.some (f.func x h)  )
          (fun _ => Option.none)

      def evalD  (default:F) :  E → F :=
              fun (x:E) ↦ match (f.eval? x) with
                            |  Option.some z =>  z
                            |  _             =>  default

      def eval!  : E → F :=  f.evalD i.default

      @[simp]
      def evalOfPos  (x:E) (hxA : x ∈ A ) : f.eval! x = f.func x hxA :=

          have h0 : f.eval? x  =  some (f.func x hxA) := dif_pos hxA
          have h1 :  _ :=
          (
            calc
              f.evalD i.default x = ( match (some (f.func x hxA)) with
                          |  Option.some z =>  z
                          |  _             =>  i.default)        := h0 ▸rfl
              _                   =  f.func x hxA                := rfl
          )

          calc
            f.eval! x  = f.evalD i.default x  := rfl
            _          = f.func x hxA         := h1


        instance instApplicationCoeFun  : CoeFun (Application A B) (λ _ ↦ (E → F )) where
          coe a := a.eval!

      #print eval?

      def im : Set F := {y ∈ B  | ∃x ∈ A , y=f x}



      def ofTotalFun
  --            (φ:E → F) : @Application E (@Set.univ E) _ F _  (@Set.univ F) := {
  --            (φ:E → F) : @Application  E E _  F _ F := {
  --            (φ:E → F) : Application (↑E) (↑F) := {
              (φ:E → F) : Application  (@Set.univ E) (@Set.univ F) := {
                func := fun  x _ ↦ φ x
                coh  := λ _ _    ↦ trivial
              }


      def ofPartialFun  (ψ:A → B) : Application A B :=
              {
                func := fun  x hxA ↦ (ψ ⟨x,hxA⟩).val
                coh  := λ x hxA    ↦ (ψ ⟨x,hxA⟩).property
              }

      def ofPartialDomainFun (α :A → F) : Application A  (@Set.univ F) :=
              {
                func := fun  x hxA ↦ α ⟨x,hxA⟩
                coh  := λ _ _    ↦ trivial
              }

      def ofPartialCodomainFun  (β:E → B) : Application (@Set.univ E) B :=
              {
                func := fun  x _ ↦ (β x).val
                coh  := λ x _    ↦ (β x).property
              }


      @[simp]
      lemma func_is_f (φ :E → F):  (Application.ofTotalFun φ).eval! = φ   := rfl

      lemma eq :  ∀ {f g : Application A B} , f.func = g.func  → f = g
  --      | ⟨ffunc,fcoh⟩ , ⟨.(ffunc),gcoh⟩, (Eq.refl ffunc) => rfl
        | ⟨_,_⟩ , ⟨_,_⟩, (Eq.refl _) => rfl

      lemma eq_of_ext  (f g : Application A B):  (∀ x∈ A, f x = g x) → f = g  :=
          λ h ↦
            have hf : f.func = g.func  := funext₂ (λ x hxA ↦
              calc
                f.func x hxA = f.eval! x    := (f.evalOfPos x hxA).symm
                _            = g.eval! x    := h x hxA
                _            = g.func x hxA := g.evalOfPos x hxA
            )

  --          have hc : f.coh = g.coh := (Application.eq hf) ▸ rfl

            Application.eq hf



      def id  [Inhabited E] : Application A A :=
        {
          func := λ x _   ↦ x
          coh  := λ _ hxA ↦ hxA
        }

      #print Set.Subset

      def restriction  (A':Set E) [DecidableSubset A'] (h: A' ⊆ A) : Application A' B :=
            {
              func := λ x hxA' ↦ f.func x (h  hxA')
              coh  := λ x _    ↦ f.coh x _
            }

      lemma restriction_eq  (A':Set E) [DecidableSubset A'] (h: A' ⊆ A) :
              ∀ x∈A',  (restriction f A' h) x = f x
              :=
              let r:= restriction f A' h
              λ x hxA' ↦
                have hxA : x ∈ A := h hxA'
                calc
                  r x = f.func x _ := evalOfPos _ x hxA'
                  _   = f x        := (evalOfPos _ x hxA).symm


      def corestriction (B':Set F)  (h:  B' ⊆ B)  (h_im : im f ⊆ B' ) : Application A B' :=
            {
              func := f.func
              coh  := λ x hxA  ↦  h_im (And.intro (f.coh x _) (
                Exists.intro x (
                  And.intro
                    hxA
                    (evalOfPos _ x hxA).symm
                )
              ))
            }

      def coprolongement (B':Set F)  (h: B ⊆ B') : Application A B' :=
            {
              func := f.func
              coh  := λ x _  ↦  h (f.coh x _)
            }

      def injective : Prop  := ∀ u∈A, ∀ v∈A, (f u = f v )  → u = v
      def surjective : Prop := ∀ y∈B, ∃ x∈ A, f x = y


      lemma injective_restr (A':Set E) [DecidableSubset A'] (h: A' ⊆ A) :
              injective f → injective ( restriction f A' h)
              :=
              λ hi ↦
                λ u huA' v hvA' hreq ↦
                  let r:= restriction f A' h
                  have hfeq : f u = f v :=
                    calc
                      f u = r u  := (restriction_eq _ _ _ u huA').symm
                      _   = r v  := hreq
                      _   = f v  := restriction_eq _ _ _ v hvA'

                  hi _ (h huA') _ (h hvA')  hfeq
      end Application

    end s1



    #check chap3.sq_increasing

    section testDecidable
      #synth DecidableSubset [1;2]

      variable (x:ℝ)
      #synth Decidable (x ≥ 1 ∧ x ≤ 2 )
      #synth Decidable (x ≥ 1 )
    end testDecidable

    noncomputable def g : Application [1;2] [1;4] :=
    {
      func := fun x hx ↦ x^2
      coh  := λ x   hx ↦
         have hx0 : x ≥ 0 := le_trans (by norm_num) hx.left
        ⟨ trans (chap3.sq_increasing _ _ (by norm_num) hx.left)  (by norm_num),
          trans (chap3.sq_increasing _ _ hx0           hx.right) (by norm_num : 2^2 = (4:ℝ))⟩
    }

    noncomputable def g2 : Application  [0;+∞)   [0;+∞)  :=
    {
      func := fun x _ ↦ x^2
      coh  := λ x   _ ↦ sq_nonneg x
    }

    section s2

      open chap3

      variable  {E:Type} {A:Set E} [DecidableSubset A] {F:Type}  [i:Inhabited F]  {B : Set F}
      variable [o:Ordonne E] [Ordonne F]

      instance Subtype.instOrdonne   : Ordonne A where
        le       := (Subtype.le).le
        le_ordre := ⟨ λ x ↦ o.le_ordre.1 ↑x , λ x y h1 h2 ↦ Subtype.eq (o.le_ordre.2.1 x y h1 h2), λ x y z ↦  o.le_ordre.2.2 x y z⟩

      #check Subtype.instOrdonne

      def croissante (f : Application A B ) : Prop  := ∀ u∈A, ∀ v∈A , u ≤ v → f u ≤ f v

      example : croissante g2 :=
        λ u hu v  hv h ↦
          calc
            g2 u = u^2      := g2.evalOfPos  _ hu
            _        ≤ v^2  := sq_increasing u v hu h
            _        = g2 v := (g2.evalOfPos _ hv).symm

    end s2


  end appSets

end chap7
