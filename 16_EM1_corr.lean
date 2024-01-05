import Esisar.Exam

/-! # Epreuve Machine 1  -/

namespace exam


-- Exercice 1

/- 2 points -/
theorem em1s0ex01 : ∃ k:ℕ, 17 = 3*k+2        := 
  Exists.intro 5 
  (
    calc 17=3*5+2 := by norm_num
  )

/- 2 points -/
theorem em1s1ex01 : ∃ k:ℕ, 14 = 5*k-1        := 
  Exists.intro 3 
  (
    calc 14=5*3-1 := by norm_num
  )

/- 2 points -/
theorem em1s2ex01 : ∃ k:ℕ, 26 = 7*k+5        := 
  Exists.intro 3 
  (
    calc 26=7*3+5 := by norm_num
  )



-- Exercice 2

-- Question 2a

/- 2 points -/
theorem em1s0ex02a : ∀ x:ℝ, 3*x+5 = 2  → x=-1   := 
  λ x:ℝ ↦
    λ h: 3*x+5 = 2 ↦
      calc
        x = (3*x+5-5)/3   := by ring_nf
        _ = (2 -5)/3      := by rw[h]
        _ = -1            := by norm_num

/- 2 points -/
theorem em1s1ex02a : ∀ x:ℝ, 2*x+5 = 9  → x= 2   := 
  λ x:ℝ ↦
    λ h: 2*x+5 = 9 ↦
      calc
        x = (2*x+5-5)/2   := by ring_nf
        _ = (9 -5)/2      := by rw[h]
        _ = 2             := by norm_num

/- 2 points -/
theorem em1s2ex02a : ∀ x:ℝ, 7*x-8 =-1  → x= 1   := 
  λ x:ℝ ↦
    λ h: 7*x-8 =-1 ↦
      calc
        x = (7*x-8+8)/7   := by ring_nf
        _ = (-1+8)/7      := by rw[h]
        _ = 1             := by norm_num



-- Question 2b

/- 2 points -/
theorem em1s0ex02b : ∀ x:ℝ, x=-1 → 3*x+5 = 2    := 
  λ x:ℝ ↦
    λ h: x=-1 ↦
      calc
        3*x+5 = 3*(-1)+5  := by rw[h]
        _     = 2         := by norm_num


/- 2 points -/
theorem em1s1ex02b : ∀ x:ℝ, x= 2 → 2*x+5 = 9    := 
  λ x:ℝ ↦
    λ h: x=2 ↦
      calc
        2*x+5 = 2*2+5  := by rw[h]
        _     = 9      := by norm_num

/- 2 points -/
theorem em1s2ex02b : ∀ x:ℝ, x= 1 → 7*x-8 =-1    := 
  λ x:ℝ ↦
    λ h: x=1 ↦
      calc
        7*x-8 = 7*1-8  := by rw[h]
        _     = -1     := by norm_num



-- Question 2c

/- 1 point -/
theorem em1s0ex02c : ∀ x:ℝ, 3*x+5 = 2  ↔ x=-1   := 
  λ x:ℝ ↦
     Iff.intro
       (em1s0ex02a x)
       (em1s0ex02b x)

/- 1 point -/
theorem em1s1ex02c : ∀ x:ℝ, 2*x+5 = 9  ↔ x= 2   := 
  λ x:ℝ ↦
     Iff.intro
       (em1s1ex02a x)
       (em1s1ex02b x)

/- 1 point -/
theorem em1s2ex02c : ∀ x:ℝ, 7*x-8 =-1  ↔ x= 1   := 
  λ x:ℝ ↦
     Iff.intro
       (em1s2ex02a x)
       (em1s2ex02b x)



-- Exercice 3

def impair (x:ℕ) : Prop := ∃ k:ℕ, x = 2*k+1 
def pair   (x:ℕ) : Prop := ∃ k:ℕ, x = 2*k

/- 2 points -/
theorem em1s0ex03 : ∀x:ℕ,∀y:ℕ, impair x ∧ impair y → pair (x+y)     := 
  λ x :ℕ ↦  
    λ y :ℕ ↦  
      λ h :  impair x ∧ impair y  ↦ 
        Exists.elim h.left 
        (
          λ (m:ℕ ) (hx : x= 2*m+1) ↦  
          Exists.elim h.right
          (
            λ (n: ℕ ) (hy : y= 2*n+1) ↦ 
              Exists.intro (m+n+1)
              (
                calc
                  x+y = (2*m+1)+(2*n+1) := by rw[hx,hy]
                  _   = 2*(m+n+1)       := by ring_nf 
              )
                 
          )
        )

/- 2 points -/
theorem em1s1ex03 : ∀x:ℕ,∀y:ℕ, pair   x ∧ impair y → impair (x+y)     := 
  λ x :ℕ ↦  
    λ y :ℕ ↦  
      λ h :  pair x ∧ impair y  ↦ 
        Exists.elim h.left 
        (
          λ (m:ℕ ) (hx : x= 2*m) ↦  
          Exists.elim h.right
          (
            λ (n: ℕ ) (hy : y= 2*n+1) ↦ 
              Exists.intro (m+n)
              (
                calc
                  x+y = (2*m)+(2*n+1) := by rw[hx,hy]
                  _   = 2*(m+n)+1     := by ring_nf 
              )
                 
          )
        )


/- 2 points -/
theorem em1s2ex03 : ∀x:ℕ,∀y:ℕ, pair   x ∧ pair   y → pair (x+y)     := 
  λ x :ℕ ↦  
    λ y :ℕ ↦  
      λ h :  pair x ∧ pair y  ↦ 
        Exists.elim h.left 
        (
          λ (m:ℕ ) (hx : x= 2*m) ↦  
          Exists.elim h.right
          (
            λ (n: ℕ ) (hy : y= 2*n) ↦ 
              Exists.intro (m+n)
              (
                calc
                  x+y = (2*m)+(2*n) := by rw[hx,hy]
                  _   = 2*(m+n)     := by ring_nf 
              )
                 
          )
        )


-- Exercice 4

/- 2 points -/
theorem em1s0ex04 : ∀ P Q : Prop, P ∨ Q → Q ∨ P  := 
  λ P Q : Prop ↦ 
    λ h: P ∨ Q ↦
      Or.elim  h
      (
        λ hP:P ↦ 
         Or.inr (hP:P) 
      )
      (
        λ hQ:Q ↦ 
         Or.inl (hQ:Q) 
      )
      

/- 2 points -/
theorem em1s1ex04 : ∀ P Q : Prop, P ∧ Q → Q ∧ P  := 
  λ P Q : Prop ↦ 
    λ h: P ∧  Q ↦
      And.intro (h.right:Q) (h.left:P)


/- 2 points -/
theorem em1s2ex04 : ∀ P Q : Prop, P ∧ Q → Q ∨ P  := 
  λ P Q : Prop ↦ 
    λ h: P ∧  Q ↦
      Or.inl (h.right:Q) 



-- Exercice 5

/- 2 points -/
theorem em1s0ex05 : ∀ (P Q R : Prop), (P ↔  R) → (P ∨ Q ↔  Q ∨ R )  := 
  λ P Q R : Prop ↦ 
    λ hPeqvR : (P ↔ R) ↦ 
      Iff.intro
      (
        λ hPouQ : P ∨ Q ↦
          Or.elim (hPouQ)
          (
            λ hP:P ↦ 
              have hR : R :=  hPeqvR.mp hP
              (Or.inr (hR : R) : Q ∨ R)
          )
          (
            λ hQ:Q ↦  
              (Or.inl (hQ : Q) : Q ∨ R)
          )
      )
      (
        λ hQouR : Q ∨ R ↦
          Or.elim (hQouR)
          (
            λ hQ:Q ↦  
              (Or.inr (hQ : Q) : P ∨ Q)
          )
          (
            λ hR:R ↦ 
              have hP : P :=  hPeqvR.mpr hR
              (Or.inl (hP : P) : P ∨ Q)
          )
      )

/- 2 points -/
theorem em1s1ex05 : ∀ P Q :Prop,  (P → Q) → (P ↔ (P ∧ Q)) :=  
  λ P Q : Prop ↦ 
    λ hPimpQ : P → Q ↦  
      Iff.intro
      (
        λ hP : P ↦
           have hQ :Q := hPimpQ hP   
          (And.intro (hP:P) (hQ:Q) : P ∧ Q)
      )
      (
        λ hPetQ : P ∧ Q ↦   
          (hPetQ.left:P)
      )

/- 2 points -/
theorem em1s2ex05 : ∀ (P Q : Prop), (P → Q) → (P ∨ Q ↔  Q )  := 
  λ P Q : Prop ↦ 
    λ hPimpQ : P → Q ↦  
      Iff.intro
      (
        λ hPouQ : P ∨ Q ↦   
          Or.elim (hPouQ)
          (
            λ hP:P ↦ 
              have hQ :Q := hPimpQ hP
              hQ
          )
          (
            λ hQ:Q ↦ 
              hQ
          )
      )
      (
        λ hQ : Q ↦   
          (Or.inr hQ : P ∨ Q)
      )





-- Exercice 6

/- 2 points -/
theorem em1s0ex06 : ∀ a b:ℝ , (∀x:ℝ, (a+1) * b *  x + a = 0) ↔   (a = 0 ∧ b = 0) :=
    λ a b : ℝ ↦
    Iff.intro
    (
      λ hl: (∀x:ℝ, (a+1) * b *  x + a = 0) ↦ 
        have ha0 : a=0 :=
         calc
           a = (a+1)*b*0 + a  := by ring_nf
           _ = 0              := hl 0
          
          have hb0 : b=0 :=
            calc
              b=  (0+1)*b*1+0 := by ring_nf
              _=  (a+1)*b*1+a := by rw[ha0]
              _ = 0           := hl 1

        (And.intro ha0 hb0 : a=0 ∧ b=0)
    )
    (
      λ hr : (a = 0 ∧ b = 0) ↦ 
        λ x:ℝ ↦
         calc
           (a+1) * b *  x + a = (0+1) * 0 *  x + 0  := by rw[hr.left,hr.right]
           _                  = 0                   := by ring_nf
    )  


/- 2 points -/
theorem em1s1ex06 : ∀ a b:ℝ , (∀x:ℝ,a * x - b = 0) ↔  (a = 0 ∧ b = 0) :=  
    λ a b : ℝ ↦
    Iff.intro
    (
      λ hl: (∀x:ℝ,a * x - b = 0) ↦ 
        have hb0 : b=0 :=
          calc
            b=  -(a*0-b) := by ring_nf
            _=  -0           := by rw[hl 0]
            _ = 0            := by norm_num

        have ha0 : a=0 :=
         calc
           a = a*1-b+b := by ring_nf
           _ = 0+0     := by rw[hl 1,hb0]
           _ = 0       := by norm_num
          
        (And.intro ha0 hb0 : a=0 ∧ b=0)
    )
    (
      λ hr : (a = 0 ∧ b = 0) ↦ 
        λ x:ℝ ↦
         calc
           a * x - b = 0 * x - 0  := by rw[hr.left,hr.right]
           _         = 0          := by ring_nf
    )  

/- 2 points -/
theorem em1s2ex06 : ∀ a b:ℝ , (∀x:ℝ,a  + b * x^2 = 0) ↔  (a = 0 ∧ b = 0) :=  
    λ a b : ℝ ↦
    Iff.intro
    (
      λ hl: (∀x:ℝ,a  + b * x^2 = 0) ↦ 
        have ha0 : a=0 :=
         calc
           a = a+b*0^2  := by ring_nf
           _ = 0        := hl 0
          
          have hb0 : b=0 :=
            calc
              b=  a+b*1^2-a := by ring_nf
              _=  0-0       := by rw[hl 1, ha0]
              _ = 0         := by norm_num
          
        (And.intro ha0 hb0 : a=0 ∧ b=0)
    )
    (
      λ hr : (a = 0 ∧ b = 0) ↦ 
        λ x:ℝ ↦
         calc
           a  + b * x^2 = 0  + 0 * x^2  := by rw[hr.left,hr.right]
           _            = 0             := by ring_nf
    )  


-- Exercice 7
/- 2 points -/
theorem em1s0ex07   : ∀ P Q R:Prop,  P ∨ (Q ∧ R)  ↔ (P ∨ Q) ∧ (P ∨ R) := 
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h:P ∨ (Q ∧ R) ↦ 
        Or.elim h
        ( 
          λ hP:P ↦ 
            And.intro
              (Or.inl hP)
              (Or.inl hP)
        )
        ( 
          λ hQR : Q ∧ R  ↦ 
            And.intro
              (Or.inr hQR.left)
              (Or.inr hQR.right)
        )
    ) 
    (
      λ h: (P ∨ Q) ∧ (P ∨ R)  ↦ 
        Or.elim h.left
        ( 
          λ hP : P  ↦
            (Or.inl hP:  P ∨ ( Q ∧ R) )
        )
        (
          λ hQ : Q  ↦
            Or.elim h.right
            (
              λ hP : P  ↦ 
                (Or.inl hP :  P ∨ ( Q ∧ R)  ) 
            )
            (
              λ hR: R ↦ 
                have h_QR    : Q ∧ R         := And.intro hQ hR
                have h_P_QR  : P ∨ ( Q ∧ R)  := Or.inr h_QR
                h_P_QR
            )
        )
    )


/- 2 points -/
theorem em1s0'ex07  : ∀ P Q R:Prop,  P ∧ (Q ∨ R)  ↔ (P ∧ Q) ∨ (P ∧ R) := 
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h: P ∧ (Q ∨ R) ↦ 
        Or.elim (h.right : Q ∨ R)
        (
           λ hQ: Q ↦ 
             Or.inl (And.intro (h.left:P) hQ  : P ∧ Q )
        )
        (
           λ hR: R ↦ 
             Or.inr (And.intro (h.left:P) hR  : P ∧ R )
        )
    )
    (
      λ h: (P ∧ Q) ∨ (P ∧ R) ↦ 
        Or.elim h
        (
           λ hPQ: P ∧ Q ↦ 
             (And.intro (hPQ.left:P) (Or.inl (hPQ.right:Q) : Q ∨ R)  : P ∧ (Q ∨ R) )
        )
        (
           λ hPR: P ∧ R ↦ 
             (And.intro (hPR.left:P) (Or.inr (hPR.right:R) : Q ∨ R)  : P ∧ (Q ∨ R) )
        )

    )


/- 2 points -/
theorem em1s1ex07   : ∀ P Q R:Prop,  (R ∨ Q)  ∧ P  ↔ (R ∧ P) ∨ (Q ∧ P) := 
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h: (R ∨ Q)  ∧ P  ↦ 
        Or.elim (h.left : R ∨ Q)
        (
           λ hR: R ↦ 
             Or.inl (And.intro hR (h.right:P)   : R ∧ P )
        )
        (
           λ hQ: Q ↦ 
             Or.inr (And.intro  hQ (h.right:P)   : Q ∧ P )
        )
    )
    (
      λ h:  (R ∧ P) ∨ (Q ∧ P) ↦ 
        Or.elim h
        (
           λ hRetP: R ∧ P ↦ 
             have hRouQ : R ∨ Q :=  Or.inl (hRetP.left:R) 
             (And.intro  (hRouQ: R ∨ Q  )   (hRetP.right:P) :  (R ∨ Q) ∧ P)
        )
        (
           λ hQetP: Q ∧ P ↦ 
             have hRouQ : R ∨ Q :=  Or.inr (hQetP.left:Q) 
             (And.intro  (hRouQ: R ∨ Q  )   (hQetP.right:P) :  (R ∨ Q) ∧ P)
        )

    )


/- 2 points -/
theorem em1s2ex07   : ∀ P Q R:Prop,  (Q ∧ R) ∨ P ↔ (Q ∨ P) ∧ (R ∨ P) := 
  λ P Q R : Prop ↦
    Iff.intro
    (
      λ h: (Q ∧ R) ∨ P ↦ 
        Or.elim h
        ( 
          λ hQR : Q ∧ R  ↦ 
            And.intro
              (Or.inl hQR.left)
              (Or.inl hQR.right)
        )
        ( 
          λ hP:P ↦ 
            And.intro
              (Or.inr hP)
              (Or.inr hP)
        )
    ) 
    (
      λ h: (Q ∨ P) ∧ (R ∨ P)   ↦ 
        Or.elim h.left
        (
          λ hQ : Q  ↦
            Or.elim h.right
            (
              λ hR: R ↦ 
                have h_QR     : Q ∧ R         := And.intro hQ hR
                have h_QRorP  : ( Q ∧ R) ∨ P  := Or.inl h_QR
                h_QRorP
            )
            (
              λ hP : P  ↦ 
                (Or.inr hP :  ( Q ∧ R) ∨ P  ) 
            )
        )
        ( 
          λ hP : P  ↦
            (Or.inr hP:  (Q ∧ R) ∨ P  )
        )
    )




-- Exercice 8
/- 2 points -/
theorem em1s0ex08 : ∀ x:ℝ, x^2=x → ¬(x=3 ∨ x=-4 ) := 
  λ x:ℝ ↦
    λ h: x^2=x ↦ 
      λ ha: x=3 ∨ x=-4  ↦ 
        Or.elim ha
        (
          λ ha3 : x=3 ↦
            have h_3p2eq3 := 
              calc 
                3^2=x^2  := by rw[ha3]
                _  = x   := h 
                _  = 3   := ha3
            absurd ( h_3p2eq3 : 3^2 = (3:ℝ)) (by norm_num: 3^2 ≠ (3:ℝ) )
        )
        (
          λ ham4 : x=-4 ↦ 
            have h_m4p2eqm4 := 
              calc 
                (-4)^2=x^2  := by rw[ham4]
                _  = x      := h 
                _  = (-4)   := ham4
            absurd ( h_m4p2eqm4 : (-4)^2 = ((-4):ℝ)) (by norm_num: (-4)^2 ≠ ((-4):ℝ) )
        )


/- 2 points -/
theorem em1s1ex08 : ∀ x:ℝ, x^3 - 2*x  = 1 → ¬(x=2 ∨ x=-2 ) := 
  λ x:ℝ ↦
    λ h: x^3 - 2*x  = 1 ↦ 
      λ ha: x=2 ∨ x=-2  ↦ 
        Or.elim ha
        (
          λ ha2 : x=2 ↦
            have h_calc := 
              calc 
                2^3-2*2=x^3-2*x := by rw[ha2]
                _  = 1          := h 
            absurd ( h_calc : 2^3-2*2 = (1:ℝ)) (by norm_num: 2^3-2*2 ≠ (1:ℝ) )
        )
        (
          λ ham2 : x=-2 ↦ 
            have h_calc := 
              calc 
                (-2)^3-2*(-2)=x^3-2*x  := by rw[ham2]
                _  = 1          := h 
            absurd ( h_calc : (-2)^3-2*(-2) = (1:ℝ)) (by norm_num: (-2)^3-2*(-2) ≠ (1:ℝ) )
        )

/- 2 points -/
theorem em1s2ex08 : ∀ x:ℝ, 2*x^4+x^2 = 2 → ¬(x=3 ∨ x=-2 ) := 
  λ x:ℝ ↦
    λ h: 2*x^4+x^2 = 2 ↦ 
      λ ha: x=3 ∨ x=-2  ↦ 
        Or.elim ha
        (
          λ ha3 : x=3 ↦
            have h_calc := 
              calc 
                 2*3^4+3^2= 2*x^4+x^2 := by rw[ha3]
                _        = 2          := h 
            absurd ( h_calc : 2*3^4+3^2 = (2:ℝ)) (by norm_num: 2*3^4+3^2 ≠ (2:ℝ) )
        )
        (
          λ ham2 : x=-2 ↦ 
            have h_calc := 
              calc 
                 2*(-2)^4+(-2)^2= 2*x^4+x^2  := by rw[ham2]
                _  = 2                       := h 
            absurd ( h_calc : 2*(-2)^4+(-2)^2 = (2:ℝ)) (by norm_num: 2*(-2)^4+(-2)^2 ≠ (2:ℝ) )
        )

-- Exercice 9

/- 2 points -/
theorem em1s0ex09 : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) := 
  λ P Q : Prop ↦  
    λ hnPQ : ¬ (P ∨ Q)  ↦ 
      And.intro
        (
          λ hP : P ↦ 
            have hPQ : P ∨ Q := Or.inl hP
            absurd (hPQ : P ∨ Q ) (hnPQ : ¬ (P ∨ Q)) 
        )
        (
          λ hQ : Q ↦ 
            have hPQ : P ∨ Q := Or.inr hQ
            absurd (hPQ : P ∨ Q ) (hnPQ : ¬ (P ∨ Q)) 
        )


/- 2 points -/
theorem em1s1ex09 : ∀ P Q : Prop,  (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) := 
  λ P Q : Prop ↦  
    λ hnPnQ : (¬ P) ∧ (¬ Q) ↦ 
      λ hPQ : P ∨ Q ↦ 
        Or.elim hPQ
          (
            λ hP:P ↦  
              absurd (hP:P) (hnPnQ.left : ¬ P )
          )
          (
            λ hQ:Q ↦  
              absurd (hQ:Q) (hnPnQ.right : ¬ Q )
          )


/- 2 points -/
theorem em1s2ex09 : ∀ P Q : Prop,  (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) :=
  λ P Q : Prop ↦ 
    λ h1 : (¬ P) ∨ (¬ Q) ↦ 
      λ h2 : P ∧ Q ↦ 
        Or.elim h1
        (
          λ hnP: ¬ P ↦
            absurd (h2.left:P) (hnP: ¬ P) 
        )
        (
          λ hnQ: ¬ Q ↦
            absurd (h2.right:Q) (hnQ:¬ Q) 
        )


-- Exercice 10
--#check of_not_not
--example (P:Prop) ( h:  ¬¬P  ) : P := of_not_not h

/- 2 points -/
theorem em1s0ex10 : ∀ P Q : Prop,  (¬ (P → Q) ) ↔ (P ∧ ¬ Q) := 
  λ P Q : Prop ↦ 
    Iff.intro
    (
      λ hnPQ : ¬ (P → Q)  ↦ 
        And.intro
        (
          have hnnP :¬¬ P :=
            λ hnP : ¬ P ↦
              have hPimpQ : P → Q := 
                λ hP:P ↦  
                  (absurd (hP:P) (hnP: ¬ P) : Q)

              absurd (hPimpQ : P → Q) (hnPQ : ¬ (P → Q)) 

          (of_not_not hnnP : P)
        )
        (
          λ hQ : Q ↦ 
              have hPimpQ : P → Q := 
                λ _:P ↦  
                  (hQ:Q)
            absurd (hPimpQ : P →Q ) (hnPQ : ¬ (P → Q))
        )
    )
    (
      λ hPnQ :  P ∧ ¬ Q  ↦ 
        λ hPQ : P → Q ↦ 
          have hQ : Q := hPQ (hPnQ.left:P)
          absurd hQ (hPnQ.right: ¬ Q )
    )


/- 2 points -/
theorem em1s1ex10 : ∀ P Q : Prop,    (¬ P ∨ Q) → (P → Q)   := 
  λ P Q:Prop ↦
    λ hnPorQ : ¬ P ∨ Q ↦ 
      Or.elim (hnPorQ)
      (
        λ hnP: ¬ P ↦  
          λ hP:P ↦  
            (absurd (hP:P) (hnP: ¬ P) : Q)
      )
      (
        λ hQ: Q ↦  
          λ _:P ↦  
            (hQ:Q)
      )

/- 2 points -/
theorem em1s2ex10 : ∀ P Q : Prop,  (¬Q → ¬P) ↔(P → Q)  :=  
   λ P Q : Prop ↦ 
     Iff.intro
     (
       λ hc:  ¬Q → ¬P ↦ 
         λ hP:P ↦ 
           have hnnQ : ¬¬Q := 
              λ hnQ : ¬Q ↦
                absurd (hP:P) (hc hnQ :¬ P)

           of_not_not (hnnQ : ¬¬ Q)
     )
     (
       λ hd:  P → Q ↦ 
         λ hnQ : ¬ Q ↦
           λ hP : P ↦ 
             absurd (hd hP : Q)  (hnQ : ¬ Q)
     )





end exam
