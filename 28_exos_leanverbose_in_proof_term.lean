/-
Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  By hf applied to ε using ε_pos we get δ such that
    (δ_pos : δ > 0) (Hf : ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε)
  By hu applied to δ using δ_pos we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  By Hf applied to u n it suffices to prove |u n - x₀| ≤ δ
  We conclude by Hu applied to n using n_ge
QED

Example "Constant sequences converge."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume: (h : ∀ n, u n = l)
  Conclusion: u converges to l
Proof:
  Fix ε > 0
  Let's prove that ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  Let's prove that 0 works
  Fix n ≥ 0
  Calc |u n - l| = |l - l| by We rewrite using h
   _             = 0       by We compute
   _             ≤ ε       by We conclude by ε_pos
QED

Example "A sequence converging to a positive limit is ultimately positive."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume: (hl : l > 0) (h :u converges to l)
  Conclusion: ∃ N, ∀ n ≥ N, u n ≥ l/2
Proof:
  By h applied to [l/2, half_pos hl] we get N such that hN : ∀ n ≥ N, |u n - l| ≤ l / 2
  Let's prove that N works
  Fix n ≥ N
  By hN applied to n using (n_ge : n ≥ N) we get hN' : |u n - l| ≤ l / 2
  By hN' we get (h₁ : -(l/2) ≤ u n - l) (h₂ : u n - l ≤ l / 2)
  We conclude by h₁
QED


Example "Addition of convergent sequences."
  Given: (u v : ℕ → ℝ) (l l' : ℝ)
  Assume: (hu : u converges to l) (hv : v converges to l')
  Conclusion: (u + v) converges to (l + l')
Proof:
  Fix ε > 0
  By hu applied to [ε/2, half_pos ε_pos] we get N₁
      such that (hN₁ : ∀ (n : ℕ), n ≥ N₁ → |u n - l| ≤ ε / 2)
  By hv applied to [ε/2, half_pos ε_pos] we get N₂
      such that (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Let's prove that max N₁ N₂ works
  Fix n ≥ max N₁ N₂
  By n_ge we get (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fact fait₁ : |u n - l| ≤ ε/2
    from hN₁ applied to n using hn₁
  Fact fait₂ : |v n - l'| ≤ ε/2
    from hN₂ applied to n using hn₂
  Calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| by We compute
                     _ ≤ |u n - l| + |v n - l'|     by We apply abs_add
                     _ ≤  ε/2 + ε/2                 by We combine [fait₁, fait₂]
                     _ =  ε                         by We compute
QED

Example "The squeeze theorem."
  Given: (u v w : ℕ → ℝ) (l : ℝ)
  Assume: (hu : u converges to l) (hw : w converges to l)
    (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n)
  Conclusion: v converges to l
Proof:
  Fix ε > 0
  By hu applied to ε using ε_pos we get N such that hN : ∀ n ≥ N, |u n - l| ≤ ε
  By hw applied to ε using ε_pos we get N' such that hN' : ∀ n ≥ N', |w n - l| ≤ ε
  Let's prove that max N N' works
  Fix n ≥ max N N'
  By (n_ge : n ≥ max N N') we get (hn : N ≤ n) (hn' : N' ≤ n)
  By hN applied to n using hn we get
   (hNl : -ε ≤ u n - l) (hNd : u n - l ≤ ε)
  By hN' applied to n using hn' we get
    (hN'l : -ε ≤ w n - l) (hN'd : w n - l ≤ ε)
  Let's first prove that -ε ≤ v n - l
  Calc -ε ≤ u n - l by We conclude by hNl
      _   ≤ v n - l by We conclude by h applied to n
  Let's now prove that v n - l ≤ ε
  Calc v n - l ≤ w n - l  by We conclude by h' applied to n
      _        ≤ ε        by We conclude by hN'd
QED

Example "A reformulation of the convergence definition."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume:
  Conclusion: (u converges to l) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Proof:
  Let's first prove that (u converges to l) → ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |u n - l| < ε)
  Assume hyp : u converges to l
  Fix ε > 0
  By hyp applied to ε/2 using half_pos ε_pos we get N
      such that hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  Let's prove that N works
  Fix n ≥ N
  Calc |u n - l| ≤ ε/2  by We conclude by hN applied to [n, n_ge]
       _         < ε    by We conclude by ε_pos
  Let's now prove that (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) → u converges to l
  Assume hyp : ∀ (ε : ℝ), ε > 0 → (∃ N, ∀ n ≥ N, |u n - l| < ε)
  Fix ε > 0
  By hyp applied to ε using ε_pos we get N such that hN : ∀ n ≥ N, |u n - l| < ε
  Let's prove that N works
  Fix n ≥ N
  We conclude by hN applied to n using n_ge
QED


Example "Uniqueness of limits."
  Given: (u : ℕ → ℝ) (l l' : ℝ)
  Assume: (h : u converges to l) (h': u converges to l')
  Conclusion: l = l'
Proof:
  By eq_of_forall_dist_le it suffices to prove that ∀ ε > 0, |l - l'| ≤ ε
  Fix ε > 0
  By h applied to [ε/2, half_pos ε_pos] we get N
      such that hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  By h' applied to [ε/2, half_pos ε_pos] we get N'
      such that hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  By hN applied to [max N N', le_max_left _ _]
     we get hN₁ : |u (max N N') - l| ≤ ε / 2
  By hN' applied to [max N N', le_max_right _ _]
    we get hN'₁ : |u (max N N') - l'| ≤ ε / 2
  Calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')|  by We compute
  _             ≤ |l - u (max N N')| + |u (max N N') - l'| by We apply abs_add
  _             = |u (max N N') - l| + |u (max N N') - l'| by We rewrite using abs_sub_comm
  _             ≤ ε                                        by We combine [hN₁, hN'₁]
QED

Example "An increasing sequence having a finite supremum tends to it."
  Given: (u : ℕ → ℝ) (M : ℝ)
  Assume: (h : M is a supremum of u) (h' : u is increasing)
  Conclusion: u converges to M
Proof:
  Fix ε > 0
  By h we get (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  By sup_M_ep applied to ε using ε_pos we get n₀ such that (hn₀ : u n₀ ≥ M - ε)
  Let's prove that n₀ works : ∀ n ≥ n₀, |u n - M| ≤ ε
  Fix n ≥ n₀
  By inf_M applied to n we get (inf_M' : u n ≤ M)
  Let's first prove that -ε ≤ u n - M
  · By h' applied to [n₀, n, n_ge] we get h'' : u n₀ ≤ u n
    We combine [h'', hn₀]
  Let's now prove that u n - M ≤ ε
  ·  We combine [inf_M', ε_pos]
QED


-/

import Mathlib.Data.Real.Basic



  macro " [ " a:term  " ; " b:term  " ] "  : term => do
    `({x:ℝ | x ≥ ($a) ∧ x ≤ ($b) })

  #check [1;3]



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


--example (a b:ℝ) (x:ℝ)  : abs (x-b) ≤ a ↔ x ∈ [b-a;b+a]:= by exact?
example (a:ℝ) (x:ℝ)  : abs (x) ≤ a ↔ x ≥ -a ∧ x ≤ a:= by exact? -- abs_le

  lemma dist_le {a b:ℝ} {x:ℝ} : abs (x-b) ≤ a ↔ x ∈ [b-a;b+a]:=
    calc
      abs (x-b) ≤ a ↔ x-b ∈ [-a; a]  := abs_le
      _             ↔  x ∈ [b-a;b+a] := Iff.and (Iff.trans (add_le_add_iff_right b).symm (by ring_nf)) (Iff.trans (add_le_add_iff_right b).symm (by ring_nf))


namespace v1

def converges (u: ℕ → ℝ ) (ℓ : ℝ ) : Prop :=
    ∀ ε>0, ∃n0, ∀ n ≥ n0, (u n) ≥ ℓ - ε  ∧ u n ≤ ℓ + ε

def continuous (f:ℝ → ℝ ) (a: ℝ ) : Prop :=
    ∀ ε >0, ∃η>0, ∀x, x ≥ a - η  ∧ x ≤ a+ η  →  (f x)  ≥ (f a) - ε ∧ (f x) ≤ (f a ) + ε

--Exercise "Continuity implies sequential continuity"
theorem continuity_implies_sequential_continuity
     (f : ℝ → ℝ) (u : ℕ → ℝ) (a : ℝ)
     (hu : converges u  a) (hf : continuous f a)
    : converges (f ∘ u)  (f a)
 :=

   λ (ε :ℝ) (hε :  ε>0) ↦

     Exists.elim (hf ε hε)
     (
       λ (η:ℝ)  (hη: η>0 ∧ ∀x:ℝ, (x ≥ a-η ∧ x ≤ a+η) → (f x ≥ f a - ε ∧ f x ≤ f a + ε) ) ↦

        Exists.elim (hu η hη.left)
          (
            λ (n0:ℕ)  (hn0: ∀ n ≥ n0, (u n) ≥ a-η  ∧ (u n) ≤ a+η ) ↦

              Exists.intro n0
                λ (n:ℕ) (hn: n ≥ n0 ) ↦
                  have : (u n)   ≥ a-η     ∧ (u n)   ≤ a+η     := hn0 n hn
                  have : f (u n) ≥ f a - ε ∧ f (u n) ≤ f a + ε := hη.right (u n) this
                  this
          )
     )

--Exercise "Continuity implies sequential continuity"
theorem continuity_implies_sequential_continuity_short
     (f : ℝ → ℝ) (u : ℕ → ℝ) (a : ℝ)
     (hu : converges u  a) (hf : continuous f a)
    : converges (f ∘ u)  (f a)
 :=
   λ ε hε ↦
     let ⟨ η, ⟨ h_ηpos , hη ⟩ ⟩  := hf ε hε
     let ⟨ n0,hn0 ⟩              := hu η h_ηpos
     ⟨ n0, λ n hn ↦ hη (u n) (hn0 n hn) ⟩


end v1






namespace v2

def converges (u: ℕ → ℝ ) (ℓ : ℝ ) : Prop :=
    ∀ ε>0, ∃n0, ∀ n ≥ n0, |(u n) - ℓ| ≤ ε

def continuous (f:ℝ → ℝ ) (a: ℝ ) : Prop :=
    ∀ ε >0, ∃η>0, ∀x, |x - a|  ≤  η  →  |(f x)  - (f a)|  ≤  ε


--Exercise "Continuity implies sequential continuity"
theorem continuity_implies_sequential_continuity
     (f : ℝ → ℝ) (u : ℕ → ℝ) (a : ℝ)
     (hu : converges u  a) (hf : continuous f a)
    : converges (f ∘ u)  (f a)
 :=

   λ (ε :ℝ) (hε :  ε>0) ↦

     Exists.elim (hf ε hε)
     (
       λ (η:ℝ)  (hη: η>0 ∧ ∀x:ℝ, |x - a|  ≤  η → |(f x) - (f a)|  ≤  ε ) ↦

        Exists.elim (hu η hη.left)
          (
            λ (n0:ℕ)  (hn0: ∀ n ≥ n0, |(u n) - a|  ≤  η ) ↦

              Exists.intro n0
                λ (n:ℕ) (hn: n ≥ n0 ) ↦
                  have : |(u n) - a|  ≤  η         := hn0 n hn
                  have : |(f (u n)) - (f a)|  ≤  ε := hη.right (u n) this
                  this
          )
     )


--Exercise "Continuity implies sequential continuity"
theorem continuity_implies_sequential_continuity_short
     (f : ℝ → ℝ) (u : ℕ → ℝ) (a : ℝ)
     (hu : converges u  a) (hf : continuous f a)
    : converges (f ∘ u)  (f a)
 :=
   λ ε hε ↦
     let ⟨ η, ⟨ h_ηpos , hη ⟩ ⟩  := hf ε hε
     let ⟨ n0,hn0 ⟩              := hu η h_ηpos
     ⟨ n0, λ n hn ↦ hη (u n) (hn0 n hn) ⟩


--Example "Constant sequences converge."
theorem constant_sequences_converge
  (u : ℕ → ℝ) (ℓ : ℝ)
  (h : ∀ n, u n = ℓ)
   : converges u ℓ
  :=

    λ (ε :ℝ) (hε :  ε>0) ↦

      Exists.intro 0
        λ (n:ℕ) _ ↦
          calc
            |(u n) - ℓ| = |ℓ-ℓ| := by rw[h]
            _           = |0|   := by ring_nf
            _           = 0     := by norm_num -- abs_zero
            _           ≤ ε     := by rel[hε]


--Example "Constant sequences converge."
theorem constant_sequences_converge'
  (u : ℕ → ℝ) (ℓ : ℝ)
  (h : ∀ n, u n = ℓ)
   : converges u ℓ
  :=

    λ _ hε ↦ ⟨ 0, λ n _ ↦ Trans.trans (by simp[h] : (|u n - ℓ| = 0)) (by rel[hε]) ⟩



--Example "A sequence converging to a positive limit is ultimately positive."
theorem a_sequence_converging_to_a_positive_limit_is_ultimately_positive
   (u : ℕ → ℝ) (ℓ : ℝ)
   (hℓ : ℓ > 0) (h :converges u ℓ)
  : ∃ N, ∀ n ≥ N, u n ≥ ℓ/2
:=
  Exists.elim (h (ℓ/2) (by linarith : ℓ/2 >0 ))
    (
      λ (n0:ℕ) (hn0 : ∀n:ℕ, n≥n0 → |(u n) - ℓ| ≤ ℓ/2) ↦
      Exists.intro n0
      (
        λ (n:ℕ) (hn: n≥n0)  ↦
          have : |(u n) - ℓ| ≤ ℓ/2         := hn0 n hn
          have : u n ∈ [ℓ - ℓ/2 ; ℓ + ℓ/2] := dist_le.mp this
          calc
            u n ≥  ℓ - ℓ/2   := this.left
            _   = ℓ/2        := by ring_nf

      )
    )

theorem a_sequence_converging_to_a_positive_limit_is_ultimately_positive'
   (u : ℕ → ℝ) (ℓ : ℝ)
   (hℓ : ℓ > 0) (h :converges u ℓ)
  : ∃ N, ∀ n ≥ N, u n ≥ ℓ/2
:=
  let ⟨n0,hn0⟩:=  h (ℓ/2) (by linarith )
  ⟨n0, λ n hn ↦ have : _ := (dist_le.mp (hn0 n hn)).left ; by linarith ⟩



--Example "Addition of convergent sequences."
  theorem addition_of_convergent_sequences
    (u v : ℕ → ℝ) (ℓ ℓ' : ℝ)
    (hu : converges u ℓ) (hv : converges v ℓ')
  : converges (u + v) (ℓ + ℓ')
:=
  λ (ε: ℝ)  (hε: ε > 0) ↦
  have hε2 : ε / 2 > 0 := by linarith

  Exists.elim ( hu (ε / 2) hε2 )
  (
    λ (n1:ℕ)  (hn1 : ∀ (n : ℕ), n ≥ n1 → |u n - ℓ| ≤ ε / 2 ) ↦
      Exists.elim ( hv (ε / 2) hε2 )
      (
        λ (n2:ℕ)  (hn2 : ∀ (n : ℕ), n ≥ n2 → |v n - ℓ'| ≤ ε / 2 ) ↦
          let n0 := max n1 n2

          Exists.intro n0
          (
            λ (n:ℕ) (hn : n≥ n0) ↦
              have hnn1 : n≥ n1          :=  le_of_max_le_left  hn
              have hnn2 : n≥ n2          :=  le_of_max_le_right hn

              have hu1 : |u n - ℓ|  ≤ ε/2 :=  hn1 n hnn1
              have hv1 : |v n - ℓ'| ≤ ε/2 :=  hn2 n hnn2

              calc
                |(u+v) n - (ℓ+ℓ')| = |(u n + v n) - (ℓ+ℓ')|   := rfl
                _                  = |(u n - ℓ) + (v n - ℓ')| := by ring_nf
                _                  ≤ |u n - ℓ| + |v n - ℓ'|   := abs_add _ _
                _                  ≤ ε/2 + ε/2                := by rel[hu1,hv1] -- add_le_add hu1 hv1
                _                  = ε                        := by ring_nf
          )
      )
  )


-- Example "The squeeze theorem."
theorem the_squeeze_theorem
   (u v w : ℕ → ℝ) (ℓ : ℝ)
   (hu : converges u ℓ) (hw : converges w ℓ)
   (h : ∀ n:ℕ , u n ≤ v n)
   (h' : ∀ n:ℕ , v n ≤ w n)
  : converges v ℓ
  :=
  λ (ε: ℝ)  (hε: ε > 0) ↦
    Exists.elim ( hu ε hε )
    (
      λ (n1:ℕ)  (hn1 : ∀ (n : ℕ), n ≥ n1 → |u n - ℓ| ≤ ε ) ↦
        Exists.elim ( hw ε hε )
        (
          λ (n2:ℕ)  (hn2 : ∀ (n : ℕ), n ≥ n2 → |w n - ℓ| ≤ ε ) ↦
          let n0 := max n1 n2

          Exists.intro n0
          (
            λ (n:ℕ) (hn : n≥ n0) ↦
              have hnn1 : n≥ n1          :=  le_of_max_le_left  hn
              have hnn2 : n≥ n2          :=  le_of_max_le_right hn

              have hu1 : |u n - ℓ| ≤ ε :=  hn1 n hnn1
              have hw2 : |w n - ℓ| ≤ ε :=  hn2 n hnn2

              abs_le.mpr
              (
                And.intro
                  (show -ε ≤ v n - ℓ from
                    calc
                      -ε ≤ u n - ℓ := (abs_le.mp hu1).left
                      _  ≤ v n - ℓ := by rel[h n]
                  )

                  (show v n - ℓ ≤ ε  from
                    calc
                      v n - ℓ ≤ w n - ℓ := by rel[h' n]
                      _       ≤ ε       := (abs_le.mp hw2).right
                  )
              )
          )
        )
    )
theorem the_squeeze_theorem'
   (u v w : ℕ → ℝ) (ℓ : ℝ)
   (hu : converges u ℓ) (hw : converges w ℓ)
   (h : ∀ n:ℕ , u n ≤ v n)
   (h' : ∀ n:ℕ , v n ≤ w n)
  : converges v ℓ
  :=
  λ (ε: ℝ)  (hε: ε > 0) ↦
    Exists.elim ( hu ε hε )
    (
      λ (n1:ℕ)  (hn1 : ∀ (n : ℕ), n ≥ n1 → |u n - ℓ| ≤ ε ) ↦
        Exists.elim ( hw ε hε )
        (
          λ (n2:ℕ)  (hn2 : ∀ (n : ℕ), n ≥ n2 → |w n - ℓ| ≤ ε ) ↦
          let n0 := max n1 n2

          Exists.intro n0
          (
            λ (n:ℕ) (hn : n≥ n0) ↦
              have hnn1 : n≥ n1          :=  le_of_max_le_left  hn
              have hnn2 : n≥ n2          :=  le_of_max_le_right hn

              have hu1 : |u n - ℓ| ≤ ε :=  hn1 n hnn1
              have hw2 : |w n - ℓ| ≤ ε :=  hn2 n hnn2

              have hl : -ε ≤ v n - ℓ :=
                calc
                  -ε ≤ u n - ℓ := (abs_le.mp hu1).left
                  _  ≤ v n - ℓ := by rel[h n]

              have hr : v n - ℓ ≤ ε :=
                calc
                  v n - ℓ ≤ w n - ℓ := by rel[h' n]
                  _       ≤ ε       := (abs_le.mp hw2).right

              abs_le.mpr ( And.intro hl hr )
          )
        )
    )

theorem the_squeeze_theorem''
   (u v w : ℕ → ℝ) (ℓ : ℝ)
   (hu : converges u ℓ) (hw : converges w ℓ)
   (h : ∀ n:ℕ , (u n ≤ v n) ∧ (v n ≤ w n))
  : converges v ℓ
  :=
  λ (ε: ℝ)  (hε: ε > 0) ↦
    Exists.elim ( hu ε hε )
    (
      λ (n1:ℕ)  (hn1 : ∀ (n : ℕ), n ≥ n1 → |u n - ℓ| ≤ ε ) ↦
        Exists.elim ( hw ε hε )
        (
          λ (n2:ℕ)  (hn2 : ∀ (n : ℕ), n ≥ n2 → |w n - ℓ| ≤ ε ) ↦
          let n0 := max n1 n2

          Exists.intro n0
          (
            λ (n:ℕ) (hn : n≥ n0) ↦
              have hnn1 : n≥ n1          :=  le_of_max_le_left  hn
              have hnn2 : n≥ n2          :=  le_of_max_le_right hn

              have hu1 : |u n - ℓ| ≤ ε :=  hn1 n hnn1
              have hw2 : |w n - ℓ| ≤ ε :=  hn2 n hnn2

              have hl : -ε ≤ v n - ℓ :=
                calc
                  -ε ≤ u n - ℓ := (abs_le.mp hu1).left
                  _  ≤ v n - ℓ := by rel[(h n).left]

              have hr : v n - ℓ ≤ ε :=
                calc
                  v n - ℓ ≤ w n - ℓ := by rel[(h n).right]
                  _       ≤ ε       := (abs_le.mp hw2).right

              abs_le.mpr ( And.intro hl hr )
          )
        )
    )


theorem the_squeeze_theorem'''
   (u v w : ℕ → ℝ) (ℓ : ℝ)
   (hu : converges u ℓ) (hw : converges w ℓ)
   (h : ∀ n:ℕ , (u n ≤ v n) ∧ (v n ≤ w n))
  : converges v ℓ
  :=
  λ (ε: ℝ)  (hε: ε > 0) ↦
    let ⟨n1,hn1⟩ := hu ε hε
    let ⟨n2,hn2⟩ := hw ε hε
    Exists.intro (max n1 n2)
    (
      λ n hn ↦
        have hl : -ε ≤ v n - ℓ :=
          calc
            -ε ≤ u n - ℓ := (abs_le.mp (hn1 n (le_of_max_le_left  hn))).left
            _  ≤ v n - ℓ := by rel[(h n).left]

        have hr : v n - ℓ ≤ ε :=
          calc
            v n - ℓ ≤ w n - ℓ := by rel[(h n).right]
            _       ≤ ε       := (abs_le.mp (hn2 n (le_of_max_le_right hn))).right

        abs_le.mpr ( And.intro hl hr )
    )

--Example "A reformulation of the convergence definition."
theorem a_reformulation_of_the_convergence_definition
  (u : ℕ → ℝ) (ℓ : ℝ)
  : (converges u ℓ) ↔ ∀ ε > 0, ∃ N:ℕ , ∀ n ≥ N, |u n - ℓ| < ε
  :=
  Iff.intro
  (
    λ h : converges u ℓ ↦
     λ (ε:ℝ) (hε : ε>0) ↦
       have hε2 : ε/2>0 := by linarith
       Exists.elim (h (ε/2) hε2)
       (
         λ (N:ℕ) (hN : ∀ n ≥ N, |u n - ℓ| ≤ ε/2) ↦
           Exists.intro N
           (
             λ (n:ℕ) (hn : n≥ N) ↦
               calc
                 |u n - ℓ| ≤ ε/2   := hN n hn
                 _         < ε     := by linarith
/-                 _         = ε/2+0    := by ring_nf
                 _         < ε/2+ε/2  := by rel[hε2]
                 _         = ε        := by ring_nf-/
           )
       )
  )
  (
    λ h : ∀ ε > 0, ∃ N:ℕ , ∀ n ≥ N, |u n - ℓ| < ε ↦
     λ (ε:ℝ) (hε : ε>0) ↦
       Exists.elim (h ε hε)
       (
         λ (N:ℕ) (hN : ∀ n ≥ N, |u n - ℓ| < ε) ↦
           Exists.intro N
           (
             λ (n:ℕ) (hn : n≥ N) ↦
               show |u n - ℓ| ≤ ε from by rel[hN n hn]
           )
       )
  )


example (a b:ℝ ) : |a-b| = |b-a| := by exact? -- abs_sub_comm

--Example "Uniqueness of limits."
  lemma eq_of_forall_dist_le
    (a:ℝ)
    (h: ∀ ε>0, |a| ≤ ε)
    : a = 0
    :=
    Or.elim (gt_or_eq_of_le (abs_nonneg a))
    (
      λ ha : |a| > 0 ↦
        have ha2  : |a|/2 > 0  := by linarith
        absurd
        (
          calc
            |a| ≤ |a|/2 := h (|a|/2) ha2
            _   < |a|   := by linarith
        )
        (lt_irrefl (|a|))
    )
    (
      λ ha : |a| = 0 ↦
        abs_eq_zero.mp ha
    )


  theorem uniqueness_of_limits
   (u : ℕ → ℝ) (ℓ ℓ' : ℝ)
   (h : converges u ℓ) (h': converges u ℓ')
  : ℓ = ℓ'
  :=
  have h0 :  ∀ ε > 0, |ℓ  - ℓ'| ≤ ε :=
    λ (ε:ℝ) (hε : ε >0 ) ↦
      have hε2  : ε/2 > 0  := by linarith
      Exists.elim (h (ε/2) hε2)
      (
        λ (n1:ℕ) (hn1: ∀ n≥n1, |u n - ℓ|≤ ε/2  ) ↦
          Exists.elim (h' (ε/2) hε2)
          (
            λ (n2:ℕ) (hn2: ∀ n≥n2, |u n - ℓ'|≤ ε/2  ) ↦
              let n:=max n1 n2
              calc
                |ℓ - ℓ'| = |(ℓ - (u n) )+( (u n) - ℓ')| := by ring_nf
                _        ≤ |ℓ - (u n)| + |(u n) - ℓ'| := abs_add _ _
                _        = |(u n) - ℓ| + |(u n) - ℓ'| := by rw[abs_sub_comm _ _]
                _        ≤ ε/2 + ε/2                  := add_le_add (hn1 n (le_max_left n1 n2)) (hn2 n (le_max_right n1 n2))
                _        = ε                          := by ring_nf
          )
      )

  calc
    ℓ = (ℓ-ℓ') + ℓ' := by ring_nf
    _ = 0    +  ℓ'  := by rw[eq_of_forall_dist_le (ℓ - ℓ') h0]
    _ = ℓ'          := by ring_nf








  theorem uniqueness_of_limits'
   (u : ℕ → ℝ) (ℓ ℓ' : ℝ)
   (h : converges u ℓ) (h': converges u ℓ')
  : ℓ = ℓ'
  :=
    let ε := |ℓ' - ℓ| /3
    have hε0: 0 ≤ |ℓ' - ℓ|/3  :=  have : _ := abs_nonneg (ℓ' - ℓ ) ; by linarith -- trans (zero_div 3).symm ((div_le_div_right (by norm_cast)).mpr (abs_nonneg (ℓ' - ℓ )))
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
                3 = ε*3/ε := by linarith -- (mul_div_cancel_left 3 (ne_of_gt hε0')).symm
                _ ≤ ε*2/ε := by rel[h3ε]
                _ = 2     := by linarith -- (mul_div_cancel_left 2 (ne_of_gt hε0'))

            absurd h32 (by norm_cast)
        )
      )
    )
    (λ hε0'': 0 =ε ↦
      have h_dℓℓ' : |ℓ' - ℓ|=0 :=
        calc
--          |ℓ' - ℓ|=0*3  :=  (div_eq_iff (by norm_cast: (3:ℝ )≠ 0)).mp hε0''.symm
          |ℓ' - ℓ|= ε*3  := by ring_nf
          _       = 0*3  := by rw[hε0'']
          _       = 0    := by norm_cast

      have h_ℓℓ': ℓ' - ℓ = 0 := abs_eq_zero.mp h_dℓℓ'
      by linarith   -- (eq_of_sub_eq_zero h_ℓℓ').symm
    )



/-
def image (u:ℕ→ ℝ ) : Set ℝ := {x:ℝ | ∃n:ℕ, x= u n }

def supremum (u:ℕ→ ℝ ) (M:ℝ ) : Prop := IsLUB (image u) M
lemma supremum_iff (u:ℕ→ ℝ ) (M:ℝ ) :
   (supremum u M) ↔ (M ∈ upperBounds (image u)) ∧ (∀ ε>0, ∃n:ℕ, u n > M - ε )
   :=
   sorry
-/
def supremum (u:ℕ→ ℝ ) (M:ℝ ) : Prop := (∀n:ℕ , u n ≤ M ) ∧ (∀ ε>0, ∃n:ℕ, u n > M - ε )
def is_increasing (u:ℕ→ ℝ ) : Prop := ∀ m n:ℕ, m ≤ n → u m ≤ u n


-- Example "An increasing sequence having a finite supremum tends to it."
theorem an_increasing_sequence_having_a_finite_supremum_tends_to_it
  (u : ℕ → ℝ) (M : ℝ)
  (h : supremum  u M) (h' : is_increasing u)
  : converges u M

  :=

  λ (ε:ℝ)  (hε : ε>0) ↦
    Exists.elim (h.right ε hε  )
     (
       λ (n0:ℕ) (hn0 : u n0 > M - ε ) ↦
         Exists.intro n0
           (
             λ (n:ℕ) (hn:n≥ n0) ↦
             dist_le.mpr
             (
               And.intro
                 (
                   calc
                     u n ≥ u n0   := h' n0 n hn
                     _   ≥ M - ε  := by rel[hn0]
                 )
                 (
                   calc
                     u n ≤ M   := h.left n
                     _   ≤ M+ε := by linarith
                 )
             )
           )
     )


end v2
