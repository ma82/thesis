
\begin{code}
{-# OPTIONS --no-termination-check --no-positivity-check #-}
module thesis.IntroMod where

open import AD.Misc
\end{code}

\begin{code}
module Monolithic where
\end{code}

\begin{code}
 data Exp : Set where
   [_] :         ℕ → Exp
   _⊕_ : Exp → Exp → Exp
\end{code}

\begin{code}
 ⟦_⟧Exp : Exp → ℕ
 ⟦ [ n ]   ⟧Exp = n
 ⟦ e1 ⊕ e2 ⟧Exp = ⟦ e1 ⟧Exp + ⟦ e2 ⟧Exp
\end{code}

\begin{code}
 data Exp' : Set where
   [_] :           ℕ → Exp'
   _⊕_ : Exp' → Exp' → Exp'
   _⊗_ : Exp' → Exp' → Exp'
\end{code}

\begin{code}
 ⟦_⟧Exp' : Exp' → ℕ
 ⟦ [ n ]   ⟧Exp' = n
 ⟦ e1 ⊕ e2 ⟧Exp' = ⟦ e1 ⟧Exp' + ⟦ e2 ⟧Exp'
 ⟦ e1 ⊗ e2 ⟧Exp' = ⟦ e1 ⟧Exp' * ⟦ e2 ⟧Exp'
\end{code}

\begin{code}
module Modular where
\end{code}

\begin{code}
 data ExpF (X : Set) : Set where
   [_] :     ℕ → ExpF X
   _⊕_ : X → X → ExpF X
\end{code}

\begin{code}
 data TimesF (X : Set) : Set where
   _⊗_ : X → X → TimesF X
\end{code}

\begin{code}
 data μ (F : Set → Set) : Set where
   In : F (μ F) → μ F
\end{code}

\begin{code}
 Exp = μ ExpF
\end{code}

\begin{code}
 _:+:_ : (Set → Set) → (Set → Set) → Set → Set
 (F :+: G) X = F X ⊎ G X
\end{code}

\begin{code}
 Exp' = μ (ExpF :+: TimesF)
\end{code}

\begin{code}
 cata : ∀ {F}⦃ map : ∀ {A B} → (A → B) → F A → F B ⦄{X} → (F X → X) → μ F → X
 cata ⦃ map ⦄ α (In xs) = α (map (cata ⦃ map ⦄ α) xs)
\end{code}

\begin{code}
 mapExpF   : ∀ {A B} → (A → B) → ExpF   A → ExpF   B
 mapTimesF : ∀ {A B} → (A → B) → TimesF A → TimesF B
 map+      : ∀ {F G} → (∀ {A B} → (A → B) → F A → F B)
                     → (∀ {A B} → (A → B) → G A → G B)
                     →  ∀ {A B} → (A → B) → (F :+: G) A → (F :+: G) B
\end{code}

\begin{code}
 mapExpF f [ n   ] = [ n ]
 mapExpF f (l ⊕ r) = f l ⊕ f r
 mapTimesF f (l ⊗ r) = f l ⊗ f r
 map+ mapF mapG f (inl x) = inl (mapF f x)
 map+ mapF mapG f (inr y) = inr (mapG f y)
\end{code}

\begin{code}
 algExpF : ExpF ℕ → ℕ
 algExpF [ n ]   = n
 algExpF (l ⊕ r) = l + r
\end{code}

\begin{code}
 ⟦_⟧Exp : Exp → ℕ
 -- TODO 9B5Q ⦃⦄ was not needed with Agda 2.4.0.2
 ⟦_⟧Exp = cata ⦃ mapExpF ⦄ algExpF
\end{code}

\begin{code}
 algTimesF : TimesF ℕ → ℕ
 algTimesF (l ⊗ r) = l * r

 ⟦_⟧Exp' : Exp' → ℕ
 ⟦_⟧Exp' = -- TODO 9B5Q was (_ = map+ mapExpF mapTimesF) in 2.4.0.2
           let m = map+ mapExpF mapTimesF in
           -- TODO 9B5Q ⦃⦄ was not needed in 2.4.0.2
           cata ⦃ m ⦄ ⊎.[ algExpF , algTimesF ]
\end{code}

\begin{code}
 [[_]] : ∀ {F}⦃ inj : ∀ {X} → ExpF X → F X ⦄ → ℕ → μ F
 [[_]] ⦃ inj ⦄ n = In (inj [ n ])

 _[⊕]_ : ∀ {F}⦃ inj : ∀ {X} → ExpF X → F X ⦄ → μ F → μ F → μ F
 _[⊕]_ ⦃ inj ⦄ e1 e2 = In (inj (e1 ⊕ e2))

 _[⊗]_ : ∀ {F}⦃ inj : ∀ {X} → TimesF X → F X ⦄ → μ F → μ F → μ F
 _[⊗]_ ⦃ inj ⦄ e1 e2 = In (inj (e1 ⊗ e2))
\end{code}

\begin{code}
 -- TODO 9B5Q worked in 2.4.0.2
 example : Exp'
 example = TODO -- ([[ 1 ]] [⊕] [[ 2 ]]) [⊗] [[ 3 ]]
\end{code}

\begin{code}
  where
   open import thesis.TODO
   -- TODO 9B5Q `instance` is not enough
   instance
    a : ∀ {X} → ExpF   X → (ExpF :+: TimesF) X ; a = inl
    b : ∀ {X} → TimesF X → (ExpF :+: TimesF) X ; b = inr
\end{code}

\begin{code}
module MonolithicFamilies where

 open import Data.Bool as Bool hiding (_≟_)
\end{code}

\begin{code}
 data I : Set where
  nat bool : I
\end{code}

\begin{code}
 Ty : I → Set
 Ty nat  = ℕ
 Ty bool = Bool
\end{code}

\begin{code}
 data A : I → Set where
  [_] : ∀ {i} → Ty i  → A i
  _⊕_ : A nat → A nat → A nat
\end{code}

\begin{code}
 ⟦_⟧A : ∀ {i} → A i → Ty i
 ⟦ [ x ]   ⟧A = x
 ⟦ e1 ⊕ e2 ⟧A = ⟦ e1 ⟧A + ⟦ e2 ⟧A
\end{code}

\begin{code}
 data A+L : I → Set where
  [_]       : ∀ {i}  → Ty i → A+L i
  _⊕_       : A+L nat → A+L nat → A+L nat
  _=?_      : ∀ {i} → A+L i → A+L i → A+L bool
  if_th_el_ : ∀ {i} → A+L bool → A+L i → A+L i → A+L i
\end{code}

\begin{code}
 _≟_ : ∀ {i} → Ty i → Ty i → Bool
 _≟_ {bool} true    true    = true
 _≟_ {bool} false   false   = true
 _≟_ {bool} _       _       = false
 _≟_ {nat } zero    zero    = true
 _≟_ {nat } (suc m) (suc n) = m ≟ n
 _≟_ {nat } _       _       = false
\end{code}

\begin{code}
 ⟦_⟧A+L : ∀ {i} → A+L i → Ty i
 ⟦ [ x ]            ⟧A+L = x
 ⟦ e1 ⊕ e2          ⟧A+L = ⟦ e1 ⟧A+L + ⟦ e2 ⟧A+L
 ⟦ e1 =? e2         ⟧A+L = ⟦ e1 ⟧A+L ≟  ⟦ e2 ⟧A+L
 ⟦ if b th e1 el e2 ⟧A+L = if ⟦ b ⟧A+L then ⟦ e1 ⟧A+L else ⟦ e2 ⟧A+L
\end{code}

\begin{code}
 data AF (X : I → Set) : I → Set where
  [_] : ∀ {i} → Ty i  → AF X i
  _⊕_ : X nat → X nat → AF X nat

 data LF (X : I → Set) : I → Set where
  _=?_      : ∀ {i} → X i → X i → LF X bool
  if_th_el_ : ∀ {i} → X bool → X i → X i → LF X i
\end{code}

\begin{code}
 data μ (F : (I → Set) → I → Set)(i : I) : Set where
  In : F (μ F) i → μ F i
\end{code}

\begin{code}
 algAF : ∀ {i} → AF Ty i → Ty i
 algAF   [ x ] = x
 algAF (l ⊕ r) = l + r

 algLF : ∀ {i} → LF Ty i → Ty i
 algLF (l =? r        ) = l ≟ r
 algLF (if x th l el r) = if x then l else r
\end{code}

\begin{code}
module ModularFamilies where
\end{code}

\begin{code}
data U : Set where
 `I   : U
 `1   : U
 _`+_ : U → U → U
 _`×_ : U → U → U
\end{code}

\begin{code}
El : U → Set → Set
El `I       X = X
El `1       X = ⊤
El (L `+ R) X = El L X ⊎ El R X
El (L `× R) X = El L X × El R X
\end{code}

\begin{code}
data μ (F : U) : Set where
 In : El F (μ F) → μ F
\end{code}

