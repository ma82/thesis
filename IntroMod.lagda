
\begin{code}
{-# OPTIONS --no-termination-check --no-positivity-check --copatterns #-}
module thesis.IntroMod where

open import AD.Misc hiding (true; false)
open import AD.Hints
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
 infixr 5 _:+:_

 _:+:_ : (Set → Set) → (Set → Set) → Set → Set
 (F :+: G) X = F X ⊎ G X
\end{code}

\begin{code}
 Exp' = μ (ExpF :+: TimesF)
\end{code}

\begin{code}

 record Func (F : Set → Set) : Set₁ where
   constructor func
   field
     unfunc : ∀ {A B} → (A → B) → F A → F B
 open Func

 cata : ∀ {F}⦃ map : Func F ⦄{X} → (F X → X) → μ F → X
 cata ⦃ map ⦄ α (In xs) = α (unfunc map (cata α) xs)
\end{code}

\begin{code}
 instance
   mapExpF   : Func ExpF
   mapTimesF : Func TimesF
   map+      : ∀ {F G}⦃ l : Func F ⦄ ⦃ r : Func G ⦄ → Func (F :+: G)
\end{code}

\begin{code}
   unfunc mapExpF                  f [ n   ] = [ n ]
   unfunc mapExpF                  f (l ⊕ r) = f l ⊕ f r
   unfunc mapTimesF                f (l ⊗ r) = f l ⊗ f r
   unfunc (map+ ⦃ mapF ⦄ ⦃ mapG ⦄) f (inl x) = inl (unfunc mapF f x)
   unfunc (map+ ⦃ mapF ⦄ ⦃ mapG ⦄) f (inr y) = inr (unfunc mapG f y)
\end{code}

\begin{code}
 algExpF : ExpF ℕ → ℕ
 algExpF [ n ]   = n
 algExpF (l ⊕ r) = l + r
\end{code}

\begin{code}
 ⟦_⟧Exp : Exp → ℕ
 ⟦_⟧Exp = cata algExpF
\end{code}

\begin{code}
 algTimesF : TimesF ℕ → ℕ
 algTimesF (l ⊗ r) = l * r

 ⟦_⟧Exp' : Exp' → ℕ
 ⟦_⟧Exp' = cata ⊎.[ algExpF , algTimesF ]
\end{code}

\begin{code}
 infix 3 _:<:_
 record _:<:_ (F G : Set → Set) : Set₁ where
   field
     un:<: : F ⇛ G
 open _:<:_

 instance
  injId : ∀ {F}                    → F :<: F      
  injL  : ∀ {F L R}⦃ p : F :<: L ⦄ → F :<: L :+: R
  injR  : ∀ {F L R}⦃ q : F :<: R ⦄ → F :<: L :+: R
  un:<: injId        _ x = x
  un:<: (injL ⦃ p ⦄) _ x = inl (un:<: p _ x)
  un:<: (injR ⦃ p ⦄) _ x = inr (un:<: p _ x)
\end{code}

\begin{code}
 [[_]] : ∀ {F}⦃ inj : ExpF :<: F ⦄ → ℕ → μ F
 [[_]] ⦃ inj ⦄ n = In (un:<: inj _ [ n ])

 infix 3 _[⊕]_

 _[⊕]_ : ∀ {F}⦃ inj : ExpF :<: F ⦄ → μ F → μ F → μ F
 _[⊕]_ ⦃ inj ⦄ e1 e2 = In (un:<: inj _ (e1 ⊕ e2))

 infix 4 _[⊗]_

 _[⊗]_ : ∀ {F}⦃ inj : TimesF :<: F ⦄ → μ F → μ F → μ F
 _[⊗]_ ⦃ inj ⦄ e1 e2 = In (un:<: inj _ (e1 ⊗ e2))
\end{code}

\begin{code}
 example : Exp'
 example = [[ 1 ]] [⊕] [[ 2 ]] [⊗] [[ 3 ]]
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

