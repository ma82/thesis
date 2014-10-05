
\begin{code}
module thesis.Mu-A where

open import AD.Misc
open import thesis.Codes {Z}
open import thesis.Mu
open Nameless.AF hiding ([_] ; _⊕_)
\end{code}

\begin{code}
A : Set^ I _
A = μ `AF
\end{code}

\begin{code}
[_] : ∀ {i} → Ty i → A i
[ x ] = ⟨ inl _ , x , _ ⟩

_⊕_ : A nat → A nat → A nat
l ⊕ r = ⟨ inr _ , (refl , _) , ↑ l , ↑ r ⟩
\end{code}
