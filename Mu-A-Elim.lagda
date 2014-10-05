
\begin{code}
module thesis.Mu-A-Elim where

open import AD.Misc
open import thesis.Codes {Z}
open import thesis.Mu
open Nameless.AF hiding ([_] ; _⊕_)
open import thesis.Mu-A
\end{code}

\begin{code}
elimA : (P : {i : I} → A i → Set) →
        (m[] : {i : I}(x : Ty i) → P {i} [ x ]) →
        (m⊕  : {l r : A nat} → P l → P r → P (l ⊕ r)) →
        {i : I}(x : A i) → P x
elimA P m[] m⊕ x = Elim.elim `AF M m (, x) where
  M : Mot `AF _
  M (i , a) = P {i} a
  m : `AF me> M
  m (_    , inl _ , (x    ,  _    ))                _  = m[] x
  m (.nat , inr _ , (refl ,  _) , _) (_ , ↑ hl , ↑ hr) = m⊕ hl hr
\end{code}

