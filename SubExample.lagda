
\begin{code}
module thesis.SubExample where

open import AD.Misc
open import thesis.Codes {Z}
open import thesis.Mu
open Nameless.AF hiding ([_] ; _⊕_)
open import thesis.Sub
open Kit
\end{code}

\begin{code}
module _ {A I : Set}(A B C D : En A I) where
\end{code}

\begin{code}
 B<A+B+C+D : B <: A [⊕] B [⊕] C [⊕] D
 B<A+B+C+D = ]> (<[ [])
\end{code}

\begin{code}
module _ {A I : Set}(F : En A I) where
\end{code}

\begin{code}
 F<F+F₁ : F <: F [⊕] F
 F<F+F₁ = <[ []

 F<F+F₂ : F <: F [⊕] F
 F<F+F₂ = ]> []
\end{code}

\begin{code}
module PlusTimes {A I : Set}(F : I [ A ]▻ I)(`plus `times : A) where
\end{code}

\begin{code}
 Plus  = ¡ `plus  ⟩ F
 Times = ¡ `times ⟩ F

 Plus<:Plus+Times : Plus  <: Plus [⊕] Times
 Plus<:Plus+Times = <[ []

 Times<:Plus+Times : Times <: Plus [⊕] Times
 Times<:Plus+Times = ]> []
\end{code}
