
\begin{code}
module thesis.Nat where

open import AD.Misc hiding (_+_ ; zero ; suc)
open import thesis.Codes; open Nameless
open import thesis.Mu {Z}{⊤}
\end{code}

\begin{code}
data NatTags : Set where `zero `suc : NatTags

NatF : En ⊤
NatF _ = `Σ NatTags λ { `zero → `1 ; `suc → `I _ }

Nat : Set
Nat = μ NatF _
\end{code}

\begin{code}
zero : Nat
zero = ⟨ `zero , tt ⟩

suc : Nat → Nat
suc n = ⟨ `suc , ↑ n ⟩
\end{code}

\begin{code}
open Cata
open Elim
\end{code}

\begin{code}
+alg : NatF alg> nκ (Nat → Nat)
+alg _ (`zero , _) = id
+alg _ (`suc  , m) = suc ∘ ↓ m
\end{code}

\begin{code}
_+_ : Nat → Nat → Nat
_+_ = cata +alg _
\end{code}

\begin{code}
2+1≡3 : suc (suc zero) + suc zero ≡ suc (suc (suc zero))
2+1≡3 = <>
\end{code}

\begin{code}
+-associative : ∀ m n o → (m + n) + o ≡ m + (n + o)
+-associative = elim NatF P me ∘ ,_
 where P  : ⊤ × Nat → Set
       P (_ , m) = ∀ n o → (m + n) + o ≡ m + (n + o)
       me : NatF me> P
       me (α , `zero , xs) ih n o = <>
       me (α , `suc  , xs) ih n o = suc $≡ ↓_ ih n o
\end{code}

