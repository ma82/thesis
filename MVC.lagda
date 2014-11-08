
\begin{code}
open import AD
module thesis.MVC {lI lA}{A : Set lA} where
open import thesis.Sub; open Kit
open Functor
\end{code}

\begin{code}
record Lang {I : Set lI}{lD}(Dom : ★^ I lD) : Set (S lI ⊔ lD ⊔ lA) where
  constructor mk
  field    
    lang : En A I
    alg  : lang alg> Dom
open Lang public
\end{code}

\begin{code}
_[_]Lang+_ : {I : Set lI}{D : ★^ I lI} → Lang D → 1+ A → Lang D → Lang D
L1 [ a ]Lang+ L2 = mk (a ⟩ (lang L1 ⊕ lang L2)) [ alg L1 , alg L2 ]⟦⟧
\end{code}

\begin{code}
  where open TreeCase a
\end{code}

\begin{code}
record MVC {O N : Set lI}{DSo : ★^ N lI}{DTa : ★^ O lI}
           (So : Lang DSo)(H : Functor O N lI lI)(Ta : Lang DTa)
           {lP}(_ℝ_ : ∀ {i} → DSo i → ∣ H ∣ DTa i → Set lP)
           : Set (S lI ⊔ S lP ⊔ lA) where

  constructor mk

  private
    SoF = lang So ; module So = Cata {F = SoF}
    TaF = lang Ta ; module Ta = Cata {F = TaF}
\end{code}

\begin{code}
  eval : μ SoF ⇛ DSo
  eval = So.cata (alg So)

  exec : μ TaF ⇛ DTa
  exec = Ta.cata (alg Ta)
\end{code}

\begin{code}
  field
    compAlg : lang So alg> ∣ H ∣ (μ (lang Ta))
\end{code}

\begin{code}
  comp : μ SoF ⇛ ∣ H ∣ (μ TaF)
  comp = So.cata compAlg
\end{code}

\begin{code}
  field
    OK : (G : Sup SoF) → let G , p = G in
         (β : G alg> _) → alg So  <:alg[ p ] β →
         (γ : G alg> _) → compAlg <:alg[ p ] γ →
         let module G = Cata {F = G} in
         let P = uc λ n x → G.cata β n x ℝ ∣ H ∣map exec _ (G.cata γ _ x) in
         ∀ n,xs → let n , xs = n,xs in
         □/ SoF P (n , xs) →
\end{code}

\begin{code}
           alg So _ (G.mapCata β (SoF `$ n) xs)
         ℝ ∣ H ∣map exec _ (compAlg _ (G.mapCata γ (SoF `$ n) xs))
\end{code}

\begin{code}
  ok : (n : N)(x : μ SoF n) → eval _ x  ℝ  ∣ H ∣map exec _ (comp n x)
  ok = cu $ Elim.elim SoF _ (OK (SoF , []) (alg So) (λ _ → <>) compAlg (λ _ → <>))
\end{code}

\begin{code}
module MVC+ {O N : Set lI}{DSo : ★^ N lI}{DTa : ★^ O lI}
            (S1 S2 : Lang DSo)(H : Functor O N _ lI)(T : Lang DTa)
            {lP}(_ℝ_ : ∀ {i} → DSo i → ∣ H ∣ DTa i → Set lP)
            (a : 1+ A) where
\end{code}

\begin{code}
 open TreeCase {O = N}{N} a
\end{code}

\begin{code}
 private
  S12 = S1 [ a ]Lang+ S2; F1 = lang S1; F2 = lang S2; F12 = a ⟩ (F1 ⊕ F2)
  TF = lang T
\end{code}

\begin{code}
 _MVC+_ : MVC S1 H T _ℝ_ → MVC S2 H T _ℝ_ → MVC S12 H T _ℝ_
 (mk c1 m1) MVC+ (mk c2 m2) = mk [ c1 , c2 ]⟦⟧ m where
\end{code}

\begin{code}
  m : ∀ G β _ γ _ xs → _ → _
  m (G , <) β <β γ <γ (n , « _ , ls) ih =
   m1 (G , <:-invL <) β (uc λ n xs →   β n $≡ (inj≡inj∘inj _ < (n , xs))
                                     ⊚ <β (n , « _ , snd xs))
                      γ (uc λ n xs →   γ n $≡ (inj≡inj∘inj _ < (n , xs))
                                     ⊚ <γ (n , « _ , snd xs))
                      (n , _ , ls) ih
  m (G , <) β <β γ <γ (n , » _ , rs) ih = 
   m2 (G , <:-invR <) β (uc λ n xs →   β n $≡ (inj≡inj∘inj _ < (n , xs))
                                    ⊚ <β (n , » _ , snd xs))
                      γ (uc λ n xs →   γ n $≡ (inj≡inj∘inj _ < (n , xs))
                                    ⊚ <γ (n , » _ , snd xs))
                      (n , _ , rs) ih
\end{code}

