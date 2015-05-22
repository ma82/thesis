
\begin{code}
open import AD.Misc public

module thesis.Mu {lI}{I : Set lI} where

open import thesis.Codes {lI}; open Nameless
\end{code}

\begin{code}
data μ (F : En I)(i : I) : Set lI where
  ⟨_⟩ : ⟪ F ⟫ (μ F) i → μ F i
\end{code}

\begin{code}
⟩_⟨ : {F : En I}{i : I} → μ F i → ⟦ F i ⟧ (μ F)
⟩ ⟨ xs ⟩ ⟨ = xs
\end{code}

\begin{code}
In : {F : En I} → F alg> μ F
In _ = ⟨_⟩
\end{code}

\begin{code}
module Cata {F : En I}{lY}{Y : Pow I lY}(α : F alg> Y) where
\end{code}

\begin{code}
 module No where
  {-# TERMINATING #-}
\end{code}

\begin{code}
  cata : μ F ⇛ Y
  cata i ⟨ xs ⟩ = α i (⟪ F ⟫map cata i xs)
\end{code}

\begin{code}
 mapCata  : (D : De I)(xs : ⟦ D ⟧ (μ F)) → ⟦ D ⟧ Y
 mapCata (`I k)   (↑ ⟨ xs ⟩) = ↑ (α k (mapCata (F k) xs))
 mapCata (`Σ S T) (s , t)    = , mapCata (T s) t
 mapCata (`Π S T)  f         = λ s → mapCata (T s) (f s)
\end{code}

\begin{code}
 mapCata  (`1    )  x         = tt
 mapCata  (L `× R) (l , r)    = mapCata L l , mapCata R r
\end{code}

\begin{code}
 cata : μ F ⇛ Y
 cata i x = ↓ mapCata (`I i) (↑ x)
\end{code}

\begin{code}
 mapCata-OK : (D : De I)(e : ExtFor D (lI ⊔ lY)) → mapCata D Π≡ ⟦ D ⟧map cata
 mapCata-OK (`I k  ) _ (↑ ⟨ xs ⟩) = <>
 mapCata-OK (`Σ S T) e (s , t)    = _,_ s $≡ mapCata-OK (T s) (e s) t
 mapCata-OK (`Π S T) e f          = e λ s → mapCata-OK (T s) (extFor e (T s)) (f s)
\end{code}

\begin{code}
 mapCata-OK (`1    ) _ _          = <>
 mapCata-OK (L `× R) e (ls , rs)  = ap₂ _,_ (mapCata-OK L (fst e) ls)
                                            (mapCata-OK R (snd e) rs)
\end{code}

\begin{code}
 module Init (eF : ExtFor/ F _)
             (k : μ F ⇛ Y)
             (h : α ∘⇛ ⟪ F ⟫map k ⇛≡ k ∘⇛ In) where

  mapInit : (D : De I)(eD : ExtFor D (lY ⊔ lI)) → mapCata D Π≡ ⟦ D ⟧map k
  mapInit (`I j  ) _   (↑ ⟨ xs ⟩) = ↑_ $≡ (α j $≡ mapInit (F j) (eF j) xs ⊚ h (, xs))
  mapInit (`Σ S T) eT  (s , t)    = _,_ s $≡ mapInit (T s) (eT s) t
  mapInit (`Π S T) e   f          = e λ s → mapInit (T s) (extFor e (T s)) (f s)
\end{code}

\begin{code}
  mapInit (`1)     _           xs = <>
  mapInit (L `× R) eLR (ls , rs)  = ap₂ _,_ (mapInit L (fst eLR) ls)
                                            (mapInit R (snd eLR) rs)
\end{code}

\begin{code}
  init : cata ⇛≡ k
  init (i , ⟨ xs ⟩) = α i $≡ mapInit (F i) (eF i) xs ⊚ h (i , xs)
\end{code}

\begin{code}
Mot = λ F lP → Pow/ (μ F) lP

_me>_ : ∀ (F : En I){lP} → Mot F lP → Set (lP ⊔ S lI)
F me> P = □/ F P ⇛ P ∘ Σ.< fst , ⟨_⟩ ∘ snd >

_-ME_ : En I → ∀ lP → Set _
F -ME lP = Σ (Mot F lP) (_me>_ F)
\end{code}

\begin{code}
module Elim (F : En I){lP}(P : Mot F lP)(m : F me> P) where
\end{code}

\begin{code}
 module No where
  {-# TERMINATING #-}
\end{code}

\begin{code}
  elim : Π _ P
  elim (i , ⟨ xs ⟩) = m (, xs) (◽ (F i) elim xs)
\end{code}

\begin{code}
 ◽Elim  : (D : De I)(xs : ⟦ D ⟧ (μ F)) → □ D P xs
 ◽Elim (`I k  ) (↑ ⟨ xs ⟩) = ↑ (m (, xs) (◽Elim (F k) xs))
 ◽Elim (`Σ S T) (s , t)    = ◽Elim (T s) t
 ◽Elim (`Π S T) f          = λ s → ◽Elim (T s) (f s)
\end{code}

\begin{code}
 ◽Elim  (`1    ) x         = tt
 ◽Elim  (L `× R) (l , r)   = ◽Elim L l , ◽Elim R r
\end{code}

\begin{code}
 elim : Π (Σ I (μ F)) P
 elim (i , ⟨ xs ⟩) = m (, xs) (◽Elim (F i) xs)
\end{code}

\begin{code}
module CataAp {F : En I}{lY}(eF : ∀ i → ExtFor (F i) (lI ⊔ lY))
              {Y : I → Set lY}
              (α β : F alg> Y)(p : α ⇛≡ β) where

  open Cata {F = F}

  mapCata-ap : (D : De I)(eD : ExtFor D (lY ⊔ lI)) →
               mapCata α D Π≡ mapCata β D
  mapCata-ap (`I k)   _   (↑ ⟨ xs ⟩) =
    ↑_ $≡ (p _ ⊚ β k $≡ (mapCata-ap (F k) (eF k) xs))
  mapCata-ap `1       _    xs        = <>
  mapCata-ap (L `× R) eLR (ls , rs)  = ap₂ _,_ (mapCata-ap L (fst eLR) ls)            
                                               (mapCata-ap R (snd eLR) rs)            
  mapCata-ap (`Σ S T) eT  (s , t)    = ,_ $≡ mapCata-ap (T s) (eT s) t                
  mapCata-ap (`Π S T) e   f          = e λ s → mapCata-ap (T s) (extFor e (T s)) (f s)

  cata-ap : cata α ⇛≡ cata β
  cata-ap (i , ⟨ xs ⟩) = p _ ⊚ β i $≡ mapCata-ap (F i) (eF i) xs
\end{code}

\begin{code}
module Fusion (F : En I){lY}(eF : ExtFor/ F (lI ⊔ lY))
              {lX}{X : Pow I lX}{Y : Pow I lY}
              (α : F alg> X)(β : F alg> Y)
              (k : X ⇛ Y)(h : β ∘⇛ ⟪ F ⟫map k ⇛≡ k ∘⇛ α) where

  open Cata {F = F}

  mapFusion : (D : _)(eD : ExtFor D (lI ⊔ lY)) →
              ⟦ D ⟧map k ∘ mapCata α D Π≡ mapCata β D
  mapFusion (`I k)   _   (↑ ⟨ xs ⟩) = ↑_ $≡ ((! h _) ⊚ (β k) $≡ (mapFusion (F k) (eF k) xs))
  mapFusion (`Σ S T) eT  (s , t)    = ,_ $≡ (mapFusion (T s) (eT s) t)
  mapFusion (`Π S T) e   f          = e λ s → mapFusion (T s) (extFor e (T s)) (f s)
\end{code}

\begin{code}
  mapFusion `1       _   xs         = <>
  mapFusion (L `× R) eLR (ls , rs)  = ap₂ _,_ (mapFusion L (fst eLR) ls)
                                              (mapFusion R (snd eLR) rs)
\end{code}

\begin{code}
  fusion : k ∘⇛ cata α ⇛≡ cata β
  fusion (i , ⟨ xs ⟩) = (! h _) ⊚ (β i) $≡ (mapFusion (F i) (eF i) xs)
\end{code}

\begin{code}
pt→alg : {F G : En I} → F pt> G → F alg> μ G
pt→alg t n xs = ⟨ t _ n xs ⟩

μhomap : {F G : En I} → F pt> G → μ F ⇛ μ G
μhomap {F} = cata ∘ pt→alg {F = F} where open Cata {F = F}
\end{code}

\begin{code}
module FunctorFusion (F : En I)(eF : ExtFor/ F lI)
                     (G : En I)(eG : ExtFor/ G lI)
                     {X : I → Set lI}
                     (α : G alg> X)(f# : F nt> G) where

  open Cata

  f = fst f#

  mapFFusion : (D : De I)(eD : ExtFor D lI) →
                    ⟦ D ⟧map (cata {F = G} α)
                  ∘ mapCata {F = F} (pt→alg {F = F} f) D
               Π≡   mapCata (α ∘⇛ f _) D

  mapFFusion (`I k)   _   (↑ ⟨ xs ⟩) = ↑_ $≡
    (α k $≡ (  mapCata-OK α (G k) (eG k) (f _ _ (mapCata _ (F k) xs))
             ⊚ (! snd f# (cata α) (k , mapCata _ (F k) xs))
             ⊚ (f X k $≡ (mapFFusion (F k) (eF k) xs))))
  mapFFusion (`Σ S T) eT  (s , t)    = ,_ $≡ mapFFusion (T s) (eT s) t
  mapFFusion (`Π S T) e   f          = e λ s → mapFFusion (T s) (extFor e (T s)) (f s)
  mapFFusion `1       _   xs         = <>
  mapFFusion (L `× R) eLR (ls , rs)  = ap₂ _,_ (mapFFusion L (fst eLR) ls)
                                               (mapFFusion R (snd eLR) rs)

  ffusion : cata {F = G} α ∘⇛ μhomap {F = F} f ⇛≡ cata (α ∘⇛ f _)
  ffusion (i , ⟨ xs ⟩) =
    α i $≡ (  mapCata-OK α (G i) (eG i) (f _ _ (mapCata _ (F i) xs))
            ⊚ (! snd f# (cata α) (i , mapCata _ (F i) xs))
            ⊚ f X i $≡ mapFFusion (F i) (eF i) xs)
\end{code}

\begin{code}
module _ {F : En I}{lY}{Y : Pow I lY} where
\end{code}

\begin{code}
 alg→me : F alg> Y → F me> (Y ∘ fst)
 alg→me α (i , xs) = α i ∘ □→⟦⟧ (F i) xs
\end{code}

\begin{code}
 cata' : F alg> Y → μ F ⇛ Y
 cata' = cu ∘ Elim.elim F _ ∘ alg→me
\end{code}

\begin{code}
_,_hpara>_ : ∀ (F H : En I){lY} → Pow I lY → Set _
F , H hpara> Y = ⟪ F ⟫ (μ H ×/ Y) ⇛ Y

_para>_ : ∀ (F : En I){lY} → Pow I lY → Set _
F para> Y = F , F hpara> Y
\end{code}

\begin{code}
_,_hnme>_ : ∀ (F H : En I){lY} → Pow I lY → Set _
F , H hnme> Y = □/ {X = μ H} F (Y ∘ fst) ⇛ Y ∘ fst

_nme>_ : ∀ (F : En I){lY} → Pow I lY → Set _
F nme> Y = F , F hnme> Y

private test : ∀ {F lY}{Y : Pow I lY} → (F nme> Y) ≡ (F me> (Y ∘ fst))
        test = <>
\end{code}

\begin{code}
module hpara↔hnme {lY}{Y : Pow I lY}(F H : En I) where

  module M = IH {X = μ H} (Y ∘ fst)

  to : F , H hpara> Y → F , H hnme> Y
  to α (i , xs) ih = α i (M.fr (F i) (xs , ih))

  fr : F , H hnme> Y → F , H hpara> Y
  fr α i xs = let ls , rs = M.to (F i) xs in α (i , ls) rs
\end{code}

\begin{code}
module para↔nme {lY}{Y} F = hpara↔hnme {lY}{Y} F F
\end{code}

\begin{code}
module Para {F : En I}{lY}{Y : Pow I lY}(α : F para> Y) where

 para : μ F ⇛ Y
 para = cu (Elim.elim F _ (para↔nme.to F α))
\end{code}

