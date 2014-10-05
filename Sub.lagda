
\begin{code}
module thesis.Sub {lI lA} where

open import AD.Misc
open import thesis.Codes
import thesis.Mu as Mu
\end{code}

\begin{code}
infixr 3 _⊕_ 
infix  7 _⟩_
\end{code}

\begin{code}
mutual

 record _[_]►_ (O : Set lI)(A : Set lA)(N : Set lI) : Set (S lI ⊔ lA) where
  inductive
  constructor _⟩_
  field
    name : 1+ A
    code : O [ A ]▻ N

 data _[_]▻_ (O : Set lI)(A : Set lA)(N : Set lI) : Set (S lI ⊔ lA) where
   [_] : (F   :   N → De O) → O [ A ]▻ N
   _⊕_ : (L R : O [ A ]► N) → O [ A ]▻ N
\end{code}

\begin{code}
open _[_]►_ public
\end{code}

\begin{code}
module _ {A : Set lA}{O N : Set lI} where

 open Nameless
\end{code}

\begin{code}
 module Easy where
\end{code}

\begin{code}
  _`$_ : {A : Set lA}{O N : Set lI} → O [ A ]► N → O ▻ N
  (_ ⟩ [ F ]  ) `$ n = F n
  (_ ⟩ (L ⊕ R)) `$ n = `Σ (name L +∋ name R) ⊎.[ (λ _ → L `$ n) , (λ _ → R `$ n) ]
\end{code}

\begin{code}
    where open _[_]►_ ; open import AD; open Manifest lI
\end{code}

\begin{code}
 open import AD.TagTree
 open Tree ; open ⟦⟧Tree {A = 1+ A}{lI}
\end{code}

\begin{code}
 tag▻ : O [ A ]▻ N → Tree▻ (1+ A)
 tag▻ [ F   ] = []
 tag▻ (L ⊕ R) = (name L , tag▻ (code L)) ** (name R , tag▻ (code R))

 code▻ : (F : O [ A ]▻ N) → ⟦ tag▻ F ⟧Tree▻ → N → De O
 code▻ [   F ]     t  n = F n
 code▻ (L ⊕ R) (« Ls) n = code▻ (code L) Ls n
 code▻ (L ⊕ R) (» Rs) n = code▻ (code R) Rs n

 _`$_ : O [ A ]► N → O ▻ N
 F `$ n = `Σ (⟦ tag▻ (code F) ⟧Tree▻) (code▻ (code F) § n)

 to▻ = _`$_
\end{code}

\begin{code}
 module TreeCase (a : 1+ A){lX}{X : Set^ O lX}{lY}{Y : Set^ N lY}
                 {F G : O [ A ]► N}
                 where

  open Nameless
\end{code}

\begin{code}
  [_,_]⟦⟧ : ⟪ to▻ F             ⟫ X ⇛ Y →
            ⟪ to▻ G             ⟫ X ⇛ Y →
            ⟪ to▻ (a ⟩ (F ⊕ G)) ⟫ X ⇛ Y
  [ α , β ]⟦⟧ n (« x , p) = α n (x , p)
  [ α , β ]⟦⟧ n (» x , p) = β n (x , p)
\end{code}

\begin{code}
module Kit where

 ExtFor/ : ∀ {A : Set lA}{O N} → O [ A ]► N → ∀ lE → Set (S (lI ⊔ lE))
 ExtFor/ F lE = ∀ n → ExtFor (F `$ n) lE

 extFor/ : ∀ {lE} → Ext lI lE → ∀ {O A N} → (F : O [ A ]► N) → ExtFor/ F lE
 extFor/ e F = extFor e ∘ _`$_ F

 ⟪_⟫ : ∀ {A : Set lA}{O N} → O [ A ]► N → ∀ {lX} → Op O N lX (lX ⊔ lI)
 ⟪ G ⟫ X n = ⟦ G `$ n ⟧ X
\end{code}

\begin{code}
 □/ : ∀ {A : Set lA}{O N : Set lI}(F : O [ A ]► N){lX}{X : Set^ O lX}{lP} →
        Set^Σ X lP → Set^Σ (⟪ F ⟫ X) _
 □/ F P (n , xs) = □ (F `$ n) P xs
\end{code}

\begin{code}
 module IH/ {A : Set lA}{O N : Set lI}{lX}{X : Set^ O lX}{lP}(P : Set^Σ X lP) where

  open IH P

  to/ : (F : O [ A ]► N) → ⟪ F ⟫ (Σ/ X P) ⇛ Σ/ (⟪ F ⟫ X) (□/ F P)
  to/ F n xs = to (F `$ n) xs

  fr/ : (F : O [ A ]► N) → Σ/ (⟪ F ⟫ X) (□/ F P) ⇛ ⟪ F ⟫ (Σ/ X P)
  fr/ F n xs = fr (F `$ n) xs

 module _ {A : Set lA}{O N : Set lI} where

  ⟪_⟫map : ∀ (F : O [ A ]► N){lX}{X : O → Set lX}{lY}{Y : O → Set lY} → 
           (f : X ⇛ Y) → ⟪ F ⟫ X ⇛ ⟪ F ⟫ Y
  ⟪ F ⟫map f n = ⟦ F `$ n ⟧map f

  ⟪_,_⟫map-id⇛ : ∀ F {lX}(eF : ExtFor/ F (lX ⊔ lI)){X : Set^ O lX} →
                 ⟪ F ⟫map {X = X} id⇛ ⇛≡ id⇛
  ⟪ F , eF ⟫map-id⇛ (n , xs) = ⟦ F `$ n , eF n ⟧map-id⇛ xs

  ⟪_,_⟫map-∘⇛ : ∀ F {lZ}(eF : ExtFor/ F (lI ⊔ lZ))
                {lX}{X : O → Set lX}{lY}{Y : O → Set lY}{Z : O → Set lZ}
                {f : Y ⇛ Z}{g : X ⇛ Y} →
                ⟪ F ⟫map f ∘⇛ ⟪ F ⟫map g ⇛≡ ⟪ F ⟫map (f ∘⇛ g)
  ⟪ F , eF ⟫map-∘⇛ (n , xs) = ⟦ F `$ n , eF n ⟧map-∘⇛ xs

  ⟪_,_⟫map-cong : ∀ F {lY}(e : ExtFor/ F (lI ⊔ lY))
                 {lX}{X : O → Set lX}{Y : O → Set lY}
                 {f g : X ⇛ Y} → f ⇛≡ g → ⟪ F ⟫map f ⇛≡ ⟪ F ⟫map g
  ⟪ F , eF ⟫map-cong p (n , xs) = ⟦ F `$ n , eF n ⟧map-cong p xs


  functor : ∀ (F : O [ A ]► N) {lX} eF → Functor O N lX (lX ⊔ lI)
  functor F eF = mk (mk ⟪ F ⟫ ⟪ F ⟫map) ⟪ F , eF ⟫map-id⇛ ⟪ F , eF ⟫map-∘⇛

  functor-ap : ∀ (F : O [ A ]► N) {lX} eF → FunctorAp O N lX (lX ⊔ lI)
  functor-ap F eF = mk (functor F eF) ⟪ F , eF ⟫map-cong

  □/→⟪⟫ : (F : O [ A ]► N) → 
          ∀ {lX}{X : Set^ O lX}{lY}{Y : Set^ O lY} → 
            □/ F {X = X} (Y ∘ fst) ⇛ ⟪ F ⟫ Y ∘ fst
  □/→⟪⟫ F (n , xs) = □→⟦⟧ (to▻ F n) xs
\end{code}

\begin{code}
 infixr 8 _`∙_

 _`∙_ : {A : Set lA}{O S N : Set lI} → S [ A ]► N → O [ A ]► S → O [ A ]► N
 (n ⟩   [ F ]) `∙ G = n ⟩ [ (λ n → F n `>>= _`$_ G) ]
 (n ⟩ (L ⊕ R)) `∙ G = n ⟩ (L `∙ G ⊕ R `∙ G)
\end{code}

\begin{code}
 En : Set lA → Set lI → Set _
 En A I = I [ A ]► I
\end{code}

\begin{code}
 <_> : ∀ {A O N} → O [ A ]▻ N → O [ A ]► N
 <_> = _⟩_ ε

 infixr 5 _[⊕]_

 _[⊕]_ : ∀ {A O N} → O [ A ]► N → O [ A ]► N → O [ A ]► N
 L [⊕] R = < L ⊕ R >
\end{code}

\begin{code}
 infixr 5 _[⊗]_
 _[⊗]_ : {A : _}{O N : _} → O [ A ]► N → O [ A ]► N → O [ A ]► N
 L [⊗] R = < [ (λ n → L `$ n `× R `$ n) ] >
\end{code}

\begin{code}
 module NT+ where

   infixr 6 _pt[_]>_ _pt>_ _nt[_]>_ _nt>_

   _pt[_]>_ : ∀ {A : Set lA}{O N}
                (F : O [ A ]► N)(l : _)(G : O [ A ]► N) → Set (S l ⊔ lI)
   F pt[ l ]> G = (X : Set^ _ l) → ⟪ F ⟫ X ⇛ ⟪ G ⟫ X

   isNat : ∀ {A : Set lA}{O N}(F G : O [ A ]► N){l : _} →
             F pt[ l ]> G → Set (S l ⊔ lI)
   isNat F G α = ∀ {A B}(f : A ⇛ B) → α B ∘⇛ ⟪ F ⟫map f ⇛≡ ⟪ G ⟫map f ∘⇛ α _

   _pt>_ : ∀ {A : Set lA}{O N}(F : O [ A ]► N)(G : O [ A ]► N) → Set (S lI)
   F pt> G = F pt[ lI ]> G

   _nt[_]>_ : ∀ {A : Set lA}{O N}
                (F : O [ A ]► N) l (G : O [ A ]► N) → Set (S l ⊔ lI)
   F nt[ l ]> G = Σ (F pt[ l ]> G) (isNat F G)

   _nt>_ : ∀ {A : Set lA}{O N}
             (F : O [ A ]► N)(G : O [ A ]► N) → Set (S lI)
   F nt> G = F nt[ lI ]> G
\end{code}

\begin{code}
 infix 6 _alg>_

 _alg>_ : {A : Set lA}{I : Set lI} →
          En A I → ∀ {lY} → (I → Set lY) → Set (lI ⊔ lY)
 F alg> Y = ⟪ F ⟫ Y ⇛ Y

 mapAlg : ∀ {A : Set lA}{I : Set lI}{lX}{X Y : I → Set lX}{F : En A I} →
          (X ⇛ Y) → (Y ⇛ X) → F alg> X → F alg> Y
 mapAlg {F = F} f g α n xs = f n (α n (⟪ F ⟫map g n xs))
\end{code}

\begin{code}
 Mot : ∀ {A I}(F : En A I) lP → Set (S lP ⊔ lI)
 Mot F = Mu.Mot (to▻ F)

 _me>_ : ∀ {A I}(F : En A I){lP} → Mot F lP → Set (lP ⊔ S lI)
 _me>_ = λ F → Mu._me>_ (to▻ F)

 μ : {A : Set lA}{I : Set lI}(F : En A I)(i : I) → Set lI
 μ = Mu.μ ∘ to▻

 module Cata {A}{I}{F : En A I} = Mu.Cata {F = to▻ F}
 module Elim {A}{I}(F : En A I) = Mu.Elim (to▻ F)

 open Mu public using (⟨_⟩)
\end{code}

\begin{code}
module _ {A : Set lA}{I : Set lI} where
 open Kit
 infix 2 _<:_
\end{code}

\begin{code}
 data _<:_ : En A I → En A I → Set (lA ⊔ S lI) where
   [] : ∀ {F}                            → F  <: F
   <[ : ∀ {L1 L2 R}{n : 1+ A} → L1 <: L2 → L1 <: n ⟩ (L2 ⊕ R )
   ]> : ∀ {L R1 R2}{n : 1+ A} → R1 <: R2 → R1 <: n ⟩ (L  ⊕ R2)
\end{code}

\begin{code}
 _<:∘_ : {F G H : En A I} → F <: G → G <: H → F <: H
 p <:∘ []   = p
 p <:∘ <[ q = <[ (p <:∘ q)
 p <:∘ ]> q = ]> (p <:∘ q)
\end{code}

\begin{code}
 <:∘-assoc : {F1 F2 F3 F4 : En A I}
             (p : F1 <: F2)(q : F2 <: F3)(r : F3 <: F4) →
             (p <:∘ q) <:∘ r ≡ p <:∘ (q <:∘ r)
 <:∘-assoc p q []     = <>
 <:∘-assoc p q (<[ r) = <[ $≡ <:∘-assoc p q r
 <:∘-assoc p q (]> r) = ]> $≡ <:∘-assoc p q r
\end{code}

\begin{code}
 open _[_]►_ 
\end{code}

\begin{code}
 <:-invL : {F G H : En A I}{n : 1+ A} → (n ⟩ (F ⊕ G)) <: H → F <: H
 <:-invL < = <[ [] <:∘ <
 <:-invR : {F G H : En A I}{n : 1+ A} → (n ⟩ (F ⊕ G)) <: H → G <: H
 <:-invR < = ]> [] <:∘ <
\end{code}

\begin{code}
 ¬<:L : {F G : En A I}{n : 1+ A} → n ⟩ (F ⊕ G) <: F → ⊥Z
 ¬<:R : {F G : En A I}{n : 1+ A} → n ⟩ (F ⊕ G) <: G → ⊥Z
 ¬<:L {F = n ⟩ (L ⊕ R)} (<[  p) = ¬<:L (<:-invL p)
 ¬<:L {F = n ⟩ (L ⊕ R)} (]>  p) = ¬<:R (<:-invL p)
 ¬<:R {G = n ⟩ (L ⊕ R)} (<[  p) = ¬<:L (<:-invR p)
 ¬<:R {G = n ⟩ (L ⊕ R)} (]>  p) = ¬<:R (<:-invR p)
\end{code}

\begin{code}
 <:-antisym : {F G : En A I} → F <: G → G <: F → F ≡ G
 <:-antisym []          []  = <>  
 <:-antisym []      (<[  q) = <>  
 <:-antisym []      (]>  q) = <>  
 <:-antisym (<[  p)      q  = magic (¬<:L (q <:∘ p))
 <:-antisym (]>  p)      q  = magic (¬<:R (q <:∘ p))
\end{code}

\begin{code}
 open Kit; open NT+
\end{code}

\begin{code}
 inj : ∀ {l}{F G : En A I}⦃ p : F <: G ⦄ → F pt[ l ]> G
 inj ⦃ []   ⦄ _ _ xs = xs
 inj ⦃ <[ p ⦄ _ _ xs = let t , ys = inj _ _ xs in « t , ys
 inj ⦃ ]> p ⦄ _ _ xs = let t , ys = inj _ _ xs in » t , ys

 injNat : ∀ {l}{F G : En A I}⦃ p : F <: G ⦄ → isNat F G (inj {l} ⦃ p ⦄)
 injNat ⦃ []   ⦄ f _        = <>  
 injNat ⦃ <[ p ⦄ f (i , xs) = Σ.map (λ x → « x) id $≡ injNat ⦃ p ⦄ f (, xs)
 injNat ⦃ ]> p ⦄ f (i , xs) = Σ.map (λ x → » x) id $≡ injNat ⦃ p ⦄ f (, xs)

 inj# : ∀ {l}{F G : En A I}⦃ p : F <: G ⦄ → F nt[ l ]> G
 inj# ⦃ p ⦄ = inj ⦃ p ⦄ , injNat ⦃ p ⦄
\end{code}

\begin{code}
 module _ {lX}{X : Set^ I lX}{i} where
\end{code}

\begin{code}
  injectivity-inj : {F G : En A I}⦃ p : F <: G ⦄ →
                    ∀ {as bs} → inj ⦃ p ⦄ X i as ≡ inj ⦃ p ⦄ X i bs → as ≡ bs
  injectivity-inj                    ⦃ []   ⦄                   h = h
  injectivity-inj {F} {n ⟩ (L2 ⊕ R)} ⦃ <[ p ⦄ {tx , x} {ty , y} h =
    injectivity-inj ⦃ p ⦄ (Σ≡→≡ (Σ.map «-inj (λ {a} p → help a p ⊚ p) (≡→Σ≡ h)))
    where help = λ a p → coe-erasable ((λ s → ⟦ code▻ (code L2) s i ⟧ X) $≡ «-inj a)
                                      ((λ s → ⟦ code▻ (L2 ⊕ R ) s i ⟧ X) $≡       a)
                                      (snd (inj X i (tx , x)))
  injectivity-inj {F} {n ⟩ (L ⊕ R2)} ⦃ ]> p ⦄ {tx , x} {ty , y} h =
    injectivity-inj ⦃ p ⦄ (Σ≡→≡ (Σ.map »-inj (λ {a} p → help a p ⊚ p) (≡→Σ≡ h)))
    where help = λ a p → coe-erasable ((λ s → ⟦ code▻ (code R2) s i ⟧ X) $≡ »-inj a)
                                      ((λ s → ⟦ code▻ (L  ⊕ R2) s i ⟧ X) $≡       a)
                                      (snd (inj X i (tx , x)))
\end{code}

\begin{code}
 module _ {lX}{X : Set^ I lX} where
\end{code}

\begin{code}
  inj≡inj∘inj : ∀ {F G H}(p : F <: G)(q : G <: H) →
                  inj ⦃ p <:∘ q ⦄ X ⇛≡ inj ⦃ q ⦄ _ ∘⇛ inj ⦃ p ⦄ _
  inj≡inj∘inj p []      (i , xs) = <>  
  inj≡inj∘inj p (<[  q) (i , xs) = Σ.map (λ x → « x) id $≡ inj≡inj∘inj p q (, xs)
  inj≡inj∘inj p (]>  q) (i , xs) = Σ.map (λ x → » x) id $≡ inj≡inj∘inj p q (, xs)
\end{code}

\begin{code}
 module _ {lX}{X : Set^ I lX}{lP}{P : Set^Σ X lP} where

  □inj : {F G : En A I}⦃ < : F <: G ⦄ →
         □/ F P ⇛ □/ G P ∘ mapΣ id (inj ⦃ < ⦄ _)
\end{code}

\begin{code}
  □inj ⦃ []    ⦄ (n , xs) ih = ih
  □inj ⦃ <[  _ ⦄ (n , xs) ih = □inj (n , xs) ih
  □inj ⦃ ]>  _ ⦄ (n , xs) ih = □inj (n , xs) ih
\end{code}

\begin{code}
 module _ {lX}{X : Set^ I lX}{lY}{Y : Set^ I lY} where
\end{code}

\begin{code}
  me-inj-<: : {F G H : En A I}(p : F <: G)(q : G <: H)
              (β : (i : I)(xs : ⟪ H ⟫ X i) → □/ H (Y ∘ fst) (i , xs) → Y i) →
              (i : I)(xs : ⟪ F ⟫ X i)(ih : □/ F (Y ∘ fst) (i , xs)) →
                β i (inj ⦃ p <:∘ q ⦄ _ i xs) (□inj ⦃ p <:∘ q ⦄ (i , xs) ih)
              ≡ β i (inj ⦃ q ⦄ _ i (inj ⦃ p ⦄ _ i xs))
                    (□inj ⦃ q ⦄ (i , inj ⦃ p ⦄ _ i xs) (□inj ⦃ p ⦄ (i , xs) ih))
  me-inj-<: p []                β i xs ih = <>
  me-inj-<: p (<[  {L2 = L2} q) β i xs ih =
    me-inj-<: p q (λ i xs → β i (« _ , snd xs)) i xs ih
  me-inj-<: p (]>  {R2 = R2} q) β i xs ih =
    me-inj-<: p q (λ i xs → β i (» _ , snd xs)) i xs ih
\end{code}

\begin{code}
 import thesis.Mu as Mu
\end{code}

\begin{code}
 => : ∀ {F G : En A I}⦃ p : F <: G ⦄{i} → ⟪ F ⟫ (μ G) i → μ G i
 => xs = ⟨ inj _ _ xs ⟩
\end{code}

\begin{code}
 Sub : (F : En A I) → Set _
 Sub F = Σ _ λ G → G <: F
\end{code}

\begin{code}
 mapSub : {G H : En A I} → G <: H → Sub G → Sub H
 mapSub p (_ , q) = _ , q <:∘ p
\end{code}

\begin{code}
 subs : (F : En A I) → List (Sub F)
 subs (n ⟩   [ F ]) = (_ , []) ∷ []
 subs (n ⟩ (L ⊕ R)) = (_ , []) ∷    mapL (mapSub (<[ [])) (subs L)
                                 ++ mapL (mapSub (]> [])) (subs R)
\end{code}

\begin{code}
 Sup : (F : En A I) → Set _
 Sup F = Σ _ λ G → F <: G

 pamSup : {H F : En A I} → H <: F → Sup F → Sup H
 pamSup p (_ , q) = _ , p <:∘ q
\end{code}

\begin{code}
 open Pointed (lA ⊔ S lI)
\end{code}

\begin{code}
 smartSubs<: : ∀ {F G} → F <: G → List ★∙
 smartSubs<: F<G = mapL (λ { (H , H<G) → _ , H<G }) (mapL (mapSub F<G) (subs _))

 smartSubs : (F : En A I) → List ★∙
 smartSubs F = smartSubs<: {F = F} []
\end{code}

\begin{code}
 -- postulate
 --  a b : A


 -- postulate
 --  i : I
 --  x : ⟪ F ⟫ (μ H) i

 -- y : μ H i
 -- y = => {!#!} where open 8Points (smartSubs G) 0
\end{code}

\begin{code}
 module _ {lX}{X : Set^ I lX}{F G : En A I} where
\end{code}

\begin{code}
  _<:alg[_]_ : F alg> X → F <: G → G alg> X → Set _
  α <:alg[ < ] β = β ∘⇛ inj _ ⇛≡ α
\end{code}

\begin{code}
 _spara>_ :  ∀ (F : En A I){lY} → Set^ I lY → Set _
 F spara> Y = (HS : Sup F) → (to▻ F) Mu., to▻ (fst HS) hpara> Y
\end{code}

\begin{code}
 module spara<: {F G : En A I}{lY}{Y : Set^ I lY} where

   _spara[_]<:_ : F spara> Y → F <: G → G spara> Y → Set _
   α spara[ p ]<: β = ∀ H n xs →   β H n (inj ⦃ p ⦄ _ n xs)
                                 ≡ α (fst H , p <:∘ snd H) n xs

 open spara<: public

 module _ {F G : En A I}{lY}{Y : Set^ I lY} where

   sparaSub : F spara> Y → (G <: F) → Set _
   sparaSub α < = Σ _ λ β → β spara[ < ]<: α

   sparaSup : F spara> Y → (F <: G) → Set _
   sparaSup α < = Σ _ λ β → α spara[ < ]<: β
\end{code}

\begin{code}
 open import AD.TagTree

 _−_ : ∀ {F} G → F <: G → En A I
 (n ⟩ (L ⊕ R)) − (<[ <) = n ⟩ ((L − <) ⊕ R)
 (n ⟩ (L ⊕ R)) − (]> <) = n ⟩ (L ⊕ (R − <))
 G             − []     = ε ⟩ [ (λ _ → `K ⊥) ]

 _+alg[_]_ : ∀ {F G}{lY}{Y : Set^ I lY} →
               F alg> Y → (< : F <: G) → (G − <) alg> Y → G alg> Y
 α +alg[ []   ] β = α
 α +alg[ <[ w ] β =
   λ i → uc (uc ⊎.[ (λ _ → cu ((α +alg[ w ] (β ∘⇛ (λ i → uc injL))) i))
                  , (λ _ t xs → β i (» t , xs))                         ])
 α +alg[ ]> w ] β =
   λ i → uc (uc ⊎.[ (λ _ t xs → β i (« t , xs))                         
                  , (λ _ → cu ((α +alg[ w ] (β ∘⇛ (λ i → uc injR))) i)) ])

 cata+- : ∀ {F G : En A I}(< : F <: G){lY}{Y : Set^ I lY} → 
            (+ : F alg> Y)(- : (G − <) alg> Y) → μ G ⇛ Y
 cata+- {G = G} w + - = Cata.cata {F = G} (+ +alg[ w ] -)
\end{code}

