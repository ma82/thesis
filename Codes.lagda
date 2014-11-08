
\begin{code}
open import AD.Misc public
module thesis.Codes {lI : Level} where
\end{code}

\begin{code}
infixr 5 _`×_
\end{code}

\begin{code}
data De (I : Set lI) : Set (S lI) where
\end{code}

\begin{code}
  `I : (i : I) → De I
  `Σ `Π : (S : Set lI)(T : S → De I) → De I
\end{code}

\begin{code}
  `1   : De I
  _`×_ : De I → De I → De I
\end{code}

\begin{code}
`K : ∀ {I} → Set lI → De I
`K S = `Σ S λ _ → `1
\end{code}

\begin{code}
`ValF `AddF `ExpF : De ⊤
`ValF = `K (^ _ ℕ)
`AddF = `I _ `× `I _
`ExpF = `Σ Two ⊎.[ nκ `ValF , nκ `AddF ]
\end{code}

\begin{code}
ExtFor : ∀ {I} → De I → ∀ lE → Set _
ExtFor (`I k  ) _  = ⊤
ExtFor (`Σ S T) lE = Π S λ s → ExtFor (T s) lE
ExtFor (`Π S T) lE = Ext lI lE
ExtFor (`1    ) _  = ⊤
ExtFor (L `× R) lE = ExtFor L lE × ExtFor R lE
\end{code}

\begin{code}
extFor : ∀ {I lE} → Ext lI lE → (D : De I) → ExtFor D lE
extFor e (`I k  ) = tt
extFor e (`Σ S T) = λ s → extFor e (T s)
extFor e (`Π S T) = e
extFor e (`1    ) = tt
extFor e (L `× R) = extFor e L , extFor e R
\end{code}

\begin{code}
⟦_⟧ : ∀ {I} → De I → ∀ {lX} → ★^ I lX → ★ (lX ⊔ lI)
⟦ `I i   ⟧ X = ^ lI (X i)
⟦ `Σ S T ⟧ X = Σ S λ s → ⟦ T s ⟧ X
⟦ `Π S T ⟧ X = Π S λ s → ⟦ T s ⟧ X
⟦ `1     ⟧ _ = ⊤
⟦ L `× R ⟧ X = ⟦ L ⟧ X × ⟦ R ⟧ X
\end{code}

\begin{code}
ExpF : Set lI → Set _
ExpF X = ⟦ `ExpF ⟧ λ _ → X
\end{code}

\begin{code}
module ExpF where
\end{code}

\begin{code}
 [_] : ∀ {X} → ℕ → ExpF X
 _⊕_ : ∀ {X} → X → X → ExpF X
\end{code}

\begin{code}
 [ n ] = inl _ , ↑ n , _
 l ⊕ r = inr _ , ↑ l , ↑ r
\end{code}

\begin{code}
module _ {I} where
\end{code}

\begin{code}
 ′1 : De I
 ′1 = `Π ⊥ ⊥-elim

 _′×_ : De I → De I → De I
 L ′× R = `Π Two ⊎.[ κ L , κ R ]
\end{code}

\begin{code}
module Redundant {I : Set lI}{lX}{X : ★^ I lX} where
\end{code}

\begin{code}
 `1→′1 : ⟦ `1 ⟧ X → ⟦ ′1 ⟧ X
 `1→′1 _ = ⊥-elim

 ′1→`1 : ⟦ ′1 ⟧ X → ⟦ `1 ⟧ X
 ′1→`1 _ = _

 `×→′× : ∀ {L R} → ⟦ L `× R ⟧ X → ⟦ L ′× R ⟧ X
 `×→′× (l , r) = ⊎.[ κ l , κ r ]

 ′×→`× : ∀ {L R} → ⟦ L ′× R ⟧ X → ⟦ L `× R ⟧ X
 ′×→`× p = p (inl _) , p (inr _)
\end{code}

\begin{code}
module _ {I}{lX}{X : ★^ I lX}{lY}{Y : ★^ I lY} where
\end{code}

\begin{code}
 ⟦_⟧map : (D : De I) → X ⇛ Y → ⟦ D ⟧ X → ⟦ D ⟧ Y
 ⟦ `I k   ⟧map f (↑ x)   = ↑ (f k x)
 ⟦ `Σ S T ⟧map f (s , t) =   s , ⟦ T s ⟧map f t
 ⟦ `Π S T ⟧map f g       = λ s → ⟦ T s ⟧map f (g s)
\end{code}

\begin{code}
 ⟦     `1 ⟧map f _         = tt
 ⟦ L `× R ⟧map f (ls , rs) = ⟦ L ⟧map f ls , ⟦ R ⟧map f rs
\end{code}

\begin{code}
mapExpF : ∀ {X Y} → (X → Y) → ExpF X → ExpF Y
mapExpF f = ⟦ `ExpF ⟧map (κ f)
\end{code}

\begin{code}
module _ {I : Set lI}{lX}{X : ★^ I lX} where
  
 private l = lI ⊔ lX
\end{code}

\begin{code}
 ⟦_,_⟧map-id⇛ : (D : De I)(eD : ExtFor D l) → ⟦ D ⟧map (id⇛ {X = X}) Π≡ id
 ⟦ `I n   , _   ⟧map-id⇛ (↑ x)   = <>
 ⟦ `Σ S T , eT  ⟧map-id⇛ (s , t) = ,_ $≡ ⟦ T s , eT s ⟧map-id⇛ t
 ⟦ `Π S T , e   ⟧map-id⇛ f       = e λ s → ⟦ T s , extFor e (T s) ⟧map-id⇛ (f s)
\end{code}

\begin{code}
 ⟦ `1     , _   ⟧map-id⇛ _         = <>
 ⟦ L `× R , eLR ⟧map-id⇛ (ls , rs) = ap₂ _,_ (⟦ L , fst eLR ⟧map-id⇛ ls)
                                             (⟦ R , snd eLR ⟧map-id⇛ rs)
\end{code}

\begin{code}
module _ {I : Set lI}{lZ}{lX lY}
         {X : ★^ I lX}{Y : ★^ I lY}{Z : ★^ I lZ}{f : Y ⇛ Z}{g : X ⇛ Y}
         where

  private l = lI ⊔ lZ
\end{code}

\begin{code}
  ⟦_,_⟧map-∘⇛ : (D : De I)(e : ExtFor D l) →
                ⟦ D ⟧map f ∘ ⟦ D ⟧map g Π≡ ⟦ D ⟧map (f ∘⇛ g)
  ⟦ `I n   , _   ⟧map-∘⇛ (↑ x)   = <>
  ⟦ `Σ S T , eT  ⟧map-∘⇛ (s , t) = ,_ $≡ ⟦ T s , eT s ⟧map-∘⇛ t
  ⟦ `Π S T , e   ⟧map-∘⇛ f       = e λ s → ⟦ T s , extFor e (T s) ⟧map-∘⇛ (f s)
\end{code}

\begin{code}
  ⟦ `1     , _   ⟧map-∘⇛ _         = <>
  ⟦ L `× R , eLR ⟧map-∘⇛ (ls , rs) = ap₂ _,_ (⟦ L , fst eLR ⟧map-∘⇛ ls)
                                             (⟦ R , snd eLR ⟧map-∘⇛ rs)
\end{code}

\begin{code}
⟦_,_⟧map-cong : ∀ {I : Set lI}(D : De I){lX lY}(e : ExtFor D (lI ⊔ lY))
                  {X : ★^ I lX}{Y : ★^ I lY}
                  {f g : X ⇛ Y} → f ⇛≡ g → ⟦ D ⟧map f Π≡ ⟦ D ⟧map g
\end{code}

\begin{code}
⟦_,_⟧map-cong (`I k) _ p (↑ xs) = ↑_ $≡ p (k , xs)
⟦_,_⟧map-cong (`Σ S T) eT p (s , t) = ,_ $≡ ⟦ T s , eT s ⟧map-cong p t
⟦_,_⟧map-cong (`Π S T) e p f = e λ s → ⟦ T s , extFor e (T s) ⟧map-cong p (f s)
⟦_,_⟧map-cong `1 _ p xs = <>
⟦_,_⟧map-cong (L `× R) eLR p (ls , rs) = ap₂ _,_ (⟦ L , fst eLR ⟧map-cong p ls)
                                                 (⟦ R , snd eLR ⟧map-cong p rs)
\end{code}

\begin{code}
module _ {I : Set lI}{lX}{X : I → Set lX}{lP} where
 private l = lP ⊔ S lI
\end{code}

\begin{code}
 □ : (D : De I) → ★^Σ X lP → ★^ (⟦ D ⟧ X) l
 □ (`I k)   P (↑ x)   = ^ (S lI) (P (, x))
 □ (`Σ S T) P (s , t) = □ (T s) P t
 □ (`Π S T) P f       = Π S λ s → □ (T s) P (f s)
\end{code}

\begin{code}
 □ (`1)     P _         = ⊤
 □ (L `× R) P (ls , rs) = □ L P ls × □ R P rs
\end{code}

\begin{code}
module IH {I : Set lI}{lX}{X : ★^ I lX}{lP}(P : ★^Σ X lP) where
\end{code}

\begin{code}
 to : (D : De I) → ⟦ D ⟧ (Σ/ X P) → Σ (⟦ D ⟧ X) (□ D P)
 to (`I k)   (↑ (x , p)) = ↑ x , ↑ p
 to (`Σ S T) (s , t)     = (s , fst rec) , snd rec
                           where rec = to (T s) t
 to (`Π S T) f           = (fst ∘ rec)   , snd ∘ rec
                           where rec = λ s → to (T s) (f s)
\end{code}

\begin{code}
 to `1       _          = _
 to (L `× R) (ls , rs)  = (fst recL , fst recR) , (snd recL , snd recR)
                          where recL = to L ls ; recR = to R rs
\end{code}

\begin{code}
 fr : (D : De I) → Σ (⟦ D ⟧ X) (□ D P) → ⟦ D ⟧ (Σ/ X P)
 fr (`I k  ) (↑ x , ↑ ih)   = ↑ (x , ih)
 fr (`Σ S T) ((s , t) , ih) = s , fr (T s) (t , ih)
 fr (`Π S T) (f , ih)       = λ s → fr (T s) (f s , ih s)
\end{code}

\begin{code}
 fr `1       xs                        = tt
 fr (L `× R) ((ls , rs) , (ihL , ihR)) = fr L (ls , ihL) , fr R (rs , ihR)
\end{code}

\begin{code}
 fr∘to : (D : De I)(e : ExtFor D (lP ⊔ lX ⊔ lI)) → fr D ∘ to D Π≡ id
 fr∘to (`I k)   e (↑ x) = <>
 fr∘to (`Σ S T) e (s , t) = _,_ s $≡ fr∘to (T s) (e s) t
 fr∘to (`Π S T) e f = e λ s → fr∘to (T s) (extFor e (T s)) (f s)
\end{code}

\begin{code}
 fr∘to `1       e _ = <>
 fr∘to (L `× R) (eL , eR) (ls , rs) = ap₂ _,_ (fr∘to L eL ls) (fr∘to R eR rs)
\end{code}

\begin{code}
 module _ (⊘ : ∅) where

  to∘fr : (D : De I)(e : ExtFor D (lX ⊔ lI))(eP : ExtFor D (lP ⊔ S lI)) → to D ∘ fr D Π≡ id
  to∘fr (`I k)   e _ (_ , ↑ x) = ,_ ∘′ ↑_ $≡ <>
  to∘fr (`Σ S T) e eP ((s , t) , ih) = 
   let p , q = ≡→Σ≡ $ to∘fr (T s) (e s) (eP s) (t , ih) in
   let a =    ((λ st → □ (T (fst st)) P (snd st)))
           $≡ ((λ y → s , y) $≡ fst (≡→Σ≡ (to∘fr (T s) (e s) (eP s) (t , ih)))) in
   let b = □ (T s) P $≡ fst (≡→Σ≡ (to∘fr (T s) (e s) (eP s) (t , ih))) in
   Σ≡→≡ (,_ $≡ p , coe-erasable a b _ ⊚ q)
  to∘fr (`Π S T) e eP (f , ihT) =
   let rec = λ s → ≡→Σ≡ $ to∘fr (T s) (extFor e (T s)) (extFor eP (T s)) (f s , ihT s) in
   let a = (λ v → (s : S) → □ (T s) P (v s)) $≡
            e (λ s → fst (≡→Σ≡ (to∘fr (T s) (extFor e (T s))
                                            (extFor eP (T s))
                                            (f s , ihT s)))) in
   let b = λ s → □ (T s) P $≡ fst (≡→Σ≡ (to∘fr (T s) (extFor e  (T s))
                                                     (extFor eP (T s))
                                                     (f s , ihT s))) in
   Σ≡→≡ ( e  (λ s → fst (rec s)) , eP (λ s → ⊘ ⊚ snd (rec s)))
\end{code}

\begin{code}
  to∘fr `1       e _ _ = <>
  to∘fr (L `× R) (eL , eR) (eLP , eRP) ((ls , rs) , (ihL , ihR)) =
    let la , lb = ≡→Σ≡ $ to∘fr L eL eLP (ls , ihL) in
    let ra , rb = ≡→Σ≡ $ to∘fr R eR eRP (rs , ihR) in
    Σ≡→≡ (ap₂ _,_ la ra , Σ≡→≡ ((⊘ ⊚ lb) , ⊘ ⊚ rb))
\end{code}

\begin{code}
  l⊔ = S lI ⊔ lX ⊔ lP

  ⟦Σ⟧≅Σ⟦⟧□ : (D : De I) → ⟦ D ⟧ (Σ/ X P) Ext l⊔ , l⊔ →≅ Σ (⟦ D ⟧ X) (□ D P)
  ⟦Σ⟧≅Σ⟦⟧□ D =
    iso (to D) (fr D) (λ e → ↓ext l⊔ l⊔ e (fr∘to D (extFor (↓ext l⊔ l⊔ e) D)))
                      (λ e → ↓ext l⊔ l⊔ e (to∘fr D (extFor (↓ext l⊔ l⊔ e) D)
                                                   (extFor (↓ext l⊔ l⊔ e) D)))
\end{code}

\begin{code}
module _ {I : Set lI}{lX : _}{X : I → Set lX}{lY : _}{Y : I → Set lY} where
 open IH
\end{code}

\begin{code}
 □→⟦⟧ : (D : De I) → ∀ i → □ {X = X} D (Y ∘ fst) i → ⟦ D ⟧ Y
 □→⟦⟧ D = cu (⟦ D ⟧map snd/ ∘ fr _ D)
\end{code}

\begin{code}
module _ {I : Set lI}{lX}{X : ★^ I lX}{lP}{P : ★^Σ X lP} where
\end{code}

\begin{code}
 ◽ : (D : De I) → Π _ P → Π _ (□ D P)
 ◽ (`I i  ) f (↑ xs ) = ↑ f (, xs)
 ◽ (`Σ S T) f (s , t) = ◽ (T s) f t
 ◽ (`Π S T) f g       = λ s → ◽ (T s) f (g s)
\end{code}

\begin{code}
 ◽ `1 f xs = tt
 ◽ (L `× R) f (ls , rs) = ◽ L f ls , ◽ R f rs
\end{code}

\begin{code}
module Nameless where
\end{code}

\begin{code}
 _▻_ = λ (O N : Set lI) → N → De O
\end{code}

\begin{code}
 ⟪_⟫ : ∀ {O N} → (F : O ▻ N) → ∀ {lX} → ★^ O lX → ★^ N _
 ⟪ F ⟫ X n = ⟦ F n ⟧ X
\end{code}

\begin{code}
 En = λ I → I ▻ I
\end{code}

\begin{code}
 module AF where

  data I : Set lI where
   nat bool : I

  open import Data.Bool

  Ty : I → Set lI
  Ty nat  = ^ _ ℕ
  Ty bool = ^ _ Bool
\end{code}

\begin{code}
  `AF : En I
  `AF i = `Σ Two ⊎.[ nκ (`K (Ty i)) , nκ (`K (i == nat) `× `I nat `× `I nat) ]

  AF : ★^ I lI → ★^ I lI
  AF = ⟪ `AF ⟫
\end{code}

\begin{code}
  [_] : ∀ {X i} → Ty i → AF X i
  [ x ] = inl _ , x , _

  _⊕_ : ∀ {X} → X nat → X nat → AF X nat
  l ⊕ r = inr _ , (refl , _) , ↑ l , ↑ r
\end{code}

\begin{code}
 module _ {O N}{lX}{X : ★^ O lX}{lY}{Y : ★^ O lY} where
\end{code}

\begin{code}
  ⟪_⟫map : (F : O ▻ N) → X ⇛ Y → ⟪ F ⟫ X ⇛ ⟪ F ⟫ Y
  ⟪ F ⟫map f i = ⟦ F i ⟧map f
\end{code}

\begin{code}
 module _ {O N}{lX}{X : ★^ O lX}{lP} where
\end{code}

\begin{code}
  □/ : (F : O ▻ N) → ★^Σ X lP → ★^Σ (⟪ F ⟫ X) _
  □/ F X (n , xs) = □ (F n) X xs
\end{code}

\begin{code}
 module _ {O N} where
\end{code}

\begin{code}
  ExtFor/ = λ (F : O ▻ N) l → ∀ i → ExtFor (F i) l
\end{code}

\begin{code}
 module _ {I : Set lI} where
\end{code}

\begin{code}
  _alg>_ : (F : En I) → ∀ {lY} → ★^ I lY → _
  F alg> Y = ⟪ F ⟫ Y ⇛ Y

  _-ALG_ : En I → ∀ lY → Set _
  F -ALG lY = Σ (★^ _ lY) (_alg>_ F)
\end{code}

\begin{code}
 module _ {O N : Set lI} where
  infixr 6 _pt[_]>_ _pt>_ _nt[_]>_ _nt>_
\end{code}

\begin{code}
  _pt[_]>_ : (F : O ▻ N) → ∀ l (G : O ▻ N) → Set _
  F pt[ l ]> G = (X : ★^ O l) → ⟪ F ⟫ X ⇛ ⟪ G ⟫ X
\end{code}

\begin{code}
  _pt>_ : (F G : O ▻ N) → Set _
  F pt> G = (X : ★^ _ lI) → ⟪ F ⟫ X ⇛ ⟪ G ⟫ X
\end{code}

\begin{code}
  isNat : (F G : O ▻ N) → ∀ {l} → F pt[ l ]> G → Set _
  isNat F G α = ∀ {A B}(f : A ⇛ B) → α B ∘⇛ ⟪ F ⟫map f ⇛≡ ⟪ G ⟫map f ∘⇛ α _
\end{code}

\begin{code}
  _nt[_]>_ : ∀ (F : O ▻ N) l (G : N → De O) → Set _
  F nt[ l ]> G = Σ (F pt[ l ]> G) (isNat F G)
\end{code}

\begin{code}
  _nt>_ : (F G : O ▻ N) → Set _
  F nt> G = F nt[ lI ]> G
\end{code}

\begin{code}
`return : ∀ {I} → I → De I
`return = `I

infix 8 _`>>=_

_`>>=_ : ∀ {O N} → De N → (N → De O) → De O
`I k     `>>= F = F k
`Σ S T   `>>= F = `Σ S λ s → T s `>>= F
`Π S T   `>>= F = `Π S λ s → T s `>>= F
\end{code}

\begin{code}
`1       `>>= F = `1
(L `× R) `>>= F = L `>>= F `× R `>>= F

`map : ∀ {A B} → (A → B) → De A → De B
`map f D = D `>>= `return ∘ f

open Nameless
\end{code}

\begin{code}
_`∘_ : ∀ {A B C} → B ▻ C → A ▻ B → A ▻ C
(F `∘ G) c = F c `>>= G
\end{code}

\begin{code}
module _ {O N : Set lI} where
\end{code}

\begin{code}
 `ΔF : (δ : N → O) → O ▻ N
 `ΔF δ   = `I ∘ δ
\end{code}

\begin{code}
 `ΣF : (σ : O → N) → O ▻ N
 `ΣF σ n = `Σ (σ ⁻¹ n) (`I ∘ fst)
\end{code}

\begin{code}
 `ΠF : (π : O → N) → O ▻ N
 `ΠF π n = `Π (π ⁻¹ n) (`I ∘ fst)
\end{code}

