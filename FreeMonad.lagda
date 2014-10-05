
\begin{code}
open import AD
\end{code}

\begin{code}
module thesis.FreeMonad {lA}{A : Set lA}{lI}{I : Set lI} where
\end{code}

\begin{code}
open import thesis.Codes
import thesis.Mu as Mu
open import thesis.Sub; open Kit; open TreeCase {A = A}{O = I}{I} ε
\end{code}

\begin{code}
_⋆_ : En A I → Set^ I lI → En A I
F ⋆ X = ε ⟩ (F ⊕ ε ⟩ [ `K ∘ X ])
\end{code}

\begin{code}
infixr 8 _✶_

_✶_ : (F : En A I) → Op I I lI lI
F ✶ X = μ (F ⋆ X)
\end{code}

\begin{code}
roll : {F : En A I}{X : Set^ I lI} → F alg> F ✶ X
roll i (t , xs) = ⟨ (« t , xs) ⟩

var  : {F : En A I}{X : Set^ I lI} → X ⇛ F ✶ X
var i v = ⟨ (» _ , v , _) ⟩
\end{code}

\begin{code}
module Cata✶ {lY}{F : En A I}{X : Set^ I lI}{Y : Set^ I lY} where

 open Cata {F = F ⋆ X}
\end{code}

\begin{code}
 cata✶ : F alg> Y → X ⇛ Y → F ✶ X ⇛ Y
 cata✶ α ξ = cata [ α , ξ ∘⇛ fst/ ∘⇛ snd/ ]⟦⟧
\end{code}

\begin{code}
cata✶⊥ : ∀ {lY}{F : En A I}{Y : Set^ I lY} →
         F alg> Y → (F ✶ ⊥/) ⇛ Y
cata✶⊥ = Cata✶.cata✶ § magic/
\end{code}

\begin{code}
open NT+

✶⊥→μ-pt : {F : En A I} → F ⋆ ⊥/ pt> F
✶⊥→μ-pt X = [ id⇛ , magic/ ∘⇛ fst/ ∘⇛ snd/ ]⟦⟧

✶⊥→μ : {F : En A I} → F ✶ ⊥/ ⇛ μ F
✶⊥→μ {F} = Mu.μhomap (✶⊥→μ-pt {F = F})

μ→✶⊥-pt : {F : En A I} → F pt> F ⋆ ⊥/
μ→✶⊥-pt X n (t , xs) = « t , xs

μ→✶⊥ : {F : En A I} → μ F ⇛ F ✶ ⊥/
μ→✶⊥ {F} = Mu.μhomap (μ→✶⊥-pt {F = F})
\end{code}

\begin{code}
return : ∀ {F X i} → X i → F ✶ X $ i
return = var _
\end{code}

\begin{code}
↑return : ∀ {F X i l} → X i → ^ l (F ✶ X $ i)
↑return = ↑_ ∘ return
\end{code}

\begin{code}
extend : ∀ {F A B} → (A ⇛ F ✶ B) → F ✶ A ⇛ F ✶ B
extend = cata✶ roll
\end{code}

\begin{code}
 where open Cata✶
\end{code}

\begin{code}
_>>=_ : ∀ {F A B i} → F ✶ A $ i → (A ⇛ F ✶ B) → F ✶ B $ i
m >>= f = extend f _ m
\end{code}

\begin{code}
_>>_ : ∀ {F A B i} → F ✶ A $ i → (∀ i → F ✶ B $ i) → F ✶ B $ i
m >> n = m >>= λ i _ → n i
\end{code}

\begin{code}
_=>=_ : ∀ {F A B i j} → F ✶ [ A := j ] $ i  →
                 (A j → F ✶ B          $ j) →
                        F ✶ B          $ i
m =>= f = m >>= λ { ._ (<> , a) → f a }
\end{code}

\begin{code}
✑ : ∀ F i j (X : Set^ I lI) → Set lI
✑ F i j X = F ✶ [ X := j ] $ i

✑return : ∀ {F A i} → A i → ✑ F i i A
✑return a = return (<> , a)
\end{code}

\begin{code}
pure = ✑return

_⊗_ : ∀ {F i j k}{X Y} → ✑ F i j ((X ⇨ Y) ∘ κ k) → ✑ F j k X → ✑ F i k Y
fs ⊗ xs = fs =>= λ f → xs =>= λ x → pure (f x)
\end{code}

\begin{code}
join-alg : ∀ {F X} → (F ⋆ (F ✶ X)) alg> F ✶ X
join-alg = [ roll , fst/ ∘⇛ snd/ ]⟦⟧ 
\end{code}

\begin{code}
join : ∀ {F X} → F ✶ (F ✶ X) ⇛ F ✶ X
join = extend (λ _ → id)
\end{code}

\begin{code}
fmap-alg : ∀ {F A B} → (A ⇛ B) → F ⋆ A alg> F ✶ B
fmap-alg f = [ roll , var ∘⇛ f ∘⇛ fst/ ∘⇛ snd/ ]⟦⟧
\end{code}

\begin{code}
fmap : ∀ {F A B} → (A ⇛ B) → F ✶ A ⇛ F ✶ B
fmap f = extend (var ∘⇛ f)
\end{code}

\begin{code}
module Init✶ (F : En A I)(eF : ∀ {l} → ExtFor/ F l)
             {X : Set^ I lI}{lY}{Y : Set^ I lY}
             (α : F alg> Y)(ξ : X ⇛ Y)
             (k : F ✶ X ⇛ Y)
             (hr : α ∘⇛ ⟪ F ⟫map k ⇛≡ k ∘⇛ roll)
             (hv : ξ ⇛≡ k ∘⇛ var)
             where

 open Cata✶ {F = F}{X = X}{Y = Y}
 open Cata  {F = F ⋆ X}

 init✶ : cata✶ α ξ ⇛≡ k
 init✶ = Init.init [ α , ξ ∘⇛ fst/ ∘⇛ snd/ ]⟦⟧
                   (λ i → uc ⊎.[ κ (eF i) , _ ]) k
                    λ { (i , « t , ls   ) → hr (i , t , ls)
                      ; (i , » t , x , _) → hv (i , x)      }
\end{code}

\begin{code}
open NT+

module _ {F G : En A I} where

 pt→pt⋆ : ∀ {l} → F pt[ l ]> G → ∀ {X} → F ⋆ X pt[ l ]> G ⋆ X
 pt→pt⋆ f Y i (« t , xs) = let t , xs = f Y i (t , xs) in « t , xs
 pt→pt⋆ f Y i (» t , xs) = » t , xs

 nt→nt⋆ : ∀ {l} → F nt[ l ]> G → ∀ {X} → F ⋆ X nt[ l ]> G ⋆ X
 nt→nt⋆ (f , nat) {X} = f✶ , nat✶ where
  f✶ = pt→pt⋆ f {X}
  nat✶ : ∀ {A B}(g : A ⇛ B) →
         f✶ B ∘⇛ ⟪ F ⋆ X ⟫map g ⇛≡ ⟪ G ⋆ X ⟫map g ∘⇛ f✶ A
  nat✶ g (i , « t , xs) = (λ ■ → « (fst ■) , snd ■) $≡ nat g (i , t , xs)
  nat✶ g (i , » t , xs) = <>
\end{code}

\begin{code}
 inj⋆# : ⦃ _ : F <: G ⦄{X : Set^ I lI} → F ⋆ X nt> G ⋆ X
 inj⋆# = nt→nt⋆ inj#

 inj⋆ : ⦃ _ : F <: G ⦄{X : Set^ I lI} → F ⋆ X pt> G ⋆ X
 inj⋆ = fst inj⋆#

 =>✶ : ⦃ p : F <: G ⦄{X : Set^ I lI}{i : I} → ⟪ F ⟫ (G ✶ X) i → (G ✶ X) i
 =>✶ (t , xs) = ⟨ inj⋆ _ _ (« t , xs) ⟩
\end{code}

\begin{code}
 ✶homap : F pt> G → (X : Set^ I lI) → F ✶ X ⇛ G ✶ X
 ✶homap f X i xs = Mu.μhomap (pt→pt⋆ f) i xs
\end{code}

\begin{code}
 =>✶' : ⦃ p : F <: G ⦄{X : Set^ I lI}{i : I} → ⟪ F ⟫ (G ✶ X) i → (G ✶ X) i
 =>✶' xs = roll _ (inj _ _ xs)
\end{code}

\begin{code}
 private test : ∀ ⦃ p : F <: G ⦄{X i} → =>✶ ⦃ p ⦄ {X}{i} ≡ =>✶' ⦃ p ⦄
         test = <>
\end{code}

\begin{code}
module ✶homap-nat (F : En A I)⦃ eF : ExtFor/ F lI ⦄
                  (G : En A I)⦃ eG : ExtFor/ G lI ⦄
                  (f# : F nt> G)
                  {X Y : Set^ I lI}(h : X ⇛ Y) where

 private
  f = fst f#

  fY : F ⋆ Y alg> G ✶ Y
  fY = Mu.pt→alg {F = to▻ (F ⋆ Y)} (pt→pt⋆ f)
  fX : F ⋆ X alg> G ✶ X
  fX = Mu.pt→alg {F = to▻ (F ⋆ X)} (pt→pt⋆ f)

  f' = ✶homap {F}{G} f
\end{code}

\begin{code}
 open Cata

 module G✶X = Cata {F = G ⋆ X}
 module F✶X = Cata {F = F ⋆ X}
 module F✶Y = Cata {F = F ⋆ Y}

 map✶homap-nat : (D : De I)(eD : ExtFor D lI) →
                    G✶X.mapCata (fmap-alg {F = G} h) D ∘ F✶X.mapCata fX D
                 Π≡ F✶Y.mapCata fY D ∘ F✶X.mapCata (fmap-alg {F = F} h) D
 map✶homap-nat' : ∀ i →    G✶X.mapCata (fmap-alg {F = G} h) (G `$ i) ∘ f _ i ∘ F✶X.mapCata fX (F `$ i)
                        Π≡ f _ i ∘ F✶Y.mapCata fY (F `$ i) ∘ F✶X.mapCata (fmap-alg {F = F} h) (F `$ i)
 map✶homap-nat (`I i  ) _ (↑ ⟨ « t , xs ⟩) = (↑_ ∘ ⟨_⟩ ∘ (λ ■ → « (fst ■) , snd ■)) $≡ map✶homap-nat' i (t , xs)
 map✶homap-nat (`I i  ) _ (↑ ⟨ » t , xs ⟩) = <>
 map✶homap-nat (`Σ S T) eT (s , t) = ,_ $≡ map✶homap-nat (T s) (eT s) t
 map✶homap-nat (`Π S T) e f = e λ s → map✶homap-nat (T s) (extFor e (T s)) (f s)
 map✶homap-nat (`1    ) _ xs = <>
 map✶homap-nat (L `× R) (eL , eR) (ls , rs) = ap₂ _,_ (map✶homap-nat L eL ls) (map✶homap-nat R eR rs)
 map✶homap-nat' i xs = help i _ ⊚ (f _ i $≡ map✶homap-nat (F `$ i) (eF i) xs) where
  m  = fmap {F = G} h
  ma = fmap-alg h
  nat : ⟪ G ⟫map m ∘⇛ f _ ⇛≡ f _ ∘⇛ ⟪ F ⟫map m
  nat = !_ ∘ snd f# m
  help : ∀ i → G✶X.mapCata ma (G `$ i) ∘ f _ i Π≡ f _ i ∘ G✶X.mapCata ma (F `$ i)
  help i xs =   G✶X.mapCata-OK ma (G `$ i) (eG i) _
              ⊚ nat (i , xs)
              ⊚ f _ i $≡ ! (G✶X.mapCata-OK ma (F `$ i) (eF i) _)
\end{code}

\begin{code}
 ✶homap-nat : fmap h ∘⇛ f' _ ⇛≡ f' _ ∘⇛ fmap h
 ✶homap-nat (i , ⟨ « t , xs ⟩) =    (⟨_⟩ ∘ (λ ■ → « (fst ■) , snd ■))
                                 $≡ map✶homap-nat' i (t , xs)
 ✶homap-nat (i , ⟨ » t , xs ⟩) = <>
\end{code}

