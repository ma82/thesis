
\begin{code}
module thesis.MVCExample where

open import AD
open Functor

module _ {I : Set} where
\end{code}

\begin{code}
 HF : Op (List I × List I) I Z Z
 HF X i = (is : List I) → X (is , i ∷ is)

 Hmap : ∀ {A B} → A ⇛ B → HF A ⇛ HF B
 Hmap f i = Πmap λ x → f (x , i ∷ x)

 H : Functor (List I × List I) I _ _
 H = record { RF         = mk HF Hmap
            ; ∣_∣map-id⇛ = λ _ → <>
            ; ∣_∣map-∘⇛  = λ _ → <> }
\end{code}

\begin{code}
module Stack {I : Set}(Ty : ★^ I Z) where
\end{code}

\begin{code}
 head : ∀ {X : ★^ I Z}{i is} → □List X (i ∷ is) → X i
 head (x , _) = x

 tail : ∀ {X : ★^ I Z}{i is} → □List X (i ∷ is) → □List X is
 tail (_ , xs) = xs
\end{code}

\begin{code}
 Stack : List I → Set
 Stack = □List Ty
\end{code}

\begin{code}
 ST : List I × List I → Set
 ST (ss , ts) = Stack ss → Stack ts
\end{code}

\begin{code}
 module Add {addTy? : I → I → 1+ I}
            (_+_ : ∀ {i j k}⦃ q : addTy? i j ≡ ¡ k ⦄ → Ty i → Ty j → Ty k)
            where
\end{code}

\begin{code}
   stackAdd : {t1 t2 t : I}⦃ q : addTy? t1 t2 ≡ ¡ t ⦄
              (ss : List I) → ST (t2 ∷ t1 ∷ ss , t ∷ ss)
   stackAdd _ (v2 , v1 , vs) = v1 + v2 , vs
 \end{code}

\iffalse
\begin{code}
 open Add public
 open Functor
\end{code}

\begin{code}
 _ℝ_ : {i : I} → Ty i → ∣ H ∣ ST i → Set
 e ℝ f = ∀ ss xs → e , xs ≡ f ss xs
\end{code}

\begin{code}
open import thesis.Codes
open import thesis.Sub {Z}{Z}; open Kit
open import thesis.MVC
open import Data.Nat
open import Data.Bool
\end{code}

\begin{code}
module Prog {I A : Set}(`PUSH `+++ `<> `ADD : A)
            (addTy? : I → I → 1+ I)
            (Ty     : ★^ I Z)
            (_+_    : ∀ {i j k}⦃ q : addTy? i j ≡ ¡ k ⦄ → Ty i → Ty j → Ty k)
            where
\end{code}

\begin{code}
 private J = List I × List I
\end{code}

\begin{code}
 PushF : J → De J
 PushF (ss , []    ) = `K ⊥
 PushF (ss , t ∷ ts) = `K (ss ≡ ts × Ty t) 

 Push : En A J
 Push = ¡ `PUSH ⟩ [ PushF ]
\end{code}

\begin{code}
 ePush : ∀ {l} → ExtFor/ Push l
 ePush (_ ,     []) _ = _
 ePush (_ , t ∷ ts) _ = _
\end{code}

\begin{code}
 Append : En A J
 Append = ¡ `+++ ⟩ [ (λ { (as , cs) → `Σ _ λ bs → `I (as , bs) `× `I (bs , cs) }) ]
\end{code}

\begin{code}
 Nil : En A J
 Nil = ¡ `<> ⟩ [ `K ∘ uc _≡_ ]
\end{code}

\begin{code}
 AddF : J → De J
 AddF (t1 ∷ t2 ∷ ss , t ∷ ts) = `K (ss ≡ ts × addTy? t1 t2 ≡ ¡ t)
 AddF                      _  = `K ⊥

 Add : En A J
 Add = ¡ `ADD ⟩ [ AddF ]
\end{code}

\begin{code}
 PUSH : ∀ {F}⦃ p : ||| Push <: F ⦄{bs t} → Ty t → μ F (bs , t ∷ bs)
 PUSH n = => ⦃ km-<: ⦄ $ _ , (<> , n) , _

 infixr 5 _+++_

 _+++_ : ∀ {F}⦃ p : ||| Append <: F ⦄{as bs cs} →
         μ F (as , bs) → μ F (bs , cs) → μ F (as , cs)
 _+++_ p1 p2 = => ⦃ km-<: ⦄ $ _ , _ , ↑ p1 , ↑ p2

 <-> : ∀ {F}⦃ p : ||| Nil <: F ⦄{ss} → μ F (ss , ss)
 <-> = => ⦃ km-<: ⦄ $ _ , <> , _

 ADD : ∀ {F}⦃ p : ||| Add <: F ⦄{t t1 t2 ts}⦃ q : addTy? t1 t2 ≡ ¡ t ⦄ →
       μ F $ t1 ∷ t2 ∷ ts , t ∷ ts
 ADD ⦃ q = q ⦄ = => ⦃ km-<: ⦄ $ _ , (<> , q) , _
\end{code}

\begin{code}
 open Stack Ty

 evalPush : Push alg> ST
 evalPush (._ , _ ∷ _) (_ , (<> , t) , _) = _,_ t
 evalPush (_  ,    []) (_ , ()       , _)

 evalNil : Nil alg> ST
 evalNil _ (_ , q , _) = rew Stack q

 evalAppend : Append alg> ST
 evalAppend _ (_ , _ , ↑ st1 , ↑ st2) = st2 ∘ st1

 evalAdd : Add alg> ST
 evalAdd (t1 ∷ t2 ∷ .ts , t ∷ ts) (_ , (<> , p), _) (x1 , x2 , xs) = (x1 + x2) , xs
 evalAdd ([]     , _ ∷ _) (_ , () , _)
 evalAdd (_ ∷ [] , _ ∷ _) (_ , () , _)
 evalAdd (_      ,    []) _ _ = _
\end{code}

\begin{code}
 Prog : En A J
 Prog = Push [⊕] Append [⊕] Nil [⊕] Add
\end{code}

\begin{code}
 ProgL : Lang ST
 ProgL = mk Prog [ evalPush , [ evalAppend , [ evalNil , evalAdd ]⟦⟧ ]⟦⟧ ]⟦⟧
\end{code}

\begin{code}
         where open TreeCase ε
\end{code}

\begin{code}
module Val {I A : Set}(`val : A)(Ty : ★^ I Z) where

 ValF : En A I
 ValF = ¡ `val ⟩ [ `K ∘ Ty ]

 val : {F : En A I}⦃ p : ||| ValF <: F ⦄ → {i : I} → Ty i → μ F i
 val v = => ⦃ km-<: ⦄ $ _ , v , _
\end{code}

\begin{code}
 evalAlg : ValF alg> Ty
 evalAlg _ (_ , a , _) = a

 ValL : Lang Ty
 ValL = mk ValF evalAlg
\end{code}

\begin{code}
 module Comp (`PUSH `+++ `<> `ADD : A) addTy?
             (_+_ : ∀ {i j k}⦃ q : addTy? i j ≡ ¡ k ⦄ → Ty i → Ty j → Ty k)
             where

  open Prog `PUSH `+++ `<> `ADD addTy? Ty _+_
  open Hints (smartSubs Prog)

  compAlg : ValF alg> ∣ H ∣ (μ Prog)
  compAlg i (_ , v , _) _ = PUSH v +++ <->
\end{code}

\begin{code}
  open Stack Ty

  mvc : MVC ValL H ProgL _ℝ_
  mvc = mk compAlg λ _ _ _ _ _ _ _ _ _ → <>
\end{code}

\begin{code}
module Plus {I A : Set}(`plus : A)
            (addTy? : I → I → 1+ I)(Ty : ★^ I Z)
            (_+_ : ∀ {i j k}⦃ q : addTy? i j ≡ ¡ k ⦄ → Ty i → Ty j → Ty k)
            where
\end{code}

\begin{code}
 Plus : En A I
 Plus = ¡ `plus ⟩ [ (λ k → `Σ _ λ i → `Σ _ λ j → 
                           `Σ (addTy? i j ≡ ¡ k) λ _ → `I i `× `I j) ]
\end{code}

\begin{code}
 module _ {F}⦃ p : ||| Plus <: F ⦄{i j k}⦃ ijk : ||| addTy? i j ≡ ¡ k ⦄ where

  infixr 4 _plus_

  _plus_ : μ F i → μ F j → μ F k
  x plus y = => ⦃ km p ⦄ $ _ , _ , _ , km ijk , ↑ x , ↑ y
\end{code}

\begin{code}
 evalAlg : Plus alg> Ty
 evalAlg _ (_ , _ , _ , _ , ↑ x , ↑ y) = x + y

 PlusL : Lang Ty
 PlusL = mk Plus evalAlg
\end{code}

\begin{code}
 module Comp (`PUSH `+++ `<> `ADD : A) where

  open Prog `PUSH `+++ `<> `ADD addTy? Ty _+_
  open Hints (smartSubs Prog)

  compAlg : Plus alg> ∣ H ∣ (μ Prog)
  compAlg i (_ , _ , _ , _ , ↑ c2 , ↑ c1) is = c1 is +++ (c2 _ +++ ADD)
\end{code}

\begin{code}
  open Stack Ty

  mvc : MVC PlusL H ProgL _ℝ_
  mvc = mk compAlg meth where
   meth : ∀ G β _ γ _ xs ih is ss → _
   meth G β _ γ _ (k , t , i , j , p , ↑ e1 , ↑ e2) (↑ ihL , ↑ ihR) is ss =
    goal where
     module G = Cata {F = fst G}
     module P = Cata {F = Prog }
     d1 : Ty i ; d1 = G.cata β i e1
     d2 : Ty j ; d2 = G.cata β j e2
     c1 : ∀ is → ST (is , i ∷ is)
     c1 = ∣ H ∣map (P.cata (alg ProgL)) i (G.cata γ i e1)
     c2 : ∀ is → ST (is , j ∷ is)
     c2 = ∣ H ∣map (P.cata (alg ProgL)) j (G.cata γ j e2)
     lhs = d1 , d2 , ss
     rhs = c1 (j ∷ is) (c2 is ss)
     rec : lhs ≡ rhs
     rec = ihL (j ∷ is) _ ⊚ c1 (j ∷ is) $≡ ihR is ss
     infix 4 _≣_
     _≣_ = Id (Stack (k ∷ is))
     goal : d1 + d2 , ss ≣ head rhs + head (tail rhs) , tail (tail rhs)
     goal = rew (λ s →   (d1 + d2 , ss)
                       ≣ (head s + head (tail s) , tail (tail s)))
                rec <>
\end{code}

\begin{code}
module Val+Plus where

 data Names : Set where `val `plus `PUSH `+++ `<> `ADD : Names
 data Types : Set where `nat : Types

 Ty : Types → Set
 Ty t = ℕ

 addTy? : Types → Types → 1+ Types
 addTy? `nat `nat = ¡ `nat

 open Hints (((addTy? `nat `nat ≡ ¡ `nat) , <>) ∷ [])

 open Stack Ty
\end{code}

\begin{code}
 module V  = Val    `val                       Ty     ; open V
 module VC = V.Comp `PUSH `+++ `<> `ADD addTy?    _+_
 module P  = Plus   `plus               addTy? Ty _+_ ; open P
 module PC = P.Comp `PUSH `+++ `<> `ADD
 open        Prog   `PUSH `+++ `<> `ADD addTy? Ty _+_
\end{code}

\begin{code}
 open MVC+ ValL PlusL H ProgL (λ {i} → _ℝ_ {i}) ε

 mvc = VC.mvc MVC+ PC.mvc
\end{code}

\begin{code}
 open module M = MVC mvc
 ExpL = ValL [ ε ]Lang+ PlusL

 private
  testOK : (t : Types)(x : μ (lang ExpL) t)
              (ss : List Types)(xs : Stack ss) →
                 eval _ x , xs ≡ exec _ (comp _ x ss) xs
  testOK = ok
\end{code}

\begin{code}
 open Hints (smartSubs (lang ExpL))

 exp : μ (lang ExpL) `nat
 exp = val 14 plus val 8 plus val 10
\end{code}

\begin{code}
 private
  test-exp-0 : eval _ exp , tt ≡ exec _ (comp _ exp []) tt
  test-exp-0 = <>

  test-exp-1 : 32 , tt ≡ 32 , tt
  test-exp-1 = ok _ exp _ _

  test-exp-2 : test-exp-0 ≡ test-exp-1
  test-exp-2 = <>
\end{code}

** Problem **

Strangely enough, the following gives "stack overflow".

\begin{code}
--  test-exp-3 : eval _ exp , tt ≡ exec _ (comp _ exp []) tt
--  test-exp-3 = ok _ exp _ _
\end{code}

\begin{code}
module IfThEl {A I : Set}{`ite : A}{`bool : I} where

 IfThEl : En A I
 IfThEl = ¡ `ite ⟩ [ (λ i → `I `bool `× `I i `× `I i) ]

 if_th_el_ : {F : En A I}⦃ p : ||| IfThEl <: F ⦄
             {i : I}(b : μ F `bool)(e1 e2 : μ F i) → μ F i
 if b th e1 el e2 = => ⦃ km-<: ⦄ $ _ , ↑ b , ↑ e1 , ↑ e2

 module _ {Ty}⦃ p : Ty `bool ≡ Bool ⦄
          ⦃ _≟_ : ∀ {i}(x y : Ty i) → Dec (x ≡ y) ⦄ where

  evalAlg : IfThEl alg> Ty
  evalAlg i (_ , ↑ b , ↑ e1 , ↑ e2) = if (rew id p b) then e1 else e2

  IfThElL : Lang Ty
  IfThElL = mk IfThEl evalAlg
\end{code}

\begin{code}
module Equals {A I : Set}{`ε `== : A}{`bool : I} where

 Equals : En A I
 Equals = ¡ `== ⟩ [ (λ i → `Σ (i ≡ `bool) λ _ → `Σ _ λ j → `I j `× `I j) ]

 _?=_ : {F : En A I}⦃ p : Equals <: F ⦄ → ∀ {j} → μ F j → μ F j → μ F `bool
 e1 ?= e2 = => $ _ , <> , _ , ↑ e1 , ↑ e2

 module _ {Ty : I → Set}{true false : Ty `bool}
          ⦃ _≟_ : ∀ {i}(x y : Ty i) → Dec (x ≡ y) ⦄ where

   evalEquals : Equals alg> Ty
   evalEquals ._ (_ , <> , _ , ↑ v1 , ↑ v2) with v1 ≟ v2
   evalEquals ._ (_ , <> , _ , ↑ v1 , ↑ v2) | yes ,  p = true
   evalEquals ._ (_ , <> , _ , ↑ v1 , ↑ v2) | no  , ¬p = false

   EqualsL : Lang Ty
   EqualsL = mk Equals evalEquals
\end{code}

