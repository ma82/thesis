
\begin{code}
module thesis.Eff where

open import AD
open import thesis.Codes
open import thesis.Sub; open Kit
open import thesis.FreeMonad
open import Data.Char
open import Data.Bool
open import Data.String as S
\end{code}

\begin{code}
infixr 1 _⊢_↓_
\end{code}

\begin{code}
_⊢_↓_ = λ {A I : Set}(F : En A I)(s : I)(X : Set^ I _) → F ✶ X $ s
\end{code}

\begin{code}
[[_]] : {I : Set} → Set → Set^ I _
[[ X ]] _ = X
\end{code}

\begin{code}
Contents = String
FilePath = String
\end{code}

\begin{code}
data State : Set where
 Open Closed : State
\end{code}

\begin{code}
open import IO.Primitive as IO using (IO)
\end{code}

\begin{code}
postulate
 getCh   : IO Char
 putCh   : Char → IO ⊤Z
\end{code}

\begin{code}
 openFi  : FilePath → IO State
 readFi  : IO Contents
 closeFi : IO ⊤Z
\end{code}

\begin{code}
module Teletype {A : Set}(`TT `getChar `putChar : A)(I : Set) where
\end{code}

\begin{code}
 GetCharF PutCharF : En A I
 GetCharF = ¡ `getChar  ⟩ [ (λ i → `Π Char λ _ → `I i) ]
 PutCharF = ¡ `putChar  ⟩ [ (λ i → `Σ Char λ _ → `I i) ]
\end{code}

\begin{code}
 TeletypeF : En A I
 TeletypeF = ¡ `TT ⟩ (GetCharF ⊕ PutCharF)
\end{code}

\begin{code}
 getChar : ∀ {F} → ⦃ _ : GetCharF <: F ⦄ → ∀ {i} → F ⊢ i ↓ (≡ i ×/ [[ Char ]])
 getChar = =>✶ (_ , λ c → ↑return (<> , c))

 putChar : ∀ {F} → ⦃ _ : PutCharF <: F ⦄ → Char → ∀ {i} → F ⊢ i ↓ (≡ i ×/ [[ ⊤ ]])
 putChar c = =>✶ (_ , c , ↑return (<> , _))
\end{code}

\begin{code}
 evalAlg : ∀ {A} → TeletypeF ⋆ A alg> IO ∘ A
 evalAlg i (« « t , f      ) = getCh   IO.>>= ↓_ ∘ f
 evalAlg i (« » t , c , ↑ x) = putCh c IO.>>= λ _ → x
 evalAlg i (» _   , x , _  ) = IO.return x
\end{code}

\begin{code}
module FileSystem {A : Set}(`FS `openFile `readFile `closeFile : A) where
\end{code}

\begin{code}
 OpenFileF ReadFileF CloseFileF : En A State
\end{code}

\begin{code}
 OpenFileF = ¡ `openFile  ⟩ [ > ] where
   > : _ → _
   > Closed = `Σ FilePath λ _ → `Π State λ s → `I s
   > _      = `K ⊥
\end{code}

\begin{code}
 ReadFileF = ¡ `readFile  ⟩ [ > ] where
   > : _ → _
   > Open = `Π (1+ Contents) λ { (¡ xs) → `I Open
                               ; ε      → `I Closed }
   > _    = `K ⊥
\end{code}

\begin{code}
 CloseFileF = ¡ `closeFile  ⟩ [ > ] where
   > : _ → _
   > Open = `I Closed
   > _    = `K ⊥
\end{code}

\begin{code}
 FileSystemF : En A State
 FileSystemF = ¡ `FS ⟩ (OpenFileF [⊕] ReadFileF ⊕ CloseFileF )
\end{code}

\begin{code}
 openFile : ∀ {F}⦃ p : OpenFileF <: F ⦄ → FilePath → F ⊢ Closed ↓ [[ ⊤ ]]
 openFile path = =>✶ (_ , path , λ _ → ↑return tt)

 readFile : ∀ {F}⦃ p : ReadFileF <: F ⦄ → F ⊢ Open ↓ [κ String := Open ] ⊎/ ≡ Closed
 readFile ⦃ p ⦄ = =>✶ ⦃ p ⦄ (_ , λ { (¡ x) → ↑return (inl (<> , x))
                                   ;    ε  → ↑return (inr  <>     ) })

 closeFile : ∀ {F}⦃ p : CloseFileF <: F ⦄ → F ⊢ Open ↓ ≡ Closed
 closeFile = =>✶ (_ , ↑ return <>)
\end{code}

\begin{code}
 evalAlg : {A : Set} → FileSystemF ⋆ [[ A ]] alg> [[ IO A ]]
 evalAlg Closed (« « « _ , fn , f) = openFi fn IO.>>= ↓_ ∘ f
 evalAlg Open   (« « « _ , () , f)
 evalAlg Closed (« « » _ , () , _)
 evalAlg Open   (« « » _ , f     ) = readFi  IO.>>= ↓_ ∘ f ∘ ¡
 evalAlg Closed (« » _   , () , _)
 evalAlg Open   (« » _   , m     ) = closeFi IO.>>= λ _ → ↓ m
 evalAlg _      (» _     , a , _ ) = IO.return a
\end{code}

\begin{code}
 module Example {F}⦃ p : FileSystemF <: F ⦄ where

  -- TODO 9B5Q ⦃⦄ was not needed in Agda 2.4.0.2
  open 16Points (smartSubs<: p) 0 public

  example : F ⊢ Closed ↓ [κ String := Closed ]
  -- TODO 9B5Q ⦃⦄ was not needed in Agda 2.4.0.2
  example = openFile ⦃ #2 ⦄ "test.txt" >>
            λ { Closed → return (<> , "Error while opening.")
              -- TODO 9B5Q ⦃⦄ was not needed in Agda 2.4.0.2
              ; Open   → readFile ⦃ #3 ⦄ >>= postRead  }
    where
      postRead : [κ String := Open ] ⊎/ ≡ Closed ⇛ _
      -- TODO 9B5Q ⦃⦄ was not needed in Agda 2.4.0.2
      postRead .Open  (inl (<> , contents)) = closeFile ⦃ #4 ⦄ >>= λ { ._ <> →
                                              return (<> , contents) }
      postRead Closed (inr              <>) = return (<> , "Error while reading.")
\end{code}

\begin{code}
module Cat {A : Set}
           (`TT `getChar  `putChar             : A) 
           (`FS `openFile `readFile `closeFile : A)
           where

 open module F = FileSystem `FS `openFile `readFile `closeFile
 open module T = Teletype   `TT `getChar  `putChar  State
\end{code}

\begin{code}
 cat : ∀ {F} ⦃ p : FileSystemF <: F ⦄ ⦃ q : TeletypeF <: F ⦄ → 
       FilePath → F ⊢ Closed ↓ ≡ Closed
\end{code}

\begin{code}
 cat {F} ⦃ p ⦄ ⦃ q ⦄ fp =
   openFile ⦃ #2 ⦄ fp >>= λ { Closed x → putChars openErrorMsg =>= λ _ →
                                         return <>
                            ; Open   x → readFile ⦃ #3 ⦄ >>= postRead }
  where

   open 16Points (smartSubs<: p List.++ smartSubs<: q) 0

   openErrorMsg = S.toList "Error while opening the file!\n"
   readErrorMsg = S.toList "Error while reading the file!\n"

   putChars : List Char → F ⊢ Closed ↓ ≡ Closed ×/ [[ ⊤ ]]
   putChars []       = return (<> , tt)
   putChars (x ∷ xs) = putChar ⦃ #7 ⦄ x =>= λ _ → putChars xs

   postRead : ≡ Open ×/ [[ String ]] ⊎/ ≡ Closed ⇛ F ✶ ≡ Closed
   postRead  Closed (inl (() , _)  )
   postRead .Closed (inr <>        ) = putChars readErrorMsg =>= λ _ →
                                       return <>
   postRead .Open   (inl (<> , str)) = closeFile ⦃ #4 ⦄ >>= λ { .Closed <> →
                                       putChars (S.toList str) =>= λ _ →
                                       return <> }
\end{code}

