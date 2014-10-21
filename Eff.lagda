
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
 getChar : ∀ {F} → ⦃ _ : Instance (GetCharF <: F) ⦄ → ∀ {i} → F ⊢ i ↓ (≡ i ×/ [[ Char ]])
 getChar = =>✶ ⦃ km-<: ⦄ (_ , λ c → ↑return (<> , c))

 putChar : ∀ {F} → ⦃ _ : Instance (PutCharF <: F) ⦄ → Char → ∀ {i} → F ⊢ i ↓ (≡ i ×/ [[ ⊤ ]])
 putChar c = =>✶ ⦃ km-<: ⦄ (_ , c , ↑return (<> , _))
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
 openFile : ∀ {F}⦃ p : Instance (OpenFileF <: F) ⦄ → FilePath → F ⊢ Closed ↓ [[ ⊤ ]]
 openFile path = =>✶ ⦃ km-<: ⦄ (_ , path , λ _ → ↑return tt)

 readFile : ∀ {F}⦃ p : Instance (ReadFileF <: F) ⦄ → F ⊢ Open ↓ [κ String := Open ] ⊎/ ≡ Closed
 readFile = =>✶ ⦃ km-<: ⦄ (_ , λ { (¡ x) → ↑return (inl (<> , x))
                                 ;    ε  → ↑return (inr  <>     ) })

 closeFile : ∀ {F}⦃ p : Instance (CloseFileF <: F) ⦄ → F ⊢ Open ↓ ≡ Closed
 closeFile = =>✶ ⦃ km-<: ⦄ (_ , ↑ return <>)
\end{code}

\begin{code}
 module Example {F}⦃ p : FileSystemF <: F ⦄ where

  open Instances (smartSubs<: p)

  example : F ⊢ Closed ↓ [κ String := Closed ]
  example = openFile "test.txt" >> λ
            { Closed → return (<> , "Error while opening.")
            ; Open   → readFile >>= postRead }
    where
      postRead : [κ String := Open ] ⊎/ ≡ Closed ⇛ _
      postRead .Open  (inl (<> , contents)) = closeFile >>= λ { ._ <> →
                                              return (<> , contents) }
      postRead Closed (inr              <>) = return (<> , "Error while reading.")
\end{code}

\begin{code}
module Cat {A : Set}(`TT `getChar  `putChar             : A) 
                    (`FS `openFile `readFile `closeFile : A)
           (let open FileSystem `FS `openFile `readFile `closeFile)
           (let open Teletype   `TT `getChar  `putChar  State)
           {F} ⦃ p : FileSystemF <: F ⦄ ⦃ q : PutCharF <: F ⦄
           where
\end{code}

\begin{code}
  open Instances (smartSubs<: p AD.++ smartSubs<: q)

\end{code}

\begin{code}
  cat : FilePath → F ⊢ Closed ↓ ≡ Closed
  cat fp = openFile fp >>= λ { Closed x → putChars openErrorMsg =>= λ _ →
                                          return <>
                             ; Open   x → readFile >>= postRead }
   where

    openErrorMsg = S.toList "Error while opening the file!\n"
    readErrorMsg = S.toList "Error while reading the file!\n"

    putChars : List Char → F ⊢ Closed ↓ ≡ Closed ×/ [[ ⊤ ]]
    putChars []       = return (<> , tt)
    putChars (x ∷ xs) = putChar x =>= λ _ → putChars xs

    postRead : ≡ Open ×/ [[ String ]] ⊎/ ≡ Closed ⇛ F ✶ ≡ Closed
    postRead  Closed (inl (() , _)  )
    postRead .Closed (inr <>        ) = putChars readErrorMsg =>= λ _ →
                                        return <>
    postRead .Open   (inl (<> , str)) = closeFile >>= λ { .Closed <> →
                                        putChars (S.toList str) =>= λ _ →
                                        return <> }
\end{code}

