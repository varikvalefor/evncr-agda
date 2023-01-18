\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∄}{\ensuremath{\mathnormal\nexists}}
\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{∨}{\ensuremath{\mathnormal\vee}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{∶}{\ensuremath{\mathnormal\colon\!\!}}
\newunicodechar{⊹}{\ensuremath{\mathnormal\dag}}
\newunicodechar{𝕗}{\ensuremath{\mathbb{f}}}
\newunicodechar{ℙ}{\ensuremath{\mathbb{P}}}
\newunicodechar{𝔽}{\ensuremath{\mathbb{F}}}
\newunicodechar{𝕄}{\ensuremath{\mathbb{M}}}
\newunicodechar{𝔹}{\ensuremath{\mathbb{B}}}
\newunicodechar{ν}{\ensuremath{\nu}}
\newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{◆}{\ensuremath{\mathnormal\blackdiamond}}
\newunicodechar{∸}{\ensuremath{\mathnormal\dotdiv}}
\newunicodechar{ᵇ}{\ensuremath{^\mathrm{b}}}
\newunicodechar{≥}{\ensuremath{\mathnormal{\geq}}}
\newunicodechar{ϕ}{\ensuremath{\mathnormal{\phi}}}
\newunicodechar{χ}{\ensuremath{\mathnormal{\chi}}}
\newunicodechar{∧}{\ensuremath{\mathnormal{\wedge}}}
\newunicodechar{∅}{\ensuremath{\mathnormal{\emptyset}}}
\newunicodechar{∣}{\ensuremath{\mathnormal{|}}}
\newunicodechar{⁇}{\ensuremath{\mathrm{?\!?}}}
\newunicodechar{∘}{\ensuremath{\mathnormal{\circ}}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{ℓ}{\ensuremath{\ell}}
\newunicodechar{σ}{\ensuremath{\sigma}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{ₘ}{\ensuremath{_\mathsf{m}}}
\newunicodechar{ₛ}{\ensuremath{_\mathsf{s}}}
\newunicodechar{⊤}{\ensuremath{\mathnormal{\top}}}
\newunicodechar{◈}{\ensuremath{\diamond\hspace{-0.39em}\cdot}}
\newunicodechar{≤}{\ensuremath{\mathnormal{\leq}}}
\newunicodechar{⍉}{\ensuremath{∘\hspace{-0.455em}\backslash}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lBrace}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{\rBrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_i}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_l}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_o}}}
\newunicodechar{ₚ}{\ensuremath{\mathnormal{_p}}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound

\begin{document}
\begin{code}
{-# OPTIONS --guardedness #-}

open import IO
  renaming (
    lift to liftᵢₒ;
    _>>=_ to _>>=ᵢₒ_
  )
  hiding (
    _<$>_
  )
open import Data.Fin
open import Data.Nat
open import Data.Vec
  hiding (
    _++_;
    drop
  )
open import Function
open import Data.Bool
open import Data.Char
  using (
    Char
  )
  renaming (
    toℕ to C2N
  )
open import Data.List
  using (
    List;
    _++_;
    [];
    upTo;
    drop;
    _∷_
  )
  renaming (
    intersperse to intersperseₗ;
    length to lengthₗ
  )
open import Data.Float
  using (
    Float
  )
open import Data.Maybe
  renaming (
    map to mapₘ
  )
open import Data.String
  renaming (
    _++_ to _++ₛ_;
    toList to toListₗ
  )
  using (
    String
  )
open import Data.Product
  using (
    _×_;
    _,_
  )
open import IO.Primitive
  renaming (
    IO to PIO;
    _>>=_ to _>>=ₚᵢₒ_;
    return to returnₚᵢₒ
  )
open import Category.Monad
open import Agda.Builtin.Unit
  renaming (
    ⊤ to Unit
  )
open import Category.Applicative
open import Data.Maybe.Instances
open import Data.Unit.Polymorphic
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Show
  using ()
open import Data.Fin.Show
  using (
    readMaybe
  )
\end{code}

\chapter{le srana be lo nu tcimi'e}

\section{la'oi .\F{selsniduXipa}.}
ni'o la'oi .\F{selsniduXipa}.\ bitmu fo lo me'oi .Lerfu.

\begin{code}
postulate selsniduXiPa : Float
\end{code}

\section{la'oi .\F{ddvs}.}
ni'o la'oi .\F{ddvs}.\ me'oi .path. lo datnyveiste poi ke'a vasru lo sance datnyvei pe la'oi .EVANNOUNCER.

.i zo'oi .ddvs.\ cmavlaka'i lu datni datnyveiste li'u

\begin{code}
postulate ddvs : String
\end{code}

\chapter{le me'oi .\AgdaKeyword{record}.\ je le me'oi .\AgdaKeyword{instance}.\ je zo'e}

\section{la'oi .\F{Showable}.}
ni'o la .varik.\ cu na jinvi le du'u sarcu fa lo nu jmina lo velcki\ldots kei kei je cu na djuno lo du'u ma kau zabna velcki la'oi .\F{Showable}.

\begin{code}
record Showable {a} (A : Set a) : Set a
  where
  field
    show : A → String
\end{code}

\subsection{le me'oi .instance\ldots ja co'e}

\begin{code}
instance
  showableℕ : Showable ℕ
  showableℕ = record {show = Data.Nat.Show.show}
  showableFloat : Showable Float
  showableFloat = record {show = Data.Float.show}
\end{code}

\chapter{le me'oi .\AgdaKeyword{data}.}

\section{la'oi .\D{Midnoi}.}
ni'o ro da poi me'oi .\D{Midnoi}.\ zo'u da sinxa lo .uniks.\ midnoi

\begin{code}
Midnoi : Set
Midnoi = String
\end{code}

\section{la'oi .\D{Case}.}

\begin{code}
data Case : Set
  where
  Barda : Case
  Cmalu : Case
  Namcu : Case
  Curly : Case
  Kurfa : Case
  Cukla : Case
  Jganu : Case
  Snile'u : Case
\end{code}

\section{la'oi .\F{LTyp}.}

\subsection{le ctaipe}

\begin{code}
data LTyp : Set
  where
  Latmo : LTyp
  Xrabo : LTyp
  Vrici : LTyp
  Kalri : LTyp
  Ganlo : LTyp
\end{code}

\begin{code}
\end{code}

\section{la'oi .\D{Lerfu}.}
ni'o ro da poi me'oi .\D{Lerfu}.\ je poi toldra zo'u da sinxa lo selvau be la'oi .ASCII.

.i go fo'a goi la'oi .\B x.\ toldra gi\ldots
\begin{itemize}
	\item gonai ge ko'a goi la'o zoi.\ \F{ctyp} \B x .zoi.\ du la'oi .\F{Xrabo}.\ gi ge fo'a sinxa lo me'oi .digit.\ lerfu gi ge ko'e goi la'o zoi.\ \F{case} \B x .zoi.\ du la'oi .\F{Namcu}.\ gi ko'i goi la'o zoi.\ \F{bnam} \B x .zoi.\ sumji lo namcu poi selsni la'oi .\B x.\ ku'o livobi gi
  \item gonai ge ko'a du la'oi .\F{Latmo}.\ gi\ldots
  \begin{itemize}
    \item gonai ge ko'e du la'oi .\F{Barda}.\ gi ge la'oi .\B x.\ sinxa lo me'oi .majuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li xamu gi
    \item ge ko'e du la'oi .\F{Cmalu}.\ gi ge la'oi .\B x.\ sinxa lo me'oi .minuscule.\ lerfu gi ko'i sumji lo mu'oi glibau.\ 0-indexed .glibau.\ se meirmoi be lo me'oi .caseless.\ versiio be lo selsni be la'oi .\B x.\ li soze gi
  \end{itemize}
  \item gonai ge ko'a du la'oi .\F{Kalri}.\ gi ge ko'i du li sopa gi\ldots
  \begin{itemize}
    \item gonai ge ko'e du la'oi .\F{Curly}.\ gi fo'a sinxa lo tolsti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li pareci pe la .asycy'i'is.\ gi
    \item gonai ge ko'e du la'oi .\F{Kurfa}.\ gi fo'a sinxa lo tolsti kurfa bo me'oi .bracket.\ noi ke'a selsni li sopa pe la .asycy'i'is.\ gi
    \item ge ko'e du la'oi .\F{Cukla}.\ gi fo'a sinxa lo tolsti cukla bo me'oi .bracket.\ noi ke'a selsni li vono pe la .asycy'i'is.\ gi
  \end{itemize}
  \item ge ko'a du la'oi .\F{Ganlo}.\ gi ge ko'i du li soci gi\ldots
  \begin{itemize}
    \item gonai ge ko'e du la'oi .\F{Curly}.\ gi fo'a sinxa lo sisti me'oi .curly.\ bo me'oi .bracket.\ noi ke'a selsni li paremu pe la .asycy'i'is.\ gi
    \item gonai ge ko'e du la'oi .\F{Kurfa}.\ gi fo'a sinxa lo sisti kurfa bo me'oi .bracket.\ noi ke'a selsni li soci pe la .asycy'i'is.\ gi
    \item gonai ge ko'e du la'oi .\F{Cukla}.\ gi fo'a sinxa lo sisti cukla bo me'oi .bracket.\ noi ke'a selsni li vopa pe la .asycy'i'is.\ gi
  \end{itemize}
  \item ge ko'a du la'oi .\F{Vrici}.\ gi ge ko'e du la'oi .\F{Snile'u}.\ gi ko'i .asycy'i'is.\ sinxa lo selsni be fo'a
\end{itemize}

\begin{code}
record Lerfu : Set
  where
  field
    ctyp : LTyp
    case : Case
    bnam : Fin 128
\end{code}

\chapter{le vrici je fancu}

\section{la'oi .\F{show}.}
ni'o la'o zoi.\ \F{show} \B q .zoi.\ me'oi .String.\ je cu sinxa la'oi .\B q.

\begin{code}
show : ∀ {a} → {A : Set a} → ⦃ _ : Showable A ⦄
     → A → String
show ⦃ Q ⦄ = Showable.show Q
\end{code}

\section{la'oi .\Sym{◈}.}
ni'o lakne fa lo nu le mu'oi glibau.\ type signature .glibau.\ cu banzuka

\begin{code}
_◈_ : ∀ {a} → {A B C : Set a}
    → {M : Set a → Set _} → ⦃ _ : RawApplicative M ⦄
    → (B → C) → (A → M B) → A → M C
_◈_ ⦃ Q ⦄ g f = RawApplicative._<$>_ Q g ∘ f
\end{code}

\section{la'oi .\F{liftx}.}
ni'o cadga fa lo nu le se ctaipe cu banzu lo nu jimpe

\begin{code}
liftx : ∀ {a} → PIO Unit → IO {a} ⊤
liftx q = liftᵢₒ (q >>=ₚᵢₒ λ _ → returnₚᵢₒ _)
\end{code}

\section{la'oi .\F{intersperse}.}
ni'o cadga fa lo nu le se ctaipe cu xamgu velcki

.i la .varik.\ cu milxe le ka ce'u sorpa'a lo nu jdikygau le se ctaipe lo ni ce'u vasru lo lerpinsle\ldots je lo lerfu

.i lo nu jdikygau le se ctaipe lo nu ce'u vasru lo lerfu cu cumki lo nu ciska lo lojysra ja co'e be la'o zoi.\ (\D{Vec} \B A \Sym\$ \F{lengthₗ} \Sym\$ \F{intersperseₗ} \B t \Sym\$ \F{toList} \B q) \Sym ≡ (\B n \Sym * 2 \Sym ∸ 1) .zoi.

\begin{code}
intersperse : ∀ {a} → {n : ℕ} → {A : Set a}
            → (t : A) → (q : Vec A n)
            → Vec A $ lengthₗ $ intersperseₗ t $ toList q
intersperse q = fromList ∘ intersperseₗ q ∘ Data.Vec.toList
\end{code}

\chapter{le skicu fancu}
\section{la'oi .\F{plicu'a}.}
ni'o ga jonai ga je ga je la'oi .\B K.\ vasru la'o zoi.\ (\B x \Sym, \B y) .zoi.\ gi la'oi .\B q.\ mleca la'oi .\B x.\ gi ko'a goi la'o zoi.\ \F{plicu'a} \B q \B n \B K .zoi.\ du la'oi .\B y.\ gi ga jonai ga je lo nilzilcmi be la'oi .\B k.\ cu zmadu li pa gi ko'a du la'o zoi.\ \F{plicu'a} \B q \B n \Sym\$ \F{tail} \B K .zoi.\ gi ko'a du la'oi .\B n.

to .i li renoreci pi'e pa pi'e pare cu detri le nu le mu'oi glibau.\ parsing expression .glibau.\ gerna cu na mapti di'u\ldots noi ke'a drani  .i lo skami cu mabla .u'e nai toi

\begin{code}
plicu'a : ∀ {a} {A : Set a} → ℕ → A → List $ List ℕ × A → A
plicu'a _ d [] = d
plicu'a q x ((a , b) ∷ xs) = if q elem a then b else plicu'a q x xs
  where
  _elem_ : ℕ → List ℕ → Bool
  _elem_ _ [] = false
  _elem_ x (y ∷ ys) = (x ≡ᵇ y) ∨ (x elem ys)
\end{code}

\section{la'oi .\F{intdMm}.}
ni'o la'o zoi.\ \F{intdMm} \B a \B b .zoi.\ vasru lo ro kacna'u poi ke'a dubjavmau la'oi .\B a.\ je cu mleca la'oi .\B b.

\begin{code}
intdMm : ℕ → ℕ → List ℕ
intdMm a b = drop a $ upTo b
\end{code}

\section{la'oi .\F{toBnam}.}

\begin{code}
toBnam : Fin 128 → ℕ
toBnam q = plicu'a q' q' ns
  where
  q' : ℕ
  q' = toℕ q
  du40 = 40 ∷ 41 ∷ 60 ∷ 62 ∷ 91 ∷ 93 ∷ 123 ∷ 125 ∷ []
  cmalu = intdMm 97 123
  ns : List $ List ℕ × ℕ
  ns = (du40 , 40) ∷ (cmalu , q' ∸ 32) ∷ []
\end{code}

\section{la'oi .\F{toCase}.}
\newcommand\BQ{la'oi .\B q.}
\newcommand\toCase{la'o zoi.\ \F{toCase \B q} .zoi.}
ni'o ga jonai ga je \B q .asycy'i'is.\ sinxa lo latmo glibau lerfu gi \toCase\ du la'oi .\F{Latmo}.\ gi ga jonai ga je la'oi .\B q.\ 

\begin{code}
toCase : Fin 128 → Case
toCase q = plicu'a (toℕ q) Snile'u ns
  where
  f : ℕ → Case → Case → Case
  f a b c = if (toℕ q) <ᵇ a then b else c
  namcu = intdMm 48 58
  barda = intdMm 65 91
  cmalu = intdMm 97 123
  cukla = 40 ∷ 41 ∷ []
  jganu = 60 ∷ 62 ∷ []
  kurfa = 91 ∷ 93 ∷ []
  curly = 123 ∷ 125 ∷ []
  ns : List $ List ℕ × Case
  ns = (cukla , Cukla) ∷ (namcu , Namcu) ∷
       (jganu , Jganu) ∷ (barda , Barda) ∷
       (kurfa , Kurfa) ∷ (curly , Curly) ∷
       (cmalu , Cmalu) ∷ []
\end{code}

\section{la'oi .\F{toLtyp}.}

\begin{code}
toLtyp : Fin 128 → LTyp
toLtyp q = plicu'a q' Vrici ns
  where
  q' : ℕ
  q' = toℕ q
  kalri = 40 ∷ 60 ∷ 91 ∷ 123 ∷ []
  ganlo = 41 ∷ 61 ∷ 93 ∷ 125 ∷ []
  latmo = intdMm 65 91 ++ intdMm 97 123
  xrabo = intdMm 48 58
  ns : List $ List ℕ × LTyp
  ns = (kalri , Kalri) ∷ (ganlo , Ganlo) ∷
       (xrabo , Xrabo) ∷ (latmo , Latmo) ∷ []
\end{code}

\section{la'oi .\F{toLerfu}.}
ni'o gonai ge la'oi .\B n.\ mleca li panobi gi ko'a goi la'o zoi.\ \F{toLerfu} \B n .zoi.\ me'oi .\F{just}.\ be lo sinxa lo .asycy'i'is.\ lerfu poi meirmoi la'oi .\B n.\ fo le'i ro .asyci'is.\ lerfu gi ko'a me'oi .\F{nothing}.

\begin{code}
toLerfu : ℕ → Maybe Lerfu
toLerfu = finToLerfu ◈ readMaybe 10 ∘ show
  where
  finToLerfu : Fin 128 → Lerfu
  finToLerfu a = record {ctyp = lt; case = cs; bnam = a}
    where
    lt : LTyp
    lt = toLtyp a
    cs : Case
    cs = toCase a
\end{code}

\section{la'oi .\F{genturfa'i}.}
ni'o ga jonai ga je la'oi .\B x.\ .aski gi ga je ko'a goi la'o zoi.\ \F{genturfa'i} \B x.\ .zoi.\ du la'oi .\B x.\ lo ni ce'u vasru gi ro da poi ke';a kacna'u je cu mleca lo nilzilcmi be ko'a zo'u lo meirmoi be da bei fo ko'a cu sinxa lo meirmoi be da bei la'oi .\B x.\ gi ko'a du la'oi .\F{nothing}.

\begin{code}
genturfa'i : String → Maybe $ List Lerfu
genturfa'i = sikh ∘ Data.List.map c2l? ∘ toListₗ
  where
  _<$>ₘ_ = RawMonad._<$>_ maybeMonad
  sikh : List $ Maybe Lerfu → Maybe $ List Lerfu
  sikh (just x ∷ xs) = (_∷_ x) <$>ₘ sikh xs
  sikh (nothing ∷ _) = nothing
  sikh [] = just []
  c2l? : Char → Maybe Lerfu
  c2l? = toLerfu ∘ C2N
\end{code}

\chapter{le fancu be fi lo .uniks.\ midnoi}

\section{la'oi .\F{spkCL}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCL} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .\F{ltyp}.\ be la'oi .\B x.

\begin{code}
spkCL : Lerfu → Midnoi
spkCL q = "mplayer " ++ₛ ddvs ++ₛ f (Lerfu.ctyp q)
  where
  postulate f : LTyp → String
\end{code}

\section{la'oi .\F{spkCC}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCC} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .case.\ be la'oi .\B x.

\begin{code}
spkCC : Lerfu → Midnoi
spkCC q = "mplayer " ++ₛ ddvs ++ₛ f (Lerfu.case q)
  where
  postulate f : Case → String
\end{code}

\section{la'oi .\F{spkCF}.}
ni'o lo nu xamgu .uniks.\ bo co'e la'o zoi.\ \F{spkCF} \B x .zoi.\ cu rinka lo nu selsnapra lo velski be lo me'oi .\F{bnam}.\ be la'oi .\B x.

\begin{code}
spkCF : Lerfu → Midnoi
spkCF q = "mplayer " ++ₛ ddvs ++ₛ f (Lerfu.bnam q)
  where
  f : Fin 128 → String
  f = Data.Nat.Show.show ∘ toℕ
\end{code}

\section{la'oi .\F{doit}.}

\begin{code}
doit : ∀ {a} → String → IO {a} ⊤
doit = liftx ∘ doit'
  where
  postulate doit' : String → PIO Unit
  {-# FOREIGN GHC import System.IO #-}
  {-# FOREIGN GHC import Data.Text #-}
  {-# FOREIGN GHC import Control.Monad #-}
  {-# FOREIGN GHC import System.Process #-}
  {-# COMPILE GHC doit' = \_ -> void . runCommand . unpack #-}
\end{code}

\section{la'oi .\F{spk}.}
ni'o ga naja co'e zoi zoi.\ \F{spk} \B q .zoi.\ gi lo skami cu bacru pe'a ru'e la'oi .\B q.

\begin{code}
spk : ∀ {a} → Lerfu → IO {a} ⊤
spk l = vecMapM′ doit $ intersperse denpaXipa $ spks l
  where
  vecMapM′ : ∀ {a b} → {n : ℕ} → {A : Set a}
           → (A → IO {b} ⊤) → Vec A n → IO {b} ⊤
  vecMapM′ f = IO.List.mapM′ f ∘ Data.Vec.toList
  denpaXipa : Midnoi
  denpaXipa = "sleep " ++ₛ Data.Float.show selsniduXiPa
  spks : Lerfu → Vec Midnoi _
  spks l = Data.Vec.map (flip _$_ l) $ spkCL ∷ spkCC ∷ spkCF ∷ []
\end{code}

\section{la'oi .\F{main}.}

\begin{code}
main = run $ getLine >>=ᵢₒ maybe bacru spojaPe'aRu'e ∘ genturfa'i
  where
  spojaPe'aRu'e : ∀ {a} → IO {a} ⊤
  spojaPe'aRu'e = liftx $ erroy $ jbo ++ₛ "\n\n" ++ₛ eng
    where
    jbo = "ni'o pruce fe lo lerfu poi \
          \ke'a na srana la .asycy'i'is."
    eng = "Inputs a non-ASCII character."
    postulate erroy : String → PIO Unit
    {-# COMPILE GHC erroy = \_ -> hPutStrLn stderr . unpack #-}
  bacru : ∀ {a} → List Lerfu → IO {a} ⊤
  bacru = ignore ∘ IO.List.sequence ∘ Data.List.map spk
\end{code}
\end{document}
