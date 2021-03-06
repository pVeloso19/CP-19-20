\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2021t}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2021t_media/#1.png}}
\let\uk=\emph
\def\aspas#1{``#1"}
%================= lhs2tex=====================================================%
%include polycode.fmt 
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const f) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format (cataA (f) (g)) = "\cata{" f "~" g "}_A"
%format (anaA (f) (g)) = "\ana{" f "~" g "}_A"
%format (cataB (f) (g)) = "\cata{" f "~" g "}_B"
%format (cata (f)) = "\cata{" f "}"
%format (anaB (f) (g)) = "\ana{" f "~" g "}_B"
%format Either a b = a "+" b 
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format e1 = "e_1 "
%format e2 = "e_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format BTree = "\fun{BTree} "
%format LTree = "\mathsf{LTree}"
%format inNat = "\mathsf{in}"
%format (cataNat (g)) = "\cata{" g "}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "

%---------------------------------------------------------------------------

\title{
       	C??lculo de Programas
\\
       	Trabalho Pr??tico
\\
       	MiEI+LCC --- 2020/21
}

\author{
       	\dium
\\
       	Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{red}{#1}}
\begin{document}

\maketitle

\begin{center}\large
\begin{tabular}{ll}
\textbf{Grupo} nr. & 51
\\\hline
a89557 & Pedro Veloso	
\\
a89587 & Carlos Preto	
\\
a93319 & Catarina Morales	
\end{tabular}
\end{center}

\section{Pre??mbulo}

\CP\ tem como objectivo principal ensinar
a progra\-ma????o de computadores como uma disciplina cient??fica. Para isso
parte-se de um repert??rio de \emph{combinadores} que formam uma ??lgebra da
programa????o (conjunto de leis universais e seus corol??rios) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto ??,
agregando programas j?? existentes.
  
Na sequ??ncia pedag??gica dos planos de estudo dos dois cursos que t??m
esta disciplina, opta-se pela aplica????o deste m??todo ?? programa????o
em \Haskell\ (sem preju??zo da sua aplica????o a outras linguagens 
funcionais). Assim, o presente trabalho pr??tico coloca os
alunos perante problemas concretos que dever??o ser implementados em
\Haskell.  H?? ainda um outro objectivo: o de ensinar a documentar
programas, a valid??-los e a produzir textos t??cnico-cient??ficos de
qualidade.

\section{Documenta????o} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma t??cnica de programa\-????o dita
``\litp{liter??ria}'' \cite{Kn92}, cujo princ??pio base ?? o seguinte:
%
\begin{quote}\em Um programa e a sua documenta????o devem coincidir.
\end{quote}
%
Por outras palavras, o c??digo fonte e a documenta????o de um
programa dever??o estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que est?? a ler ?? j?? um exemplo de
\litp{programa????o liter??ria}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrar?? no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} ??
um pre-processador que faz ``pretty printing''
de c??digo Haskell em \Latex\ e que deve desde j?? instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} ?? execut??vel e cont??m
o ``kit'' b??sico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2021t.lhs
\end{Verbatim}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where 
import Cp
import List hiding (fac)
import Nat
import LTree
import Data.List hiding (find)
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim ??: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
?? seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho te??rico-pr??tico deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avalia????o (datas para submiss??o do relat??rio e sua defesa
oral) s??o os que forem publicados na \cp{p??gina da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder ??s quest??es que ser??o colocadas
na \emph{defesa oral} do relat??rio.

Em que consiste, ent??o, o \emph{relat??rio} a que se refere o par??grafo anterior?
?? a edi????o do texto que est?? a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relat??rio dever?? conter ainda a identifica????o dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relat??rio deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o ??ndice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-?? ainda instalar o utilit??rio
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
gera????o de gr??ficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invoc??-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o n??mero de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) c??digo
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
c??digo \Haskell\ relativo aos problemas que se seguem. Esse anexo dever??
ser consultado e analisado ?? medida que isso for necess??rio.

\subsection{Stack}

O \stack{Stack} ?? um programa ??til para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito espec??fica:

\begin{itemize}
\item Os m??dulos auxiliares encontram-se na pasta \emph{src}.
\item O m??dulos principal encontra-se na pasta \emph{app}.
\item A lista de dep??ndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as dep??ndencias externas ser??o instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados alg??bricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Gra??as ?? sua flexibilidade,
torna-se trivial implementar \DSL s
e at?? mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programa????o}.

Paralelamente, um t??pico bastante estudado no ??mbito de \DL\ 
?? a deriva????o autom??tica de express??es matem??ticas, por exemplo, de derivadas.
Duas t??cnicas que podem ser utilizadas para o c??lculo de derivadas s??o:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplica????o sucessiva de transforma????es
(leia-se: fun????es) que sejam congruentes com as regras de deriva????o. O resultado
final ser?? a express??o da derivada.

O leitor atento poder?? notar um problema desta t??cnica: a express??o
inicial pode crescer de forma descontrolada, levando a um c??lculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da express??o em todos os passos.
Para tal, ?? necess??rio calcular o valor da express??o \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de express??es matem??ticas simples e
implementar as duas t??cnicas de deriva????o autom??tica.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam opera????es bin??rias e un??rias, respectivamente:

\begin{code}
data BinOp = Sum
           | Product
           deriving (Eq, Show)

data UnOp = Negate
          | E
          deriving (Eq, Show)
\end{code}

\noindent
O construtor |E| simboliza o exponencial de base $e$.

Assim, cada express??o pode ser uma vari??vel, um n??mero, uma opera????o bin??ria
aplicada ??s devidas express??es, ou uma opera????o un??ria aplicada a uma express??o.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na nota????o matem??tica habitual.

\begin{enumerate}
\item A defini????o das fun????es |inExpAr| e |baseExpAr| para este tipo ?? a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as fun????es |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| s??o testemunhas de um isomorfismo,
    isto ??,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma express??o aritm??tica e um escalar para substituir o |X|,
	a fun????o

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da express??o. Na p??gina \pageref{pg:P1}
    esta fun????o est?? expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A fun????o |eval_exp| respeita os elementos neutros das opera????es.
\begin{code}
prop_sum_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idr a exp = eval_exp a exp .=?=. sum_idr where
  sum_idr = eval_exp a (Bin Sum exp (N 0))

prop_sum_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idl a exp = eval_exp a exp .=?=. sum_idl where
  sum_idl = eval_exp a (Bin Sum (N 0) exp)

prop_product_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idr a exp = eval_exp a exp .=?=. prod_idr where
  prod_idr = eval_exp a (Bin Product exp (N 1))

prop_product_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idl a exp = eval_exp a exp .=?=. prod_idl where
  prod_idl = eval_exp a (Bin Product (N 1) exp)

prop_e_id :: (Floating a, Real a) => a -> Bool
prop_e_id a = eval_exp a (Un E (N 1)) == expd 1

prop_negate_id :: (Floating a, Real a) => a -> Bool
prop_negate_id a = eval_exp a (Un Negate (N 0)) == 0
\end{code}
    \end{propriedade}
    \begin{propriedade}
      Negar duas vezes uma express??o tem o mesmo valor que n??o fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item ?? poss??vel otimizar o c??lculo do valor de uma express??o aritm??tica tirando proveito
  dos elementos absorventes de cada opera????o. Implemente os genes da fun????o
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na p??gina \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual ?? a vantagem de implementar a fun????o |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A fun????o |optimize_eval| respeita a sem??ntica da fun????o |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma express??o, ?? necess??rio aplicar transforma????es
?? express??o original que respeitem as regras das derivadas:\footnote{%
	Apesar da adi????o e multiplica????o gozarem da propriedade comutativa,
	h?? que ter em aten????o a ordem das opera????es por causa dos testes.}

\begin{itemize}
  \item Regra da soma:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
  \item Regra do produto:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}

  Defina o gene do catamorfismo que ocorre na fun????o
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma express??o aritm??tica, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A fun????o |sd| respeita as regras de deriva????o.
\begin{code}
prop_const_rule :: (Real a, Floating a) => a -> Bool
prop_const_rule a = sd (N a) == N 0

prop_var_rule :: Bool
prop_var_rule = sd X == N 1

prop_sum_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_sum_rule exp1 exp2 = sd (Bin Sum exp1 exp2) == sum_rule where
  sum_rule = Bin Sum (sd exp1) (sd exp2)

prop_product_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_product_rule exp1 exp2 = sd (Bin Product exp1 exp2) == prod_rule where
  prod_rule =Bin Sum (Bin Product exp1 (sd exp2)) (Bin Product (sd exp1) exp2)

prop_e_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_e_rule exp = sd (Un E exp) == Bin Product (Un E exp) (sd exp)

prop_negate_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_negate_rule exp = sd (Un Negate exp) == Un Negate (sd exp)
\end{code}
    \end{propriedade}

\item Como foi visto, \emph{Symbolic differentiation} n??o ?? a t??cnica
mais eficaz para o c??lculo do valor da derivada de uma express??o.
\emph{Automatic differentiation} resolve este problema c??lculando o valor
da derivada em vez de manipular a express??o original.

  Defina o gene do catamorfismo que ocorre na fun????o
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma express??o aritm??tica e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a express??o original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| ?? equivalente a calcular a derivada da express??o e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programa????o din??mica} por c??lculo,
recorrendo ?? lei de recursividade m??tua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, p??gina \pageref{eq:fokkinga}.}

Para o caso de fun????es sobre os n??meros naturais (|Nat0|, com functor |fF
X = 1 + X|) ?? f??cil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que n??o tenham estudado
\cp{C??lculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
c??lculo do ciclo-\textsf{for} que implementa a fun????o de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-?? de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| ter?? tantos argumentos quanto o n??mero de fun????es mutuamente recursivas.
\item	Para as vari??veis escolhem-se os pr??prios nomes das fun????es, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros s??mbolos, mas numa primeira leitura
d?? jeito usarem-se tais nomes.}
\item	Para os resultados v??o-se buscar as express??es respectivas, retirando a vari??vel |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das fun????es, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polin??mios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o m??todo estudado nas aulas\footnote{Sec????o 3.17 de \cite{Ol18} e t??pico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade m??tua} nos v??deos das aulas te??ricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas fun????es mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementa????o, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}
O que se pede ent??o, nesta pergunta?
Dada a f??rmula que d?? o |n|-??simo \catalan{n??mero de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementa????o de $C_n$ que n??o calcule factoriais nenhuns.
Isto ??, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta fun????o.

\begin{propriedade}
A fun????o proposta coincidem com a defini????o dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugest??o}: Come??ar por estudar muito bem o processo de c??lculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da fun????o exponencial.


\Problema 

As \bezier{curvas de B??zier}, designa????o dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre B??zier},
s??o curvas ub??quas na ??rea de computa????o gr??fica, anima????o e modela????o.
Uma curva de B??zier ?? uma curva param??trica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ ?? a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de B??zier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} ?? um m??todo recursivo capaz de calcular
curvas de B??zier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo ?? numericamente mais est??vel, trocando velocidade por corre????o.

De forma sucinta, o valor de uma curva de B??zier de um s?? ponto $\{P_0\}$
(ordem $0$) ?? o pr??prio ponto $P_0$. O valor de uma curva de B??zier de ordem
$N$ ?? calculado atrav??s da interpola????o linear da curva de B??zier dos primeiros
$N-1$ pontos e da curva de B??zier dos ??ltimos $N-1$ pontos.

A interpola????o linear entre 2 n??meros, no intervalo $[0, 1]$, ?? dada pela
seguinte fun????o:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpola????o linear entre 2 pontos de dimens??o $N$ ?? calculada atrav??s
da interpola????o linear de cada dimens??o.

O tipo de dados |NPoint| representa um ponto com $N$ dimens??es.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimens??es e um ponto de 3 dimens??es podem ser
representados, respetivamente, por:
\begin{spec}
p2d = [1.2, 3.4]
p3d = [0.2, 10.3, 2.4]
\end{spec}
%
O tipo de dados |OverTime a| representa um termo do tipo |a| num dado instante
(dado por um |Float|).
\begin{code}
type OverTime a = Float -> a
\end{code}
%
O anexo \ref{sec:codigo} tem definida a fun????o 
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpola????o linear entre 2 pontos, e a fun????o
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua defini????o com a propriedade:
    \begin{propriedade} Defini????o alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a fun????o |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de B??zier s??o sim??tricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a fun????o |runBezier| e aprecie o seu trabalho\footnote{%
        A representa????o em Gloss ?? uma adapta????o de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que ?? aberta (que cont??m, a verde, um ponto
        inicila) com o bot??o esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a f??rmula que calcula a m??dia de uma lista n??o vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto ??, para sabermos a m??dia de uma lista precisamos de dois catamorfismos: o que faz o somat??rio e o que calcula o comprimento a lista.
Contudo, ?? facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ est?? em recursividade m??tua com $length$ e o par de fun????es pode ser expresso por um ??nico catamorfismo, significando que a lista apenas ?? percorrida uma vez.

\begin{enumerate}

\item	Recorra ?? lei de recursividade m??tua para derivar a fun????o
|avg_aux = cata (either b q)| tal que 
|avg_aux = split avg length| em listas n??o vazias. 

\item	Generalize o racioc??nio anterior para o c??lculo da m??dia de todos os elementos de uma \LTree\ recorrendo a uma ??nica travessia da ??rvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas fun????es testando a propriedade seguinte:
\begin{propriedade}
A m??dia de uma lista n??o vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 mil??simas:
\begin{code}
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta quest??o ?? \textbf{opcional} e funciona como \textbf{valoriza????o} apenas para os alunos que desejarem faz??-la.) 

\vskip 1em \noindent
Existem muitas linguagens funcionais para al??m do \Haskell, que ?? a linguagem usada neste trabalho pr??tico. Uma delas ?? o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os m??dulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede ?? a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execu????o: o c??digo que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para al??m disso, os grupos podem demonstrar o c??digo na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir c??lculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.} 
\begin{eqnarray*}
\start
	|id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
		p1 . id = f
	)(
		p2 . id = g
	)|
%
\just\equiv{ identity }
%
        |lcbr(
		p1 = f
	)(
		p2 = g
	)|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo ?? \emph{package} \LaTeX\ 
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo: 
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Programa????o din??mica por recursividade m??ltipla}\label{sec:recmul}
Neste anexo d??o-se os detalhes da resolu????o do Exerc??cio \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, p??gina \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o c??lculo da aproxima????o at?? |i=n| da fun????o exponencial $exp\ x = e^x$,
via s??rie de Taylor:
\begin{eqnarray}
	exp\ x 
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a fun????o que d?? essa aproxima????o.
?? f??cil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
m??tua. Se repetirmos o processo para |h x n| etc obteremos no total tr??s fun????es nessa mesma
situa????o:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na p??gina \ref{pg:regra} deste enunciado,
ter-se-??, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{C??digo fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Defini????o da s??rie de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Or??culo para inspec????o dos primeiros 26 n??meros de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}

\subsection*{Problema 3}
Algoritmo:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = nil
deCasteljau [p] = const p
deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljau (init l)
  q = deCasteljau (tail l)
\end{spec}
Fun????o auxiliar:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}
2D:
\begin{code}
bezier2d :: [NPoint] -> OverTime (Float, Float)
bezier2d [] = const (0, 0)
bezier2d l = \z -> (fromRational >< fromRational) . (\[x, y] -> (x, y)) $ ((deCasteljau l) z)
\end{code}
Modelo:
\begin{code}
data World = World { points :: [NPoint]
                   , time :: Float
                   }
initW :: World
initW = World [] 0

tick :: Float -> World -> World
tick dt world = world { time=(time world) + dt }

actions :: Event -> World -> World
actions (EventKey (MouseButton LeftButton) Down _ p) world =
  world {points=(points world) ++ [(\(x, y) -> map toRational [x, y]) p]}
actions (EventKey (SpecialKey KeyDelete) Down _ _) world =
    world {points = cond (== []) id init (points world)}
actions _ world = world

scaleTime :: World -> Float
scaleTime w = (1 + cos (time w)) / 2

bezier2dAtTime :: World -> (Float, Float)
bezier2dAtTime w = (bezier2dAt w) (scaleTime w)

bezier2dAt :: World -> OverTime (Float, Float)
bezier2dAt w = bezier2d (points w)

thicCirc :: Picture
thicCirc = ThickCircle 4 10

ps :: [Float]
ps = map fromRational ps' where
  ps' :: [Rational]
  ps' = [0, 0.01..1] -- interval
\end{code}
Gloss:
\begin{code}
picture :: World -> Picture
picture world = Pictures
  [ animateBezier (scaleTime world) (points world)
  , Color white . Line . map (bezier2dAt world) $ ps
  , Color blue . Pictures $ [Translate (fromRational x) (fromRational y) thicCirc | [x, y] <- points world]
  , Color green $ Translate cx cy thicCirc
  ] where
  (cx, cy) = bezier2dAtTime world
\end{code}
Anima????o:
\begin{code}
animateBezier :: Float -> [NPoint] -> Picture
animateBezier _ [] = Blank
animateBezier _ [_] = Blank
animateBezier t l = Pictures
  [ animateBezier t (init l)
  , animateBezier t (tail l)
  , Color red . Line $ [a, b]
  , Color orange $ Translate ax ay thicCirc
  , Color orange $ Translate bx by thicCirc
  ] where
  a@(ax, ay) = bezier2d (init l) t
  b@(bx, by) = bezier2d (tail l) t
\end{code}
Propriedades e \emph{main}:
\begin{code}
runBezier :: IO ()
runBezier = play (InWindow "B??zier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compila????o e execu????o dentro do interpretador:\footnote{Pode ser ??til em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma fun????o
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
C??digo para gera????o de testes:
\begin{code}
instance Arbitrary UnOp where
  arbitrary = elements [Negate, E]

instance Arbitrary BinOp where
  arbitrary = elements [Sum, Product]

instance (Arbitrary a) => Arbitrary (ExpAr a) where
  arbitrary = do
    binop <- arbitrary
    unop  <- arbitrary
    exp1  <- arbitrary
    exp2  <- arbitrary
    a     <- arbitrary

    frequency . map (id >< pure) $ [(20, X), (15, N a), (35, Bin binop exp1 exp2), (30, Un unop exp1)]


infixr 5 .=?=.
(.=?=.) :: Real a => a -> a -> Bool
(.=?=.) x y = (toRational x) == (toRational y)


\end{code}

\subsection*{Outras fun????es auxiliares}
%----------------- Outras defini????es auxiliares -------------------------------------------%
L??gicas:
\begin{code}
infixr 0 .==>.
(.==>.) :: (Testable prop) => (a -> Bool) -> (a -> prop) -> a -> Property
p .==>. f = \a -> p a ==> f a

infixr 0 .<==>.
(.<==>.) :: (a -> Bool) -> (a -> Bool) -> a -> Property
p .<==>. f = \a -> (p a ==> property (f a)) .&&. (f a ==> property (p a))

infixr 4 .==.
(.==.) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f .==. g = \a -> f a == g a

infixr 4 .<=.
(.<=.) :: Ord b => (a -> b) -> (a -> b) -> (a -> Bool)
f .<=. g = \a -> f a <= g a

infixr 4 .&&&.
(.&&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
f .&&&. g = \a -> ((f a) && (g a))
\end{code}

%----------------- Solu????es dos alunos -----------------------------------------%

%format (expn (a) (n)) = "{" a "}^{" n "}"

\section{Solu????es dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas solu????es para os exerc??cios
propostos, de acordo com o "layout" que se fornece. N??o podem ser
alterados os nomes ou tipos das fun????es dadas, mas pode ser adicionado
texto, disgramas e/ou outras fun????es auxiliares que sejam necess??rias.

Valoriza-se a escrita de \emph{pouco} c??digo que corresponda a solu????es
simples e elegantes. 

\subsection*{Problema 1} \label{pg:P1}
S??o dadas:
\begin{code}
cataExpAr g = g . recExpAr (cataExpAr g) . outExpAr
anaExpAr g = inExpAr . recExpAr (anaExpAr g) . g
hyloExpAr h g = cataExpAr h . anaExpAr g

eval_exp :: Floating a => a -> (ExpAr a) -> a
eval_exp a = cataExpAr (g_eval_exp a)

optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
optmize_eval a = hyloExpAr (gopt a) clean

sd :: Floating a => ExpAr a -> ExpAr a
sd = p2 . cataExpAr sd_gen

ad :: Floating a => a -> ExpAr a -> a
ad v = p2 . cataExpAr (ad_gen v)
\end{code}
Para se descobrir a defini????o de |outExpAr|, e uma vez que j?? se sabe a defini????o de |inExpAr|, recorreu-se ?? propriedade dos isomorfismos |out . in = id|.

\begin{eqnarray*}
\start
  outExpAr . inExpAr = id
%
\just\equiv{inExpAr = [(const X), num\textunderscore ops]}
%
  |outExpAr . [(const X), num_ops] = id|
%
\just\equiv{ (20) }
%
  |[outExpAr . (const X), outExpAr . num_ops] = id|
%
\just\equiv{ (17) }
%
        |lcbr(
    id . i1 = outExpAr . (const X)
  )(
    id . i2 = outExpAr . num_ops
  )|
%
\just\equiv{ (1), Esquerda: (71) }
%
        |lcbr(
    i1 x = (outExpAr . (const X)) x
  )(
    i2 = outExpAr . num_ops
  )|
%
\just\equiv{ Esquerda: (72) }
%
        |lcbr(
    i1 x = outExpAr ((const X) x) 
  )(
    i2 = outExpAr . num_ops
  )|
%
\just\equiv{ Esquerda: (74) }
%
        |lcbr(
    i1 () = outExpAr X 
  )(
    i2 = outExpAr . num_ops
  )|
%
\just\equiv{ Direita: num\textunderscore ops = [N, ops]}
%
        |lcbr(
    i1 () = outExpAr X
  )(
    i2 = outExpAr . [N, ops]
  )|
%
\just\equiv{ Direita: (20), (17)}
%
        |lcbr(
    i1 () = outExpAr X
  ) (lcbr (
    i2 . i1 = outExpAr . N)  (i2 . i2 = outExpAr . ops
  ))|
%
\just\equiv{ Primeira Direita: (71)}
%
        |lcbr(
    i1 () = outExpAr X
  ) (lcbr (
    (i2 . i1) x = (outExpAr . N) x) (i2 . i2 = outExpAr . ops
  ))|
%
\just\equiv{ Pimeira Direita: (72)}
%
        |lcbr(
    i1 () = outExpAr X
  ) (lcbr (
    i2 (i1 x) = outExpAr (N x)) (i2 . i2 = outExpAr . ops))|
%
\just\equiv{ Segunda Direita: ops = [bin, (uncurry Un)]}
%
        |lcbr(
    i1 () = outExpAr X
  ) (lcbr (
    i2 (i1 x) = outExpAr (N x)) (i2 . i2 = outExpAr . [bin, (uncurry Un)]))
    |
%
\just\equiv{ Segunda Direita: (20), (17)}
%
        |lcbr(
    i1 () = outExpAr X
  ) (lcbr (
    i2 (i1 x) = outExpAr (N x)) (lcbr (
    i2 . i2 . i1 = outExpAr . bin) (i2 . i2 . i2 = outExpAr . (uncurry Un))))|
%
\just\equiv{ Segunda Direita: (71)}
%
        |lcbr(
    i1 () = outExpAr X
  ) (lcbr (
    i2 (i1 x) = outExpAr (N x)) (lcbr (
    (i2 . i2 . i1) (x, (y,z)) = (outExpAr . bin) (x, (y,z))) ((i2 . i2 . i2) (x, y) = (outExpAr . (uncurry Un)) (x, y))))|
%
\just\equiv{ Segunda Direita: (72)}
%
        |lcbr(
    i1 () = outExpAr X
  ) (lcbr (
    i2 (i1 x) = outExpAr (N x)) (lcbr (i2 (i2 (i1 (x, (y,z)))) = outExpAr (Bin x y z)) (i2 (i2 (i2 (x, y)) = outExpAr (Un x y))))|
%
\end{eqnarray*}\par

Assim, outExpAr pode ser definido como:

\begin{code}
outExpAr X = i1 ()
outExpAr (N a) = i2 (i1 a)
outExpAr (Bin bp l r) = i2 (i2 (i1 (bp,(l,r))))
outExpAr (Un up e) = i2 (i2 (i2 (up,e)))
\end{code}

Uma vez descoberto o tipo de saida de |outExpAr|, torna-se bastante f??cil definir a fun????o |recExpAr|, visto que apenas nos interessa aplicar a recursividade aos tipos |ExpAr|, enquanto que nos restantes basta aplicar a fun????o id, fazendo com que nunca se alterem. 

\begin{code}
recExpAr f = baseExpAr id id id f f id f
\end{code}

Realtivamente ao gene de |eval_exp|, recorreu-se ao seguinte diagrama, de maneira a facilitar a compreens??o dos tipos.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr a| \ar[d]_-{|eval_exp|} \ar@@/^1pc/[r]^-{|outExpAr|}
&
    |1 + (a + (BinOp >< (ExpAr a >< ExpAr a) + UnOp >< ExpAr a))| \ar@@/^1pc/[l]^-{|inExpAr|} \ar[d]^{|id + (id + (id >< (eval_exp >< eval_exp) + id >< eval_exp))|}
\\
     |a|
&
     |1 + (a + (BinOp >< (a >< a) + UnOp >< a))| \ar[l]^-{|g_eval_exp|}
}
\end{eqnarray*}

Como se pode observar, o gene do catamorfismo corresponde ?? seta mais abaixo no diagrama. ?? f??cil perceber que, quando o termo for vazio, basta devolver o valor escalar que nos ?? fornecido, e quando o termo j?? for um valor do tipo |a|, simplesmente se devolve o pr??prio elemento. Relativamente ?? parte recursiva, foram criadas duas fun????es auxiliares, sendo essas a |operationBin| e a |operationUn|. A |operationBin| trata os casos onde se recebe como primeiro elemento um par do tipo |BinOp| e como segundo elemento um par de valores do tipo |a|. Caso |BinOp| seja do tipo |Sum|, soma-se os dois valores, e caso seja do tipo |Product|, realiza-se a sua multiplica????o. A |operationUn| trata os casos onde se recebe um par com o primeiro elemento do tipo |UnOp| e o segundo elemento um valor do tipo |a|. Aqui, caso |UnOp| se trate de um |Negate|, devolve-se a nega????o do elemento, e caso se trate de |E|, devolve-se a exponencia????o de |a|.

\newpage

\begin{code}
g_eval_exp a = either (const a) (g_val_exp_aux a)
             where g_val_exp_aux a = either id (either operationBin operationUn)
\end{code}

\begin{code}
operationBin (f,(a,b)) = if f == Sum then a+b
                         else a*b

operationUn (f,a) = if f == Negate then -a
                    else expd a
\end{code}

Para definir os genes da fun????o |optmize_eval|, foi necess??rio definir o seu diagrama, como um hilomorfismo, para perceber os tipos de entrada e sa??da de cada gene. 

\begin{eqnarray*}
\xymatrix@@C=3cm@@R=1cm{
    |ExpAr a| \ar[d]_-{|clean|} \ar@@/^1pc/[r]^-{|gene de clean|}
&
    |1 + (a + (BinOp >< (ExpAr a >< ExpAr a) + UnOp >< ExpAr a))| \ar[d]^{|id + (id + (id >< (clean >< clean) + id >< clean))|}
\\
     |ExpAr a| \ar@@/^1pc/[r]^-{|outExp|} \ar[d]_-{|gopt|}
&
     |1 + (a + (BinOp >< (ExpAr a >< ExpAr a) + UnOp >< ExpAr a))| \ar@@/^1pc/[l]^-{|inExpAr|} \ar[d]^{|id + (id + (id >< (gopt >< gopt) + id >< gopt))|}
\\
     |a|
&
     |1 + (a + (BinOp >< (a >< a) + UnOp >< a))| \ar[l]^-{|gene de gopt|}
}
\end{eqnarray*}

Ao analisar o diagrama, percebe-se que estamos perante um caso particular de um anamorfismo, onde a estrutura que o anamorfismo devolve ?? do mesmo tipo de entrada. Assim, |clean| pode ser visto como um tipo especial de |outExpAr|, s?? que desta vez, quando se estiver perante o elemento absorvente da multiplica????o, que ?? 0, ao inv??s de retornar a express??o da multiplica????o, pode simplesmente devolver-se |N 0|, diminuindo assim o trabalho do catamorfismo. Tamb??m se considerou que, o exponencial |e| elevado a 0 dar?? sempre 1. A fun????o auxiliar |anyZero| verifica se algum elemento da esquerda ou da direita ?? |N 0|, devolvendo |True| caso tal se verifique.

\begin{code}
clean X = i1 ()
clean (N a) = i2 (i1 a)
clean (Bin bp l r) = if (bp == Product && (anyZero(l,r))) then i2 (i1 0)
                     else i2 (i2 (i1 (bp,(l,r))))
clean (Un up e) = if (up == E && (e == (N 0))) then i2 (i1 1)
                  else i2 (i2 (i2 (up,e)))
 
anyZero(l,r) = if (l == (N 0) || r == (N 0)) then True
               else False
\end{code}

Relativamente ao gene de |gopt|, ?? poss??vel perceber que este ?? semelhante ao gene da fun????o |g_eval_exp|, pelo que se reutilizar?? as fun????es |operationBin| e |operationUn|.

\begin{code}
gopt a = either (const a) (gopt_aux a)
        where gopt_aux a = either id (either operationBin operationUn) 
\end{code}

Analisando o c??digo fornecido para a fun????o |sd|, verifica-se que o resultado se encontra no segundo elemento do par devolvido pelo cataExpAr |sd_gen|. 

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr a| \ar[d]_-{|cata sd_gen|} \ar@@/^1pc/[r]^-{|outExpAr|}
&
    |1 + (a + (BinOp >< (ExpAr a >< ExpAr a) + UnOp >< ExpAr a))| \ar@@/^1pc/[l]^-{|inExpAr|} \ar[d]^{|id + (id + (id >< (cata sd_gen >< cata sd_gen) + id >< cata sd_gen))|}
\\
     |ExpAr a|
&
     |1 + (a + (BinOp >< (ExpAr a >< ExpAr a) + UnOp >< ExpAr a))| \ar[l]^-{|[g1, g2]|}
}
\end{eqnarray*}

No caso de paragem apenas se necessita de devolver um par onde no primeiro elemento est?? o termo |X| (visto que quando se aplica |outExpAr| a |X| este d?? o ??nico habitante do tipo 1), e no segundo elemento a derivada de |X| (que ser?? sempre |N 1|).
\par Quando o termo ?? do tipo |a| apenas se necessita de devolver um par onde no primeiro elemento est?? o termo |N a|, e no segundo elemento a respetiva derivada |N 0|.
\par Tamb??m se pode estar na presen??a de um par do tipo |(BinOp, ((a, b),(c, d)))|, onde ?? importante notar que o primeiro par |(a, b)| corresponde ?? primeira |ExpAr| e ?? sua derivada, e o par |(c, d)| corresponde ?? segunda |ExpAr| e ?? sua derivada. 
\par Por fim, pode-se estar na presen??a de um par do tipo |(UnOp, (a,b))|, onde mais uma vez, o termo |a| tem o valor da |ExpAr| e o termo |b| tem a derivada desse valor. Assim, com base na explica????o de deriva????es presentes no documento, ?? poss??vel produzir duas fun????es axiliares, |decideBin| e |decideUn|, que tratam de derivar corretamente as express??es.

\begin{code}
sd_gen :: Floating a => 
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a)))) 
    -> (ExpAr a, ExpAr a)
sd_gen = either (\() -> (X, N 1)) sd_gen_aux1
       where sd_gen_aux1 = either  (\a -> (N a, N 0)) sd_gen_aux2

\end{code}

\begin{code}
sd_gen_aux2 = either decideBin decideUn

decideBin (f, ((a, b),(c, d))) = if f == Sum then (Bin Sum a c, Bin Sum b d)
                                 else (Bin Product a c, Bin Sum (Bin Product a d) (Bin Product b c))    

decideUn (f, (a,b)) = if f == Negate then (Un Negate a, Un Negate b)
                      else (Un E a, Bin Product (Un E a) b)
\end{code}

Por fim, foi necess??rio definir |ad_gen|. Analisando a fun????o |ad|, percebe-se que esta devolve um par, em que o resultado da derivada no ponto se encontra no segundo elemento do par devolvido pelo cataExpAr |ad_gen v|. Conclui-se assim que |ad_gen| ir?? devolver um par, onde no primeiro elemento estar?? o resultado da substitui????o do ponto na express??o original, e no segundo elemento estar?? o resultado da derivada no ponto. 
\par Quando o termo ?? do tipo |(BinOp, ((a, b), (c, d)))|, no termo |a| estar?? o resultado da substitui????o do ponto na primeira |ExpAr|, no termo |b| estar?? a derivada dessa |ExpAr| no ponto, no termo |c| estar?? o resultado da substitui????o do ponto na segunda |ExpAr| e no termo |d| estar?? a derivada dessa |ExpAr| no ponto. Assim, na fun????o auxiliar |dB|, conforme o tipo de |BinOp|, ?? poss??vel descobrir todos os valores necess??rios.
\par Por ??ltimo, quando o termo ?? do tipo |(UnOp, (a, b))|, no termo |a| estar?? o valor do ponto pretendido e no termo |b| estar?? a derivada da |ExpAr| no ponto. Assim, na fun????o auxiliar |dU|, se estivermos perante um |Negate|, devolve-se um par com a nega????o do ponto e a nega????o da sua derivada. Se estivermos perante um |E|, ent??o devolve-se um par com a exponencial do ponto e com a multiplica????o da exponencial no ponto pela derivada da |ExpAr| no ponto.

\begin{code}
ad_gen v = either (ad_aux1 v) ad_aux2

ad_aux1 v () = (v, 1)

ad_aux2 :: Floating a => (Either a (Either (BinOp, ((a, a), (a, a))) (UnOp, (a, a)))) -> (a, a)
ad_aux2 = either ad_aux3 ad_aux4

ad_aux3 a = (a, 0)

ad_aux4 :: Floating a => (Either (BinOp, ((a, a), (a, a))) (UnOp, (a, a))) -> (a, a)
ad_aux4 = either dB dU

dB (f, ((a, b), (c, d))) = if f == Sum then (a+c, b+d) 
                           else (a*c, a*d + b*c)

dU (f, (a, b)) = if f == Negate then (negate(a), negate(b)) 
                 else (expd(a), expd(a)*b)
\end{code}

\newpage

\subsection*{Problema 2}
Para se descobrir como simplificar o algoritmo de |Catalan|, de maneira a n??o usar fatoriais,foi necess??rio desenvolver a f??rmula fornecida pelos docentes. De seguida, apresenta-se a redu????o que foi feita na f??rmula de |Catalan|:
\begin{equation}
C_n = \frac{(2*n)!} {(n+1)!*(n)!}
\end{equation}

\begin{equation}
C_n = \frac{(2*n)(2n-1)!} {(n+1)n!*n(n-1)!}
\end{equation}

\begin{equation}
C_n = \frac{2(2n-1)!} {(n+1)n!*(n-1)!}
\end{equation}

\begin{equation}
C_n = \frac{2(2n-1)(2n-2)!} {(n+1)n!*(n-1)(n-2)!}
\end{equation}

\begin{equation}
C_n = \frac{2(2n-1)} {(n+1)} * \frac{(2n-2)!} {n!(n-1)(n-2)!}
\end{equation}

\begin{equation}
C_n = \frac{2(2n-1)} {(n+1)} * \frac{2(n-1)(2n-3)!} {n!(n-1)(n-2)!}
\end{equation}

\begin{equation}
C_n = \frac{2(2n-1)} {(n+1)} * \frac{2(2n-3)!} {n(n-1)!(n-2)!}
\end{equation}

\begin{equation}
C_n = \frac{2(2n-1)} {(n+1)} * \frac{2(2n-3)(2n-4)!} {n(n-1)!(n-2)!}
\end{equation}

\begin{equation}
C_n = \frac{2(2n-1)} {(n+1)} * \frac{2(2n-3)} {n} * ...
\end{equation}

Atrav??s do desenvolvimento da f??rmula, ?? poss??vel perceber que um determinado n??mero de |Catalan| poder?? ser calculado ?? custa do n??mero de |Catalan| anterior. Assim, ap??s simplifica????o da f??rmula, chegou-se ?? seguinte equa????o:


\begin{equation}
C_0 = 1, C_n = \frac{ 2(2n - 1)} {n+1} C_{n-1}
\end{equation}

Ap??s descoberta a f??rmula, tornou-se bastante simples definir a fun????o por recursividade m??tua. A fun????o |inic| ser?? inicializada com o par |(1, 1)|, enquante que a fun????o |loop| ser?? chamada recursivamente. Desta forma, a fun????o |loop| ter?? 2 elementos, onde o primeiro elemento ter?? o ??ndice da itera????o atual, e o segundo elemento ter?? o n??mero de |Catalan| da itera????o anterior.

\begin{code}
loop (a,b) = (a+1, div (b*(2*((2*a)-1))) (a+1))
inic = (1,1)
prj = p2
cat = prj . (for loop inic)
\end{code}

Como um ciclo for ?? definido atrav??s de um catamorfismo de naturais, a fun????o |cat| tamb??m poder?? ser especificada como um catamorfismo de naturais (denominada como catalan), como ilustrado no seguinte diagrama:


\begin{eqnarray*}
\xymatrix@@C=4cm{
    |Nat0| \ar[d]_-{|catalan|} \ar@@/^1pc/[r]^-{|out|}
&
    |1 + Nat0| \ar@@/^1pc/[l]^-{|inNat|} \ar[d]^{|id + catalan|}
\\
     |Nat0 >< Nat0|
&
     |1 + Nat0 >< Nat0| \ar[l]^-{|[const (1,1), loop]|}
}
\end{eqnarray*}

Ap??s obter como resultado o par, onde o primeiro elemento ?? o sucessor e o segundo elemento ?? o |Catalan| do natural introduzido, apenas nos interessa o segundo elemento elemento do par, de modo a obter o mesmo resultado que o obtido na fun????o |cat|.

\subsection*{Problema 3}

Com base no c??digo da fun????o |calcLine| fornecido, foi poss??vel definir este ?? custa de um catamorfismo. Numa primeira fase, definiu-se o diagrama do catamorfismo.

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |NPoint| \ar[d]_-{|calcLine|} \ar@@/^1pc/[r]^-{|outList|}
&
    |1 + Rational >< NPoint| \ar@@/^1pc/[l]^-{|inList|} \ar[d]^{|id + id >< calcLine|}
\\
     |expn (OverTime NPoint) NPoint|
&
     |1 + Rational >< expn (OverTime NPoint) NPoint| \ar[l]^-{h}
}
\end{eqnarray*}

Como |NPoint| ?? uma lista de |Rational|, ent??o cada elemento de |NPoint| ser?? do tipo |Rational|. 
No caso de paragem, ?? devolvida a lista vazia, tal como se pode verificar na fun????o auxiliar |calcLine_aux1|. 
\par A fun????o auxiliar |calcLine_aux2| recebe como par??metros um par e um |NPoint|. O primeiro elemento do par tem o elemento ?? cabe??a do primeiro |NPoint| e o segundo elemento do par tem uma fun????o que recebe um |NPoint| e devolve um |OverTime NPoint|. Se o |NPoint| for nulo, ent??o o resultado ser?? dado pela aplica????o da fun????o que recebe um |NPoint| e devolve um |OverTime NPoint|, aplicada ?? lista vazia. Caso contr??rio, basta dar como argumentos da fun????o |linear1d| o primeiro elemento do par e primeiro elemento da lista, e depois aplicar a fun????o, que se encontra no segundo elemento do par, ?? cauda do segundo |NPoint|. 

\begin{code}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine = cataList h where
   h = either calcLine_aux1 calcLine_aux2

calcLine_aux1 () = const nil

calcLine_aux2 (r, f) [] = f []
calcLine_aux2 (r, f) (h:t) = \z -> concat $ (sequenceA [singl . linear1d r h, f t]) z
\end{code}
De maneira a definir a fun????o de |deCasteljau| como um hilomorfismo, foi necess??rio definir um novo tipo de dados. Inicialmente, pensou-se na possibilidade de definir esta fun????o como um hilomorfismo de |LTree|, por??m, ap??s alguns testes, percebeu-se que o algoritmo n??o funcionava para listas vazias. Assim, desenvolveu-se o seguinte tipo de dados:

\begin{code}
data AlgForm a = Vazio | Elemento a | Raiz (AlgForm a, AlgForm a) deriving (Show, Eq)
\end{code}

O tipo de dados |AlgForm| foi baseado no tipo |LTree|, acrescentando a possibilidade de um dado elemento desse tipo poder ser |Vazio|. Al??m do |Vazio|, |AlgForm| tamb??m poder?? ser formada por apenas um |Elemento|, ou ent??o uma |Raiz| formada por um par de |AlgForm|'s, assemelhando-se assim a uma ??rvore, tal como pretendido.

Uma vez definido o tipo de dados, foi necess??rio definir o |in| e o |out|, bem como o funtor deste tipo de dados, sendo que posteriormente definidos estes, se pode definir o |cataAlgForm|, |anaAlgForm| e |hiloAlgForm|.

\begin{code}
inAlgForm = either (const Vazio) (either Elemento Raiz)

outAlgForm Vazio = i1 ()
outAlgForm (Elemento a) = i2 (i1 a)
outAlgForm (Raiz (l, r)) = i2 (i2 (l, r))

recAlgForm f = baseAlgForm id f
baseAlgForm g f = id -|- (g -|- (f >< f))
cataAlgForm a = a . (recAlgForm (cataAlgForm a)) . outAlgForm
anaAlgForm f = inAlgForm . (recAlgForm (anaAlgForm f) ) . f

hyloAlgForm f g = cataAlgForm f . anaAlgForm g
\end{code}

Uma vez definido tudo o que era necess??rio relativamente ao tipo de dados, foi necess??rio desenhar o diagrama do hilomorfismo associado ao |deCasteljau|, com base no novo tipo de dados.
\begin{eqnarray*}
\xymatrix@@C=3cm@@R=1cm{
    |NPoint*| \ar[d]_-{|coalg|} \ar@@/^1pc/[r]^-{|gene de coalg|}
&
    |1 + NPoint + NPoint* >< NPoint*| \ar[d]^{|id + (id + (coalg >< coalg))|}
\\
     |AlgForm NPoint*| \ar@@/^1pc/[r]^-{|outAlgForm|} \ar[d]_-{|alg|}
&
     |1 + NPoint + AlgForm NPoint* >< AlgForm NPoint*| \ar@@/^1pc/[l]^-{|inAlgForm|} \ar[d]^{|id + (id + (alg >< alg))|}
\\
     |OverTime NPoint|
&
     |1 + NPoint + OverTime NPoint >< OverTime NPoint| \ar[l]^-{|gene de alg|}
}
\end{eqnarray*}

Como podemos reparar, se a lista for vazia, o gene do anamorfismo devolve o ??nico habitante do tipo 1, que ?? o vazio. Se s?? tiver um elemento, o gene do anamorfismo devolve o pr??prio elemento, e, caso a lista tenha mais que um elemento, devolve um par constituido por duas listas, a primeira com todos os constituintes da lista excepto o ??ltimo elemento, e a segunda com todos os constituintes da lista excepto o primeiro elemento.
Relativamente ao gene do catamorfismo, este transformar?? o |AlgForm| de lista de |NPoint| num |OverTime NPoint|.

\begin{code}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau = hyloAlgForm alg coalg

coalg[] = i1 ()
coalg[p] = i2 (i1 p)
coalg(l) = i2 (i2 (init l, tail l))

alg = either algAux1 algAux2

algAux1 = \() -> nil
algAux2 = either g1 g2

g1 a b = a
g2 (l, r) = \pt -> (calcLine (l pt) (r pt)) pt
\end{code}


\subsection*{Problema 4}
\underline{Solu????o para listas n??o vazias:}

A solu????o para listas n??o vazias dado por um catamorfismo de listas ?? representado pelo seguinte diagrama. 

\begin{eqnarray*}
\xymatrix@@C=4cm{
    |a*| \ar[d]_-{|avg_aux|} \ar@@/^1pc/[r]^-{|outList|}
&
    |1 + a >< a*| \ar@@/^1pc/[l]^-{|inList|} \ar[d]^{|id + id >< avg_aux|}
\\
     |a >< a|
&
     |1 + a >< (a >< a)| \ar[l]^-{|[avg_aux1, avg_aux2]|}
}
\end{eqnarray*}

Assim, a fun????o |avg| devolve o primeiro elemento do par devolvido pelo catamorfismo. Na fun????o |avg_aux| considera-se que, no caso de paragem, ?? retornado o par (0,0), visto que no in??cio, quer a m??dia, quer o tamanho da lista s??o 0.
\par Quando a fun????o |avg_aux2| receber o par |(c, (a, x))|, o termo |c| corresponde ao primeiro elemento da lista, |a| corresponde ?? m??dia da lista e |x| ao n??mero de elementos da lista. Assim, para obter a nova m??dia, basta somar o termo |c| com o somat??rio da lista (dado pela multiplica????o da m??dia pelo n??mero de elementos), e dividir tudo pelo novo tamanho, que corresponde ao incremento de uma unidade no tamanho anterior.

\begin{code}
avg = p1.avg_aux

avg_aux = cataList (either avg_aux1 avg_aux2)

avg_aux1 a = (0,0)

avg_aux2 (c, (a,x)) = ((c+(x*a))/(x+1), x+1)
\end{code}
\underline{Solu????o para ??rvores de tipo \LTree:}

Definir a fun????o |avg| para ??rvores do tipo |LTree| ?? bastante semelhante a definir a fun????o |avg|, por??m, torna-se mais f??cil compreeender esta fun????o ap??s se definir o seu diagrama.

\begin{eqnarray*}
\xymatrix@@C=4cm{
    |LTree a| \ar[d]_-{|cata gene|} \ar@@/^1pc/[r]^-{|outLTree|}
&
    |a + LTree a >< LTree a| \ar@@/^1pc/[l]^-{|inLTree|} \ar[d]^{|id + cata gene >< cata gene|}
\\
     |a >< a|
&
     |a + ((a >< a) >< (a >< a))| \ar[l]^-{|[avgLTree_aux1, avgLTree_aux2]|}
}
\end{eqnarray*}

A fun????o |avgLTree| retorna o primeiro elemento do par devolvido pelo catamorfismo. Podemos verificar que, ap??s aplicada a recursividade, uma |LTree a| se transforma num par |(a, a)|, onde o primeiro elemento corresponde ao somat??rio dos elementos da ??rvore e o segundo elemento corresponde ao n??mero de elementos dessa mesma ??rvore. Assim, para saber a m??dia final, basta somar a soma dos elementos da ??rvore da esquerda com a soma dos elementos da ??rvore da direita e dividir tudo pelo tamanho total das duas ??rvores.

\begin{code}
avgLTree = p1.cataLTree gene where
   gene = either avgLTree_aux1 avgLTree_aux2

avgLTree_aux1 a = (a,1)

avgLTree_aux2 ((a1,a2),(b1,b2)) = ((a1*a2+b1*b2)/(a2+b2),a2+b2)
\end{code}

\subsection*{Problema 5}
Inserir em baixo o c??digo \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

\begin{verbatim}
module BTree

open Cp

// (1) Datatype definition ------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = either (konst Empty) (Node) x

let outBTree x =
     match x with
     | Empty -> i1 ()
     | Node (a,(t1,t2)) -> i2 (a,(t1,t2))

// (2) Ana + cata + hylo --------------------------------------------

let baseBTree f g x = (id -|- (f >< (g >< g))) x

let recBTree g x = (baseBTree id g) x 

let rec cataBTree a x = (a << (recBTree (cataBTree a)) << outBTree) x

let rec anaBTree g x =  (inBTree << (recBTree (anaBTree g) ) << g) x

let hyloBTree a c x = (cataBTree a << anaBTree c) x

// (3) Map ----------------------------------------------------------
let fmap f x = (cataBTree ( inBTree << baseBTree f id )) x

// (4) Examples -----------------------------------------------------

// (4.0) Inversion (mirror) -----------------------------------------

let invBTree x = cataBTree (inBTree <<  (id -|- (id >< swap))) x

// (4.1) Counting ---------------------------------------------------

let countBTree x = cataBTree (either (konst 0) 
(succ << (uncurry (+)) << p2)) x

// (4.2) Serialization ----------------------------------------------

let join (x,(l,r)) = l@[x]@r

let inord x = either nil join x

let inordt x = cataBTree inord x                 //in-order traversal

let f1 (x,(l,r)) = x::l@r

let preord x = (either nil f1) x

let preordt x = cataBTree preord x               //pre-order traversal

let f2 (x,(l,r)) = l@r@[x]

let postordt x = cataBTree (either nil f2) x     //post-order traversal


//-- (4.4) Quicksort --------------------------------------------------
let rec part p list =
   match list with
   | head :: tail -> if p head then let (s,l) = part p tail in (head::s,l) 
                     else let (s,l) = part p tail in (s,head::l)
   | [] -> ([],[])


let qsep list =
   match list with
   | head :: tail -> i2 (head, (part ((>) head) tail))
   | [] -> i1 ()


let qSort x = hyloBTree inord qsep x

//-- (4.5) Traces --------------------------------------------------
let rec membro a list = 
   match list with
   | [] -> false
   | x::xs -> if a=x then true else membro a xs

let rec union list1 list2 =
    match list2 with
    | [] -> list1
    | x::xs when membro  x list1 -> union list1 xs
    | x::xs -> (union list1 xs)@[x]

let tunion(a,(l,r)) = union (List.map (fun x -> a::x) l) 
(List.map (fun x -> a::x) r) 

let traces x = cataBTree (either (konst [[]]) tunion) x

//-- (4.6) Towers of Hanoi --------------------------------------------------

let present x = inord x 

let strategy x =
   match x with
   | (d,0) -> i1()
   | (d,n) -> i2 ((n-1,d), ((not d, n-1),(not d, n-1)))

let hanoi x = hyloBTree present strategy x

//-- (5) Depth and balancing (using mutual recursion) ---------------------

let hbaldepth (a, ((b1,b2),(d1,d2))) = (b1 && b2 && (abs(d1-d2) <= 1), 1 
+ (max d1 d2))

let fbaldepth ((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))

let baldepth x = cataBTree (either (konst(true,1)) (hbaldepth <<
   (id >< fbaldepth)) ) x

let balBTree x = let (s,l) = baldepth x in s 

let depthBTree x = let (s,l) = baldepth x in l 

//---------------------------- end of library ----------------------------
\end{verbatim}

%----------------- Fim do anexo com solu????es dos alunos ------------------------%

%----------------- ??ndice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
