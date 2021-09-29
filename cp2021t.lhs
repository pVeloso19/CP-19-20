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
       	Cálculo de Programas
\\
       	Trabalho Prático
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

\section{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.
  
Na sequência pedagógica dos planos de estudo dos dois cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens 
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

\section{Documentação} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pre-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
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
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder às questões que serão colocadas
na \emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-á ainda instalar o utilitário
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
geração de gráficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invocá-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o número de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) código
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
código \Haskell\ relativo aos problemas que se seguem. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Stack}

O \stack{Stack} é um programa útil para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito específica:

\begin{itemize}
\item Os módulos auxiliares encontram-se na pasta \emph{src}.
\item O módulos principal encontra-se na pasta \emph{app}.
\item A lista de depêndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as depêndencias externas serão instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados algébricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Graças à sua flexibilidade,
torna-se trivial implementar \DSL s
e até mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programação}.

Paralelamente, um tópico bastante estudado no âmbito de \DL\ 
é a derivação automática de expressões matemáticas, por exemplo, de derivadas.
Duas técnicas que podem ser utilizadas para o cálculo de derivadas são:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplicação sucessiva de transformações
(leia-se: funções) que sejam congruentes com as regras de derivação. O resultado
final será a expressão da derivada.

O leitor atento poderá notar um problema desta técnica: a expressão
inicial pode crescer de forma descontrolada, levando a um cálculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da expressão em todos os passos.
Para tal, é necessário calcular o valor da expressão \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de expressões matemáticas simples e
implementar as duas técnicas de derivação automática.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam operações binárias e unárias, respectivamente:

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

Assim, cada expressão pode ser uma variável, um número, uma operação binária
aplicada às devidas expressões, ou uma operação unária aplicada a uma expressão.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na notação matemática habitual.

\begin{enumerate}
\item A definição das funções |inExpAr| e |baseExpAr| para este tipo é a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as funções |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| são testemunhas de um isomorfismo,
    isto é,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma expressão aritmética e um escalar para substituir o |X|,
	a função

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da expressão. Na página \pageref{pg:P1}
    esta função está expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A função |eval_exp| respeita os elementos neutros das operações.
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
      Negar duas vezes uma expressão tem o mesmo valor que não fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item É possível otimizar o cálculo do valor de uma expressão aritmética tirando proveito
  dos elementos absorventes de cada operação. Implemente os genes da função
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na página \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A função |optimize_eval| respeita a semântica da função |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma expressão, é necessário aplicar transformações
à expressão original que respeitem as regras das derivadas:\footnote{%
	Apesar da adição e multiplicação gozarem da propriedade comutativa,
	há que ter em atenção a ordem das operações por causa dos testes.}

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

  Defina o gene do catamorfismo que ocorre na função
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma expressão aritmética, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A função |sd| respeita as regras de derivação.
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

\item Como foi visto, \emph{Symbolic differentiation} não é a técnica
mais eficaz para o cálculo do valor da derivada de uma expressão.
\emph{Automatic differentiation} resolve este problema cálculando o valor
da derivada em vez de manipular a expressão original.

  Defina o gene do catamorfismo que ocorre na função
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma expressão aritmética e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a expressão original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| é equivalente a calcular a derivada da expressão e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos das aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}
O que se pede então, nesta pergunta?
Dada a fórmula que dá o |n|-ésimo \catalan{número de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementação de $C_n$ que não calcule factoriais nenhuns.
Isto é, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta função.

\begin{propriedade}
A função proposta coincidem com a definição dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugestão}: Começar por estudar muito bem o processo de cálculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da função exponencial.


\Problema 

As \bezier{curvas de Bézier}, designação dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre Bézier},
são curvas ubíquas na área de computação gráfica, animação e modelação.
Uma curva de Bézier é uma curva paramétrica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ é a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de Bézier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} é um método recursivo capaz de calcular
curvas de Bézier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo é numericamente mais estável, trocando velocidade por correção.

De forma sucinta, o valor de uma curva de Bézier de um só ponto $\{P_0\}$
(ordem $0$) é o próprio ponto $P_0$. O valor de uma curva de Bézier de ordem
$N$ é calculado através da interpolação linear da curva de Bézier dos primeiros
$N-1$ pontos e da curva de Bézier dos últimos $N-1$ pontos.

A interpolação linear entre 2 números, no intervalo $[0, 1]$, é dada pela
seguinte função:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpolação linear entre 2 pontos de dimensão $N$ é calculada através
da interpolação linear de cada dimensão.

O tipo de dados |NPoint| representa um ponto com $N$ dimensões.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimensões e um ponto de 3 dimensões podem ser
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
O anexo \ref{sec:codigo} tem definida a função 
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpolação linear entre 2 pontos, e a função
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua definição com a propriedade:
    \begin{propriedade} Definição alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a função |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de Bézier são simétricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a função |runBezier| e aprecie o seu trabalho\footnote{%
        A representação em Gloss é uma adaptação de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que é aberta (que contém, a verde, um ponto
        inicila) com o botão esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a fórmula que calcula a média de uma lista não vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto é, para sabermos a média de uma lista precisamos de dois catamorfismos: o que faz o somatório e o que calcula o comprimento a lista.
Contudo, é facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ está em recursividade mútua com $length$ e o par de funções pode ser expresso por um único catamorfismo, significando que a lista apenas é percorrida uma vez.

\begin{enumerate}

\item	Recorra à lei de recursividade mútua para derivar a função
|avg_aux = cata (either b q)| tal que 
|avg_aux = split avg length| em listas não vazias. 

\item	Generalize o raciocínio anterior para o cálculo da média de todos os elementos de uma \LTree\ recorrendo a uma única travessia da árvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas funções testando a propriedade seguinte:
\begin{propriedade}
A média de uma lista não vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 milésimas:
\begin{code}
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta questão é \textbf{opcional} e funciona como \textbf{valorização} apenas para os alunos que desejarem fazê-la.) 

\vskip 1em \noindent
Existem muitas linguagens funcionais para além do \Haskell, que é a linguagem usada neste trabalho prático. Uma delas é o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os módulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede é a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execução: o código que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para além disso, os grupos podem demonstrar o código na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
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

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\ 
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

\section{Programação dinâmica por recursividade múltipla}\label{sec:recmul}
Neste anexo dão-se os detalhes da resolução do Exercício \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, página \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o cálculo da aproximação até |i=n| da função exponencial $exp\ x = e^x$,
via série de Taylor:
\begin{eqnarray}
	exp\ x 
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a função que dá essa aproximação.
É fácil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
mútua. Se repetirmos o processo para |h x n| etc obteremos no total três funções nessa mesma
situação:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado,
ter-se-á, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
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
Função auxiliar:
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
Animação:
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
runBezier = play (InWindow "Bézier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compilação e execução dentro do interpretador:\footnote{Pode ser útil em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma função
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
Código para geração de testes:
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

\subsection*{Outras funções auxiliares}
%----------------- Outras definições auxiliares -------------------------------------------%
Lógicas:
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

%----------------- Soluções dos alunos -----------------------------------------%

%format (expn (a) (n)) = "{" a "}^{" n "}"

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o "layout" que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, disgramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes. 

\subsection*{Problema 1} \label{pg:P1}
São dadas:
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
Para se descobrir a definição de |outExpAr|, e uma vez que já se sabe a definição de |inExpAr|, recorreu-se à propriedade dos isomorfismos |out . in = id|.

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

Uma vez descoberto o tipo de saida de |outExpAr|, torna-se bastante fácil definir a função |recExpAr|, visto que apenas nos interessa aplicar a recursividade aos tipos |ExpAr|, enquanto que nos restantes basta aplicar a função id, fazendo com que nunca se alterem. 

\begin{code}
recExpAr f = baseExpAr id id id f f id f
\end{code}

Realtivamente ao gene de |eval_exp|, recorreu-se ao seguinte diagrama, de maneira a facilitar a compreensão dos tipos.

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

Como se pode observar, o gene do catamorfismo corresponde à seta mais abaixo no diagrama. É fácil perceber que, quando o termo for vazio, basta devolver o valor escalar que nos é fornecido, e quando o termo já for um valor do tipo |a|, simplesmente se devolve o próprio elemento. Relativamente à parte recursiva, foram criadas duas funções auxiliares, sendo essas a |operationBin| e a |operationUn|. A |operationBin| trata os casos onde se recebe como primeiro elemento um par do tipo |BinOp| e como segundo elemento um par de valores do tipo |a|. Caso |BinOp| seja do tipo |Sum|, soma-se os dois valores, e caso seja do tipo |Product|, realiza-se a sua multiplicação. A |operationUn| trata os casos onde se recebe um par com o primeiro elemento do tipo |UnOp| e o segundo elemento um valor do tipo |a|. Aqui, caso |UnOp| se trate de um |Negate|, devolve-se a negação do elemento, e caso se trate de |E|, devolve-se a exponenciação de |a|.

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

Para definir os genes da função |optmize_eval|, foi necessário definir o seu diagrama, como um hilomorfismo, para perceber os tipos de entrada e saída de cada gene. 

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

Ao analisar o diagrama, percebe-se que estamos perante um caso particular de um anamorfismo, onde a estrutura que o anamorfismo devolve é do mesmo tipo de entrada. Assim, |clean| pode ser visto como um tipo especial de |outExpAr|, só que desta vez, quando se estiver perante o elemento absorvente da multiplicação, que é 0, ao invés de retornar a expressão da multiplicação, pode simplesmente devolver-se |N 0|, diminuindo assim o trabalho do catamorfismo. Também se considerou que, o exponencial |e| elevado a 0 dará sempre 1. A função auxiliar |anyZero| verifica se algum elemento da esquerda ou da direita é |N 0|, devolvendo |True| caso tal se verifique.

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

Relativamente ao gene de |gopt|, é possível perceber que este é semelhante ao gene da função |g_eval_exp|, pelo que se reutilizará as funções |operationBin| e |operationUn|.

\begin{code}
gopt a = either (const a) (gopt_aux a)
        where gopt_aux a = either id (either operationBin operationUn) 
\end{code}

Analisando o código fornecido para a função |sd|, verifica-se que o resultado se encontra no segundo elemento do par devolvido pelo cataExpAr |sd_gen|. 

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

No caso de paragem apenas se necessita de devolver um par onde no primeiro elemento está o termo |X| (visto que quando se aplica |outExpAr| a |X| este dá o único habitante do tipo 1), e no segundo elemento a derivada de |X| (que será sempre |N 1|).
\par Quando o termo é do tipo |a| apenas se necessita de devolver um par onde no primeiro elemento está o termo |N a|, e no segundo elemento a respetiva derivada |N 0|.
\par Também se pode estar na presença de um par do tipo |(BinOp, ((a, b),(c, d)))|, onde é importante notar que o primeiro par |(a, b)| corresponde à primeira |ExpAr| e à sua derivada, e o par |(c, d)| corresponde à segunda |ExpAr| e à sua derivada. 
\par Por fim, pode-se estar na presença de um par do tipo |(UnOp, (a,b))|, onde mais uma vez, o termo |a| tem o valor da |ExpAr| e o termo |b| tem a derivada desse valor. Assim, com base na explicação de derivações presentes no documento, é possível produzir duas funções axiliares, |decideBin| e |decideUn|, que tratam de derivar corretamente as expressões.

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

Por fim, foi necessário definir |ad_gen|. Analisando a função |ad|, percebe-se que esta devolve um par, em que o resultado da derivada no ponto se encontra no segundo elemento do par devolvido pelo cataExpAr |ad_gen v|. Conclui-se assim que |ad_gen| irá devolver um par, onde no primeiro elemento estará o resultado da substituição do ponto na expressão original, e no segundo elemento estará o resultado da derivada no ponto. 
\par Quando o termo é do tipo |(BinOp, ((a, b), (c, d)))|, no termo |a| estará o resultado da substituição do ponto na primeira |ExpAr|, no termo |b| estará a derivada dessa |ExpAr| no ponto, no termo |c| estará o resultado da substituição do ponto na segunda |ExpAr| e no termo |d| estará a derivada dessa |ExpAr| no ponto. Assim, na função auxiliar |dB|, conforme o tipo de |BinOp|, é possível descobrir todos os valores necessários.
\par Por último, quando o termo é do tipo |(UnOp, (a, b))|, no termo |a| estará o valor do ponto pretendido e no termo |b| estará a derivada da |ExpAr| no ponto. Assim, na função auxiliar |dU|, se estivermos perante um |Negate|, devolve-se um par com a negação do ponto e a negação da sua derivada. Se estivermos perante um |E|, então devolve-se um par com a exponencial do ponto e com a multiplicação da exponencial no ponto pela derivada da |ExpAr| no ponto.

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
Para se descobrir como simplificar o algoritmo de |Catalan|, de maneira a não usar fatoriais,foi necessário desenvolver a fórmula fornecida pelos docentes. De seguida, apresenta-se a redução que foi feita na fórmula de |Catalan|:
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

Através do desenvolvimento da fórmula, é possível perceber que um determinado número de |Catalan| poderá ser calculado à custa do número de |Catalan| anterior. Assim, após simplificação da fórmula, chegou-se à seguinte equação:


\begin{equation}
C_0 = 1, C_n = \frac{ 2(2n - 1)} {n+1} C_{n-1}
\end{equation}

Após descoberta a fórmula, tornou-se bastante simples definir a função por recursividade mútua. A função |inic| será inicializada com o par |(1, 1)|, enquante que a função |loop| será chamada recursivamente. Desta forma, a função |loop| terá 2 elementos, onde o primeiro elemento terá o índice da iteração atual, e o segundo elemento terá o número de |Catalan| da iteração anterior.

\begin{code}
loop (a,b) = (a+1, div (b*(2*((2*a)-1))) (a+1))
inic = (1,1)
prj = p2
cat = prj . (for loop inic)
\end{code}

Como um ciclo for é definido através de um catamorfismo de naturais, a função |cat| também poderá ser especificada como um catamorfismo de naturais (denominada como catalan), como ilustrado no seguinte diagrama:


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

Após obter como resultado o par, onde o primeiro elemento é o sucessor e o segundo elemento é o |Catalan| do natural introduzido, apenas nos interessa o segundo elemento elemento do par, de modo a obter o mesmo resultado que o obtido na função |cat|.

\subsection*{Problema 3}

Com base no código da função |calcLine| fornecido, foi possível definir este à custa de um catamorfismo. Numa primeira fase, definiu-se o diagrama do catamorfismo.

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

Como |NPoint| é uma lista de |Rational|, então cada elemento de |NPoint| será do tipo |Rational|. 
No caso de paragem, é devolvida a lista vazia, tal como se pode verificar na função auxiliar |calcLine_aux1|. 
\par A função auxiliar |calcLine_aux2| recebe como parámetros um par e um |NPoint|. O primeiro elemento do par tem o elemento à cabeça do primeiro |NPoint| e o segundo elemento do par tem uma função que recebe um |NPoint| e devolve um |OverTime NPoint|. Se o |NPoint| for nulo, então o resultado será dado pela aplicação da função que recebe um |NPoint| e devolve um |OverTime NPoint|, aplicada à lista vazia. Caso contrário, basta dar como argumentos da função |linear1d| o primeiro elemento do par e primeiro elemento da lista, e depois aplicar a função, que se encontra no segundo elemento do par, à cauda do segundo |NPoint|. 

\begin{code}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine = cataList h where
   h = either calcLine_aux1 calcLine_aux2

calcLine_aux1 () = const nil

calcLine_aux2 (r, f) [] = f []
calcLine_aux2 (r, f) (h:t) = \z -> concat $ (sequenceA [singl . linear1d r h, f t]) z
\end{code}
De maneira a definir a função de |deCasteljau| como um hilomorfismo, foi necessário definir um novo tipo de dados. Inicialmente, pensou-se na possibilidade de definir esta função como um hilomorfismo de |LTree|, porém, após alguns testes, percebeu-se que o algoritmo não funcionava para listas vazias. Assim, desenvolveu-se o seguinte tipo de dados:

\begin{code}
data AlgForm a = Vazio | Elemento a | Raiz (AlgForm a, AlgForm a) deriving (Show, Eq)
\end{code}

O tipo de dados |AlgForm| foi baseado no tipo |LTree|, acrescentando a possibilidade de um dado elemento desse tipo poder ser |Vazio|. Além do |Vazio|, |AlgForm| também poderá ser formada por apenas um |Elemento|, ou então uma |Raiz| formada por um par de |AlgForm|'s, assemelhando-se assim a uma árvore, tal como pretendido.

Uma vez definido o tipo de dados, foi necessário definir o |in| e o |out|, bem como o funtor deste tipo de dados, sendo que posteriormente definidos estes, se pode definir o |cataAlgForm|, |anaAlgForm| e |hiloAlgForm|.

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

Uma vez definido tudo o que era necessário relativamente ao tipo de dados, foi necessário desenhar o diagrama do hilomorfismo associado ao |deCasteljau|, com base no novo tipo de dados.
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

Como podemos reparar, se a lista for vazia, o gene do anamorfismo devolve o único habitante do tipo 1, que é o vazio. Se só tiver um elemento, o gene do anamorfismo devolve o próprio elemento, e, caso a lista tenha mais que um elemento, devolve um par constituido por duas listas, a primeira com todos os constituintes da lista excepto o último elemento, e a segunda com todos os constituintes da lista excepto o primeiro elemento.
Relativamente ao gene do catamorfismo, este transformará o |AlgForm| de lista de |NPoint| num |OverTime NPoint|.

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
\underline{Solução para listas não vazias:}

A solução para listas não vazias dado por um catamorfismo de listas é representado pelo seguinte diagrama. 

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

Assim, a função |avg| devolve o primeiro elemento do par devolvido pelo catamorfismo. Na função |avg_aux| considera-se que, no caso de paragem, é retornado o par (0,0), visto que no início, quer a média, quer o tamanho da lista são 0.
\par Quando a função |avg_aux2| receber o par |(c, (a, x))|, o termo |c| corresponde ao primeiro elemento da lista, |a| corresponde à média da lista e |x| ao número de elementos da lista. Assim, para obter a nova média, basta somar o termo |c| com o somatório da lista (dado pela multiplicação da média pelo número de elementos), e dividir tudo pelo novo tamanho, que corresponde ao incremento de uma unidade no tamanho anterior.

\begin{code}
avg = p1.avg_aux

avg_aux = cataList (either avg_aux1 avg_aux2)

avg_aux1 a = (0,0)

avg_aux2 (c, (a,x)) = ((c+(x*a))/(x+1), x+1)
\end{code}
\underline{Solução para árvores de tipo \LTree:}

Definir a função |avg| para árvores do tipo |LTree| é bastante semelhante a definir a função |avg|, porém, torna-se mais fácil compreeender esta função após se definir o seu diagrama.

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

A função |avgLTree| retorna o primeiro elemento do par devolvido pelo catamorfismo. Podemos verificar que, após aplicada a recursividade, uma |LTree a| se transforma num par |(a, a)|, onde o primeiro elemento corresponde ao somatório dos elementos da árvore e o segundo elemento corresponde ao número de elementos dessa mesma árvore. Assim, para saber a média final, basta somar a soma dos elementos da árvore da esquerda com a soma dos elementos da árvore da direita e dividir tudo pelo tamanho total das duas árvores.

\begin{code}
avgLTree = p1.cataLTree gene where
   gene = either avgLTree_aux1 avgLTree_aux2

avgLTree_aux1 a = (a,1)

avgLTree_aux2 ((a1,a2),(b1,b2)) = ((a1*a2+b1*b2)/(a2+b2),a2+b2)
\end{code}

\subsection*{Problema 5}
Inserir em baixo o código \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

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

%----------------- Fim do anexo com soluções dos alunos ------------------------%

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
