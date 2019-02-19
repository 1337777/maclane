(* #+TITLE: maclaneSolution2.thy *)

section \<open>ASSOCIATIVITY ELIMINATION\<close>

theory maclaneSolution2
  imports Main
begin

text \<open>

Proph

@{url "https://github.com/1337777/maclane/blob/master/maclaneSolution2.thy"}

@{url "https://github.com/1337777/maclane/blob/master/maclaneSolution2.v"}

@{url "https://github.com/1337777/dosen/blob/master/coherence2.v"}

solves how 1337777 mom associativity pentagon is some recursive square
(reflective-functorial associativity-bracket-elimination cut-elimination
resolution) .  The only thing to remember : this grammatical
associativity-bracket-elimination cut-elimination resolution and confluence
technique is the foundation of polymorph mathematics ...

\bigskip
\centerline{What is the metalogic for polymorphism ? ( ``HOL vs COQ'' )}

\bigskip
   \indent HOL has its own metalogic which is parallel-search ( ``sequent/natural'' , using
unlimited-outer-nesting-of-metaconsequences as questioned by Kubota )
deduction with unification of metavariables . Therefore HOL may erase
logical-properties from progamming and instead deleguate , to some ad-hoc
particular ``object-logic'' , the task of automatic inferences involved during
programming-under-logical-context . For example , definite/indefinite
descriptions or how to simulate implicit parameters in the polymorphism
object-logic : 

\bigskip
@{text "( wellIndexed f A B ==> wellIndexed g B C ==> 
CompositionImplicit f g = ( Composition A B f C g :: morphismsDatatype ) )" }

\bigskip
   \indent COQ unites programs carrying logical-properties via indexed/dependent
datatypes ; the consequence is the semi-automatic inference/unification of
implicit/hidden parameters via existential/meta-variables . Does this say that
dependent-types ( beyond its semi-automatic inference/unification algorithms )
is better for polymorphism ( ``category theory'' ) ?  NO ...  The pretty search
into the ``categorical semantics of (higher-)dependent-types as internal logic''
is for the museum mostly ; the angle of view of polymorphism mathematics is
that itself is ( by-definition ... ) some computational logic .

\begin{verbatim}

A + ( B + [ C + D ] )    ( A + B ) + ( C + D )   ( [ A + B ] + C ) + D

  _________________>_______________|______________>_______________
  |                                                               .
  |                                                               .
  |                                                               .
  |                                                               .
  v              |--->                           ( [ 1 + 1 ] + 1 ) + 1
  |                                                               .
  |                                                               .
  |                                                               .
  |________________>_______________|______________>_______________.

A + ( [ B + C ] + D )    ( A + [ B + C ] ) + D   ( [ A + B ] + C ) + D

\end{verbatim}
\<close>

datatype obLogic =
  Atom nat
| Multiply0 obLogic obLogic (infixr "&0" 65)

datatype morLogic =
  Poly obLogic obLogic morLogic obLogic morLogic  ("'( `_,_`_ o> `_`_ ')"  [1000, 1000, 1000, 1000, 1000] 1000)
| Iden obLogic
| Multiply1 obLogic obLogic morLogic obLogic obLogic morLogic  ("'( `_,_`_ &1 `_,_`_ ')" [1000, 1000, 1000, 1000, 1000, 1000] 1000)
| BracketL obLogic obLogic obLogic

inductive wellIndexed :: "morLogic \<Rightarrow> obLogic \<Rightarrow> obLogic \<Rightarrow> bool" where 
  Poly_rule [intro!]: "wellIndexed a A1 A2 \<Longrightarrow>  wellIndexed a' A2 A3 \<Longrightarrow> wellIndexed ( `A1,A2`a o> `A3`a') A1 A3 "
| Iden_rule  [intro!]: "wellIndexed (Iden A) A A"
| Multiply1_rule [intro!]: "wellIndexed a A1 A2 \<Longrightarrow>  wellIndexed b B1 B2 \<Longrightarrow> wellIndexed ( `A1,A2`a &1 `B1,B2`b ) (A1 &0 B1) (A2 &0 B2)"
| BracketL_rule [intro!]: "wellIndexed (BracketL A B C) (A &0 (B &0 C)) ((A &0 B) &0 C)"

lemma wellIndexed_uniqueIndex [simp, intro]:  "wellIndexed a1 A1 A2 \<Longrightarrow> wellIndexed a1 A1' A2' \<Longrightarrow> A1' = A1 \<and> A2' = A2"
  by (induct arbitrary: A1' A2' rule:wellIndexed.induct; rotate_tac -1; drule wellIndexed.cases; blast)

inductive convLogic   :: "morLogic \<Rightarrow>  morLogic \<Rightarrow> bool" (infix "~~" 50) where
  convLogics_Refl [intro!] : " a ~~ a"
| convLogics_Sym [intro] : "  wellIndexed a A1 A2 \<Longrightarrow> a ~~ b \<Longrightarrow> b ~~ a"
| convLogics_Trans [intro,trans] : " a ~~ uTrans \<Longrightarrow> uTrans ~~ b \<Longrightarrow> a ~~ b"
| Poly_congL [intro!]  : " a ~~ a0 \<Longrightarrow> ( `A1,A2`a o> `A3`b ) ~~ ( `A1,A2`a0 o> `A3`b )"
| Poly_congR [intro!] : " b ~~ b0 \<Longrightarrow> ( `A1,A2`a o> `A3` b ) ~~ ( `A1,A2`a o> `A3`b0 )"
| Multiply1_congL [intro!] : " a ~~ a0 \<Longrightarrow> ( `A1,A2`a &1 `B1,B2`b ) ~~ ( `A1,A2`a0 &1 `B1,B2`b )"
| Multiply1_congR [intro!] : " b ~~ b0 \<Longrightarrow> ( `A1,A2`a &1 `B1,B2`b )  ~~ ( `A1,A2`a &1 `B1,B2`b0 )"
| Poly_morphism [intro!]  : " ( `A1,A2`a o> `A4`( `A2,A3`a' o> `A4`a'' ) ) ~~  ( `A1,A3`( `A1,A2`a o> `A3`a' ) o> `A4`a'' ) "
| Multiply1L_morphism [intro!]: " ( `A1,A3`( `A1,A2`a o> `A3`a') &1 `B,B`(Iden B) )  ~~ ( `(A1 &0 B),(A2 &0 B)`( `A1,A2`a &1 `B,B`(Iden B) ) o> `(A3 &0 B)`( `A2,A3`a' &1 `B,B`(Iden B) ) ) "
| Multiply1R_morphism [intro!]: " ( `B,B`(Iden B) &1 `A1,A3`( `A1,A2`a o> `A3`a' ) )  ~~ ( `(B &0 A1),(B &0 A2)`( `B,B`(Iden B) &1 `A1,A2`a ) o> `(B &0 A3)`( `B,B`(Iden B) &1 `A2,A3`a' ) ) "
| BracketL_morphism [intro!]: " wellIndexed a A A' \<Longrightarrow> wellIndexed b B B' \<Longrightarrow> wellIndexed c C C' \<Longrightarrow>
  ( `(A &0 (B &0 C)),((A &0 B) &0 C)`(BracketL A B C) o> `((A' &0 B') &0 C')`(`(A &0 B),(A' &0 B')`(`A,A'`a &1 `B,B'`b) &1 `C,C'`c) )
  ~~ ( `(A &0 (B &0 C)),(A' &0 (B' &0 C'))`( `A,A'`a &1 `(B &0 C),(B' &0 C')`( `B,B'`b &1 `C,C'`c ) ) o> `((A' &0 B') &0 C')`(BracketL A' B' C') )   "
| Iden_Poly [intro!]: " ( `A,A`(Iden A) o> `B`b )  ~~ b "
| Poly_Iden [intro!]: " ( `A,B`a o> `B`(Iden B) )  ~~ a "
| Multiply1_Iden [intro!]: " ( `A,A`(Iden A) &1 `B,B`(Iden B) )  ~~ (Iden ( A &0 B )) "

lemma convLogic_wellIndexed [intro] : "a ~~ b \<Longrightarrow> wellIndexed a A1 A2 \<Longrightarrow> wellIndexed b A1 A2"
proof (induction arbitrary: A1 A2 rule: convLogic.induct)
case (convLogics_Refl a)
then show ?case  by auto
next
  case (convLogics_Sym a A1' A2' b)
  then show ?case 
    by (subgoal_tac "A1 = A1'"  "A2 = A2'" , clarify ; 
       (subgoal_tac "wellIndexed b A1' A2'" ; simp (no_asm_simp) add: wellIndexed_uniqueIndex))
next
  case (convLogics_Trans a uTrans b)
  then show ?case by auto
next
  case (Poly_congL a a0 A1 A2 A3 b)
  then show ?case by (drule_tac wellIndexed.cases) auto
next
  case (Poly_congR b b0 A1 A2 a A3)
  then show ?case by (drule_tac wellIndexed.cases) auto
next
  case (Multiply1_congL a a0 A1 A2 B1 B2 b)
  then show ?case by (drule_tac wellIndexed.cases) auto
next
  case (Multiply1_congR b b0 A1 A2 a B1 B2)
  then show ?case by (drule_tac wellIndexed.cases) auto
next
  case  (Poly_morphism A1 A2 a A4 A3 a' a'')
  then show ?case
    by (drule_tac wellIndexed.cases; auto; drule_tac wellIndexed.cases; auto)
next
  case (Multiply1L_morphism A1 A3 A2 a a' B)
  then show ?case 
    by (drule_tac wellIndexed.cases; auto; drule_tac wellIndexed.cases; auto)
next
  case  (Multiply1R_morphism B A1 A3 A2 a a')
  then show ?case
    by (drule_tac wellIndexed.cases; auto; drule_tac wellIndexed.cases; auto)
next
  case (BracketL_morphism a A A' b B B' c C C')
  then show ?case
    by (rotate_tac -1; drule_tac wellIndexed.cases; auto)
next
  case  (Iden_Poly A B b)
  then show ?case
     by (drule_tac wellIndexed.cases; auto; drule_tac wellIndexed.cases; auto)
next
  case (Poly_Iden A B a)
  then show ?case 
    by (drule_tac wellIndexed.cases; auto; drule_tac wellIndexed.cases; auto)
next
  case  (Multiply1_Iden A B)
  then show ?case by (drule_tac wellIndexed.cases; auto)
qed

subsection \<open>solution objects and solution morphisms\<close>

datatype Sol_obLogic =
  Sol_Atom nat
| Sol_Multiply0 Sol_obLogic nat (infix "&0s" 65)

primrec toObLogic :: "Sol_obLogic \<Rightarrow> obLogic" where
  "toObLogic ( Sol_Atom A )  =  ( Atom A )" 
| "toObLogic ( A &0s B )     =  ( ( toObLogic A ) &0 ( Atom B ) )" 

datatype Sol_morLogic =
  Sol_Poly Sol_obLogic Sol_obLogic Sol_morLogic Sol_obLogic Sol_morLogic  ("'( `_,_`_ o>s `_`_ ')"  [1000, 1000, 1000, 1000, 1000] 1000)
| Sol_Iden nat
| Sol_Multiply1 Sol_obLogic Sol_obLogic Sol_morLogic nat  ("'( `_,_`_ &1s _ ')" [1000, 1000, 1000, 1000] 1000)

inductive Sol_wellIndexed :: "Sol_morLogic \<Rightarrow> Sol_obLogic \<Rightarrow> Sol_obLogic \<Rightarrow> bool" where 
  Sol_Poly_rule [intro!]: "Sol_wellIndexed a A1 A2 \<Longrightarrow> Sol_wellIndexed a' A2 A3 \<Longrightarrow> Sol_wellIndexed ( `A1,A2`a o>s `A3`a' ) A1 A3 "
| Sol_Iden_rule  [intro!]: "Sol_wellIndexed (Sol_Iden A) (Sol_Atom A) (Sol_Atom A)"
| Sol_Multiply1_rule [intro!]: "Sol_wellIndexed a A1 A2 \<Longrightarrow> Sol_wellIndexed (`A1,A2`a &1s B) (A1 &0s B) (A2 &0s B)"

primrec toMorLogic :: "Sol_morLogic \<Rightarrow> morLogic" where
  "toMorLogic ( `A1,A2`a o>s `A3`a' )  =  ( `(toObLogic A1),(toObLogic A2)`(toMorLogic a) o> `(toObLogic A3)`(toMorLogic a') )" 
| "toMorLogic ( Sol_Iden A )           =  ( Iden ( Atom A ) )" 
| "toMorLogic ( `A1,A2`a &1s B )       =  ( `(toObLogic A1),(toObLogic A2)`( toMorLogic a ) &1 `(Atom B),(Atom B)`( Iden ( Atom B ) ) )" 

lemma toMorLogicP  [intro!] : "Sol_wellIndexed a A1 A2 \<Longrightarrow> wellIndexed (toMorLogic a) (toObLogic A1) (toObLogic A2)"
  by (induction rule:Sol_wellIndexed.induct) auto

primrec resolution0_param :: "Sol_obLogic \<Rightarrow> obLogic \<Rightarrow> Sol_obLogic" (infix "'_&&0" 65) where
  "Z _&&0 Atom A      =  Z &0s A" 
| "Z _&&0 ( A &0 B )  =  ( Z _&&0 A ) _&&0 B" 

primrec resolution0 :: "obLogic \<Rightarrow> Sol_obLogic" ("&&0") where
  "&&0 ( Atom A )  =  Sol_Atom A" 
| "&&0 ( A &0 B )  =  ( &&0 A ) _&&0 B" 

declare resolution0.simps(2) [simp del]

primrec resolutor_param  :: "obLogic \<Rightarrow> obLogic \<Rightarrow> morLogic \<Rightarrow> obLogic \<Rightarrow> morLogic" ("'( `_,_` _ '_&> _ ')" [1000, 1000, 1000, 1000] 1000) where
  "( `Z1,Z2`z _&> (Atom A) )    =  ( `Z1,(toObLogic (&&0 Z2))`z &1 `(Atom A),(Atom A)`(Iden (Atom A)) ) " 
| "( `Z1,Z2`z _&> ( A &0 B ) )  =  ( `(Z1 &0 (A &0 B)),((Z1 &0 A) &0 B)`(BracketL Z1 A B) o> `(toObLogic (&&0 ((Z2 &0 A) &0 B)))`( `(Z1 &0 A),(Z2 &0 A)`( `Z1,Z2`z _&> A ) _&> B ) ) "

lemma simp1_Multiply_resolution0 : "&&0 (Z2 &0 (A1 &0 A2)) = &&0 ((Z2 &0 A1) &0 A2 )"
  by (simp add: resolution0.simps(2))

lemma simp2_BracketL_resolution0 : "&&0 (Z2 &0 A1 &0 A2 &0 A3) = ( &&0 (((Z2 &0 A1) &0 A2)  &0 A3 ) )"
  by  (simp add: resolution0.simps(2))

lemma simp3_BracketL_resolution0 : "&&0 (Z2 &0 (A1 &0 A2) &0 A3) = ( &&0 (((Z2 &0 A1) &0 A2) &0 A3 ) ) "
  by  (simp add: resolution0.simps(2))

lemma resolutor_paramP [intro!] : "wellIndexed z Z1 (toObLogic ( &&0 Z2 )) \<Longrightarrow> wellIndexed (`Z1,Z2`z _&> A) (Z1 &0 A) (toObLogic ( &&0 ( Z2 &0 A ) ))"
proof (induction A arbitrary: Z1 Z2 z)
  case (Atom x)
  then show ?case by (auto simp add: resolution0.simps(2))
next
  case (Multiply0 A1 A2)
  then show ?case
    by (auto simp add: simp1_Multiply_resolution0)
qed

lemma resolutor_param_cong [intro!] : "z ~~ z' \<Longrightarrow> (`Z1,Z2`z _&> A) ~~ (`Z1,Z2`z' _&> A)"
  by (induction A arbitrary: Z1 Z2 z z') auto

primrec resolutor :: "obLogic \<Rightarrow> morLogic" ("&>") where
  "&> (Atom A)    =  (Iden (Atom A)) " 
| "&> ( A &0 B )  =  ( `A,A`( &> A ) _&> B )"

lemma resolutorP [intro!] : "wellIndexed ( &> A ) A (toObLogic ( &&0 A ))"
  by (induction A) auto

primrec resolution1_param_Id :: "obLogic \<Rightarrow> obLogic \<Rightarrow> Sol_morLogic \<Rightarrow> obLogic \<Rightarrow> Sol_morLogic" ("'( `_,_` _ '_&&01 _ ')"  [1000, 1000, 1000, 1000] 1000) where
  "( `Z1,Z2`z _&&01 ( Atom A ) )  =  ( `(&&0 Z1),(&&0 Z2)`z &1s A ) "
| "( `Z1,Z2`z _&&01 ( A &0 B ) )  =  ( `(Z1 &0 A),(Z2 &0 A)`(`Z1,Z2`z _&&01 A ) _&&01 B )"

lemma resolution1_param_IdP [intro!] : "Sol_wellIndexed z ( &&0 Z1 ) ( &&0 Z2 ) \<Longrightarrow> Sol_wellIndexed ( `Z1,Z2`z _&&01 A ) ( &&0 ( Z1 &0 A ) ) ( &&0 ( Z2 &0 A ) ) " 
proof (induction A arbitrary: Z1 Z2 z)
  case (Atom x)
  then show ?case by (auto simp add: resolution0.simps(2))
next
  case (Multiply0 A1 A2)
  then show ?case by (auto simp add: simp1_Multiply_resolution0)
qed

primrec resolution1_Id  :: "obLogic \<Rightarrow> Sol_morLogic" ("&&01") where
  "&&01 ( Atom A )  =  ( Sol_Iden A ) "
| "&&01 ( A &0 B )  =  ( `A,A`( &&01 A ) _&&01 B ) "

lemma resolution1_IdP [intro!] : "Sol_wellIndexed ( &&01 A ) ( &&0 A ) ( &&0 A )"
  by (induction A) auto

primrec resolution1_param  :: "obLogic \<Rightarrow> obLogic \<Rightarrow> Sol_morLogic \<Rightarrow> obLogic \<Rightarrow> obLogic \<Rightarrow> morLogic \<Rightarrow> Sol_morLogic" ("'( `_,_` _ '_&&1 `_,_` _ ')"  [1000, 1000, 1000, 1000, 1000, 1000] 1000) where
  "( `Z1,Z2`z _&&1 `A1',A3'`( `A1,A2`a o> `A3`a' ) ) 
  =  ( `(&&0 ( Z1 &0 A1 )),(&&0 ( Z1 &0 A2 ))`( `Z1,Z1`( &&01 Z1 ) _&&1 `A1,A2`a ) o>s `(&&0 (Z2 &0 A3))`( `Z1,Z2`z _&&1 `A2,A3`a' ) ) "
| "( `Z1,Z2`z _&&1 `A',A''`( Iden A ) ) 
  =  ( `Z1,Z2`z _&&01 A ) "
| "( `Z1,Z2`z _&&1 `A1B1,A2B2`( `A1,A2`a &1 `B1,B2`b ) ) 
  =  ( `(Z1 &0 A1),(Z2 &0 A2)`( `Z1,Z2`z _&&1 `A1,A2`a ) _&&1 `B1,B2`b )"
| "( `Z1,Z2`z _&&1 `A_BC,AB_C`( BracketL A B C ) ) 
  =  ( `((Z1 &0 A) &0 B),((Z2 &0 A) &0 B)`( `(Z1 &0 A),(Z2 &0 A)`( `Z1,Z2`z _&&01 A ) _&&01 B ) _&&01 C )"

lemma resolution1_paramP [intro!] : "Sol_wellIndexed z ( &&0 Z1 ) ( &&0 Z2 ) \<Longrightarrow> wellIndexed a A1 A2 \<Longrightarrow>
 Sol_wellIndexed ( `Z1,Z2`z _&&1 `A1,A2`a ) ( &&0 ( Z1 &0 A1 ) ) ( &&0 ( Z2 &0 A2 ) ) "
proof (induction a arbitrary: Z1 Z2 z A1 A2)
  case (Poly x1 x2a a1 x4 a2)
  then show ?case by (drule_tac wellIndexed.cases) (auto intro: Poly.IH)
next
  case (Iden x)
  then show ?case by (drule_tac wellIndexed.cases) (auto)
next
  case (Multiply1 x1 x2a a1 x4 x5 a2)
  then show ?case
    by (drule_tac wellIndexed.cases) (auto simp add: simp1_Multiply_resolution0 intro: Multiply1.IH)
next
  case (BracketL x1 x2a x3)
  then show ?case 
    by (drule_tac wellIndexed.cases) (auto simp add: simp2_BracketL_resolution0 simp3_BracketL_resolution0) 
qed

primrec resolution1 :: "obLogic \<Rightarrow> obLogic \<Rightarrow> morLogic \<Rightarrow> Sol_morLogic" ("&&1 `_,_`_" [1000, 1000, 1000] 1000) where
  "( &&1 `A1',A3'`( `A1,A2`a o> `A3`a' ) ) 
  =  ( `(&&0 A1),(&&0 A2)`( &&1 `A1,A2`a ) o>s `(&&0 A3)`( &&1 `A2,A3`a' ) ) "
| "( &&1 `A',A''`( Iden A ) ) 
  =  ( &&01 A ) "
| "( &&1 `A1B1,A2B2`( `A1,A2`a &1 `B1,B2`b ) ) 
  =  ( `A1,A2`( &&1 `A1,A2`a ) _&&1 `B1,B2`b )"
| "( &&1 `A_BC,AB_C`( BracketL A B C ) ) 
  =  ( `(A &0 B),(A &0 B)`( `A,A`( &&01 A ) _&&1 `B,B`(Iden B) ) _&&1 `C,C`(Iden C) )"

lemma resolution1P [intro!] : "wellIndexed a A1 A2  \<Longrightarrow> Sol_wellIndexed ( &&1 `A1,A2`a ) ( &&0 A1 ) ( &&0 A2 )" 
proof (induction a arbitrary: A1 A2)
  case (Poly x1 x2a a1 x4 a2)
  then show ?case by (drule_tac wellIndexed.cases) auto
next
  case (Iden x)
  then show ?case by (drule_tac wellIndexed.cases) auto
next
  case (Multiply1 x1 x2a a1 x4 x5 a2)
  then show ?case by (drule_tac wellIndexed.cases) auto
next                                                                       
  case (BracketL x1 x2a x3)
  then show ?case by (drule_tac wellIndexed.cases) (auto simp add: simp1_Multiply_resolution0)
qed

subsection \<open>recursive square excessive axiom\<close>

definition recursive_square_excessive :: bool where
 "recursive_square_excessive  = 
 ( ALL (a :: morLogic) (A1 :: obLogic) (A2 :: obLogic). ( wellIndexed a A1 A2 \<longrightarrow> 
 ( `A1,A2`a o> `(toObLogic ( &&0 A2 ))`( &> A2 ) ) 
   ~~ ( `A1,(toObLogic ( &&0 A1 ))`( &> A1 ) o> `(toObLogic ( &&0 A2 ))`(toMorLogic ( &&1 `A1,A2`a )) ) ) )"

lemma recursive_square_excessiveLHS : 
 "wellIndexed a A1 A2 \<Longrightarrow> wellIndexed ( `A1,A2`a o> `(toObLogic ( &&0 A2 ))`( &> A2 ) ) A1 (toObLogic ( &&0 A2 ))"
  by auto

lemma recursive_square_excessiveRHS :
 "wellIndexed a A1 A2 \<Longrightarrow> wellIndexed ( `A1,(toObLogic ( &&0 A1 ))`( &> A1 ) o> `(toObLogic ( &&0 A2 ))`(toMorLogic ( &&1 `A1,A2`a ))) A1 (toObLogic (&&0 A2 ))"
  by auto

subsection \<open>critical bracket (right-inner bracket) elimination axiom :\<close>

definition recursive_square_critical_rightinner_bracket_elimination :: bool where
 "recursive_square_critical_rightinner_bracket_elimination  = 
 ( ALL (A :: obLogic) (B :: obLogic) (C :: obLogic) (D :: obLogic). 
 ( `(A &0 (B &0 (C &0 D))),(A &0 ((B &0 C) &0 D))`( `A,A`(Iden A) &1 `(B &0 (C &0 D)),((B &0 C) &0 D)`(BracketL B C D) )
          o> `(toObLogic (&&0 (A &0 ((B &0 C) &0 D))))`( &> ( A &0 ( ( B &0 C ) &0 D ) ) ) )
 ~~ ( `( A &0 ( B &0 ( C &0 D ) ) ),(toObLogic( &&0 ( A &0 ( B &0 ( C &0 D ) ) ) ))`( &> ( A &0 ( B &0 ( C &0 D ) ) ) )
             o> `(toObLogic( &&0 ( ((A &0 B) &0 C) &0 D) ))`(toMorLogic( `((A &0 B) &0 C),((A &0 B) &0 C)`( `(A &0 B),(A &0 B)`( `A,A`( &&01 A ) _&&01 B ) _&&01 C ) _&&01 D )) ) )"

text \<open> same, after simplifying computation : \<close>

text \<open>
\begin{verbatim}
((Iden A) &1 BracketL)
   o> ( BracketL o> ( ( BracketL o> ( ( (&> A) _&> B ) _&> C ) ) _&> D ) )
= ( BracketL o> ( BracketL o> ( ( ( (&> A) _&> B ) _&> C ) _&> D ) ) )
    o> toMorLogic ((((&&01 A) _&&01 B) _&&01 C) _&&01 D)
\end{verbatim}
\<close>

lemma recursive_square_critical_rightinner_bracket_eliminationLHS :
 "wellIndexed ( `(A &0 (B &0 (C &0 D))),(A &0 ((B &0 C) &0 D))`( `A,A`(Iden A) &1 `(B &0 (C &0 D)),((B &0 C) &0 D)`(BracketL B C D) )
          o> `(toObLogic (&&0 (A &0 ((B &0 C) &0 D))))`( &> ( A &0 ( ( B &0 C ) &0 D ) ) ) )
 ( A &0 ( B &0 ( C &0 D ) ) ) (toObLogic (&&0 ( ( ( A &0 B ) &0 C ) &0 D )) )"
  by (auto simp only:simp3_BracketL_resolution0 [symmetric]) 

lemma recursive_square_critical_rightinner_bracket_eliminationRHS :
  "wellIndexed ( `( A &0 ( B &0 ( C &0 D ) ) ),(toObLogic( &&0 ( A &0 ( B &0 ( C &0 D ) ) ) ))`( &> ( A &0 ( B &0 ( C &0 D ) ) ) )
             o> `(toObLogic( &&0 ( ((A &0 B) &0 C) &0 D ) ))`(toMorLogic( `((A &0 B) &0 C),((A &0 B) &0 C)`( `(A &0 B),(A &0 B)`( `A,A`( &&01 A ) _&&01 B ) _&&01 C ) _&&01 D )) )
( A &0 ( B &0 ( C &0 D ) ) ) (toObLogic (&&0 ( ( ( A &0 B ) &0 C ) &0 D )) )"
  by (safe, auto simp only:simp2_BracketL_resolution0) 

subsection \<open> pentagon shortcut axiom : \<close>

lemma post_resolutor :
 "( ALL Z1 Z2 z1. wellIndexed z1 Z1 Z2 \<longrightarrow>
 ( ALL Z3 z2. wellIndexed z2 Z2 (toObLogic ( &&0 Z3 ) ) \<longrightarrow>
 ( ( `Z1,Z3`( `Z1,Z2`z1 o> `(toObLogic ( &&0 Z3 ) )`z2 ) _&> A ) 
   ~~ ( `(Z1 &0 A),(Z2 &0 A)`( `Z1,Z2`z1 &1 `A,A`(Iden A) ) o> `(toObLogic ( &&0 (Z3 &0 A) ))`( `Z2,Z3`z2 _&> A ) ) ) ) )"
  \<comment> \<open> by : induction A , 
       Multiply1 bifunctoriality , BracketL naturality , congruence \<close>
proof (clarify; induction A)
  case (Atom A)
  then show ?case by (auto simp add: resolution0.simps(2))
next
  case (Multiply0 A1 A2)
  show ?case (is "?P ~~ ?Q")
  proof -
    from Multiply0 have "?P ~~ ( `(Z1 &0 (A1 &0 A2)),((Z1 &0 A1) &0 A2)`(BracketL Z1 A1 A2) o> `(toObLogic ( &&0 ((Z3 &0 A1) &0 A2) ))`( `(Z1 &0 A1),(Z3 &0 A1)`( `(Z1 &0 A1),(Z2 &0 A1)`( `Z1,Z2`z1 &1 `A1,A1`(Iden A1) ) o> `(toObLogic ( &&0 (Z3 &0 A1) ))`( `Z2,Z3`z2 _&> A1 ) ) _&> A2 ) )" (is "_ ~~ ?P2") 
      by auto
    moreover from Multiply0  have "?P2 ~~ ( `(Z1 &0 (A1 &0 A2)),((Z1 &0 A1) &0 A2)`(BracketL Z1 A1 A2) o> `(toObLogic ( &&0 ((Z3 &0 A1) &0 A2) ))`( `((Z1 &0 A1) &0 A2),((Z2 &0 A1) &0 A2)`( `(Z1 &0 A1),(Z2 &0 A1)`( `Z1,Z2`z1 &1 `A1,A1`(Iden A1) ) &1 `A2,A2`(Iden A2) ) o> `(toObLogic ( &&0 ((Z3 &0 A1) &0 A2) ))`( `(Z2 &0 A1),(Z3 &0 A1)`( `Z2,Z3`z2 _&> A1 ) _&> A2 ) ) )" (is "?P2 ~~ ?P3") 
      by (auto intro: Multiply0.IH(2))
    moreover from Multiply0  have "?P3 ~~ ( `(Z1 &0 (A1 &0 A2)),(Z2 &0 (A1 &0 A2))`( `Z1,Z2`z1 &1 `(A1 &0 A2),(A1 &0 A2)`((Iden (A1 &0 A2))) ) o> `(toObLogic ( &&0 ((Z3 &0 A1) &0 A2) ))`( `(Z2 &0 (A1 &0 A2)),((Z2 &0 A1) &0 A2)`(BracketL Z2 A1 A2) o> `(toObLogic ( &&0 ((Z3 &0 A1) &0 A2) ))`( `(Z2 &0 A1),(Z3 &0 A1)`( `Z2,Z3`z2 _&> A1 ) _&> A2 ) ) )" (is "?P3 ~~ ?P4")
      apply(rule_tac convLogics_Trans, rule_tac Poly_morphism)
      apply(rule_tac convLogics_Trans, rule_tac Poly_congL, rule_tac BracketL_morphism, blast, blast, blast)
      apply(rule_tac convLogics_Sym, blast)
      by (rule_tac  convLogics_Trans, rule_tac Poly_morphism, auto)
    ultimately show "?P ~~ ?Q" 
      by (auto simp add: simp1_Multiply_resolution0)
  qed
qed

text \<open>
Memo : when all objects \textit{A B C D} are atomic then this (\textit{pentagon-shortcut A B C D}) 
precisely coincide ( modulo one extra ``side'' ) with 
(\textit{recursive-square-critical-rightinner-bracket-elimination A B C D}), 
regardless of the \textit{post-resolutor} lemma 
\<close>

text \<open> pentagon shortcut axiom : \<close>

definition pentagon_shortcut :: bool where
 "pentagon_shortcut  =
 ( ALL (A :: obLogic) (B :: obLogic) (C ::obLogic) (D :: obLogic ) .
      ( `(A &0 (B &0 (C &0 D))),(A &0 ((B &0 C) &0 D))`( `A,A`(Iden A) &1 `(B &0 (C &0 D)),((B &0 C) &0 D)`(BracketL B C D) )
          o> `(((A &0 B) &0 C) &0 D)`( `(A &0 ((B &0 C) &0 D)),((A &0 (B &0 C)) &0 D)`(BracketL A (B &0 C) D) o> `(((A &0 B) &0 C) &0 D)`( `(A &0 (B &0 C)),((A &0 B) &0 C)`(BracketL A B C) &1 `D,D`(Iden D) ) ) )
        ~~  ( `(A &0 (B &0 (C &0 D))),(((A &0 B) &0 C) &0 D)`( `(A &0 (B &0 (C &0 D))),((A &0 B) &0 (C &0 D))`(BracketL A B (C &0 D)) o> `(((A &0 B) &0 C) &0 D)`(BracketL (A &0 B) C D) )
             o> `(((A &0 B) &0 C) &0 D)`( `((A &0 B) &0 C),((A &0 B) &0 C)`( `(A &0 B),(A &0 B)`( `A,A`(Iden A) &1 `B,B`(Iden B) ) &1 `C,C`(Iden C) ) &1 `D,D`(Iden D) ) ) )"

lemma pentagon_shortcutLHS :
 "wellIndexed ( `(A &0 (B &0 (C &0 D))),(A &0 ((B &0 C) &0 D))`( `A,A`(Iden A) &1 `(B &0 (C &0 D)),((B &0 C) &0 D)`(BracketL B C D) )
          o> `(((A &0 B) &0 C) &0 D)`( `(A &0 ((B &0 C) &0 D)),((A &0 (B &0 C)) &0 D)`(BracketL A (B &0 C) D) o> `(((A &0 B) &0 C) &0 D)`( `(A &0 (B &0 C)),((A &0 B) &0 C)`(BracketL A B C) &1 `D,D`(Iden D) ) ) )
     (A &0 (B &0 (C &0 D))) (((A &0 B) &0 C) &0 D)"
 by auto

lemma pentagon_shortcutRHS :
 "wellIndexed ( `(A &0 (B &0 (C &0 D))),(((A &0 B) &0 C) &0 D)`( `(A &0 (B &0 (C &0 D))),((A &0 B) &0 (C &0 D))`(BracketL A B (C &0 D)) o> `(((A &0 B) &0 C) &0 D)`(BracketL (A &0 B) C D) )
             o> `(((A &0 B) &0 C) &0 D)`( `((A &0 B) &0 C),((A &0 B) &0 C)`( `(A &0 B),(A &0 B)`( `A,A`(Iden A) &1 `B,B`(Iden B) ) &1 `C,C`(Iden C) ) &1 `D,D`(Iden D) ) )
     (A &0 (B &0 (C &0 D))) (((A &0 B) &0 C) &0 D)"
  by auto

subsection \<open> epilogue : implicit arguments \<close>

consts Poly2 :: "morLogic \<Rightarrow> morLogic \<Rightarrow> morLogic" (infix "o>>" 65)
axiomatization where
  Poly2_def : "wellIndexed f A B  \<Longrightarrow> wellIndexed g B C  \<Longrightarrow> Poly2 f g = Poly A B f C g "

primrec resolutor_param2  :: "obLogic \<Rightarrow> obLogic \<Rightarrow> morLogic \<Rightarrow> obLogic \<Rightarrow> morLogic" ("'( `_,_` _ '_&>2 _ ')" [1000, 1000, 1000, 1000] 1000) where
  "( `Z1,Z2`z _&>2 (Atom A) )    =  ( `Z1,(toObLogic (&&0 Z2))`z &1 `(Atom A),(Atom A)`(Iden (Atom A)) ) " 
| "( `Z1,Z2`z _&>2 ( A &0 B ) )  =  ( (BracketL Z1 A B) o>> ( `(Z1 &0 A),(Z2 &0 A)`( `Z1,Z2`z _&>2 A ) _&>2 B ) ) "

lemma resolutor_param2P [intro!] : "wellIndexed z Z1 (toObLogic ( &&0 Z2 )) \<Longrightarrow> wellIndexed (`Z1,Z2`z _&>2 A) (Z1 &0 A) (toObLogic ( &&0 ( Z2 &0 A ) ))"
proof (induction A arbitrary: Z1 Z2 z)
  case (Atom x)
  then show ?case by (auto simp add: resolution0.simps(2))
next
  case (Multiply0 A1 A2)
  then show ?case
    apply(simp; (subst Poly2_def)+)
    by (auto simp add: simp1_Multiply_resolution0)
qed

lemma resolutor_param2_cong [intro!] : "wellIndexed z Z1 (toObLogic ( &&0 Z2 )) \<Longrightarrow> wellIndexed z' Z1 (toObLogic ( &&0 Z2 )) \<Longrightarrow> 
 z ~~ z' \<Longrightarrow> (`Z1,Z2`z _&>2 A) ~~ (`Z1,Z2`z' _&>2 A)" 
proof (induction A arbitrary: Z1 Z2 z z')
  case (Atom x)
  then show ?case by auto
next
  case (Multiply0 A1 A2)
  then show ?case
    by (simp? ; (subst Poly2_def)? ; auto intro!: Multiply0.IH)+
qed

end

text  \<open> Voila. \<close>
