(**#+TITLE: maclaneSolution2.v

Proph

https://gitlab.com/1337777/maclane/blob/master/maclaneSolution2.v

solves how 1337777 mom associativity pentagon is some recursive square
(reflective-functorial bracket-elimination cut-elimination resolution)

 **)

(**

#+BEGIN_SRC coq :exports both :results silent **)

Module BRACKETING_ELIMINATION.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive obLogic : Type :=
| Atom : nat -> obLogic
| Destruct0 : obLogic -> obLogic -> obLogic .

Delimit Scope log_scope with log.
Open Scope log_scope.

Notation "'Atom A" :=
  (@Atom A) (at level 35, right associativity) : log_scope.

Notation "A &0 B" :=
  (@Destruct0 A B) (at level 35, right associativity) : log_scope.

Reserved Notation "''Logic(' A1 |- A2 )"
         (at level 0, format "''Logic('  A1  |-  A2  )").

Inductive Logic : obLogic -> obLogic -> Type :=
| Poly : forall A1 A2, 'Logic( A1 |- A2 ) -> forall A3, 'Logic( A2 |- A3 ) -> 'Logic( A1 |- A3 )
| Iden : forall {A}, 'Logic( A |- A )
| Destruct1 : forall A1 A2, 'Logic( A1 |- A2 ) ->
                       forall B1 B2, 'Logic( B1 |- B2 ) -> 'Logic( A1 &0 B1 |- A2 &0 B2 )
| BracketL : forall {A B C}, 'Logic( A &0 (B &0 C) |- (A &0 B) &0 C )
where "''Logic(' A1 |- A2 )" := (@Logic A1 A2) : log_scope .

Notation "a_ o> a'" :=
  (@Poly _ _ a_ _ a') (at level 35, right associativity) : log_scope.

Notation "'Iden A" :=
  (@Iden A) (at level 35, right associativity) : log_scope.

Notation "a1 &1 a2" :=
  (@Destruct1 _ _ a1 _ _ a2) (at level 35, right associativity) : log_scope.

Module Sol.

  Inductive obLogic : Type :=
  | Atom : nat -> obLogic
  | Destruct0 : obLogic -> nat -> obLogic .

  Module Import Ex_Notations'.
    Delimit Scope sol_scope with sol.
    Notation "'Atom A" :=
      (@Atom A) (at level 35, right associativity) : sol_scope.
    Notation "A &0 B" :=
      (@Destruct0 A B) (at level 35, right associativity) : sol_scope .
  End Ex_Notations'.

  Fixpoint toObLogic (A : obLogic) :=
    match A with
    | ( 'Atom A0 )%sol => ( 'Atom A0 )%log
    | ( A1 &0 A2 )%sol => ( toObLogic A1 &0 'Atom A2 )%log
    end.

  Section Section1.

    Inductive Logic : obLogic -> obLogic -> Type :=
    | Poly : forall A1 A2, 'Logic( A1 |- A2 ) -> forall A3, 'Logic( A2 |- A3 ) -> 'Logic( A1 |- A3 )
    | Iden : forall {A}, 'Logic( ( 'Atom A )%sol |- ( 'Atom A )%sol )
    | Destruct1 : forall A1 A2, 'Logic( A1 |- A2 ) ->
                           forall B, 'Logic( ( A1 &0 B ) %sol |- ( A2 &0 B ) %sol )
    where "''Logic(' A1 |- A2 )" := (@Logic A1 A2) .

  End Section1.

  Module Import Ex_Notations.
    Export Ex_Notations'.
    Notation "''Logic(' A1 |- A2 )" := (@Logic A1 A2) : sol_scope .
    Notation "a_ o> a'" :=
      (@Poly _ _ a_ _ a') (at level 35, right associativity) : sol_scope .
    Notation "'Iden A" :=
      (@Iden A) (at level 35, right associativity) : sol_scope.
    Notation "a &1 B" :=
      (@Destruct1 _ _ a B) (at level 35, right associativity) : sol_scope .
  End Ex_Notations.    

  Fixpoint toLogic A1 A2 (a : 'Logic( A1 |- A2 ) %sol)
    : 'Logic( toObLogic A1 |- toObLogic A2 ) %log :=
    match a with
    | ( a_ o> a' )%sol => ( ( @toLogic _ _ a_ ) o> ( @toLogic _ _ a' ) )%log
    | ( 'Iden A )%sol => ( 'Iden ( 'Atom A ) )%log
    | ( a &1 B )%sol => ( ( @toLogic _ _ a ) &1 ( 'Iden ( 'Atom B ) ) )%log
    end.
  
End Sol.

Import Sol.Ex_Notations.

Reserved Notation "Z _&&0 A" (at level 35, right associativity).


Fixpoint resolution0_param (Z : Sol.obLogic) (A : obLogic) {struct A} : Sol.obLogic :=
  match A with
  | 'Atom A => ( Z &0 A ) %sol
  | A &0 B => ( Z _&&0 A ) _&&0 B
  end
(*  Z _&&0 ( A &0 B )  =>  ( Z _&&0 A ) _&&0 B  *)
where "Z _&&0 A" := (resolution0_param Z A) .

Reserved Notation "&&0 A" (at level 35, right associativity).

Fixpoint resolution0 (A : obLogic) : Sol.obLogic :=
  match A with
  | 'Atom A => ( 'Atom A )%sol
  | A &0 B => ( &&0 A ) _&&0 B
  end
(*  &&0 (A &0 B)  =>  ( &&0 A ) _&&0 B  *)
where "&&0 A" := (resolution0 A) .

Reserved Notation "z _&> A" (at level 35, right associativity).

Fixpoint resolutor_param Z1 Z2 (z : 'Logic( Z1 |- Sol.toObLogic ( &&0 Z2 ) )) A
  : 'Logic( Z1 &0 A |- Sol.toObLogic ( &&0 ( Z2 &0 A ) ) ) :=
  match A with
    | 'Atom A => z &1 ( 'Iden ( 'Atom A ) )
    | A &0 B => BracketL o> ( ( z _&> A ) _&> B )
  end
(*  z _&> ( A &0 B )  =>  BracketL o> ( ( z _&> A ) _&> B )  *)
where "z _&> A" := (resolutor_param z A) .

Reserved Notation "&> A" (at level 35, right associativity).

Fixpoint resolutor A : 'Logic( A |- Sol.toObLogic ( &&0 A ) ) :=
  match A with
    | 'Atom A => 'Iden ( 'Atom A )
    | A &0 B => ( &> A ) _&> B
  end
(*  &> ( A &0 B )  =>  ( &> A ) _&> B  *)
where "&> A" := (resolutor A) .

(** pre-resolutor lemmma **)

Reserved Notation "z _&&01 A" (at level 35, right associativity).

Fixpoint resolution1_param_Id Z1 Z2 (z : 'Logic( &&0 Z1 |- &&0 Z2 )%sol) A {struct A}
  : 'Logic( &&0 ( Z1 &0 A )%log |- &&0 ( Z2 &0 A )%log )%sol :=
  (*
  { z_Id : 'Logic( &&0 ( Z1 &0 A )%log |- &&0 ( Z2 &0 A )%log )%sol
  | ( Iden _&> A ) o> ( Sol.toLogic z_Id ) = ( Sol.toLogic z ) _&> A
    (* pre-resolutor at domain corresponding to post-resolutor at codomain *) } . *)
  match A with
  | 'Atom A => ( z &1 A )%sol
  | A1 &0 A2 => ( z _&&01 A1 ) _&&01 A2
  end
where "z _&&01 A" := (@resolution1_param_Id _ _ z A) .

Reserved Notation "&&01 A" (at level 35, right associativity).

Fixpoint resolution1_Id A {struct A} :
  'Logic( &&0 A |- &&0 A ) %sol :=
  (*
  { reso1_Id : 'Logic( &&0 A |- &&0 A ) %sol
  | ( &> A ) o> ( Sol.toLogic reso1_Id ) = Iden o> ( &> A ) } . *)
  match A with
  | 'Atom A => ( 'Iden A )%sol
  | A1 &0 A2 => ( &&01 A1 ) _&&01 A2
  end
where "&&01 A" := (@resolution1_Id A) .

Reserved Notation "z _&&1 a" (at level 35, right associativity).

Fixpoint resolution1_param Z1 Z2 (z : 'Logic( &&0 Z1 |- &&0 Z2 )%sol)
         A1 A2 (a : 'Logic( A1 |- A2 )) {struct a}
  : 'Logic( &&0 ( Z1 &0 A1 )%log |- &&0 ( Z2 &0 A2 )%log )%sol :=
  (*
  : { z_a : 'Logic( &&0 ( Z1 &0 A1 )%log |- &&0 ( Z2 &0 A2 )%log )%sol
    | ( Iden _&> A1 ) o> ( Sol.toLogic z_a ) 
             = ( Iden &1 a ) o> ( ( Sol.toLogic z ) _&> A2 )
      (* pre-resolutor at domain corresponding to post-resolutor at codomain *) } . *)
  match a  with
  | a_ o> a' =>
    ( ( ( &&01 Z1 ) _&&1 a_ ) o> ( z _&&1 a' ) )%sol
  | 'Iden A =>
    z _&&01 A
  | a &1 b =>
    ( z _&&1 a ) _&&1 b
  | @BracketL A B C => ( ( z _&&01 A ) _&&01 B ) _&&01 C
  end
where "z _&&1 a" := (@resolution1_param _ _ z _ _ a) .

Reserved Notation "&&1 a" (at level 35, right associativity).

Fixpoint resolution1 A1 A2 (a : 'Logic( A1 |- A2 )) {struct a} :
  'Logic( &&0 A1 |- &&0 A2 ) %sol :=
  (*
  { reso1_a : 'Logic( &&0 A1 |- &&0 A2 ) %sol
  | ( &> A1 ) o> ( Sol.toLogic reso1_a ) = a o> ( &> A2) } . *)
  match a with
  | a_ o> a' => ( ( &&1 a_ ) o> ( &&1 a' ) )%sol
  | 'Iden A => &&01 A
  | a &1 b => ( &&1 a ) _&&1 b
  | @BracketL A B C => ( ( &&01 A ) _&&1 ( 'Iden B ) ) _&&1 ( 'Iden C )
  end
where "&&1 a" := (@resolution1 _ _ a) .


(** recursive square excessive axiom : **)

Definition recursive_square_excessive
  := forall (A1 A2 : obLogic) (a : 'Logic( A1 |- A2 )),
    ( a o> ( &> A2 )
      =  ( &> A1 ) o> (Sol.toLogic ( &&1 a )) ).

(** critical bracket (right-inner bracket) elimination axiom : **)

Definition recursive_square_critical_rightinner_bracket_elimination
  := forall A B C D : obLogic,
    ( ( ( (@Iden A) &1 (@BracketL B C D) )
          o> ( &> ( A &0 ( ( B &0 C ) &0 D ) ) ) )
      = ( ( ( &> ( A &0 ( B &0 ( C &0 D ) ) ) )
              o> ( Sol.toLogic ( ( ( ( &&01 A ) _&&01 B ) _&&01 C ) _&&01 D ) ) )
          : 'Logic( ( A &0 ( B &0 ( C &0 D ) ) )
                    |- Sol.toObLogic (&&0 ( ( ( A &0 B ) &0 C ) &0 D )) ) ) ) .

(** same, after simplifying computation : **)

Check
  forall A B C D : obLogic,
    (('Iden A) &1 BracketL)
      o> ( BracketL o> ( ( BracketL o> ( ( (&> A) _&> B ) _&> C ) ) _&> D ) )
    = ( BracketL o> ( BracketL o> ( ( ( (&> A) _&> B ) _&> C ) _&> D ) ) )
        o> Sol.toLogic ((((&&01 A) _&&01 B) _&&01 C) _&&01 D).

Section pentagon_shortcut.

  Lemma post_resolutor Z1 Z2 (z1 : 'Logic( Z1 |- Z2 ))
        Z3 (z2 : 'Logic( Z2 |- Sol.toObLogic ( &&0 Z3 ) )) A :
    ( z1 o> z2 ) _&> A  =  ( z1 &1 (@Iden A) ) o> ( z2 _&> A ) .
    (* by : induction A , 
       Destruct1 bifunctoriality , BracketL naturality , congruence *) 
  Admitted.

  (** memo : when all objects A B C D are atomic then this
      (pentagon_shortcut A B C D) precisely coincide ( modulo one
      extra "side" ) with
      (recursive_square_critical_rightinner_bracket_elimination A B C D),
      regardless of the post_resolutor lemma **)

  (** pentagon shortcut axiom : **)

  Definition pentagon_shortcut
    := forall A B C D : obLogic,
      ( ( (@Iden A) &1 (@BracketL B C D) )
          o> ( BracketL o> ( BracketL &1 (@Iden D) ) )
        =  ( BracketL o> BracketL )
             o> ( ( ( (@Iden A) &1 (@Iden B) ) &1 (@Iden C) ) &1 (@Iden D) ) ).

End pentagon_shortcut.

End BRACKETING_ELIMINATION.

(**#+END_SRC

Voila. **)
