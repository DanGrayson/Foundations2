(** * Introduction 

This is the first of the group of files which contain the (current state of) the mathematical library for the proof assistant Coq based on the Univalent Foundations.
  Univalent Foundations are inspired by the univalent model of type theory which interprets types as homotopy types, Martin-Lof equality as paths spaces and universes as bases of universal ("univalent") fibrations.
  For a detailed overview of the content see the table of content in univ_toc.html .
  In has been modified from the eralier version in a several places but most importantly the part of the earlier file concerning the h-version of the inhabited construction and constructions related to finite sets have been moved to separate files.
  I tried to keep the notations such that the names of types which are (expected to be) a property in the sense of being of h-level 1 start with "is" but I have not been very consistent about it.
  There is an increasing number of theorems which have very short proofs based on the univalence axiom  which are given much longer proofs here.
  One hopes that eventually a mechnaical procedure for the replacement of proofs using the univalence axiom by proofs which only use it in some computationally uninformative ways will be found but until then I am not using the univalence axiom in any of the constructions.
  IMPORTANT: for those who may want to add to these files.
  There are some rules which have to be followed in creating new definitions and theorems which at the moment are not tracked by the proof checker.
  1.
  The current system of Coq is not completely compatible with the univalent semantics.
  The problem (the only one as far as I know) lies in the way the universe levels (u-levels) are assigned to the objects defined by the inductive definitions of the form

Inductive Ind (...)...(...): A -> Type := ...
  The current u-level assignemet takes into account the u-levels of the constructors but not the u-level of A.
  To ensure compatibility with the univalent model the u-level of Ind should be no less than the u-level of A.
  The u-levels of the parameters (the types appearing in (...)...(...) ) do not matter.
  A particular case of this problem is the "singleton elimination" rule which provides a good example of this incompatibility.
  The inductive definition of the identity types which uses one of the points as a parametr has A=:T (the underlying type) but since no mention of T appears in the constructor the system considers that there are no u-level restrictions on the resulting object and in particular that it can be placed in Prop while still having the full Ind_rect elimninator (see elimination, singleton elimination in the Index to the Refernce Manual).
  Since in the present approach the universe management is made explicit one has:

RULE 1 Do not use inductive definitions of the form 

Inductive Ind (...)...(...): A -> UU := ...
  unless all the "arguments" of A can be typed to UU.
  2.
  While it does not lead directly to any contradictions the shape of the foundations suggests very strongly that at the moment it is best to completely avoid the use of the universes Prop and Set.
  Instead we should use the the conditions isaprop and isaset which are applicable to the types of any of the type universes.
  *)




(** Preambule.
  *)

Unset Automatic Introduction.
  (** This line has to be removed for the file to compile with Coq8.2 *)

Definition UU:= Type.

Identity Coercion UUtoType:UU >-> Sortclass.


(** We are using the standard library definitions for unit (one point set), Empty_set and nat (the set of natural numbers). *)

Definition empty:=Empty_set.

Definition initmap (X:UU) : empty -> X.
Proof. intros X H.  destruct H. Defined. 

Definition terminalmap (X:UU) : X -> unit.
Proof. intros. exact tt. Defined.

(** ** Some standard constructions not using equality. *)

(**  *** Dependent sums (fibrations) *)


Record total2 (T:UU) (P: T -> UU) := tpair {pr21 : T ; pr22 : P pr21}. 

(** One can not use a new record each time one needs it because the general theorems about this construction would not apply to new instances of "Record" due to the "generativity" of inductive definitions in Coq. One could use "Inductive" instead of "Record" here but using "Record" which is equivalent to "Structure" allows us later to use the mechanism of canonical structures with total2. *)

 

(** *** Pairwise direct products. *)




Definition dirprod (X:UU)(Y:UU):= total2 X (fun x:X => Y).
Definition dirprodpair {X Y:UU}:= tpair X (fun x:X => Y).





Definition dirprodadj (X Y Z:UU): ((dirprod X Y) -> Z) -> (X -> Y -> Z) := fun f:_ => fun x:X => fun y:Y => f (dirprodpair x y).


Definition dirprodf (X Y X' Y':UU)(f:X-> Y)(f':X' -> Y'): dirprod X X' -> dirprod Y Y':= fun xx':_ => match xx' with tpair x x' => dirprodpair (f x) (f' x') end. 


Definition ddualand (X Y P:UU)(xp: (X -> P) -> P)(yp: (Y -> P) -> P): ((dirprod X Y) -> P) -> P.
Proof. intros X Y P xpp ypp xyp. apply xpp. intro x. apply ypp. intro y. apply xyp. apply dirprodpair;assumption. Defined.


(** ***  Basic constructions related to the adjoint evaluation function [ X -> ((X -> Y) -> Y) ]. *)


Definition adjev (X Y:UU): X -> ((X -> Y)->Y) := fun x f => f x.

Definition adjev2 (X Y:UU): (((X -> Y) -> Y) ->Y) -> (X -> Y)  := fun phi x => phi (fun f => f x).



(** *** Negation and double negation. *)


Definition neg (X:UU):= X -> empty.

Definition negf {X Y:UU}(f:X -> Y): (neg Y) -> (neg X):= fun phi: neg Y => fun x:X => phi (f x).

Definition dneg (X:UU):= neg (neg X).

Definition dnegf (X:UU)(Y:UU)(f:X->Y): (dneg X) -> (dneg Y):= negf (negf f).

Definition todneg (X:UU): X -> (dneg X):= adjev X empty. 

Definition dnegnegtoneg (X:UU): dneg (neg X) -> neg X := negf  (todneg X).

Lemma dneganddnegl1 (X:UU)(Y:UU): dneg X -> dneg Y -> (X -> neg Y) -> empty.
Proof. intros X Y xx yy f. apply xx. apply (negf f).  exact yy. Defined.

Definition dneganddnegimpldneg (X:UU)(Y:UU)(dx: dneg X)(dy:dneg Y): dneg (dirprod X Y):= ddualand X Y empty dx dy. 













(** ** Paths (equalities) and operations on paths *)




(* this is the original definition of paths by Voevodsky *)
Inductive paths (T:UU)(t:T): T -> UU := idpath: paths _ t t.

(* another plausible definition, with a slightly different induction principle: *)
Inductive paths' (T:UU): T -> T -> UU := idpath': forall t:T, paths' _ t t.

(* a parametrized version of paths: *)
Inductive pathsf (S T:UU)(f:S->T)(s:S) : T -> UU := idpathf: pathsf S T f s (f s).

Definition pathsf_to_paths (S T:UU)(f:S->T)(s:S) : forall t:T, pathsf S T f s t -> paths T (f s) t.
Proof. intros ? ? ? ? ? []. apply idpath. Defined.

(* prove an induction principle for paths with endpoints reversed *)
Lemma paths_rectr (T : UU) (t : T) (P : forall u : T, paths T u t -> Type):
        P t (idpath T t) -> forall (v : T) (p : paths T v t), P v p.
Proof. intros T t P p v e. destruct e. assumption. Defined.

(* prove the induction principle of paths' for paths *)
Lemma paths_rect2 (T : UU) (P : forall t u : T, paths T t u -> Type) :
       (forall t : T, P t t (idpath T t)) -> 
       forall (t u : T) (p : paths T t u), P t u p.
Proof. intros T P p t u e.  destruct e. apply p. Defined.

(* prove the induction principle of paths for paths' *)
Lemma paths'_rect1 (T : UU) (t : T) (P : forall u : T, paths' T t u -> Type):
        P t (idpath' T t) -> forall (v : T) (p : paths' T t v), P v p.
Proof. intros T t P p v e. destruct e. assumption. Defined.

(* prove an induction principle for paths' with endpoints reversed *)
Lemma paths'_rect2 (T : UU) (t : T) (P : forall u : T, paths' T u t -> Type):
        P t (idpath' T t) -> forall (v : T) (p : paths' T v t), P v p.
Proof. intros T t P p v e. destruct e. assumption. Defined.

Lemma twopathnotions1 (T:UU) (t t':T) : paths _ t t' -> paths' _ t t'.
Proof. intros T t t' e. induction e. apply idpath'. Defined.

Lemma twopathnotions2 (T:UU) (t t':T) : paths' _ t t' -> paths _ t t'.
Proof. intros T t t' e. induction e. apply idpath.  Defined.

Lemma twopathnotions12 (T:UU) (t t':T)(e:paths' _ t t') : paths' _ (twopathnotions1 _ _ _ (twopathnotions2 _ _ _ e)) e.
Proof. intros. induction e. unfold twopathnotions2, twopathnotions1. simpl. apply idpath'. Defined.

Lemma twopathnotions21 (T:UU) (t t':T)(e:paths _ t t') : paths' _ (twopathnotions2 _ _ _ (twopathnotions1 _ _ _ e)) e.
Proof. intros. induction e. unfold twopathnotions2, twopathnotions1. simpl. apply idpath'. Defined.

Definition pathscomp0 (T:UU) (a b c:T) : paths _ a b -> paths _ b c -> paths _ a c.
Proof. intros T a b c e1 e2. induction e1.  assumption. Defined.

Definition pathscomp0' (T:UU) (a b c:T) : paths _ a b -> paths _ b c -> paths _ a c.
Proof. intros T a b c e1 e2. induction e2.  assumption. Defined.

Definition pathscomp0rid  (T:UU) (a b:T)(e1: paths _ a b): paths _ (pathscomp0 _ _ _ _ e1 (idpath _ b)) e1. 
Proof. intros.  induction e1. simpl. apply idpath.  Defined. 

Definition pathscomp0rid'  (T:UU) (b c:T)(e2: paths _ b c): paths _ (pathscomp0 _ _ _ _ (idpath _ b) e2) e2. 
Proof. intros.  induction e2. simpl. apply idpath.  Defined. 

Definition pathscomp0path (T:UU) (a b c:T) (e1: paths _ a b) (e2: paths _ b c) : paths _ (pathscomp0 _ _ _ _ e1 e2) (pathscomp0' _ _ _ _ e1 e2).
Proof. intros. induction e1. induction e2. apply idpath. Defined.

Definition pathsinv0 {T:UU} (a:T) (b:T) : paths _ a b -> paths _ b a.
Proof. intros T a b e. induction e.  apply idpath. Defined. 

Definition pathsinv0l1 (X:UU)(a:X)(b:X)(e: paths _ a b): paths _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ e) e) (idpath _ _).
Proof. intros. induction e. simpl. apply idpath. Defined. 

Definition pathsinv0inv0 (X:UU)(x x':X)(e: paths _ x x'): paths _ (pathsinv0 _ _ (pathsinv0 _ _ e)) e.
Proof. intros. destruct e. simpl. apply idpath. Defined.  

Definition pathsinv0r1 (X:UU)(a:X)(b:X)(e: paths _ a b): paths _ (pathscomp0 _ _ _ _ e (pathsinv0 _ _ e)) (idpath _ _).
Proof. intros. induction e. simpl.  apply idpath. Defined. 

Definition pathsinv1r (T:UU)(a:T)(b:T)(c:T)(e1:paths _ a b)(e2: paths _ b c): paths _ (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e1 e2) (pathsinv0 _ _  e2)) e1.
Proof. intros. induction e1. simpl. induction e2. simpl. apply idpath.  Defined. 

Definition pathsinv1l (T:UU)(a:T)(b:T)(c:T)(e1:paths _ a b)(e2: paths _ b c): paths _ (pathscomp0 _ _ _ _ (pathsinv0 _ _  e1) (pathscomp0 _ _ _ _ e1 e2))  e2.
Proof. intros.  induction e2. simpl.  induction e1. simpl.  apply idpath. Defined. 


Definition pathscomp021 (T:UU) (a:T)(b:T) (c:T)
          (e11: paths _ a b)(e12: paths _ a b)(ee1: paths _ e11 e12)(e2:paths _ b c)
        : paths _ (pathscomp0 _ _ _ _ e11 e2) (pathscomp0 _ _ _ _ e12 e2).
Proof. intros. induction ee1.  apply idpath. Defined. 

Definition pathscomp022 (T:UU) (a b c:T)
          (e1: paths _ a b)(e21 e22:paths _ b c)(ee2:paths _ e21 e22)
        : paths _ (pathscomp0 _ _ _ _ e1 e21) (pathscomp0 _ _ _ _ e1 e22).
Proof. intros. induction ee2.  apply idpath. Defined. 

Definition maponpaths (X Y:UU) : forall f:X -> Y, forall x x':X, paths _ x x' -> paths _ (f x) (f x').
Proof. intros X Y f x x' e.  induction e. apply idpath. Defined. 

Lemma transportproperty : forall (T:UU) (P : T -> Type) (t u:T), paths _ t u -> P t -> P u.
Proof. intros T P t u e. induction e. trivial. Defined.

Lemma transportpropertyofpaths1 (T:UU)
        (P : forall (t u:T), paths T t u -> Type)
        (s t u:T)
        (f:paths _ s t)
        (e:paths _ t u):
        P t u e -> P s u (pathscomp0 _ _ _ _ f e).
Proof. intros T P s t u f e p. induction f. assumption. Defined.

Lemma transportpropertyofpaths1r (T:UU)
        (P : forall (t u:T), paths T t u -> Type)
        (s t u:T)
        (f:paths _ s t)
        (e:paths _ t u):
        P s u (pathscomp0 _ _ _ _ f e) -> P t u e.
Proof. intros T P s t u f e p. induction f. assumption. Defined.

Lemma transportpropertyofpaths2 (T:UU)
        (P : forall (t u:T), paths T t u -> Type)
        (t u v:T)
        (g:paths _ u v)
        (e:paths _ t u):
        P t u e -> P t v (pathscomp0 _ _ _ _ e g).
Proof.
  intros.
  induction g.
  apply (transportproperty _ (P _ _) e).
    apply pathsinv0, pathscomp0rid.
  assumption.
Defined.

Lemma transportpropertyofpaths2r (T:UU)
        (P : forall (t u:T), paths T t u -> Type)
        (t u v:T)
        (g:paths _ u v)
        (e:paths _ t u):
        P t v (pathscomp0 _ _ _ _ e g) -> P t u e.
Proof.
  intros.
  induction g.
  apply (transportproperty _ (P _ _) (pathscomp0 T t u u e (idpath T u)) e).
    apply pathscomp0rid.
  assumption.
Defined.

Lemma transportpropertyofpathsf1 (T U:UU) (f:T->U)
        (P : forall (t u:T), paths U (f t) (f u) -> Type)
        (s t u:T)
        (b:paths _ s t)
        (e:paths _ (f t)(f u)):
        P t u e -> P s u (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ b) e).
Proof. intros T U f P s t u b e p. induction b. assumption. Defined.

Lemma transportpropertyofpathsf1r (T U:UU) (f:T->U)
        (P : forall (t u:T), paths U (f t) (f u) -> Type)
        (s t u:T)
        (b:paths _ s t)
        (e:paths _ (f t)(f u)):
        P s u (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ b) e) -> P t u e.
Proof. intros T U f P s t u b e p. induction b. assumption. Defined.

Lemma transportpropertyofpathsf2 (T U:UU) (f:T->U)
        (P : forall (t u:T), paths U (f t) (f u) -> Type)
        (t u v:T)
        (g:paths _ u v)
        (e:paths _ (f t) (f u)):
        P t u e -> P t v (pathscomp0 _ _ _ _ e (maponpaths _ _ f _ _ g)).
Proof.
  intros.
  induction g.
  apply (transportproperty _ (P _ _) e).
    apply pathsinv0, pathscomp0rid.
  assumption.
Defined.

Lemma transportpropertyofpathsf2r (T U:UU) (f:T->U)
        (P : forall (t u:T), paths _ (f t) (f u) -> Type)
        (t u v:T)
        (g:paths _ u v)
        (e:paths _ (f t) (f u)):
        P t v (pathscomp0 _ _ _ _ e (maponpaths _ _ f _ _ g)) -> P t u e.
Proof.
  intros.
  induction g.
  apply (transportproperty _ (P _ _) (pathscomp0 _ _ _ _ e (idpath _ (f u))) e).
    apply pathscomp0rid.
  assumption.
Defined.

Lemma idtoid1 (X Y:UU)(f:X -> Y)(x:X) : paths _ (maponpaths _ _ f _ _ (idpath _ x)) (idpath _ (f x)).
Proof. intros. apply idpath. Defined. 


Definition maponpathscomp0 (X:UU)(Y:UU)(f:X -> Y)(x1:X)(x2:X)(x3:X)(e1: paths _ x1 x2)(e2: paths _ x2 x3)
        : paths _ (maponpaths _ _ f _ _ (pathscomp0 _ _ _ _ e1 e2))
                  (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ e1) (maponpaths _ _ f _ _ e2)).
Proof. intros. induction e1. apply idpath. Defined. 

Definition compose {X Y Z:Type} (g:Y->Z) (f:X->Y) := fun x => g (f x).
Definition idfun (T:UU) := fun t:T => t.

Definition constfun {X Y:UU} (y:Y) : X -> Y := fun x => y.

Definition maponpaths2a (X Y Z:UU)(f1 f2:X -> Y)(g:Y -> Z)
        : paths _ f1 f2 -> paths _ (compose g f1) (compose g f2).
Proof.
 intros X Y Z f1 f2 g e.
 induction e.
 apply idpath.
Defined.

Definition maponpaths2b (X Y Z:UU)(f:X-> Y)(g1:Y->Z)(g2:Y -> Z)
        : paths _ g1 g2 -> paths _ (compose g1 f) (compose g2 f).
Proof. intros X Y Z f g1 g2 e.  destruct e. apply idpath. Defined.

Lemma maponpathsidfun (X:UU)(x:X)(x':X)(e:paths _ x x'): paths _ (maponpaths _ _ (idfun X) _ _ e) e. 
Proof. intros. destruct e. apply idpath. Defined.

Lemma maponpathsfuncomp (X Y Z:UU)(f:X-> Y)(g:Y->Z)(x:X)(x':X)(e: paths _ x x')
        : paths _ (maponpaths _ _ g _ _ (maponpaths _ _ f _ _ e))
                  (maponpaths _ _ (compose g f) _ _ e).
Proof. intros. induction e. apply idpath. Defined.

(** The following four statements show that maponpaths defined by a function f which is homotopic to the identity is "surjective". It is later used to show that the maponpaths defined by a function which is a weak equivalence is itself a weak equivalence. *) 


Definition maponpathshomidinv (X:UU)(f:X -> X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X)
  : paths _ (f x) (f x') -> paths _ x x'
  := fun e: paths _ (f x) (f x') => pathscomp0 _ _ _ _ (pathsinv0 _ _ (h x)) (pathscomp0 _ _ _ _ e (h x')).

Ltac path_via x := apply (pathscomp0 _ _ x).
Ltac path_via' x := apply (pathscomp0' _ _ x).
Ltac path_from f := apply (maponpaths _ _ f).

Lemma maponpathshomid1 (X:UU)(f:X -> X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X)(e:paths _ x x')
        : paths _ (maponpaths _ _ f _ _ e)
                  (pathscomp0 _ _ _ _ (h x) (pathscomp0 _ _ _ _ e (pathsinv0 _ _ (h x')))).
Proof.
  intros.
  induction e.
  path_via (idpath _ (f x)).
   apply idtoid1.
  apply pathsinv0, pathsinv0r1.
Defined. 

Lemma maponpathshomid12 (X:UU)(x:X)(x':X)(fx fx':X)(e:paths _ fx fx')(hx:paths _ fx x)(hx':paths _ fx' x')
  : paths _ (pathscomp0 _ _ _ _ (hx) (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ (hx)) (pathscomp0 _ _ _ _ e (hx'))) (pathsinv0 _ _ (hx'))))
            e.
Proof. intros. induction hx. induction hx'. induction e.  apply idpath. Defined. 

Lemma pathscompfunc (T:UU) (a:T)(b:T)(c:T)
          (p:paths _ a b)(p':paths _ a b)(pp':paths _ p p')
          (q:paths _ b c)(q':paths _ b c)(qq':paths _ q q')
        : paths _ (pathscomp0 _ _ _ _ p q) (pathscomp0 _ _ _ _ p' q').
Proof. intros. induction pp'. induction qq'. apply idpath. Defined.

Lemma pathsinvfunc (T:UU)(a b:T)
                (p:paths _ a b)(p':paths _ a b)(pp':paths _ p p')
              : paths _ (pathsinv0 _ _ p) (pathsinv0 _ _ p').
Proof. intros. induction pp'. apply idpath. Defined.

Lemma pathscompassociativity (T:UU)(a b c d:T)(e:paths T a b)(f:paths T b c)(g:paths T c d)
      : paths _ (pathscomp0 _ _ _ _ e (pathscomp0 _ _ _ _ f g))
                (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e f) g).
Proof. intros. induction e. apply idpath. Defined.

Lemma maponpathsinv (T U:UU)(f:T->U)(a b:T)(e:paths _ a b)
                : paths _ (pathsinv0 _ _ (maponpaths _ _ f _ _ e))
                          (maponpaths _ _ f _ _ (pathsinv0 _ _ e)).
Proof. induction e. apply idpath. Defined.

(** an induction principle for paths over Y relative to a weq f : X -> Y with a "good" homotopy inverse: *)
Lemma paths_rect2w (X Y: UU)(f:X->Y)(g:Y->X)
        (b: forall x:X, paths _ (g (f x)) x)
        (c: forall y:Y, paths _ (f (g y)) y)
        (bc: forall x:X, paths _ (maponpaths _ _ f _ _ (b x)) (c (f x)))
        (P : forall x x' : X, paths Y (f x) (f x') -> Type) :
       (forall x : X, P x x (idpath Y (f x))) -> 
       forall (x x' : X) (q : paths Y (f x) (f x')), P x x' q.
Proof.
  intros X Y f g b c bc P p.
  (* use g to transport the property P and then prove it *)
  assert( K : forall (y y' : Y)(q' : paths Y y y'), P (g y) (g y') (pathscomp0 _ _ _ _ (c y) (pathscomp0 _ _ _ _ q'(pathsinv0 _ _ (c y'))))).
    intros y y' q'.
    destruct q'.
    set (p' := p (g y)).
    clearbody p'.
    apply (transportproperty _ (P _ _) (idpath _ _) _).
      path_via (pathscomp0 _ _ _ _ (c y) (pathsinv0 _ _ (c y))).
        apply pathsinv0, pathsinv0r1.
      apply pathsinv0,pathscomp0rid'.
    apply p.    
  clear p.
  intros x x' q.
  set (k := K (f x) (f x') q).
  clearbody k.
  clear K.
  (* the goal is now    P x x' q  *)
  apply (transportpropertyofpathsf2r _ _ _ _ _ _ _ (pathsinv0 _ _ (b x'))).
  apply (transportpropertyofpathsf1r _ _ _ _ _ _ _ (b x)).
  apply (transportproperty _ (P (g (f x)) (g (f x'))) (pathscomp0 _ _ _ _ (c (f x)) (pathscomp0 _ _ _ _ q (pathsinv0 _ _ (c (f x')))))).
  apply pathscompfunc.
  apply pathsinv0.
  apply bc.
  apply pathscomp022.
  path_via (pathsinv0 _ _ (maponpaths _ _ f _ _ (b x'))).    
  apply pathsinvfunc.  
  apply pathsinv0.
  apply bc.
  apply maponpathsinv.
  exact k.
Defined.

Lemma maponpathshomid2 (X:UU)(f:X->X)(h: forall x:X, paths _ (f x) x)(x:X)(x':X)(e:paths _ (f x) (f x'))
        : paths _ (maponpaths _ _ f _ _ (maponpathshomidinv _ f h _ _ e)) e.
Proof.
  (*

       x <------h x-------- (f x) -----e-----> (f x') ------h x'-----> x'   
     
         apply f to that to get 

     f x ----------------------------------------------------------> f x' 

          and get a path from that to e

   *)  
  intros.
  path_via (pathscomp0 _ _ _ _ 
            (h x)
            (pathscomp0 _ _ _ _ 
              (pathscomp0 _ _ _ _ 
                (pathsinv0 _ _ (h x))
                (pathscomp0 _ _ _ _ 
                  e
                  (h x')))
              (pathsinv0 _ _ (h x')))).
     apply maponpathshomid1.
  apply (maponpathshomid12 _ _ _ _ _ e).
Defined. 


(** Here we consider the behavior of maponpaths in the case of a projection p with a section s. *)


Definition pathssec1 (X Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _  (p (s x)) x): forall x:X, forall y:Y, paths _ (s x) y -> paths _ x (p y).
Proof. intros. path_via (p (s x)). apply pathsinv0, eps. path_from p. assumption. Defined.

Definition pathssec2 (X Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _ (p (s x)) x): forall (x x':X), paths _ (s x) (s x') -> paths _ x x'.
Proof. intros. path_via (p (s x')). apply (pathssec1 _ _ s); assumption. apply eps. Defined.

Definition pathssec2id (X Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _ (p (s x)) x)
        : forall x:X, paths _ (pathssec2 _ _ s p eps _ _ (idpath _ (s x))) (idpath _ x).
Proof.
  intros.
  path_via (pathscomp0 _ _ _ _ (pathsinv0 _ _ (eps x)) (eps x)).
   apply (maponpaths _ _ (fun e0 => pathscomp0 _ _ _ _ e0 (eps x))).
    apply pathscomp0rid.
  apply pathsinv0l1.
Defined. 


Definition pathssec3 (X Y:UU)(s:X-> Y)(p:Y->X)(eps: forall x:X, paths _ (p (s x)) x)
        : forall (x x':X) (e: paths _ x x'), paths _  (pathssec2 _ _ s p eps _ _ (maponpaths _ _ s _ _ e)) e.
Proof. intros. induction e.  apply pathssec2id.  Defined. 


(** ** Fibrations and paths. *)


Definition tppr (T:UU)(P:T -> UU)(x: total2 T P): paths _ x (tpair _ _ (pr21 _ _ x) (pr22 _ _ x)).
Proof. intros. induction x. apply idpath. Defined. 

(* this construction lifts a path e from x to x' in the base to a family of paths _ between the fibers P x and P x' *)
Definition constr1 (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): 
           total2 (P x -> P x')
                  (fun f: P x -> P x' => 
                    (total2
                      (
                        forall  p: P x, paths _ (tpair _ _ x p) (tpair _ _ x' (f p)))
                      (fun ee: 
                        forall  p: P x, paths _ (tpair _ _ x p) (tpair _ _ x' (f p)) =>
                        forall pp: P x, paths _ (maponpaths _ _ (pr21 _ _) _ _ (ee pp)) e
                      )
                    )
                  ). 
Proof. intros. induction e. split with (idfun (P x)). split with (fun p: P x => idpath _ _). intro. apply idpath. Defined. 

(* this function lifts a path e from x to x' in X "forward" to a function from the fiber P x to the fiber P x' *)
Definition transportf (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): P x -> P x'.
Proof. intros. destruct e. assumption. Defined.

Lemma  transportfid (X:UU)(P:X -> UU)(x:X)(p: P x): paths _ (transportf _ P _ _ (idpath _ x) p) p.
Proof. intros. apply idpath. Defined. 

(* this function lifts a path e from x to x' in X "backward" to a function from the fiber P x' to the fiber P x *)
Definition transportb (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): P x' -> P x.
Proof. intros. induction e. assumption. Defined.

Lemma functtransportf (X:UU)(Y:UU)(f:X->Y)(P:Y->UU)(x:X)(x':X)(e: paths _ x x')(p: P (f x))
        : paths _ (transportf _ (compose P f) _ _ e p)
                  (transportf _ P _ _ (maponpaths _ _ f _ _ e) p).
Proof.  intros. induction e. apply idpath. Defined.   

(** ** First homotopy notions *)


(** *** Contractibility, homotopy fibers etc. *)



Definition iscontr (T:UU) : UU := total2 T (fun cntr => forall t, paths _ t cntr).

Definition iscontrpair (T:UU) cntr (e: forall t:T, paths _ t cntr) : iscontr T := tpair T (fun cntr => forall t, paths _ t cntr) cntr e. 

Lemma contrl1 (X Y:UU)(f:X -> Y)(g: Y-> X) : (forall y, paths _ y (f(g y))) -> iscontr X -> iscontr Y.
Proof.
  intros ? ? ? ? efg [x0 nh].  
  split with (f x0).
  intro y.
  path_via (f (g y)).
   apply efg.
  path_from f.
  apply nh.
Defined. 

Lemma contrl1' (X Y:UU)(f:X -> Y)(g: Y -> X) : (forall y, paths _ (f(g y)) y) -> iscontr X -> iscontr Y.
Proof.
  intros ? ? ? ? efg is.
  apply (contrl1 _ _ f g).
   intro y.
   apply pathsinv0, efg.
  exact is.
Defined.

Lemma contrl2 (X:UU) : iscontr X -> forall x x':X, paths _ x x'.
Proof.
   intros ? [ x0 nh ] x x'.
   path_via x0.
    apply nh.
   apply pathsinv0, nh.
Defined.

(* Here "coconustot" = "co conus to t", and "conus" = "cone" *)
Definition coconustot (T:UU) (t:T) := total2 T (fun t' => paths _ t' t).
Definition coconustotpair (T:UU) (t t':T) (e: paths _ t' t) : coconustot T t := tpair _ (fun t' => paths _ t' t) t' e.

Lemma connectedcoconustot: forall T:UU, forall t:T, forall e1: coconustot _ t, forall e2:coconustot _ t, paths _ e1 e2.
Proof. intros T t [ x0 [] ] [ x1 [] ]. apply idpath. Defined. 

Lemma iscontrcoconustot (T:UU) (t:T) : iscontr (coconustot T t).
Proof. intros. unfold iscontr.  set (t0:= tpair _ (fun t' => paths _ t' t) t (idpath _ t)).  split with t0. intros. apply  connectedcoconustot. Defined.



(* coconusfromt = co conus from t *)
Definition coconusfromt (T:UU)(t:T) :=  total2 T (fun t' => paths _ t t').
Definition coconusfromtpair (T:UU) (t:T) (t':T) (e: paths _ t t'):coconusfromt T t := tpair T (fun t' => paths _ t t') t' e.

Lemma connectedcoconusfromt: forall T:UU, forall t:T, forall e1: coconusfromt T t, forall e2:coconusfromt T t, paths _ e1 e2.
Proof. intros T t [x1 []] [x2 []]. apply idpath. Defined.

Lemma iscontrcoconusfromt (T:UU) (t:T) : iscontr (coconusfromt T t).
Proof. intros.  split with (tpair _ (fun t' => paths _ t t') t (idpath _ t)). intros. apply  connectedcoconusfromt. Defined.



Definition pathsspace (T:UU) := total2 T (fun t => coconusfromt _ t).
Definition pathsspacetriple (T:UU) (t1:T)(t2:T)(e: paths _ t1 t2): pathsspace T := tpair _ _  t1 (coconusfromtpair _ _ t2 e). 

Definition deltap (T:UU) : T -> pathsspace T := (fun t:T => pathsspacetriple _ t t (idpath _ t)). 

Definition pathsspace' (T:UU) := total2 (dirprod T T) (fun xy:_ => (match xy with tpair x y => paths _ x y end)).


Definition hfiber (X:UU)(Y:UU)(f:X -> Y)(y:Y) : UU := total2 X (fun x:X => paths _ (f x) y). 
Definition hfiberpair  (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e: paths _ (f x) y): hfiber _ _ f y.
  intros. apply tpair with x, e.  Defined.

Definition hfiberpairpath (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e e': paths _ (f x) y)(p: paths _ e e') : paths _ (hfiberpair _ _ f y x e)(hfiberpair _ _ f y x e').
Proof. intros. destruct p. apply idpath. Defined.

Lemma hfibertriangle1 (X Y:UU)(f:X -> Y)(y:Y)(xe1 xe2: hfiber _ _ f y)(e: paths _ xe1 xe2)
           : paths _ (pr22 _ _ xe1) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (maponpaths _ _ (pr21 _ _ ) _ _ e)) (pr22 _ _ xe2)).
Proof. intros. destruct e. apply idpath. Defined. 

Lemma hfibertriangle2 (X Y:UU)(f:X -> Y)(y:Y)
        (xe1 xe2: hfiber _ _ f y)
        (ee: paths _ (pr21 _ _ xe1) (pr21 _ _ xe2))
        (eee: paths _ (pr22 _ _ xe1) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ ee) (pr22 _ _ xe2)))
        : paths _ xe1 xe2.
Proof. intros ? ? ? ? [ x e ] [ x' e' ] ee eee. 
       simpl in ee. destruct ee.
       path_from (fun e: paths _ (f x) y => hfiberpair _ _ f _ _ e); assumption.
Defined.

Definition hfibertransport (X Y:UU)(f:X->Y)(y:Y)(y':Y) : paths _ y y' -> hfiber _ _ f y -> hfiber _ _ f y'.
Proof.
  intros ? ? ? ? ? e [x e'].
  apply (hfiberpair _ _ f y' x).
  path_via y; assumption.
Defined.

Definition hfibertransport' (X Y:UU)(f:X->Y)(y:Y)(y':Y) : paths _ y y' -> hfiber _ _ f y -> hfiber _ _ f y'.
Proof.
  intros ? ? ? ? ? e [x e'].
  apply (hfiberpair _ _ f y' x).
  path_via' y; assumption.
Defined.

Lemma hfibertransportcompare (X Y:UU)(f:X->Y)(y:Y)(y':Y)(p:paths _ y y')(xe:hfiber _ _ f y) 
        : paths _ (hfibertransport _ _ _ _ _ p xe) (hfibertransport' _ _ _ _ _ p xe).
Proof.
  intros ? ? ? ? ? ? [x e]. 
  apply hfiberpairpath, pathscomp0path.
Defined.

Lemma hfibertransportid' (X Y:UU)(f:X->Y)(y:Y)(xe: hfiber _ _ f y) : paths _ xe (hfibertransport' _ _ _ _ _ (idpath _ y) xe).
Proof.
  intros ? ? ? ? [x e].
  apply idpath.
Defined.

Lemma hfibertransportid (X Y:UU)(f:X->Y)(y:Y)(xe: hfiber _ _ f y) : paths _ xe (hfibertransport _ _ _ _ _ (idpath _ y) xe).
Proof.
  intros ? ? ? ? [x e].
  apply hfiberpairpath, pathsinv0, pathscomp0rid.
Defined.

Definition constr3 (X:UU)(Y:UU)(f:X -> Y)(y:Y) (x:X) (e1 e2: paths _ (f x) y) (ee: paths _  e1 e2)
                : paths _ (hfiberpair _ _ _ _ x e1) (hfiberpair _ _ _ _ x e2).
Proof. intros. destruct ee. apply idpath.  Defined.

Definition coconusf (X Y:UU) (f: X -> Y):= total2 Y (fun y => hfiber _ _ f y).

Definition fromcoconusf (X Y:UU)(f: X -> Y) : coconusf _ _ f -> X := fun yxe:_ => pr21 _ _ (pr22 _ _ yxe).

Definition tococonusf (X Y:UU)(f: X -> Y) : X -> coconusf _ _ f := fun x:_ => tpair _ _ (f x) (hfiberpair _ _ _ _ x (idpath _ _)).   

Definition tococonush (X Y:UU)(f: X -> Y)(y: Y) : hfiber _ _ f y -> coconusf _ _ f.
Proof.
  intros ? ? ? ? xe.
  apply (tpair _ _ y xe).
Defined.

Definition coconushhtransportpath (X Y:UU)(f:X->Y)(y:Y)(y':Y)(xe : hfiber X Y f y)(e' : paths _ y y') 
           : paths (coconusf X Y f) (tococonush _ _ _ _ xe) (tococonush _ _ _ _ (hfibertransport _ _ _ _ _ e' xe)).
Proof.
  intros ? ? ? ? ? [x e] [].
  unfold tococonush, hfibertransport, hfiberpair. 
  assert (p : paths _ e (pathscomp0 _ _ _ _ e (idpath Y y))).
    apply pathsinv0, pathscomp0rid.
  destruct p.
  apply idpath.
Defined.  

Definition coconusfhtransportpath (X Y:UU)(f:X->Y)(x:X)(y:Y)(e' : paths _ (f x) y) 
           : paths (coconusf X Y f) (tococonusf _ _ _ x) (tococonush _ _ _ _ (hfibertransport _ _ _ _ _ e' (hfiberpair _ _ _ _ x (idpath _ _)))).
Proof.
  intros.
  unfold tococonush, tococonusf, hfibertransport, hfiberpair. 
Abort.

(** ** Weak equivalences *)

(** *** Basics. *)


Definition isweq (X Y:UU)(F:X -> Y) : UU := forall y:Y, iscontr (hfiber _ _ F y) .

Definition invmap (X:UU) (Y:UU) (f:X-> Y) (isw: isweq X Y f): Y->X.
Proof. intros X Y f isw y. unfold isweq in isw. apply (pr21 _ _ (pr21 _ _ (isw y))). Defined.

Lemma idisweq (T:UU) : isweq _ _ (idfun T).
Proof. 
  unfold isweq.
  intros T y.
  split with (tpair T (fun t => paths _ t y) _ (idpath _ y)). 
  intros [x []].  
  apply idpath.
Defined. 

Definition weq (X Y:UU) : UU := total2 _ (fun f:X->Y => isweq X Y f) .
Definition underlying_function (X Y : UU) := pr21 _ (fun f:X->Y => isweq _ _ f) : weq X Y -> (X -> Y).
Coercion underlying_function: weq >-> Funclass. 
Definition weqpair {X Y:UU}(f:X-> Y)(is: isweq X Y f) : weq X Y := tpair _ (isweq _ _) f is. 
Definition idweq (X:UU) : weq X X :=  tpair _ (isweq _ _) (idfun X) (idisweq _).

Lemma weqisweq (X Y : UU) (f : weq X Y) : isweq _ _ (underlying_function _ _ f).
Proof.
 intros.
 exact (pr22 _ _ f).
Defined.

Definition isweqtoempty (X:UU)(f:X -> empty): isweq _ _ f.
Proof. intros. intro. exact (initmap _ y). Defined. 

(** We now define different homotopies and maps between the paths _ spaces corresponding to a weak equivalence. What may look like unnecessary complexity in the  definition of weqgf is due to the fact that the "naive" definition, that of weqgf00, needs to be corrected in order for the lemma weqfgf to hold. *)



Definition weqfg (T1:UU) (T2:UU) (f:T1-> T2) (is1: isweq _ _ f): forall t2:T2, paths _ (f ((invmap _ _ f is1) t2)) t2.
Proof. intros. unfold invmap. simpl. unfold isweq in  is1. apply (pr22 _ _  (pr21 _ _  (is1 t2))). Defined.


Definition weqgf0  (X Y:UU) (f:X -> Y) (is: isweq _ _ f)(x:X): paths _ x (invmap _ _ f is (f x)).
Proof. intros. unfold isweq in is.  set (isfx:= is (f x)). set (pr21fx:= pr21 X (fun x':X => paths _ (f x') (f x))).
set (xe1:= (hfiberpair _ _ f (f x) x (idpath _ (f x)))). apply  (maponpaths _ _ pr21fx _ _ (pr22 _ _ isfx xe1)). Defined.

Definition weqgf (X Y:UU) (f:X -> Y) (is: isweq _ _ f)(x:X): paths _ (invmap _ _ f is (f x)) x := pathsinv0 _ _ (weqgf0 _ _ f is x).

Lemma diaglemma2 (X Y:UU)(f:X -> Y)(x x':X)
        (e1: paths _ x x')
        (e2: paths _ (f x') (f x))
        (ee: paths _ (idpath _ (f x)) (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ e1) e2))
        : paths _ (maponpaths _ _ f _ _ (pathsinv0 _ _ e1)) e2.
Proof. intros.  induction e1. simpl. simpl in ee. assumption. Defined. 

Definition weqfgf (X Y:UU)       (f:X->Y) (is: isweq _ _ f) (x:X) : paths _  (maponpaths _ _ f _ _ (weqgf _ _ f is x)) (weqfg _ _ f is (f x)).
Proof. intros. 
        set (xe1 := hfiberpair _ _ f (f x) x (idpath _ _)).
        apply diaglemma2, (hfibertriangle1 _ _ f (f x) xe1).
        Defined.

(** another induction principle for paths, building on paths_rect2w: *)
Lemma paths_rect2weq (X Y: UU)(f:X->Y)(is: isweq _ _ f)
        (P : forall x x' : X, paths Y (f x) (f x') -> Type)
      :  (forall x : X, P x x (idpath Y (f x)))
      ->  forall (x x' : X) (q : paths Y (f x) (f x')), P x x' q.
Proof.
  intros X Y f is P p x x' q.
  apply (paths_rect2w _ _ f (invmap _ _ _ is) (weqgf _ _ _ _) (weqfg _ _ _ _) (weqfgf _ _ _ _) _ p).
Defined.

Definition pathsweq2 (X Y:UU)(f:X-> Y)(is1: isweq _ _ f)
        :  forall x x':X, paths _ (f x) (f x') -> paths _ x x'
        := pathssec2 _ _ f (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq2id (X Y:UU)(f:X-> Y)(is1: isweq _ _ f)
        :  forall x:X, paths _ (pathsweq2 _ _ f is1 _ _ (idpath _ (f x))) (idpath _ x)
        := pathssec2id X Y f  (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq1 (X Y:UU)(f:X-> Y)(is1: isweq _ _ f)
        :  forall x:X, forall y:Y, paths _ (f x) y -> paths _ x (invmap _ _ f is1 y)
        := pathssec1 _ _ f (invmap _ _ f is1) (weqgf _ _ f is1).

Definition pathsweq1' (X Y:UU)(f:X -> Y)(is1: isweq _ _ f)
        :  forall x:X, forall y:Y, paths _ x (invmap _ _ f is1 y) -> paths _ (f x) y
        := fun (x:X) (y:Y) e => pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ e) (weqfg _ _ f is1 y).

Definition pathsweq3 (X Y:UU)(f:X-> Y)(is1: isweq _ _ f)
        :  forall x:X, forall x':X, forall e: paths _ x x', paths _  (pathsweq2 _ _ f is1 _ _ (maponpaths _ _ f _ _ e)) e
        := pathssec3 X Y f  (invmap _ _ f is1) (weqgf _ _ f is1).

Lemma maponpathsfunc (X Y : UU) (f : X -> Y) (x x' : X) (e e':paths _ x x') (ee:paths _ e e')
                : paths _ (maponpaths _ _ f _ _ e) (maponpaths _ _ f _ _ e').
Proof. intros. induction ee. apply idpath. Defined.

Definition pathsweq4 (X Y:UU)(f:X-> Y)(is1: isweq _ _ f)(x x':X)(e: paths _ (f x) (f x'))
        :  paths _ (maponpaths _ _ f _ _ (pathsweq2 _ _ f is1 _ _ e)) e.  
Proof.
  intros X Y f is.
  apply paths_rect2weq.
  assumption.
  intro x.
  path_via (maponpaths _ _ f _ _ (idpath _ x)).
    apply maponpathsfunc, pathsweq2id.
  apply idtoid1.
Defined.

(** *** Weak equivalences between contractible types (other implications are proved below). *)



Lemma iscontrxifiscontry (X Y:UU)(f:X -> Y) : isweq _ _ f -> iscontr Y -> iscontr X.
Proof. exact (fun X Y f is1 X0 => contrl1 _ _ (invmap _ _ f is1) f (weqgf0 _ _ f is1) X0).  Defined. 




(** *** Functions between fibers defined by a path on the base are weak equivalences. *)






Lemma isweqtransportf (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): isweq _ _ (transportf X P x x' e).
Proof. intros. induction e. apply idisweq. Defined. 


Lemma isweqtransportb (X:UU)(P:X -> UU)(x:X)(x':X)(e:paths _ x x'): isweq _ _ (transportb X P x x' e).
Proof. intros. induction e. apply idisweq. Defined. 

(** *** A type T:UU is contractible if and only if T -> unit is a weak equivalence. *)



Lemma unitl0: paths _ tt tt -> coconustot unit tt.
Proof. intros X. apply (coconustotpair unit tt tt X). Defined.

Lemma unitl1: coconustot unit tt -> paths _ tt tt.
Proof. intro X. destruct X as [ x t ]. destruct x.  assumption.  Defined.

Lemma unitl2: forall e: paths _ tt tt, paths _ (unitl1 (unitl0 e)) e.
Proof. intros. unfold unitl0. simpl.  apply idpath.  Defined.

Lemma unitl3: forall e:paths _ tt tt, paths _ e (idpath _ tt).
Proof. intros.
assert (e0: paths _ (unitl0 (idpath _ tt)) (unitl0 e)). eapply connectedcoconustot.
assert (e1:paths _ (unitl1 (unitl0 (idpath _ tt)))
    (unitl1 (unitl0 e))).   apply (maponpaths _ _ unitl1 (unitl0 (idpath _ tt)) (unitl0 e)  e0).    
assert (e2:  paths _ (unitl1 (unitl0 e)) e). eapply unitl2.
assert (e3: paths _  (unitl1 (unitl0 (idpath _ tt))) (idpath _ tt)). eapply unitl2.
 induction e1. clear e0. induction e2. assumption.  Defined. 


Theorem iscontrunit: iscontr unit.
Proof. assert (forall x, paths _ x tt). intros. induction x. apply idpath.
  apply tpair with tt.  assumption. Defined. 

Lemma ifcontrthenunitl0: forall e1: paths _ tt tt, forall e2: paths _ tt tt, paths _ e1 e2.
Proof. intros. assert (e3: paths _ e1 (idpath _ tt) ). apply unitl3.
assert (e4: paths _ e2 (idpath _ tt)). apply unitl3. induction e3.  induction e4. apply idpath. Defined. 

Lemma isweqcontrtounit: forall T:UU, iscontr T -> isweq T unit (terminalmap T).
Proof. intros T [t E] [].
 apply (iscontrpair _ (hfiberpair _ _ _ _ t (idpath _ tt))).
 intros [t0 x0]. 
 assert (e := E t0). destruct e.
 assert (e := ifcontrthenunitl0 (idpath _ tt) x0). destruct e.
 apply idpath. 
Defined. 

Theorem iscontrifweqtounit (X:UU): weq X unit -> iscontr X.
Proof. intros X X0.  apply (iscontrxifiscontry _ _ _ (pr22 _ _ X0)), iscontrunit. Defined.


(** *** A homotopy equivalence is a weak equivalence *)


Definition hfibersgftog (X:UU) (Y:UU) (Z:UU) (f:X -> Y) (g: Y -> Z) (z:Z) : hfiber _ _ (compose g f) z -> hfiber _ _ g z.
Proof. intros X Y Z f g z X0. destruct X0 as [ t x ]. apply (hfiberpair _ _ g z (f t) x).  Defined. 


Lemma constr2 (X:UU)(Y:UU)(f:X -> Y)(g: Y-> X)(efg: forall y:Y, paths _ (f(g y)) y) (z: X)
        : forall ye: hfiber _ _ g z,
                total2 (hfiber _ _ (compose g f) z)
                       (fun xd => paths _ ye (hfibersgftog _ _ _ f g z xd)). 
Proof.
  intros.
  destruct ye as [ y e ].
  assert (eint: paths _ y (f z)).
   induction e.
   apply pathsinv0, efg.
  destruct (constr1 _ (fun y => paths _ (g y) z) y (f z) eint) as [ pmap L ].
  split with (hfiberpair _ _ (compose g f) _ _ (pmap e)).
  apply L.
Defined. 


Lemma isweql1 (X:UU)(Y:UU)(f:X -> Y)(g: Y -> X) : 
        (forall y, paths _ (f(g y)) y) 
        -> forall  z: X,
                iscontr (hfiber _ _ (compose g f) z)
                -> iscontr (hfiber _ _ g z).
Proof.
 intros X Y f g efg z.
 exact (contrl1 _ _ 
   (hfibersgftog _ _ _ f g z)
   (fun z' => pr21 _ _ (constr2 _ _ _ _ efg z z'))
   (fun y' => pr22 _ _ (constr2 _ _ _ _ efg z y'))).
Defined.

Lemma isweql2 (X:UU)(Y:UU)(f1:X-> Y) (f2:X->Y) : (forall x:X, paths _ (f2 x) (f1 x)) -> forall y:Y, iscontr (hfiber _ _ f2 y) -> iscontr (hfiber _ _ f1 y).
Proof.
  intros X Y f1 f2 h y X0.
  set (f:= (fun z:(hfiber _ _ f1 y) => match z with (tpair x e) => hfiberpair _ _ f2 y x (pathscomp0 _ _ _ _ (h x) e) end)).
  set (g:= (fun z:(hfiber _ _ f2 y) => match z with (tpair x e) => hfiberpair _ _ f1 y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ (h x)) e) end)).
  assert (egf: forall z:(hfiber _ _ f1 y), paths _ (g (f z)) z).
    intros [ x e ].
    apply (constr3 _ _ f1 y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ (h x)) (pathscomp0 _ _ _ _ (h x) e)) e (pathsinv1l _ _ _ y (h x) e)).
  apply (contrl1' _ _ g f egf X0).
Defined.


Corollary isweqhomot (X:UU)(Y:UU)(f1:X-> Y) (f2:X->Y) (h: forall x:X, paths _ (f1 x) (f2 x)): isweq _ _ f1 -> isweq _ _ f2.
Proof. intros X Y f1 f2 h X0. unfold isweq. intro. apply (isweql2 _ _ f2 f1 h). apply X0. Defined. 

Theorem gradth (X:UU)(Y:UU)(f:X->Y)(g:Y->X) : (forall x:X, paths _ (g (f x)) x) -> (forall y:Y, paths _ (f (g y)) y) -> isweq _ _ f.
Proof.
  intros ? ? ? ? egf efg y'.
  pose (fg := compose f g).
  assert (iscontr (hfiber _ _ fg y')).
    assert (efg': forall y, paths _ y (fg y)).
      intro y.
      apply pathsinv0, efg.
    apply (isweql2 _ _ fg (idfun _) efg' y' (idisweq _ y')).
  apply (isweql1 _ _ g f egf y').
  assumption.
Defined.

(** *** Some basic weak equivalences *)



Corollary isweqinvmap (X:UU)(Y:UU)(f:X->Y)(is:isweq _ _ f): isweq _ _ (invmap _ _ f is).
Proof. intros. set (invf:= invmap _ _ f is). assert (efinvf: forall y:Y, paths _ (f (invf y)) y). apply weqfg. 
assert (einvff: forall x:X, paths _ (invf (f x)) x). apply weqgf. apply (gradth _ _  invf f efinvf einvff). Defined. 

Definition weqinv {X Y:UU} : weq X Y -> weq Y X
:= fun u => weqpair (invmap _ _ (pr21 _ _ u) (pr22 _ _ u)) (isweqinvmap _ _ (pr21 _ _ u) (pr22 _ _ u)).

Corollary invinv (X Y :UU)(f:X -> Y)(is: isweq _ _ f): forall x:X, paths _  (invmap _ _ (invmap _ _ f is) (isweqinvmap _ _ f is) x) (f x).
Proof. intros. apply pathsinv0, pathsweq1, weqgf. Defined.

Corollary isweqcontr2 (X:UU)(Y:UU)(f:X -> Y)(is1: isweq _ _ f): iscontr X -> iscontr Y.
Proof. intros. apply (iscontrxifiscontry _ _ (invmap _ _ f is1) (isweqinvmap _ _ f is1)). assumption. Defined.

Corollary isweqmaponpaths (X:UU)(Y:UU)(f:X->Y)(is:isweq _ _ f)(x:X)(x':X): isweq _ _ (maponpaths _ _ f x x').
Proof. intros. apply (gradth _ _ (maponpaths _ _ f x x') (pathsweq2 _ _ f is x x') (pathsweq3 _ _ f is x x')  (pathsweq4 _ _ f is x x')). Defined.  


Corollary isweqpathsinv0 (X:UU)(x x':X): isweq _ _ (pathsinv0 x x').
Proof. intros.  apply (gradth _ _ (pathsinv0 x x') (pathsinv0 x' x) (pathsinv0inv0 _ _ _) (pathsinv0inv0 _ _ _)). Defined.


Corollary isweqpathscomp0r (X:UU)(x x' x'':X)(e': paths _ x' x''): isweq _ _ (fun e:paths _ x x' => pathscomp0 _ _ _ _ e e').
Proof.
  intros ? ? ? ? [].
  set (f:= fun e:paths _ x x' => pathscomp0 _ _ _ _ e (idpath _ x')).
  apply (gradth _ _ f f).
      intro e. destruct e. apply idpath.
  intro e. destruct e. apply idpath.
Defined. 

Corollary  isweqfromcoconusf (X Y : UU)(f:X-> Y): isweq _ _ (fromcoconusf _ _ f).
Proof.
  intros.
  apply ( gradth _ _ (fromcoconusf _ _ f) (tococonusf _ _ f) ).
      intros [t [x []]]. apply idpath.
  intro. apply idpath.
Defined.


Corollary isweqdeltap (T:UU) : isweq _ _ (deltap T).
Proof.
  intros.
  apply (gradth _ _ (deltap _) (pr21 _ _)).
      intros x. apply idpath.
  intros [ t [ x0 [] ] ]. apply idpath.
Defined. 


Corollary isweqpr21pr21 (T:UU) : isweq (pathsspace' T) T (fun a:_ => (pr21 _ _ (pr21 _ _ a))).
Proof.
  intros.
  apply (gradth _ _ (fun a:pathsspace' T => (pr21 _ _ (pr21 _ _ a))) (fun t:T => tpair _ _ (dirprodpair t t) (idpath _ t))).
      intros [[? ?] []].
      apply idpath.
  intro.
  apply idpath.
Defined. 



(** *** The 2-out-of-3 property of weak equivalences.

Theorems showing that if any two of three functions f, g, gf are weak equivalences then so is the third - the 2-out-of-3 property. *)


Theorem twooutof3a (X Y Z:UU)(f:X->Y)(g:Y->Z) : isweq _ _ (compose g f) -> isweq _ _ g -> isweq _ _ f.
Proof. intros ? ? ? ? ? isgf isg. 
  apply (gradth _ _ f (compose (invmap _ _ (compose g f) isgf) g)).

    intro x. 
    apply (weqgf _ _ (compose g f)).

    intro y.
    apply (pathsweq2 _ _ g isg), (weqfg _ _ (compose g f) isgf (g y)).

Defined.


Corollary ifcontrcontrthenweq (X:UU)(Y:UU)(f:X -> Y) : iscontr X -> iscontr Y -> isweq _ _ f.
Proof.
  intros ? ? ? isx isy.
  apply (twooutof3a _ _ _ _ (terminalmap Y)).
  apply (isweqcontrtounit X); assumption.
  apply (isweqcontrtounit Y); assumption.
Defined.

Theorem twooutof3b (X Y Z:UU)(f:X->Y)(g:Y->Z) : isweq _ _ f -> isweq _ _ (compose g f) -> isweq _ _ g.
Proof.
 intros ? ? ? ? ? isf isgf.
 set (invf := invmap _ _ f isf).
 set (gf := compose g f).
 set (invgf := invmap _ _ gf isgf).
 apply (gradth _ _ g (compose f invgf)).
  intro y.
  apply (pathsweq2 _ _ invf). 
   apply isweqinvmap.
  assert (int4: paths _ (invgf (g y)) (invf y)).
   apply (pathsweq2 _ _ gf isgf).
   assert (int1: paths _ (g y) (gf (invf y))).
    path_from g.
    apply pathsinv0, (weqfg _ _ f).
   destruct int1.
   apply (weqfg _ _ gf).
  destruct int4.
  apply (weqgf _ _ f).
 intro.
 apply (weqfg _ _ gf).
Defined.

Lemma isweql3 (X Y:UU)(f:X-> Y)(g:Y->X) : (forall x:X, paths _ (g (f x)) x) -> isweq _ _ f -> isweq _ _ g.
Proof. 
  intros ? ? ? ? egf is.
  apply (twooutof3b _ _ _ f g is), (isweqhomot _ _ (idfun _) (compose g f)  (fun x => (pathsinv0 _ _ (egf x)))), idisweq.  
Defined. 

Theorem twooutof3c (X:UU)(Y:UU)(Z:UU)(f:X->Y)(g:Y->Z) : isweq _ _ f -> isweq _ _ g -> isweq _ _ (compose g f).
Proof.
  intros ? ? ? ? ? isf isg.
  set (invf := invmap _ _ f isf).
  set (invg := invmap _ _ g isg).
  apply (gradth _ _ (compose g f) (compose invf invg)).
   intro x.
   path_via (invf (f x)).
    path_from invf.
    apply (weqgf _ _ g isg (f x)).
   apply weqgf.
  intro z.
  path_via (g (invg z)).
   path_from g.
   apply (weqfg _ _ f isf (invg z)).
  apply (weqfg _ _ g isg z).
Defined. 


Definition weqcomp {X Y Z:UU} : weq X Y -> weq Y Z -> weq X Z. 
Proof.
  intros ? ? ? u v.
  apply (weqpair (compose v u)).
  apply twooutof3c; apply weqisweq.
Defined.


(** ** Basics about fibration sequences. *)



(** *** Fibrations sequences and their first "left shifts". 

By a pre-fibration sequence we mean a structure of the form 
[ (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(e: forall x:X, paths _ (g (f x)) z) ]. Note that giving such a structure is essentially equivalent to giving a structure of the form [ (X Y Z:UU)(g:Y -> Z)(z:Z)(ezmap: X -> hfiber _ _ g z) ] where ezmap takes values of the form tpair i.e. values which are invariant under the would-be eta conversion for dependent sums. The mapping in one direction is given in the definition of ezmap below. The mapping in another is given by
 
[ f:= fun x:X => pr21 _ _ (ezmap x) ]
[ ez: fun x:X => pr22 _ _ (ezmap x) ]

A pre-fibration sequence is called a fibration sequence if ezmap is a weak equivalence. We construct for any fibration sequence [ X -> Y -> (Z,z) ] its derived seqiuences  [ paths _ (g y) z -> X -> (Y,y) ] and identify the first function in the second derived sequence [ paths _ (f x) y -> paths _ (g y) z -> (X,x) ] 


*)


Definition ezmap (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z) : X -> hfiber _ _ g z := 
fun x:X => hfiberpair _ _ g z (f x) (ez x).

Definition isfibseq (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z) := isweq _ _ (ezmap _ _ _ f g z ez). 


Definition diff1invezmap (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(y:Y) : hfiber _ _ f y -> paths _ (g y) z :=  
fun xe: hfiber _ _ f y =>
match xe with
tpair x e => pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pathsinv0 _ _ e)) (ez x)
end.



Lemma diaglemma1 (Y Z:UU)(g:Y -> Z)(y y':Y)(z:Z)
        (phi: paths _ y' y)
        (ee: paths _ (g y) z)
        (ee': paths _ (g y') z)
        (e1: paths _ ee' (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ phi) ee))
      : paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pathsinv0 _ _ phi)) ee') ee.
Proof. intros. induction phi. simpl. simpl in e1. assumption. Defined.


Lemma isweqdiff1invezmap (X Y Z:UU) (f:X -> Y) (g:Y->Z) (z:Z) (ez: forall x, paths _ (g (f x)) z) (is: isfibseq _ _ _ f g z ez) (y:Y)
  : isweq _ _ (diff1invezmap _ _ _ f g z ez y).
Proof. 
 intros.
 set (ff:= diff1invezmap _ _ _ f g z ez y).
 set (ezm:= ezmap _ _ _ f g z ez).
 set (invezm:= invmap _ _ (ezmap _ _ _ f g z ez) is).
 set (pr21y:= pr21 Y (fun y:Y => paths _ (g y) z)).
 set (gg:= fun ee:paths _ (g y) z => 
      hfiberpair _ _ f y (invezm (hfiberpair _ _ g z y ee)) (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (hfiberpair _ _ g z y ee)))). 
 apply (gradth _ _ ff gg).
  intros [x b]. 
  destruct b. 
  simpl.
  set (e:=weqgf _ _ ezm is x).
  apply (hfibertriangle2 _ _ f (f x) (gg (ez x)) (hfiberpair _ _ f (f x) x (idpath _ (f x))) e). 
  path_via (maponpaths _ _ f _ _ (weqgf _ _ ezm is x)).
   path_via (maponpaths _ _ pr21y _ _ (maponpaths _ _ ezm _ _ (weqgf _ _ ezm is x))).
    path_via (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (ezm x))).
     apply idpath.
    apply (maponpaths _ _ (fun e => maponpaths _ _ pr21y _ _ e)),
           (pathsinv0 _ _ (weqfgf _ _ ezm is x)).
   apply (maponpathsfuncomp _ _ _ ezm pr21y _ _ (weqgf _ _ ezm is x)).
  apply pathsinv0, pathscomp0rid.
 intro egyz.
 apply (
      diaglemma1 _ _ g y
      (f (invezm (hfiberpair _ _ g z y egyz))) 
      z
      (maponpaths _ _ pr21y _ _ (weqfg _ _ ezm is (hfiberpair _ _ g z y egyz)))
      egyz
      (pr22 _ _ (ezm (invezm (hfiberpair _ _ g z y egyz))))
      ). 
 apply (hfibertriangle1 _ _ g z _ _ (weqfg _ _ ezm is (hfiberpair _ _ g z y egyz))).
Defined.

Definition diff1ezmap  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)
        : paths _ (g y) z -> hfiber _ _ f y 
       := fun e: paths _ (g y) z => 
                hfiberpair _ _ _ _ (pr21 _ _ (invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y) e))
                                   (pr22 _ _ (invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y) e)).


Definition diff1f  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(e: paths _ (g y) z)
        : X
        := pr21 _ _ (diff1ezmap _ _ _ f g z ez is y e).

Definition diff1ez  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(e: paths _ (g y) z)
        : paths _ (f (diff1f _ _ _ f g z ez is y e)) y
        := pr22 _ _ (diff1ezmap _ _ _ f g z ez is y e).


Theorem isfibseqdiff1 (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)
        : isfibseq _ _ _  (diff1f _ _ _ f g z ez is y) f y (diff1ez _ _ _ f g z ez is y).
Proof.
 intros.
 apply (isweqhomot _ _ 
        (fun e: paths _ (g y) z => invmap _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y) e)
        (fun e: paths _ (g y) z => diff1ezmap _ _ _ f g z ez is y e)
        ).
  intro e.
  apply tppr.
 apply isweqinvmap.
Defined.


Lemma fibseqhomot1 (X Y Z:UU)(f:X -> Y)(g:Y->Z)
                   (z:Z)
                   (ez: forall x:X, paths _ (g (f x)) z)
                   (is: isfibseq _ _ _ f g z ez)
                   (y:Y)
                   (e: paths _ (g y) z)
  : paths _ (diff1f _ _ _ f g z ez is y e) 
            (invmap _ _ (ezmap _ _ _ f g z ez) is (tpair _ _ y e)).
Proof.
  intros.
  set (inv:= diff1invezmap _ _ _ f g z ez y).
  set (map1:= diff1ezmap _ _ _ f g z ez is y).
  set (map2:= hfiberpair _ _ g z y).
  apply pathsweq1.
  path_via (map2 (inv (map1 e))).
   assert (m: forall tx: hfiber _ _ f y, paths _ (ezmap _ _ _ f g z ez (pr21 _ _ tx)) (map2 (inv tx))).
    intros [ t x ].
    destruct x.
    apply idpath.
   apply m.
  path_from map2.
  apply (weqgf _ _ map1 (isfibseqdiff1 _ _ _ f g z ez is y)).
Defined. 



Definition diff2ezmap (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(x:X)
        :  paths _ (f x) y -> hfiber _ _ (diff1f _ _ _ f g z ez is y) x
        := diff1ezmap _ _ _ (diff1f _ _ _ f g z ez is y) f y (diff1ez _ _ _ f g z ez is y) (isfibseqdiff1 _ _ _ f g z ez is y) x.


Definition diff2f (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(x:X)
        : paths _ (f x) y -> paths _ (g y) z
        := (fun e => pr21 _ _ (diff2ezmap _ _ _ f g z ez is y x e)).


Definition diff2ez (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)(ez: forall x:X, paths _ (g (f x)) z)(is: isfibseq _ _ _ f g z ez)(y:Y)(x:X)(e: paths _ (f x) y)
        : paths _ (diff1f _ _ _ f g z ez is y (diff2f _ _ _ f g z ez is y x e)) x
        :=  pr22 _ _ (diff2ezmap _ _ _ f g z ez is y x e).


Theorem fibseqhomot2  (X Y Z:UU)(f:X -> Y)(g:Y->Z)(z:Z)
                      (ez: forall x:X, paths _ (g (f x)) z)
                      (is: isfibseq _ _ _ f g z ez)
                      (y:Y)(x:X)
        : forall e: paths _ (f x) y, paths _ (diff2f _ _ _ f g z ez is y x e)
                                             (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pathsinv0 _ _ e)) (ez x)).
Proof.
  intros.
  path_via (invmap _ _ (diff1ezmap _ _ _ f g z ez is y) (isfibseqdiff1 _ _ _ f g z ez is y) (tpair _ _ x e)).
   apply fibseqhomot1.
  apply (invinv _ _ (diff1invezmap _ _ _ f g z ez y) (isweqdiff1invezmap _ _ _ f g z ez is y)).
Defined.


(** *** The first four fibration sequences associated with a function. *)


Definition d1f (X Y:UU)(f:X -> Y)(y:Y): hfiber _ _ f y -> X := pr21 _ _.

Theorem isfibseq1 (X Y:UU)(f:X -> Y)(y:Y) : isfibseq _ _ _ (d1f _ _ f y) f y (fun xe: _ => pr22 _ _ xe).
Proof.
  intros.
  apply (isweqhomot _ _ (idfun _)).
   intro.
   apply tppr.
  apply idisweq.
Defined.


Definition d2f  (X Y:UU)(f:X -> Y)(y:Y)(x:X): paths _ (f x) y -> hfiber _ _ f y := hfiberpair _ _ f y x.


Theorem isfibseq2  (X Y:UU)(f:X -> Y)(y:Y)(x:X): isfibseq _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun e:_ => idpath _ _).
Proof. intros.  
  apply (isfibseqdiff1 _ _ _ _ _ _ _ (isfibseq1 _ _ f y) x).
Defined.


Definition d3f (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)
        : paths _ (pr21 _ _ xe') x -> paths _ (f x) y
        := diff2f _ _ _ (d1f _ _ f y) f y (fun xe => pr22 _ _ xe) (isfibseq1 _ _ f y) x xe'. 

Lemma d3fhomot  (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (pr21 _ _ xe') x)
        : paths _ (d3f _ _ f y x xe' e)
                  (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ e)) (pr22 _ _ xe')).
Proof. intros. apply fibseqhomot2. Defined.


Definition d3fez  (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)
        : forall e: paths _ (pr21 _ _ xe') x, paths _ (d2f _ _ f y x (d3f _ _ f y x xe' e)) xe'
        := diff2ez _ _ _ (d1f _ _ f y) f y (fun xe => pr22 _ _ xe) (isfibseq1 _ _ f y) x xe'. 

Theorem isfibseq3 (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)
        : isfibseq _ _ _ (d3f _ _ f y x xe') (d2f _ _ f y x) xe' (d3fez _ _ f y x xe').
Proof. intros. apply isfibseqdiff1. Defined.



Definition d4f (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e:paths _ (f x) y)
        : paths _ (hfiberpair _ _ f y x e) xe' -> paths _ (pr21 _ _ xe') x 
        := diff2f _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun xe => idpath _ _) (isfibseq2 _ _ f y x) xe' e. 
 

Lemma d4fhomot  (X Y:UU)(f:X -> Y)(y:Y)(x:X)
          (xe': hfiber _ _ f y)
          (e: paths _ (f x) y)
          (ee: paths _ (hfiberpair _ _ f y x e) xe')
        : paths _ (d4f _ _ f y x xe' e ee)
                  (maponpaths _ _ (pr21 _ _) _ _ (pathsinv0 _ _ ee)).
Proof. intros. 
  path_via (pathscomp0 _ _ _ _
            (maponpaths _ _ (d1f _ _ f y) _ _ (pathsinv0 _ _ ee))
            (idpath _ (d1f _ _ f y (d2f _ _ f y x e)))).
    apply (fibseqhomot2 _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun xe => idpath _ _) (isfibseq2 _ _ f y x) xe' e ee).  
  apply pathscomp0rid.
Defined.

Definition d4fez  (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (f x) y)
        : forall ee: paths _ (hfiberpair _ _ f y x e) xe', paths _ (d3f _ _ f y x xe' (d4f _ _ f y x xe' e ee)) e
       := diff2ez _ _ _ (d2f _ _ f y x) (d1f _ _ f y) x (fun xe: _ => idpath _ _) (isfibseq2 _ _ f y x) xe' e. 

Theorem isfibseq4 (X Y:UU)(f:X -> Y)(y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (f x) y)
        : isfibseq _ _ _ (d4f _ _ f y x xe' e) (d3f _ _ f y x xe') e (d4fez _ _ f y x xe' e).
Proof. intros. apply isfibseqdiff1. Defined.






(** ** Homotopy fibers of the projection [pr21 T P: total2 T P -> T]. 


Theorems saying that for [ T:UU ] and [ P:T -> UU ] the homotopy fiber of the projection [ total2 T P -> T ] over [ t:T ] is weakly equivalent to [ P t ]. *)




Definition fibmap1 (T:UU) (P:T-> UU) (t:T): P t -> (hfiber _ _ (pr21 T P) t) := (fun z: P t => tpair _ _ (tpair T P t z) (idpath _ t)).

Definition fibmap2 (T:UU) (P:T-> UU) (t:T): (hfiber _ _ (pr21 T P) t) -> P t:= fun z: hfiber  _ _ (pr21 T P) t =>
match z with 
tpair zz e => (transportf T P  (pr21 _ _ zz) t e (pr22 T P zz))
end.



Theorem isweqfibmap1 (T:UU) (P:T-> UU) (t:T): isweq _ _ (fibmap1 T P t).
Proof. intros. assert (e1: forall x: P t, paths _ (fibmap2 _ _ t ((fibmap1 T P t) x)) x). intros. unfold fibmap1. unfold fibmap2. simpl. apply idpath. 

assert (e2: forall x: hfiber _ _ (pr21 T P) t , paths _ (fibmap1 _ _ t (fibmap2 T P t x)) x). intros.  destruct x as [ x t0 ]. destruct t0. simpl in x.  simpl. induction x. simpl. unfold transportf. unfold fibmap1. apply idpath. 

apply (gradth _ _ (fibmap1 T P t) (fibmap2 T P t) e1 e2). Defined. 

Theorem isweqfibmap2 (T:UU) (P:T-> UU) (t:T): isweq _ _ (fibmap2 T P t).
Proof.  intros. assert (e1: forall x: P t, paths _ (fibmap2 _ _ t ((fibmap1 T P t) x)) x). intros. unfold fibmap1. unfold fibmap2. simpl. apply idpath. 

assert (e2: forall x: hfiber _ _ (pr21 T P) t , paths _ (fibmap1 _ _ t (fibmap2 T P t x)) x). intros.  destruct x as [ x t0 ]. destruct t0. simpl in x.  simpl. induction x. simpl. unfold transportf. unfold fibmap1. apply idpath. 

apply (gradth _ _  (fibmap2 T P t) (fibmap1 T P t) e2 e1). Defined. 



Corollary isweqpr21 (T:UU) (P:T -> UU) : (forall t:T, iscontr (P t)) -> isweq _ _ (pr21 T P).
Proof.
  exact (fun T P is y => (iscontrxifiscontry _ _ (fibmap2 _ P y) (isweqfibmap2 _ P y) (is y))).
Defined.

Corollary familyfibseq (T:UU)(P:T->UU)(t:T): isfibseq (P t) (total2 T P) T (fun p: P t => tpair _ _ t p) (pr21 T P) t (fun p: P t => idpath _ t).
Proof. intros. unfold isfibseq. unfold ezmap.  apply isweqfibmap1. Defined.






(** ** Construction of the fibration sequence defined by a composable pair of functions

[ (hfiber f) -> (hfiber gf) -> (hfiber g) ]


*)


Section hfibersseq.

Variables X Y Z: UU.
Variable f:X->Y.
Variable g:Y->Z.
Variable z:Z.
Variable ye: hfiber _ _ g z.

Let gf:= fun x:X => g (f x).
Let y:=pr21 _ _ ye.
Let e:=pr22 _ _ ye. 




Definition hfibersinvezmap : hfiber _ _ (hfibersgftog _ _ _ f g z) ye ->  hfiber _ _ f y.
Proof.
  intros [ [ x e'] e0 ].
  apply (hfiberpair _ _ f y x).
  apply (maponpaths _ _ (fun z: hfiber _ _ g z => pr21 _ _ z) _ _ e0).
Defined.  


Definition hfiberpath1 (y1:Y)(e1: paths _ (g y1) z)(y2:Y)(e21:paths _ y2 y1)
        : paths _ (hfiberpair _ _  g z y2 (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ e21) e1))
                  (hfiberpair _ _ g z y1 e1).
Proof. intros.  induction e21. apply idpath. Defined.  

Definition hfiberpath11 (y1:Y)(e1: paths _ (g y1) z)(y2:Y)(e21:paths _ y2 y1): paths _ (maponpaths _ _ (fun u: hfiber _ _ g z => pr21 _ _ u) _ _ (hfiberpath1 y1 e1 y2 e21)) e21.
Proof. intros. induction e21. apply idpath. Defined. 

Definition gzx: UU := total2 (hfiber _ _ g z) (fun u: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ u))). 



Definition gzxmap3: hfiber _ _ f y -> hfiber _ _ (fun t: gzx => pr21 _ _ t) ye.
Proof.
  intro X0.
  split with (tpair _ (fun u: (hfiber _ _  g z) => (hfiber _ _ f (pr21 _ _ u))) _ X0).
  apply idpath.
Defined.

Definition gzxmap4: hfiber _ _ (fun t: gzx  => pr21 _ _ t) ye -> hfiber _ _ f y.
Proof.
  intros [ [ [ y' e1 ] [ x e2 ] ] e4 ].
  apply (hfiberpair _ _ f y x).
  apply (pathscomp0 _ _ _ _ e2).
  path_from (fun z: hfiber _ _ g z => pr21 _ _ z).
  exact e4.
Defined.

Definition gzxmap1  : hfiber _ _ (hfibersgftog _ _ _ f g z) ye -> hfiber _ _ (fun t: gzx => pr21 _ _ t) ye.
Proof.
  intros [[x e'] e0].
  split with (tpair _ (fun u: hfiber _ _  g z => (hfiber _ _ f (pr21 _ _ u)))
                      (hfiberpair _ _ g _ (f x) e')
                      (hfiberpair _ _ f _ x (idpath _ (f x)))).
  exact e0.
Defined. 

Definition gzxmap2 : hfiber _ _ (fun t: gzx => pr21 _ _ t) ye ->  hfiber _ _ (hfibersgftog _ _ _ f g z) ye.
Proof.
  intros [ [ [ y' e1 ] [ x e2] ] e4 ].
  split with (hfiberpair _ _ (compose g f) z x (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ e2) e1)).
   assert (e5: paths _ (hfiberpair Y Z g z (f x) (pathscomp0 _ _ _ _ (maponpaths _ _ g (f x) y' e2) e1))
                       (tpair Y (fun pointover : Y => paths _ (g pointover) z) y' e1)).
   apply hfiberpath1.
  exact (pathscomp0 _ _ _ _ e5 e4).
Defined. 


Definition gzxhom412  (t: hfiber _ _ (fun t: gzx => pr21 _ _ t) ye): paths _ (gzxmap4  (gzxmap1 (gzxmap2  t))) (gzxmap4 t).
Proof.
  pose (pg := (pr21 _ (fun p => paths _ (g p) z))).
  intros [ [ [ y' e1 ] [ x e2 ] ] e4 ].
  pose (r := hfiberpath1 y' e1 (f x) e2).
  pose (q := (pathscomp0 _ _ _ _ (maponpaths _ _ pg _ _ r) (maponpaths _ _ pg _ _ e4))).
  assert (int1: paths _ (maponpaths _ _ pg _ _ (pathscomp0 _ _ _ _ r e4)) q).
   apply maponpathscomp0.
  assert (int2: paths _ q (pathscomp0 _ _ _ _ e2 (maponpaths _ _ pg _ _ e4))).
   apply pathscomp021.
   exact (hfiberpath11 y' e1 (f x) e2).
  exact (maponpaths _ _ (hfiberpair _ _ f y x) _ _ (pathscomp0 _ _ _ _ int1 int2)).
Defined. 


Lemma isweqgzxmap4l1  (u: hfiber _ _ f y):
   paths _ (gzxmap4  (fibmap1 _ (fun v => (hfiber _ _ f (pr21 _ _ v))) ye u)) u.  
Proof.
  intros [ t x ].
  simpl.
  destruct ye.
  path_from (hfiberpair _ _ f y t).
  apply pathscomp0rid.
Defined. 

Lemma  isweqgzxmap4 : isweq _ _ gzxmap4.
Proof.
  intros.
  apply (isweql3 _ _ (fibmap1 _ (fun ye => hfiber _ _ f (pr21 _ _ ye)) ye)).
  apply isweqgzxmap4l1.
  apply (isweqfibmap1 _ (fun ye => hfiber _ _ f (pr21 _ _ ye))).
Defined. 



Definition gzxhom12   (t: hfiber _ _ (fun t: gzx  => pr21 _ _ t) ye): paths _ (gzxmap1  (gzxmap2  t)) t. 
Proof.
  intros.
  apply (pathsweq2 _ _ gzxmap4).
   apply isweqgzxmap4.
  apply gzxhom412.
Defined. 


Definition gzxhom21  (t:hfiber _ _ (hfibersgftog _ _ _ f g z) ye) : paths _ (gzxmap2 (gzxmap1 t)) t. 
Proof. intros. destruct t as [ t x ].  destruct t. apply idpath. Defined. 


Lemma isweqgzxmap1  : isweq _ _ gzxmap1 .
Proof. intros. exact (gradth _  _ gzxmap1  gzxmap2  gzxhom21 gzxhom12 ).  Defined. 


Definition fibseqhom (u: hfiber _ _ (hfibersgftog _ _ _ f g z) ye): paths _ (gzxmap4 (gzxmap1  u)) (hfibersinvezmap  u).
Proof. intros. destruct u as [ t x ].   destruct t. apply idpath. Defined. 


Theorem isweqhfibersinvezmap : isweq _ _ hfibersinvezmap.
Proof.
  intros.
  apply (isweqhomot _ _ (compose gzxmap4 gzxmap1) hfibersinvezmap fibseqhom).
  apply (twooutof3c _ _ _ gzxmap1 gzxmap4 isweqgzxmap1 isweqgzxmap4).
Defined.


Definition hfibersezmap: hfiber _ _ f y -> hfiber _ _ (hfibersgftog _ _ _ f g z) ye := fun xe:_ => tpair _ _ (pr21 _ _ (invmap _ _ hfibersinvezmap isweqhfibersinvezmap xe)) (pr22 _ _ (invmap _ _ hfibersinvezmap isweqhfibersinvezmap xe)).

Lemma isweqhfibersezmap: isweq _ _ hfibersezmap.
Proof.
  assert (homot: forall xe , paths _  (invmap _ _ hfibersinvezmap isweqhfibersinvezmap xe) (hfibersezmap xe)).
  intro.
  apply tppr.
  apply (isweqhomot _ _ _ _ homot).
  apply isweqinvmap.
Defined.


End hfibersseq. 



(** *** Main corollaries of the constructions of hfibersseq. *)


Corollary isweqhfibersgftog (X:UU)(Y:UU)(Z:UU)(f:X -> Y)(g:Y -> Z)(z:Z): isweq _ _ f -> isweq _ _ (hfibersgftog _ _ _ f g z).
Proof.
  intros ? ? ? ? ? ? X0 y.
  apply (iscontrxifiscontry _ _ (hfibersinvezmap X Y Z f g z y) ).
  apply isweqhfibersinvezmap.
  apply X0.
Defined.


Definition hfibersftogf (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye))
        :  hfiber _ _ (compose g f) z
        := pr21 _ _ (hfibersezmap _ _ _ f g z ye xe). 


Definition hfibersez (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye))
        : paths _ (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye
        := pr22 _ _ (hfibersezmap _ _ _ f g z ye xe).



(** There are the follwing alternative definitions of hfibersftogf and hfibseqez:

[ Definition hfibersftogf (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z): hfiber _ _ f (pr21 _ _ ye) -> hfiber _ _ (fun x:X => g (f x)) z:= fun xe:_ => hfiberpair _ _ (fun x:X => g (f x)) z (pr21 _ _ xe) (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pr22 _ _ xe)) (pr22 _ _ ye)). ]


[ Definition hfibersez (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)(xe: hfiber _ _ f (pr21 _ _ ye)): paths _ (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye := hfibertriangle2 _ _ g z (hfibersgftog _ _ _ f g z (hfibersftogf _ _ _ f g z ye xe)) ye (pr22 _ _ xe) (idpath _ (pathscomp0 _ _ _ _ (maponpaths _ _ g _ _ (pr22 _ _ xe)) (pr22 _ _ ye))). ]

However I do not know whether the are equivalent to the ones given below or whether one can prove that the resulting pre-fibration sequence is a fibration sequence. *)


Corollary isfibseqhfibers (X Y Z:UU)(f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber _ _ g z)
        : isfibseq (hfiber _ _ f (pr21 _ _ ye))
                   (hfiber _ _ (fun x:X => g (f x)) z)
                   (hfiber _ _ g z)
                   (hfibersftogf _ _ _ f g z ye)
                   (hfibersgftog _ _ _ f g z)
                   ye
                   (hfibersez _ _ _ f g z ye).
Proof. intros. apply isweqhfibersezmap. Defined.


(** ** Fiber-wise weak equivalences. 


Theorems saying that a fiber-wise morphism between total spaces is a weak equivalence if and only if all the morphisms between the fibers are weak equivalences. *)


Definition totalfun (X:UU)(P:X-> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x) := (fun z: total2 X P => tpair X Q (pr21 _ _ z) (f (pr21 _ _ z) (pr22 _ _ z))).


Theorem isweqtotaltofib (X:UU)(P: X -> UU)(Q: X -> UU)(f: forall x:X, P x -> Q x):
isweq _ _ (totalfun _ _ _ f) -> forall x:X, isweq _ _ (f x).
Proof.
  intros ? ? ? ? X0 x.
  set (totf:= totalfun _ _ _ f).
  set (piq:= fun z: total2 _ Q => pr21 _ _ z).
  apply (twooutof3a _ _ _ (f x) (fibmap1 _ Q _)).
   apply (isweqhomot _ _ (compose (hfibersgftog _ _ _ totf piq _) (fibmap1 _ P _))).
    intro p.
    apply idpath.
   apply (twooutof3c _ _ _ _ _ (isweqfibmap1 _ _ _)).
  intro y.
   apply (iscontrxifiscontry _ _ (hfibersinvezmap _ _ _ totf piq _ _)).
    apply isweqhfibersinvezmap.
   apply X0.
  apply isweqfibmap1.
Defined.
 

Theorem isweqfibtototal (X:UU)(P: X -> UU)(Q: X -> UU)(f: forall x:X, P x -> Q x):
(forall x:X, isweq _ _ (f x)) -> isweq _ _ (totalfun _ _ _ f).
Proof.
  intros ? ? ? ? X0.
  set (fpq:= totalfun _ _ _ f).
  set (pr21q:= fun z: total2 _ Q => pr21 _ _ z).
  intro xq.
  set (x:= pr21q xq).
  set (hfpqx:= hfibersgftog _ _ _ fpq pr21q x).
  set (xqe:= hfiberpair _ _ pr21q _ xq (idpath _ _)).
  set (intmap:= hfibersinvezmap _ _ _ fpq pr21q _ xqe).
  apply (isweqcontr2 _ _ intmap).
  apply isweqhfibersinvezmap.
  apply (twooutof3b _ _ _ (fibmap1 _ P _)  ).
  apply(isweqfibmap1 _ P _).
  apply (twooutof3c _ _ _ (f x) (fibmap1 _ Q x)).
  apply X0.
  apply isweqfibmap1.
Defined.


(** ** Homotopy fibers of the function [fpmap: total2 X (P f) -> total2 Y P].

Given [ X Y ] in [ UU ], [ P:Y -> UU ] and [ f: X -> Y ] we get a function [ fpmap: total2 X (P f) -> total2 Y P ]. The main theorem of this section asserts that the homotopy fiber of fpmap over [ yp:total Y P ] is naturally weakly equivalent to the homotopy fiber of [ f ] over [ pr21 yp ]. In particular, if  [ f ] is a weak equivalence then so is [ fpmap ]. *)


Definition fpmap (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU) : total2 X (compose P f) -> total2 Y P := 
(fun z:total2 X (fun x:X => P (f x)) => tpair Y P (f (pr21 _ _ z)) (pr22 _ _ z)).


Definition hffpmap2 (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU):  total2 X (fun x:X => P (f x)) -> total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)).
Proof. intros X Y f P X0. set (u:= fpmap _ _ f P X0).  split with u. set (x:= pr21 _ _ X0).  split with x. simpl. apply idpath. Defined.


Definition hfiberfpmap (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU)(yp: total2 Y P): hfiber _ _ (fpmap _ _ f P) yp -> hfiber _ _ f (pr21 _ _ yp).
Proof. intros X Y f P yp X0. set (int1:= hfibersgftog _ _ _ (hffpmap2 _ _ f P) (fun u: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u))) => (pr21 _ _ u)) yp).  set (phi:= fibmap2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)) yp). apply (phi (int1 X0)).   Defined. 



Lemma centralfiber (X:UU)(P:X -> UU)(x:X): isweq _ _ (fun p: P x => tpair (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) (coconusfromtpair _ _ x (idpath _ x)) p).
Proof. intros. set (f:= fun p: P x => tpair (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) (coconusfromtpair _ _ x (idpath _ x)) p). set (g:= fun z: total2 (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)) => transportf X P (pr21 _ _ (pr21 _ _ z)) x (pathsinv0 _ _ (pr22 _ _ (pr21 _ _ z))) (pr22 _ _ z)).  

assert (efg: forall  z: total2 (coconusfromt _ x) (fun u: coconusfromt _ x => P(pr21 _ _ u)), paths _ (f (g z)) z). intro. destruct z as [ t x0 ]. destruct t as [t x1 ].   simpl. induction x1. simpl. apply idpath. 

assert (egf: forall p: P x , paths _ (g (f p)) p).  intro. apply idpath.  

apply (gradth _ _  f g egf efg). Defined. 


Lemma isweqhff (X:UU)(Y:UU)(f: X -> Y)(P:Y-> UU): isweq _ _ (hffpmap2 _ _ f P). 
Proof.
  intros.
  pose (k := fun x:X => total2 (coconusfromt _ (f x)) (compose P (pr21 _ _))).
  pose (int    := total2 X k).
  pose (intpair:= tpair  X k).
  pose (toint:= fun z: (total2 (total2 Y P) (fun u:total2 Y P => hfiber _ _ f (pr21 _ _ u)))
        => intpair (pr21 _ _ (pr22 _ _ z))
                   (tpair _  (compose P (pr21 _ _))
                             (coconusfromtpair _ _ (pr21 _ _ (pr21 _ _ z)) (pr22 _ _ (pr22 _ _ z)))
                             (pr22 _ _ (pr21 _ _ z)))).
  pose (h := fun u => toint ((hffpmap2 _ _ f P) u)).
  apply (twooutof3a _ _ _ (hffpmap2 _ _ f P) toint).
   apply (isweqfibtototal _ (compose P f) k 
                (fun x => tpair _  (compose P (pr21 _ _)) (coconusfromtpair _ _ (f x) (idpath _ _)))).
   intro x.
   apply (centralfiber _ P (f x)).
  pose (fromint := fun z: int => tpair _ (fun u => hfiber _ _ f (pr21 _ _ u))
                                         (tpair Y P (pr21 _ _ (pr21 _ _ (pr22 _ _ z))) (pr22 _ _ (pr22 _ _ z)))
                                         (hfiberpair _ _ f (pr21 _ _ (pr21 _ _ (pr22 _ _ z))) (pr21 _ _ z) (pr22 _ _ (pr21 _ _ (pr22 _ _ z))))).
  apply (gradth _ _ toint fromint).
   intros [ [y b] [x e] ].
   apply idpath.
  intros [ t [ [y b] x ] ].
  apply idpath.
Defined. 




Theorem isweqhfiberfp (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU)(yp: total2 Y P): isweq _ _ (hfiberfpmap _ _ f P yp).
Proof.
  intros.
  apply (twooutof3c _ _ _ (hfibersgftog _ _ _ (hffpmap2 _ _ f P) (pr21 _ _) yp)).
   apply isweqhfibersgftog, isweqhff.
  apply (isweqfibmap2 _ (fun u => hfiber _ _ f (pr21 _ _ u))).
Defined. 


Corollary isweqfpmap (X:UU)(Y:UU)(f:X -> Y)(P:Y-> UU): isweq _ _ f -> isweq _ _ (fpmap _ _ f P).
Proof.
  intros ? ? ? ? X0 y.
  apply (iscontrxifiscontry _ _ (hfiberfpmap _ _ _ _ _)).
  apply isweqhfiberfp.
  apply X0.
Defined. 


(** ** The maps between total spaces of families given by a map between the bases of the families and maps between the corresponding members of the families. *)


Definition bandfmap (X Y:UU)(f: X -> Y) (P:X -> UU)(Q: Y -> UU)(fm: forall x:X, P x -> (Q (f x))): total2 X P -> total2 Y Q:= fun xp:_ =>
match xp with
tpair x p => tpair Y Q (f x) (fm x p)
end.

Theorem isweqbandfmap  (X Y:UU)(f: X -> Y) (P:X -> UU)(Q: Y -> UU)
                (fm: forall x:X, P x -> (Q (f x)))
                (isf: isweq _ _ f)
                (isfm: forall x:X, isweq _ _ (fm x))
        : isweq _ _ (bandfmap _ _ _ P Q fm).
Proof.
  intros.
  set (f1:= totalfun _ P _ fm).
  set (is1:= isweqfibtototal X P (fun x:X => Q (f x)) fm isfm).
  set (f2:= fpmap _ _ f Q).
  set (is2:= isweqfpmap _ _ f Q isf).
  assert (h: forall xp, paths _ (f2 (f1 xp)) (bandfmap _ _ f P Q fm xp)).
   intros [x p].
   apply idpath.
  apply (isweqhomot _ _ _ _ h (twooutof3c _ _ _ f1 f2 is1 is2)).
Defined.

(** ** Homotopy fiber products. *)


Definition hfp {X X' Y:UU} (f:X -> Y) (f':X' -> Y):= total2 X (fun x:X => hfiber _ _ f' (f x)).
Definition hfppair {X X' Y:UU} (f:X -> Y) (f':X' -> Y):= tpair X (fun x:X => hfiber _ _ f' (f x)).
Definition hfppr1 {X X' Y:UU} (f:X -> Y) (f':X' -> Y):= pr21 X (fun x:X => hfiber _ _ f' (f x)).






(** ** Direct products, pairwise coproducts and weak equivalences. *)



(** *** Weak equivalences and pairwise direct products. *)

Corollary isweqdirprodf (X Y X' Y':UU)(f:X-> Y)(f':X' -> Y') : isweq _ _ f -> isweq _ _ f' -> isweq _ _ (dirprodf _ _ _ _ f f').
Proof.
  intros ? ? ? ? ? ? is is'.
  apply (isweqbandfmap _ _ f (constfun X') (constfun Y') (constfun f') is (constfun is')).
Defined. 


Definition weqdirprodf (X Y X' Y':UU) : weq X Y -> weq X' Y' -> weq (dirprod X X') (dirprod Y Y').
Proof.
  intros ? ? ? ? [ t x ] [ t0 x0 ].
  split with (dirprodf _ _ _ _ t t0).
  apply isweqdirprodf.
   apply x.
  apply x0.
Defined. 

Definition weqtodirprodwithunit (X:UU): weq X (dirprod X unit).
Proof.
  intros.
  set (f:=fun x:X => dirprodpair x tt).
  split with f.
  set (g:= fun xu:dirprod X unit => pr21 _ _ xu).
  apply (gradth _ _ f g).
   intro x.
   apply idpath.
  intros [ t [] ].
  apply idpath.
Defined.


(** *** Basics on pairwise coproducts (disjoint unions).  *)



Inductive coprod (X Y:UU) :UU := ii1: X -> coprod X Y | ii2: Y -> coprod X Y.

(* we use "decidable" instead of "coprod" now for clarity, if the word fits *)
Inductive decidable (X:UU) :UU := yes : X -> decidable X | no : neg X -> decidable X.

Definition tocoprod (X:UU)(d : decidable X) : coprod X (neg X).
Proof.
  intros.
  induction d.
  apply ii1; assumption.
  apply ii2; assumption.
Defined.


Definition sumofmaps {X Y Z:UU}(fx: X -> Z)(fy: Y -> Z): (coprod X Y) -> Z := fun xy:_ => match xy with ii1 x => fx x | ii2 y => fy y end.


Definition boolascoprod: weq (coprod unit unit) bool.
Proof.
  set (f:= fun xx: coprod unit unit => match xx with ii1 _ => true | ii2 _ => false end).
  set (g:= fun t => match t with true => ii1 _ _ tt | false => ii2 _ _ tt end).
  split with f.
  apply (gradth _ _ f g).
   intros [[]|[]]; apply idpath.
  intros [|]; apply idpath.
Defined.  

Definition coprodasstor (X Y Z:UU): coprod (coprod X Y) Z -> coprod X (coprod Y Z).
Proof.
  intros ? ? ? [[x|y]|z].
  apply ii1; exact x.
  apply ii2, ii1; exact y.
  apply ii2, ii2; exact z.
Defined.

Definition coprodasstol (X Y Z: UU): coprod X (coprod Y Z) -> coprod (coprod X Y) Z.
Proof.
  intros X Y Z [x|[y|z]].
  apply ii1, ii1; exact x.
  apply ii1, ii2; exact y.
  apply ii2; exact z.
Defined.

Theorem isweqcoprodasstor (X Y Z:UU): isweq _ _ (coprodasstor X Y Z).
Proof.
  intros.
  apply (gradth _ _ (coprodasstor X Y Z) (coprodasstol X Y Z)).
  intros [[x|y]|z]; apply idpath.
  intros [x|[y|z]]; apply idpath.
Defined. 

Corollary isweqcoprodasstol (X Y Z:UU): isweq _ _ (coprodasstol X Y Z).
Proof. intros. apply (isweqinvmap _ _ _ (isweqcoprodasstor X Y Z)). Defined.

Definition weqcoprodasstor (X Y Z:UU):= weqpair _ (isweqcoprodasstor X Y Z).

Definition weqcoprodasstol (X Y Z:UU):= weqpair _ (isweqcoprodasstol X Y Z).

Definition coprodcomm (X Y:UU): coprod X Y -> coprod Y X := fun xy:_ => match xy with ii1 x => ii2 _ _ x | ii2 y => ii1 _ _ y end. 

Theorem isweqcoprodcomm (X Y:UU): isweq _ _ (coprodcomm X Y).
Proof.
  intros.
  apply (gradth _ _ (coprodcomm X Y) (coprodcomm Y X) ).
  intros [x|y]; apply idpath.
  intros [y|x]; apply idpath.
Defined. 

Definition weqcoprodcomm (X Y:UU):= weqpair _ (isweqcoprodcomm X Y).

Theorem isweqcoprodwithempty (X Y:UU): neg Y -> isweq _ _ (ii1 X Y).
Proof.
  intros ? ? nf.
  apply (gradth _ _ (ii1 X Y) (fun xy => match xy with ii1 x => x | ii2 y => initmap _ (nf y) end) ).
  intro x.
  apply idpath.
  intros [x|y].
  apply idpath.
  apply (initmap _ (nf y)).
Defined.  



Theorem isweqfromcoprodwithempty (X:UU): isweq _ _ (fun ex: coprod empty X => match ex with ii1 e => initmap _ e | ii2 x => x end).
Proof.
  intros X.
  apply (gradth _ _ (fun ex => match ex with ii1 e => initmap _ e | ii2 x => x end)
                    (ii2 empty X)).
  intros [[]|x]. apply idpath.
  intro y. apply idpath.
Defined.

Definition weqfromcoprodwithempty (X:UU):= weqpair _ (isweqfromcoprodwithempty X). 


Definition coprodf (X Y:UU)(X' Y':UU)(f: X -> X')(g: Y-> Y'): coprod X Y -> coprod X' Y' := fun xy: coprod X Y =>
match xy with
ii1 x => ii1 _ _ (f x)|
ii2 y => ii2 _ _ (g y)
end. 


Theorem isweqcoprodf (X Y:UU)(X' Y':UU)(f: X -> X')(g: Y-> Y') : isweq _ _ f -> isweq _ _ g -> isweq _ _ (coprodf _ _ _ _ f g).
Proof.
  intros ? ? ? ? ? ? isf isg.
  apply (gradth _ _ (coprodf _ _ _ _ f g) (coprodf _ _ _ _ (invmap _ _ f isf) (invmap _ _ g isg))).
  intros [x|y].
   apply (maponpaths _ _ (ii1 X Y) _ _ (weqgf _ _ _ isf x)).
   apply (maponpaths _ _ (ii2 X Y) _ _ (weqgf _ _ _ isg y)).
  intros [x'|y'].
   apply (maponpaths _ _ (ii1 X' Y') _ _ (weqfg _ _ _ isf x')).
   apply (maponpaths _ _ (ii2 X' Y') _ _ (weqfg _ _ _ isg y')).
Defined. 



Definition weqcoprodf (X Y X' Y' :UU) : weq X Y -> weq X' Y' -> weq (coprod X X') (coprod Y Y').
Proof.
  intros ? ? ? ? [ t x ] [ t0 x0 ].
  split with (coprodf _ _ _ _ t t0).
  apply isweqcoprodf; assumption.
Defined.


Lemma negpathsii1ii2 (X Y:UU)(x:X)(y:Y): neg (paths _ (ii1 _ _ x) (ii2 _ _ y)).
Proof. intros. intro X0. set (dist:= fun xy: coprod X Y => match xy with ii1 x => unit | ii2 y => empty end). apply (transportf _ dist _ _ X0 tt). Defined.

Lemma negpathsii2ii1  (X Y:UU)(x:X)(y:Y): neg (paths _ (ii2 _ _ y) (ii1 _ _ x)).
Proof. intros. intro X0. set (dist:= fun xy: coprod X Y => match xy with ii1 x => empty | ii2 y => unit end). apply (transportf _ dist _ _ X0 tt). Defined.










(** *** Coproducts and direct products. *)


Definition rdistrtocoprod (X Y Z:UU): dirprod X (coprod Y Z) -> coprod (dirprod X Y) (dirprod X Z).
Proof. intros X Y Z X0. destruct X0 as [ t x ].  destruct x.   apply (ii1 _ _ (dirprodpair t y)). apply (ii2 _ _ (dirprodpair t z)). Defined.


Definition rdistrtoprod (X Y Z:UU): coprod (dirprod X Y) (dirprod X Z) ->  dirprod X (coprod Y Z).
Proof. intros X Y Z X0. destruct X0 as [ d | d ].  destruct d as [ t x ]. apply (dirprodpair t (ii1 _ _ x)). destruct d as [ t x ]. apply (dirprodpair t (ii2 _ _ x)). Defined. 


Theorem isweqrdistrtoprod (X Y Z:UU): isweq _ _ (rdistrtoprod X Y Z).
Proof. intros. set (f:= rdistrtoprod X Y Z). set (g:= rdistrtocoprod X Y Z). 
assert (egf: forall a:_, paths _ (g (f a)) a).  intro. destruct a. destruct d. apply idpath. destruct d. apply idpath. 
assert (efg: forall a:_, paths _ (f (g a)) a). intro. destruct a as [ t x ]. destruct x.  apply idpath. apply idpath.
apply (gradth _ _ f g egf efg). Defined.


Corollary isweqrdistrtocoprod (X Y Z:UU): isweq _ _ (rdistrtocoprod X Y Z).
Proof. intros. apply (isweqinvmap _ _ _ (isweqrdistrtoprod X Y Z)). Defined.

Definition weqrdistrtoprod (X Y Z: UU):= weqpair _ (isweqrdistrtoprod X Y Z).

Definition weqrdistrtocoprod (X Y Z: UU):= weqpair _ (isweqrdistrtocoprod X Y Z).
 




(** ** Extentionality axioms. 

Summary: We consider two axioms which address functional extensionality. The first one is etacorrection  which compensates for the absense of eta-reduction in Coq8.3 Eta-reduction is expected to be included as a  basic property of the language in Coq8.4 which will make this axiom and related lemmas unnecessary. The second axiom funcontr is the functional extensionality for dependent functions formulated as the condition that the space of section of a family with contractible fibers is contractible. We will show in .... that it follows from the univalence axiom applied on a higher universe level. *)


(** *** Axioms and their basic corollaries. *)

(** etacorrection *)

Axiom etacorrection: forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths _ f (fun t:T => f t). 

Lemma isweqetacorrection (T:UU)(P:T -> UU): isweq _ _ (fun f: forall t, P t => fun t => f t).
Proof. 
  intros.
  exact ( isweqhomot _ _ (fun f => f) (fun f t => f t) (fun f => etacorrection _ P f) (idisweq _) ).
Defined. 

Lemma etacorrectiononpaths (T:UU)(P:T->UU)(s1:forall t:T, P t)(s2:forall t:T, P t): paths _ (fun t:T => s1 t) (fun t:T => s2 t)-> paths _ s1 s2. 
Proof. intros T P s1 s2 X. set (ec:= fun s:forall t:T, P t => (fun t:T => s t)). set (is:=isweqetacorrection T P). apply (pathsweq2 _ _ ec is s1 s2 X). Defined. 

Definition etacor (X:UU)(Y:UU)(f:X -> Y):paths _ f (fun x:X => f x) := etacorrection X (fun T:X => Y) f.

Lemma etacoronpaths (X:UU)(Y:UU)(f1:X->Y)(f2:X->Y):paths _ (fun x:X => f1 x) (fun x:X => f2 x) -> paths _ f1 f2. 
Proof. intros X Y f1 f2 X0. set (ec:= fun f:X->Y => (fun x:X => f x)). set (is:=isweqetacorrection X (fun x:X => Y)). apply (pathsweq2 _ _ ec is f1 f2 X0). Defined.


(** Dependent functions and sections up to homotopy I *)


Definition toforallpaths (T:UU) (P:T -> UU) (f:forall t:T, P t)( g: forall t:T, P t): (paths _ f g) -> (forall t:T, paths _ (f t) (g t)).
Proof. intros T P f g X t. destruct X. apply (idpath _ (f t)). Defined. 


Definition sectohfiber (X:UU)(P:X -> UU): (forall x:X, P x) -> (hfiber (X -> total2 X P) (X -> X) (fun f:_ => fun x:_ => pr21 _ _ (f x)) (fun x:X => x)) := (fun a:forall x:X, P x => tpair _ _ (fun x:_ => tpair _ _ x (a x)) (idpath _ (fun x:X => x))).

Definition hfibertosec  (X:UU)(P:X -> UU):  (hfiber (X -> total2 X P) (X -> X) (fun f:_ => fun x:_ => pr21 _ _ (f x)) (fun x:X => x)) -> (forall x:X, P x):= fun se:_  => fun x:X => match se as se' return P x with tpair s e => (transportf X P (pr21 _ _(s x)) x (toforallpaths X (fun x:X => X)  (fun x:X => pr21 X P (s x)) (fun x:X => x) e x) (pr22 _ _ (s x))) end.

Definition sectohfibertosec (X:UU)(P:X -> UU): forall a: forall x:X, P x, paths _ (hfibertosec _ _ (sectohfiber _ _ a)) a := fun a:_ => (pathsinv0 _ _ (etacorrection _ _ a)).



(** Deduction of functional extnsionality for dependent functions (sections) from functional extensionality of usual functions *)

Axiom funextfunax : forall (X Y:UU)(f g:X->Y),  (forall x:X, paths _ (f x) (g x)) -> (paths _ f g). 

Lemma isweqlcompwithweq (X X':UU)(w: weq X X')(Y:UU): isweq (X' -> Y) (X -> Y) (fun a:X'->Y => (fun x:X => a (w x))).
Proof. intros. set (f:= (fun a:X'->Y => (fun x:X => a (w x)))). set (g := fun b:X-> Y => fun x':X' => b (weqinv w x')). 
set (egf:= (fun a:X'->Y => funextfunax X' Y (fun x':X' => (g (f a)) x') a (fun x': X' =>  maponpaths _ _ a _ _ (weqfg _ _ _ (pr22 _ _ w) x')))).
set (efg:= (fun a:X->Y => funextfunax X Y (fun x:X => (f (g a)) x) a (fun x: X =>  maponpaths _ _ a _ _ (weqgf _ _ _ (pr22 _ _ w) x)))). 
apply (gradth _ _ f g egf efg). Defined.

Lemma isweqrcompwithweq (Y Y':UU)(w: weq Y Y')(X:UU): isweq (X -> Y) (X -> Y') (fun a:X->Y => (fun x:X => w (a x))).
Proof. intros. set (f:= (fun a:X->Y => (fun x:X => w (a x)))). set (g := fun a':X-> Y' => fun x:X => (weqinv w (a' x))). 
set (egf:= (fun a:X->Y => funextfunax X Y (fun x:X => (g (f a)) x) a (fun x: X => (weqgf _ _ _ (pr22 _ _ w) (a x))))).
set (efg:= (fun a':X->Y' => funextfunax X Y' (fun x:X => (f (g a')) x) a' (fun x: X =>  (weqfg _ _ _ (pr22 _ _ w) (a' x))))). 
apply (gradth _ _ f g egf efg). Defined.

(** Theorem saying that if each member of a family is contractible then the space of sections of the family is contractible. *)

Theorem funcontr (X:UU)(P:X -> UU) : (forall x:X, iscontr (P x)) -> iscontr (forall x:X, P x).
Proof.
  intros X P IS.
  set (p := pr21 X P).
  assert (is1: isweq _ _ p).
    apply isweqpr21.
    exact IS.
  assert (X1: iscontr (hfiber _ _ (fun f x => p (f x)) (idfun X))).
    set (w1 := weqpair p is1).
    apply (isweqrcompwithweq _ _ w1 X (idfun X)).
  apply (contrl1' _ _ _ _ (sectohfibertosec X P) X1).
Defined. 

Corollary funcontrtwice (X:UU)(P: X-> X -> UU)(is: forall (x x':X), iscontr (P x x')): iscontr (forall (x x':X), P x x').
Proof. intros. 
assert (is1: forall x:X, iscontr (forall x':X, P x x')). intros. apply (funcontr _ _ (is x)). apply (funcontr _ _ is1). Defined. 


(** Proof of the fact that the [ toforallpaths ] from [paths _ s1 s2] to [forall t:T, paths _ (s1 t) (s2 t)] is a weak equivalence - a strong form 
of functional extensionality for sections of general families. The proof uses only [funcontr] which is an axiom i.e. its type is in [ hProp ]. *)


Lemma funextweql1 (T:UU)(P:T -> UU)(g: forall t:T, P t): iscontr (total2 _ (fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t))).
Proof.
  intros.
  set (X:= forall t:T, coconustot (P t) (g t)).
  assert (is1: iscontr X).
    apply (funcontr  _ (fun t:T => coconustot (P t) (g t)) (fun t:T => iscontrcoconustot (P t) (g t))).
  set (E:= fun f:forall t:T, P t => forall t:T, paths _ (f t) (g t)).
  set (R:= total2 _ E).
  set (p:= fun z: X => tpair _ 
              (fun f:forall t, P t => forall t, paths _ (f t) (g t))
              (fun t => pr21 _ _ (z t))
              (fun t => pr22 _ _ (z t))).
  set (s:= fun u:R => (fun t => coconustotpair _ _ ((pr21 _ _ u) t) ((pr22 _ _ u) t))).
  set (etap:= fun u: R => tpair _ E (fun t => ((pr21 _ _ u) t)) (pr22 _ _ u)).
  assert (eps: forall u:R, paths _ (p (s u)) (etap u)).
    intro.
    destruct u as [ t x ].
    unfold p, s, etap.
    simpl.
    induction (etacorrection _ _ x).
    apply idpath.
  apply (contrl1' _ _ p s).
    intro u.
    apply (pathscomp0 _ _ _ _ (eps u)).
      unfold etap.
      destruct u as [t x ].
      simpl.
      set (ff:= fun fe: R => tpair _ E (fun t0:T => (pr21 _ _ fe) t0) (pr22 _ _ fe)).
      assert (ee: forall fe: R, paths _ (ff (ff fe)) (ff fe)).
        intro.
        apply idpath.
      assert (eee: forall fe: R, paths _ (ff  fe) fe).
        intro fe.
        apply (pathsweq2 _ _ ff).
          apply (isweqfpmap _ _ _ E (isweqetacorrection _ P)).
        apply ee.
      apply (eee (tpair _ _ t x)).
  assumption.
Defined. 

Theorem isweqtoforallpaths(T:UU)(P:T -> UU)(f g: forall t:T, P t): isweq _ _ (toforallpaths T P f g). 
Proof.
  intros.
  set (tmap:= fun ff: total2 _ (fun f0: forall t, P t, paths _ f0 g)
                => tpair _ (fun f0:forall t, P t => forall t, paths _ (f0 t) (g t))
                           (pr21 _ _ ff)
                           (toforallpaths _ P (pr21 _ _ ff) g (pr22 _ _ ff))).
  assert (is1: iscontr (total2 _ (fun f0: forall t, P t, paths _ f0 g))).
  apply (iscontrcoconustot _ g).
  assert (is2:iscontr (total2 _ (fun f0:forall t, P t => forall t, paths _ (f0 t) (g t)))).
  apply funextweql1.
  assert (X: isweq _ _ tmap).
  apply (ifcontrcontrthenweq _ _ tmap is1 is2).
  apply (isweqtotaltofib _ _
             (fun f0:forall t, P t => forall t, paths _ (f0 t) (g t))
             (fun f0:forall t, P t => (toforallpaths _ P f0 g))
             X
             f).
Defined. 


Definition funextsec (T:UU) (P: T-> UU) (s1: forall t:T, P t)(s2: forall t:T, P t): (forall t:T, paths _ (s1 t) (s2 t)) -> paths _ s1 s2 := invmap _ _ (toforallpaths _ _ s1 s2) (isweqtoforallpaths _ _ s1 s2).

Definition funextfun (X Y:UU)(f g:X->Y) : (forall x:X, paths _ (f x) (g x)) -> (paths _ f g):= funextsec X (fun x:X => Y) f g.

(** I do not know at the moment whether [funextfun] is equal (homotopic) to [funextfunax]. It is advisable in all cases to use [funextfun] or, equivalently, [funextsec], since it can be produced from [funcontr] and therefore is well defined up to a canonbical equivalence.  In addition it is a homotopy inverse of [toforallpaths] which may be true or not for [funextsecax]. *) 

Theorem isweqfunextsec(T:UU)(P:T -> UU)(f: forall t:T, P t) (g: forall t:T, P t): isweq _ _ (funextsec T P f g).
Proof. intros. apply (isweqinvmap _ _ (toforallpaths _ _ f g) (isweqtoforallpaths _ _ f g)). Defined. 


Theorem weqfunextsec (T:UU)(P:T -> UU)(f: forall t:T, P t) (g: forall t:T, P t): weq  (paths _ f g) (forall t:T, paths _ (f t) (g t)).
Proof. intros. split with (toforallpaths T P f g). apply isweqtoforallpaths. Defined. 








(** ** Sections of "double fibration" [(P: T -> UU)(PP: forall t:T, P t -> UU)] and pairs of sections. *)

Definition totaltoforall (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) -> forall x:X, total2 (P x) (PP x).
Proof. intros X P PP X0 x. induction X0 as [ t x0 ]. split with (t x). apply (x0 x). Defined.


Definition foralltototal  (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU):  (forall x:X, total2 (P x) (PP x)) -> total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)).
Proof. intros X P PP X0. split with (fun x:X => pr21 _ _ (X0 x)). apply (fun x:X => pr22 _ _ (X0 x)). Defined.

Lemma lemmaeta1 (X:UU)(P:X->UU)(Q:(forall x:X, P x) -> UU)(s0: forall x:X, P x)(q: Q (fun x:X => (s0 x))): paths _ (tpair _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) s0 q) (tpair _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) (fun x:X => (s0 x)) q). 
Proof. intros. set (ff:= fun tp:total2 _ (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) => tpair _ _ (fun x:X => pr21 _ _ tp x) (pr22 _ _ tp)). assert (X0 : isweq _ _ ff).  apply (isweqfpmap _ _ (fun s: forall x:X, P x => (fun x:X => (s x))) Q (isweqetacorrection X P)). assert (ee: paths _ (ff (tpair (forall x : X, P x)
        (fun s : forall x : X, P x => Q (fun x : X => s x)) s0 q)) (ff (tpair (forall x : X, P x)
        (fun s : forall x : X, P x => Q (fun x : X => s x))
        (fun x : X => s0 x) q))). apply idpath. 

apply (pathsweq2 _ _ ff X0 _ _ ee). Defined. 



Definition totaltoforalltototal(X:UU)(P:X->UU)(PP:forall x:X, P x -> UU)(ss:total2 (forall x: X, P x) (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) ): paths _ (foralltototal _ _ _ (totaltoforall _ _ _ ss)) ss.
Proof. intros.  destruct ss as [ t x ]. unfold foralltototal. unfold totaltoforall.  simpl. 
set (et:= fun x:X => t x). 

assert (paths _ (tpair (forall x0 : X, P x0) (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) t x) 
(tpair (forall x0 : X, P x0) (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et x)). apply (lemmaeta1 X P (fun s: forall x:X, P x =>  forall x:X, PP x (s x)) t x).  

assert (ee: paths _ 
     (tpair (forall x0 : X, P x0)
        (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et
        x)
     (tpair (forall x0 : X, P x0)
        (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et (fun x0 : X => x x0))). assert (eee: paths _ x (fun x0:X => x x0)). apply etacorrection. induction eee. apply idpath. induction ee. apply pathsinv0. assumption. Defined. 



Definition foralltototaltoforall(X:UU)(P:X->UU)(PP:forall x:X, P x -> UU)(ss: forall x:X, total2 (P x) (PP x)): paths _ (totaltoforall _ _ _ (foralltototal _ _ _ ss)) ss.
Proof. intros. unfold foralltototal. unfold totaltoforall.  simpl. assert (ee: forall x:X, paths _ (tpair (P x) (PP x) (pr21 (P x) (PP x) (ss x)) (pr22 (P x) (PP x) (ss x))) (ss x)).  intro. apply (pathsinv0 _ _ (tppr (P x) (PP x) (ss x))).  apply (funextsec). assumption. Defined.

Theorem isweqforalltototal (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): isweq _ _ (foralltototal X P PP).
Proof. intros.  apply (gradth _ _ (foralltototal X P PP) (totaltoforall X P PP) (foralltototaltoforall  X P PP) (totaltoforalltototal X P PP)). Defined. 

Theorem isweqtotaltoforall (X:UU)(P:X->UU)(PP:forall x:X, P x -> UU): isweq _ _ (totaltoforall X P PP).
Proof. intros.  apply (gradth _ _  (totaltoforall X P PP) (foralltototal X P PP)  (totaltoforalltototal X P PP) (foralltototaltoforall  X P PP)). Defined. 




(** ** Homotopy fibers of the map [forall x:X, P x -> forall x:X, Q x]. *) 



Definition maponsec (X:UU)(P:X -> UU)(Q:X-> UU)(f: forall x:X, P x -> Q x): (forall x:X, P x) -> (forall x:X, Q x) := 
fun s: forall x:X, P x => (fun x:X => (f x) (s x)).

Definition maponsec1 (X:UU)(Y:UU)(P:Y -> UU)(f:X-> Y): (forall y:Y, P y) -> (forall x:X, P (f x)) := fun sy: forall y:Y, P y => (fun x:X => sy (f x)).



Definition hfibertoforall (X:UU)(P:X -> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): hfiber _ _ (maponsec _ _ _ f) s -> forall x:X, hfiber _ _ (f x) (s x).
Proof. intro. intro. intro. intro. intro.  unfold hfiber. 

set (map1:= totalfun (forall x : X, P x) (fun pointover : forall x : X, P x =>
      paths _ (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => toforallpaths _ _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall X P (fun x:X => (fun pointover : P x => paths _ (f x pointover) (s x)))).  

set (themap := fun a:_ => map2 (map1 a)). assumption. Defined. 



Definition foralltohfiber  (X:UU)(P:X -> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): (forall x:X, hfiber _ _ (f x) (s x)) -> hfiber _ _ (maponsec _ _ _ f) s.
Proof.  intro. intro. intro. intro.   intro. unfold hfiber. 

set (map2inv := foralltototal X P (fun x:X => (fun pointover : P x => paths _ (f x pointover) (s x)))).
set (map1inv :=  totalfun (forall x : X, P x)  (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths _ (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _ _ (fun x : X => f x (pointover x)) s)).
set (themap := fun a:_=> map1inv (map2inv a)). assumption. Defined. 


Theorem isweqhfibertoforall  (X:UU)(P:X -> UU)(Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq _ _ (hfibertoforall _ _ _ f s).
Proof. intro. intro. intro. intro. intro. 

set (map1:= totalfun (forall x : X, P x) (fun pointover : forall x : X, P x =>
      paths _ (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths _  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => toforallpaths _ _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall X P (fun x:X => (fun pointover : P x => paths _ (f x pointover) (s x)))).  

assert (is1: isweq _ _ map1). apply (isweqfibtototal _ _ _ (fun pointover: forall x:X, P x => toforallpaths _ _ (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => (isweqtoforallpaths _ _ (fun x : X => f x (pointover x)) s))).

assert (is2: isweq _ _ map2). apply isweqtotaltoforall.

apply (twooutof3c _ _ _ map1 map2 is1 is2). Defined.


Theorem isweqforalltohfiber  (X:UU)(P Q:X -> UU)(f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq _ _ (foralltohfiber _ _ _ f s).
Proof.
  intros X P Q f s.
  apply twooutof3c.
    apply isweqforalltototal.
  apply isweqfibtototal.
  intro.
  apply isweqfunextsec.
Defined. 


(** *** The map between section spaces (dependent products) defined by a family of maps [ P x -> Q x ] is a weak equivalence if all maps [ P x -> Q x ] are weak equivalences. *)




Corollary isweqmaponsec (X:UU)(P Q:X->UU)(f: forall x:X, P x -> Q x) : (forall x:X, isweq _ _ (f x)) -> isweq _ _ (maponsec _ _ _ f). 
Proof.
  unfold isweq.
  intros X P Q f isx q.
  apply (iscontrxifiscontry _ _ _ (isweqhfibertoforall _ _ _ f q)).
  apply funcontr.
  intro.
  apply isx.
Defined. 


(** ** The map between section spaces (dependent products) defined by the map between the bases [ f: Y -> X ]. *)




Definition maponsec1l0 (X:UU)(P:X -> UU)(f:X-> X)(h: forall x:X, paths _ (f x) x)(s: forall x:X, P x): (forall x:X, P x) := (fun x:X => transportf X P _ _ (h x) (s (f x))).

Lemma maponsec1l1  (X:UU)(P:X -> UU)(x:X)(s:forall x:X, P x): paths _ (maponsec1l0 _ P (fun x:X => x) (fun x:X => idpath _ x) s x) (s x). 
Proof. intros. unfold maponsec1l0.   apply idpath. Defined. 


Lemma maponsec1l2 (X:UU)(P:X -> UU)(f:X-> X)(h: forall x:X, paths _ (f x) x)(s: forall x:X, P x)(x:X): paths _ (maponsec1l0 _ P f h s x) (s x).
Proof. intro. intro. intro. intro. intros.  

set (map:= fun ff: total2 (X->X) (fun f0:X->X => forall x:X, paths _ (f0 x) x) => maponsec1l0 X P (pr21 _ _ ff) (pr22 _ _ ff) s x).
assert (is1: iscontr (total2 (X->X) (fun f0:X->X => forall x:X, paths _ (f0 x) x))). apply funextweql1. assert (e: paths _ (tpair _  (fun f0:X->X => forall x:X, paths _ (f0 x) x) f h) (tpair _  (fun f0:X->X => forall x:X, paths _ (f0 x) x) (fun x0:X => x0) (fun x0:X => idpath _ x0))). apply contrl2.  assumption.  apply (maponpaths _ _ map _ _ e). Defined. 


Theorem isweqmaponsec1 (X:UU)(Y:UU)(P:Y -> UU)(f:X-> Y) : isweq _ _ f -> isweq _ _ (maponsec1 _ _ P f).
Proof.
 intros X Y P f is.
 set (map:= maponsec1 _ _ P f).
 set (invf:= invmap _ _ f is).
 set (e1:= weqfg _ _ f is).
 set (e2:= weqgf _ _ f is).
 set (im1:= fun sx: forall x:X, P (f x) => (fun y:Y => sx (invf y))).
 set (im2:= fun sy': forall y:Y, P (f (invf y)) => (fun y:Y => transportf _ _ _ _ (weqfg _ _ _ is y) (sy' y))).
 set (invmapp := fun sx: forall x:X, P (f x) => im2 (im1 sx)).
 assert (efg0: forall sx: (forall x:X, P (f x)), forall x:X, paths _ ((map (invmapp sx)) x) (sx x)).
  intros sx x.
  simpl.
  set (ee:=e2 x).
  fold invf in ee.
  set (e3x:= fun x0:X => pathsweq2 _ _ f is (invf (f x0)) x0 (weqfg X Y f is (f x0))).
  set (e3:=e3x x).
  assert (e5:paths _ (transportf _ _ (f (invf (f x))) (f x) (weqfg _ _ f is (f x)) (sx (invf (f x))))
                     (transportf _ _ (f (invf (f x))) (f x) (maponpaths _ _ f _ _ e3) (sx (invf (f x))))).
   apply (maponpaths _ _ (fun e40:_ => (transportf _ _ (f (invf (f x))) (f x) e40 (sx (invf (f x)))))).
   apply (pathsinv0 _ _ (pathsweq4 _ _ f is (invf (f x)) x _)).
  assert (e6: paths _ (transportf _ _ (f (invf (f x))) (f x) (maponpaths _ _ f (invf (f x)) x e3) (sx (invf (f x))))
                      (transportf _ (compose P f) _ _ e3 (sx (invf (f x))))).
   apply (pathsinv0 _ _ (functtransportf _ _ f P _ _ e3 (sx (invf (f x))))).
  apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e5 e6)).
  apply (maponsec1l2 _ (compose P f) (compose invf f) e3x).
 apply (gradth _ _ map invmapp).
  intro. apply funextsec.
  intros. apply (maponsec1l2 _ _ (compose f invf)).
 intro. apply funextsec, efg0.
Defined. 


(** ** Basics about h-levels. *)



(** *** h-levels of types. *)


Fixpoint isofhlevel (n:nat) (X:UU): UU:=
    match n with
        O => iscontr X |
        S m => forall x x':X, isofhlevel m (paths _ x x')
    end.

Definition isaprop (X:UU): UU := isofhlevel 1 X. 

Definition isaset (X:UU): UU := isofhlevel 2 X. 

Theorem hlevelretract (n:nat)(X Y:UU)(p:X -> Y)(s:Y ->X)(eps: forall y:Y, paths _  (p (s y)) y): isofhlevel n X -> isofhlevel n Y.
Proof.
  intro n.
  induction n.
   intros X Y p s eps X0.
   apply (contrl1' _ _ p s); assumption.
  intros X Y p s eps Xn1 x x'.
  set (s':= maponpaths _ _ s x x').
  set (p':= pathssec2 _ _ s p eps x x').
  apply (IHn _ _ p' s').
   apply pathssec3.
  apply Xn1.
Defined. 

Corollary  isofhlevelweqf (n:nat)(X Y:UU)(f:X -> Y)(is: isweq _ _ f): isofhlevel n X -> isofhlevel n Y.
Proof. intros.  apply (hlevelretract n _ _ f (invmap _ _ f is) (weqfg _ _ f is)). assumption. Defined. 

Corollary  isofhlevelweqb (n:nat)(X Y:UU)(f:X -> Y)(is: isweq _ _ f): isofhlevel n Y -> isofhlevel n X.
Proof. intros.  apply (hlevelretract n _ _ (invmap _ _ f is) f (weqgf _ _ f is)). assumption. Defined. 

Lemma isofhlevelsn (n:nat)(X:UU) : (X -> isofhlevel (S n) X) -> isofhlevel (S n) X.
Proof. intros n X X0.  simpl.  intros.  apply (X0 x'). Defined.


Lemma isofhlevelssn (n:nat)(X:UU): (forall x:X, isofhlevel (S n) (paths _ x x)) -> isofhlevel (S (S n)) X.
Proof. intros n X X0. simpl.  intro. intro.  change (forall (x0 x'0 : paths _ x x'), isofhlevel n (paths _ x0 x'0) ) with (isofhlevel (S n) (paths _ x x')). 
assert (X1: paths _ x x' -> (isofhlevel (S n) (paths _ x x'))). intro X2. destruct X2. apply (X0 x). apply  (isofhlevelsn n _ X1). Defined. 


Theorem isapropunit: isofhlevel 1 unit.
Proof. unfold isofhlevel. intros. 
assert (c:paths _ x x'). induction x. induction x'. apply idpath.
assert (X: forall g:paths _ x x', paths _ g c). intros. assert (e:paths _ c c).   apply idpath. induction c. induction x. apply unitl3. apply (iscontrpair _ c X). Defined.  



Theorem isapropifcontr (X:UU): iscontr X -> isofhlevel 1 X.
Proof.
   intros. set (f:= terminalmap X). assert (is: isweq _ _ f). 
   apply isweqcontrtounit.  assumption. 
   apply (isofhlevelweqb 1 _ _ f is).  apply isapropunit. Defined. 

Theorem hlevelsincl (n:nat) (T:UU) : isofhlevel n T -> isofhlevel (S n) T.
Proof. intro.
  induction n.
  intro. apply (isapropifcontr T).
  intro.  intro.
  change (forall t1 t2:T, isofhlevel (S n) (paths _ t1 t2)).
  intros.
  change (forall t1 t2 : T, isofhlevel n (paths _ t1 t2)) in X.
  apply IHn, X.
Defined.

Corollary isofhlevelcontr (n:nat)(X:UU): iscontr X -> isofhlevel n X.
Proof.
  intro. induction n. intros. assumption. 
  intros. simpl. intros. assert (iscontr (paths _ x x')). apply isapropifcontr, X0. apply IHn; assumption.
Defined.

Corollary isofhlevelsnprop (n:nat)(X:UU): isaprop X -> isofhlevel (S n) X.
Proof. intros n X X0. simpl. unfold isaprop in X0.  simpl in X0. intros. apply isofhlevelcontr. apply (X0 x x'). Defined. 

Lemma iscontraprop1 (X:UU): isofhlevel 1 X -> X -> iscontr X.
Proof. intros X X0 X1. unfold iscontr. split with X1. intro.  unfold isofhlevel in X0.  set (is:= X0 t X1). apply (pr21 _ _ is). 
Defined. 

Lemma iscontraprop1inv (X:UU): (X -> iscontr X) -> (isofhlevel 1 X).
Proof. intros. assert (X -> isofhlevel 1 X). intro.  apply (hlevelsincl O _ (X0 X1)). apply (isofhlevelsn O _ X1). Defined.


(** *** h-levels of functions *)


Definition isofhlevelf (n:nat)(X:UU)(Y:UU)(f:X -> Y): UU := forall y:Y, isofhlevel n (hfiber _ _ f y).


Lemma isofhlevelfweq (n:nat)(X Y:UU)(f:X -> Y): isweq _ _ f -> isofhlevelf n _ _ f.
Proof. intros n X Y f X0.  unfold isofhlevelf. intro.  apply (isofhlevelcontr n). apply (X0 y). Defined.

Theorem isofhlevelfpmap (n:nat)(X Y:UU)(f:X -> Y)(Q:Y -> UU): isofhlevelf n _ _ f -> isofhlevelf n _ _ (fpmap _ _ f Q).
Proof. intros n X Y f Q X0. unfold isofhlevelf. unfold isofhlevelf in X0.  intro. set (yy:= pr21 _ _ y). set (g:= hfiberfpmap _ _ f Q y). set (is:= isweqhfiberfp _ _ f Q y). set (isy:= X0 yy).  apply (isofhlevelweqb n _ _ _ is isy). Defined. 



Theorem isofhlevelfpr21 (n:nat)(X:UU)(P:X -> UU)(is: forall x:X, isofhlevel n (P x)):isofhlevelf n _ _ (pr21 X P).
Proof. intros. unfold isofhlevelf. intro. rename y into x. apply (isofhlevelweqf n _ _ (fibmap1 _ _ x) (isweqfibmap1 _ _ x)  (is x)). Defined.


Theorem isofhlevelfhomot (n:nat)(X Y:UU)(f f':X -> Y)(h: forall x:X, paths _ (f x) (f' x)): isofhlevelf n _ _ f -> isofhlevelf n _ _ f'.
Proof. intros n X Y f f' h X0. unfold isofhlevelf. intro. 
set (ff:= (fun z:(hfiber _ _ f' y) =>
match z with 
(tpair x e) => hfiberpair _ _ f y x (pathscomp0 _ _ _ _ (h x) e)
end)). 

set (gg:= (fun z:(hfiber _ _ f y) =>
match z with
(tpair x e) => hfiberpair _ _ f' y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ (h x)) e)
end)). 

assert (egf: forall z:(hfiber _ _ f' y), paths _ (gg (ff z)) z). intros. destruct z as [ x e ]. 
apply (constr3 _ _ f' y x (pathscomp0 _ _ _ _ (pathsinv0 _ _ (h x)) (pathscomp0 _ _ _ _ (h x) e)) e (pathsinv1l _ (f x) (f' x) y (h x) e)).
apply (hlevelretract n _ _ gg ff egf (X0 y)). Defined.



Theorem isofhlevelfinfibseq (n:nat)(X Y:UU)(f:X-> Y): isofhlevel n X -> isofhlevel (S n) Y -> isofhlevelf n _ _ f.
Proof. intro. induction n.  intros X Y f X0 X1.
assert (is1: isofhlevel O Y). apply (iscontraprop1 Y X1 (f (pr21 _ _ X0))). apply (ifcontrcontrthenweq _ _ f X0 is1).

intros X Y f X0 X1.  unfold isofhlevelf. simpl.  
assert  (is1: forall x' x:X, isofhlevel n (paths _ x' x)). simpl in X0.  assumption.  
assert (is2: forall y' y:Y, isofhlevel (S n) (paths _ y' y)). simpl in X1.  simpl. assumption.
assert (is3: forall (y:Y)(x:X)(xe': hfiber _ _ f y), isofhlevelf n _ _ (d3f _ _ f y x xe')).  intros. apply (IHn _ _ (d3f _ _ f y x xe') (is1 (pr21 _ _ xe') x) (is2 (f x) y)). 
assert (is4: forall (y:Y)(x:X)(xe': hfiber _ _ f y)(e: paths _ (f x) y), isofhlevel n (paths _ (hfiberpair _ _ f y x e) xe')). intros.
apply (isofhlevelweqb n _ _ _ (isfibseq4 _ _ f y x xe' e) (is3 y x xe' e)).
intros. rename x into xe. rename x' into xe'. destruct xe as [ t x ]. apply (is4 y t xe' x). Defined.



Theorem isofhlevelinfibseq (n:nat)(X Y:UU)(f:X -> Y): isofhlevelf n _ _ f -> isofhlevel n Y -> isofhlevel n X.
Proof. intro. induction n.  intros X Y f X0 X1.  apply (iscontrxifiscontry _ _ f X0 X1). intros X Y f X0 X1. simpl.
assert (is1: forall (y:Y)(xe xe': hfiber _ _ f y), isofhlevel n (paths _ xe xe')). intros. apply (X0 y). 
assert (is2: forall (y:Y)(x:X)(xe': hfiber _ _ f y), isofhlevelf n _ _ (d3f _ _ f y x xe')). intros. unfold isofhlevel. intro.
apply (isofhlevelweqf n _ _ _ (isfibseq4 _ _ f y x xe' y0) (is1 y (hfiberpair _ _ f y x y0) xe')). 
assert (is3: forall (y' y : Y), isofhlevel n (paths _ y' y)). simpl in X1. assumption.
intros. rename x into x0. rename x' into x. rename x0 into x'.   
set (y:= f x').  set (e':= idpath _ y). set (xe':= hfiberpair _ _ f y x' e').
apply (IHn _ _ (d3f _ _ f y x xe') (is2 y x xe') (is3 (f x) y)). Defined. 



Theorem isofhlevelfd1f (n:nat)(X Y:UU)(f:X -> Y)(y:Y): (forall y':Y, isofhlevel n (paths _  y' y)) -> isofhlevelf n _ _ (d1f _ _ f y).
Proof.  intros n X Y f y X0.  unfold isofhlevelf. intro. rename y0 into x. 
apply (isofhlevelweqf n _ _ _ (isfibseq2 _ _ f y x) (X0 (f x))). Defined.





Theorem isofhlevelfsnd1f (n:nat)(X Y:UU)(f:X -> Y)(y:Y): isofhlevel (S n) (paths _  y y) -> isofhlevelf (S n) _ _ (d1f _ _ f y).
Proof.  intros n X Y f y X0.  unfold isofhlevelf. intro. rename y0 into x. 
assert (is1: paths _ (f x) y -> isofhlevel (S n) (paths _ (f x) y)). intro X1. destruct X1.  assumption.
assert (is2: isofhlevel (S n) (paths _ (f x) y)). apply isofhlevelsn. assumption.  
apply (isofhlevelweqf (S n) _ _ _ (isfibseq2 _ _ f y x) is2). Defined.



Corollary isofhlevelfd1fcor (n:nat)(X Y:UU)(f:X -> Y)(y:Y)(is: isofhlevel (S n) Y): isofhlevelf n (hfiber _ _ f y) X (pr21 _ _ ).
Proof. intros. apply isofhlevelfd1f. intro. apply (is y' y).   Defined. 



Theorem isofhlevelff (n:nat)(X Y Z:UU)(f:X -> Y)(g:Y -> Z): isofhlevelf n _ _ (fun x:X => g(f x)) -> isofhlevelf (S n) _ _ g -> isofhlevelf n _ _ f.
Proof. intros n X Y Z f g X0 X1. unfold isofhlevelf. intro. set (ye:= hfiberpair _ _ g (g y) y (idpath _ (g y))). 
apply (isofhlevelweqb n _ _ _ (isfibseqhfibers _ _ _ f g (g y) ye) (isofhlevelfinfibseq n _ _ _ (X0 (g y)) (X1 (g y)) ye)). Defined.


Theorem isofhlevelfgf (n:nat)(X Y Z:UU)(f:X -> Y)(g:Y -> Z): isofhlevelf n _ _ f -> isofhlevelf n _ _ g -> isofhlevelf n _ _ (fun x:X => g(f x)).
Proof. intros n X Y Z f g X0 X1.  unfold isofhlevelf. intro. rename y into z.
assert (is1: isofhlevelf n _ _ (hfibersgftog _ _ _ f g z)). unfold isofhlevelf. intro. rename y into ye. apply (isofhlevelweqf n _ _ _ (isfibseqhfibers _ _ _ f g z ye) (X0 (pr21 _ _ ye))). 
assert (is2: isofhlevel n (hfiber _ _ g z)). apply (X1 z).
apply (isofhlevelinfibseq n _ _ _ is1 is2). Defined.


Corollary isofhlevelffib (n:nat)(X:UU)(P:X -> UU)(x:X): (forall x':X, isofhlevel n (paths _ x' x)) -> isofhlevelf n _ _ (fun p: P x => tpair X P x p).
Proof. intros n X P x X0. unfold isofhlevelf. intro. set (f:= fibmap1 _ P x). set (g:= fun p: P x => tpair X P x p).  rename y into xp. set (pr21x:= pr21 X P).
assert (is1: isofhlevelf n _ _ (d1f _ _ (pr21 X P) x)). apply (isofhlevelfd1f n _ X (pr21 X P) x X0).
assert (h: forall p: P x, paths _ (d1f _ _ pr21x x (f p)) (g p)). intro. apply idpath. 
assert (is2: isofhlevelf n _ _ (fun p: P x => (d1f _ _ pr21x x (f p)))). apply (isofhlevelfgf n _ _ _ f (d1f _ _ pr21x x) (isofhlevelfweq n _ _ f (isweqfibmap1 _ _ x)) is1).  apply (isofhlevelfhomot n _ _ _ _ h is2 xp). Defined. 



Corollary isofhlevelfsnfib (n:nat)(X:UU)(P:X -> UU)(x:X): isofhlevel (S n) (paths _ x x) -> isofhlevelf (S n) _ _ (fun p: P x => tpair X P x p).
Proof. intros n X P x X0. unfold isofhlevelf.    intro.   set (f:= fibmap1 _ P x). set (g:= fun p: P x => tpair X P x p).  rename y into xp. set (pr21x:= pr21 X P).
assert (is1: isofhlevelf (S n) _ _ (d1f _ _ (pr21 X P) x)). apply (isofhlevelfsnd1f n _ X (pr21 X P) x X0). 
assert (h: forall p: P x, paths _ (d1f _ _ pr21x x (f p)) (g p)). intro. apply idpath. 
assert (is2: isofhlevelf (S n) _ _ (fun p: P x => (d1f _ _ pr21x x (f p)))). apply (isofhlevelfgf (S n) _ _ _ f (d1f _ _ pr21x x) (isofhlevelfweq (S n) _ _ f (isweqfibmap1 _ _ x)) is1).  apply (isofhlevelfhomot (S n) _ _ _ _ h is2 xp). Defined.



Theorem isofhlevelfg (n:nat)(X Y Z:UU)(f:X -> Y)(g:Y-> Z): isweq _ _ f -> isofhlevelf n _ _ (fun x:X => g (f x)) -> isofhlevelf n _ _ g.
Proof. intros n X Y Z f g X0 X1. set (gf:= fun x:X => g (f x)). set (finv:= invmap _ _ f X0). 
assert (h:forall y:Y, paths _ (gf (finv y)) (g y)). intro. apply (maponpaths _ _ g _ _ (weqfg _ _ f X0 y)).  
assert (is: isofhlevelf n _ _ (fun y:Y => gf (finv y))). apply (isofhlevelfgf n _ _ _ finv gf (isofhlevelfweq n _ _ _ (isweqinvmap _ _ f X0)) X1).  apply (isofhlevelfhomot n _ _ _ _ h is).  Defined.



Corollary isofhlevelfhomot2 (n:nat)(X X' Y:UU)(f:X -> Y)(f':X' -> Y)(w:X -> X')(h:forall x:X, paths _ (f x) (f' (w x)))(is: isweq _ _ w): isofhlevelf n _ _ f -> isofhlevelf n _ _ f'.  
Proof. intros n X X' Y f f' w h is X0.  assert (X1: isofhlevelf n _ _ (fun x:X => f' (w x))). apply (isofhlevelfhomot n _ _ f (fun x:X => f' (w x)) h X0). 
apply (isofhlevelfg n _ _ _ w f' is X1). Defined.




Theorem isofhlevelfonpaths (n:nat)(X Y:UU)(f:X -> Y)(x x':X): isofhlevelf (S n) _ _ f -> isofhlevelf n _ _ (maponpaths _ _ f x x').
Proof. intros n X Y f x x' X0. 
set (y:= f x'). set (xe':= hfiberpair _ _ f y x' (idpath _ _)). 
assert (is1: isofhlevelf n _ _ (d3f _ _ f y x xe')). unfold isofhlevelf. intro.  apply (isofhlevelweqf n _ _ _ (isfibseq4 _ _ f y x xe' y0) (X0 y (hfiberpair _ _ f y x y0) xe')). 
assert (h: forall ee:paths _ x' x, paths _ (d3f _ _ f y x xe' ee) (maponpaths _ _ f _ _ (pathsinv0 _ _ ee))). intro.
assert (e0: paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ ee)) (idpath _ _ ))  (maponpaths _ _ f _ _ (pathsinv0 _ _ ee)) ). induction ee.  simpl.  apply idpath. apply (pathscomp0 _ _ _ _ (d3fhomot _ _ f y x xe' ee) e0). apply (isofhlevelfhomot2 n _ _ _ _ _ (pathsinv0 x' x) h (isweqpathsinv0 _ _ _) is1) . Defined. 



Theorem isofhlevelfsn (n:nat)(X Y:UU)(f:X -> Y): (forall x x':X, isofhlevelf n _ _ (maponpaths _ _ f x x')) -> isofhlevelf (S n) _ _ f.
Proof. intros n X Y f X0.  unfold isofhlevelf. intro.  simpl.  intros. destruct x as [ x e ]. destruct x' as [ x' e' ].  set (xe':= hfiberpair _ _ f y x' e').  set (xe:= hfiberpair _ _ f y x e). set (d3:= d3f _ _ f y x xe'). simpl in d3.  
assert (is1: isofhlevelf n _ _ (d3f _ _ f y x xe')). 
assert (h: forall ee: paths _ x' x, paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ ee)) e') (d3f _ _ f y x xe' ee)). intro. apply (pathsinv0 _ _ (d3fhomot _ _ f y x xe' ee)). 
assert (is2: isofhlevelf n _ _ (fun ee: paths _ x' x => maponpaths _ _ f _ _ (pathsinv0 _ _ ee))).  apply (isofhlevelfgf n _ _ _ (fun ee:_ => pathsinv0 _ _ ee) (maponpaths _ _ f x x') (isofhlevelfweq n _ _ _ (isweqpathsinv0 _ _ _)) (X0 x x')). 
assert (is3: isofhlevelf n _ _ (fun ee: paths _ x' x => pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ ee)) e')). apply (isofhlevelfgf n _ _ _ _ _ is2 (isofhlevelfweq n _ _ _ (isweqpathscomp0r _ _ _ _ e'))). 
apply (isofhlevelfhomot n _ _ _ _ h is3). 
apply (isofhlevelweqb n _ _ _ (isfibseq4 _ _ f y x xe' e) (is1 e)).  Defined.


Theorem isofhlevelfssn (n:nat)(X Y:UU)(f:X -> Y): (forall x:X, isofhlevelf (S n) _ _ (maponpaths _ _ f x x)) -> isofhlevelf (S (S n)) _ _ f.
Proof.  intros n X Y f X0.  unfold isofhlevelf. intro.
assert (forall xe0: hfiber _ _ f y, isofhlevel (S n) (paths _ xe0 xe0)). intro. destruct xe0 as [ x e ].  set (x':= x). set (e':=e).  set (xe':= hfiberpair _ _ f y x' e').  set (xe:= hfiberpair _ _ f y x e). set (d3:= d3f _ _ f y x xe'). simpl in d3.  
assert (is1: isofhlevelf (S n) _ _ (d3f _ _ f y x xe')). 
assert (h: forall ee: paths _ x' x, paths _ (pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ ee)) e') (d3f _ _ f y x xe' ee)). intro. apply (pathsinv0 _ _ (d3fhomot _ _ f y x xe' ee)). 
assert (is2: isofhlevelf (S n) _ _ (fun ee: paths _ x' x => maponpaths _ _ f _ _ (pathsinv0 _ _ ee))).  apply (isofhlevelfgf (S n) _ _ _ (fun ee:_ => pathsinv0 _ _ ee) (maponpaths _ _ f x x') (isofhlevelfweq (S n) _ _ _ (isweqpathsinv0 _ _ _)) (X0 x)). 
assert (is3: isofhlevelf (S n) _ _ (fun ee: paths _ x' x => pathscomp0 _ _ _ _ (maponpaths _ _ f _ _ (pathsinv0 _ _ ee)) e')). apply (isofhlevelfgf (S n) _ _ _ _ _ is2 (isofhlevelfweq (S n) _ _ _ (isweqpathscomp0r _ _ _ _ e'))). 
apply (isofhlevelfhomot (S n) _ _ _ _ h is3). 
apply (isofhlevelweqb (S n) _ _ _ (isfibseq4 _ _ f y x xe' e) (is1 e)).  
apply (isofhlevelssn).  assumption. Defined.





(** Theorem saying that if each member of a family is of h-level n and so is the base then the total space is of h-level n. *)

Theorem isofhleveltotal2 (n:nat)(X:UU)(P:X -> UU)(is1: isofhlevel n X)(is2: forall x:X, isofhlevel n (P x)): isofhlevel n (total2 X P).
Proof. intros. apply (isofhlevelinfibseq n (total2 X P) X (pr21 _ _)). apply isofhlevelfpr21. assumption. assumption. Defined. 

Corollary isofhleveldirprod (n:nat)(X Y:UU)(is1:isofhlevel n X)(is2: isofhlevel n Y): isofhlevel n (dirprod X Y).
Proof. intros. apply isofhleveltotal2. assumption. intro. assumption. Defined. 




(** Theorem saying that if each member of a family is of h-level n then the space of sections of the family is of h-level n. *)

Theorem impred (n:nat)(T:UU)(P:T -> UU): (forall t:T, isofhlevel n (P t)) -> isofhlevel n (forall t:T, P t).
Proof.
  intro.
  induction n.
    intros T P X.
    apply (funcontr T P X).
  intros T P X.
  unfold isofhlevel in X.
  unfold isofhlevel.
  intros x x'.
  assert (is: forall t:T, isofhlevel n (paths _ (x t) (x' t))).
    intro.
    apply (X t (x t) (x' t)).
  assert (is2: isofhlevel n (forall t:T, paths _ (x t) (x' t))).
    apply (IHn _ (fun t0:T => paths _ (x t0) (x' t0)) is).
  set (u:=toforallpaths _ P x x').
  assert (is3:isweq _ _ u).
    apply isweqtoforallpaths.
  set (v:= invmap _ _ u is3).
  assert (is4: isweq _ _ v).
   apply isweqinvmap.
  apply (isofhlevelweqf n _ _ v is4).
  assumption.
Defined.

Corollary impredtwice  (n:nat)(T T':UU)(P:T -> T' -> UU): (forall (t:T)(t':T'), isofhlevel n (P t t')) -> (isofhlevel n (forall (t:T)(t':T'), P t t')).
Proof.  intros n T T' P X. assert (is1: forall t:T, isofhlevel n (forall t':T', P t t')). intro. apply (impred n _ _ (X t)). apply (impred n _ _ is1). Defined.


Corollary impredfun (n:nat)(X Y:UU)(is: isofhlevel n Y) : isofhlevel n (X -> Y).
Proof. intros. apply (impred n X (fun x:_ => Y) (fun x:X => is)). Defined. 


Theorem impredtech1 (n:nat)(X Y: UU) : (X -> isofhlevel n Y) -> isofhlevel n (X -> Y).
Proof. intro. induction n. intros X Y X0. simpl. split with (fun x:X => pr21 _ _ (X0 x)).  intro. 
assert (s1: forall x:X, paths _ (t x) (pr21 _ _ (X0 x))). intro. apply contrl2. apply (X0 x). 
apply funextsec. assumption. 

intros X Y X0. simpl. assert (X1: X -> isofhlevel (S n) (X -> Y)). intro. apply impred. assumption. intros.
assert (s1: isofhlevel n (forall xx:X, paths _ (x xx) (x' xx))). apply impred. intro. apply (X0 t). 
assert (w: weq (forall xx:X, paths _ (x xx) (x' xx)) (paths _ x x')). apply (weqinv (weqfunextsec _ _ x x' )). apply (isofhlevelweqf n _ _ (pr21 _ _ w) (pr22 _ _ w) s1). Defined. 















(** ** Fibrations with only one non-empty fiber. 

Theorem saying that if a fibration has only one non-empty fiber then the total space is weakly equivalent to this fiber. *)



Theorem onefiber (X:UU)(P:X -> UU)(x:X)(c: forall x':X, coprod (paths _ x x') (neg (P x')))
      : isweq _ _ (fun p => tpair X P x p).
Proof.
 intros.  
 set (f := fun p => tpair X P x p). 
 set (cx := c x). 
 set (cnew := fun x':X  =>
     match cx with 
         ii1 exx =>
             match c x' with 
                 ii1 exx' => ii1 _ _ (pathscomp0 _ _ _ _ (pathsinv0 _ _ exx) exx')|
                 ii2 phi => ii2 _ _ phi
             end |
         ii2 phi => c x'
     end).
 set (cnewx:= cnew x).
 set (g := fun pp: total2 X P => 
     match cnew (pr21 _ _ pp) with
         ii1 e => transportb _ _ _ _ e (pr22 _ _ pp) |
         ii2 phi =>  initmap _ (phi (pr22 _ _ pp))
     end).
 assert (efg: forall pp, paths _ (f (g pp)) pp).
  intro.
  induction pp as [t x0].
  unfold g.
  unfold f.
  simpl.
  induction (cnew t) as [x1|y].
   destruct x1.
   apply idpath.
  induction (y x0).
 assert (e1: paths _ (cnew x) cnewx).
  apply idpath. 
 unfold cnew in cnewx.
 change (c x) with cx in cnewx.  
 induction cx.  
  assert (e: paths _ cnewx (ii1 _ _ (idpath _ x))).
   apply (maponpaths _ _ (ii1 (paths _ x x) (neg (P x))) _ _ (pathsinv0l1 _ _ _ x0)).
  assert (egf: forall p, paths _ (g (f p)) p).
   intro.
   simpl in g.
   unfold g.
   unfold f.
   simpl.
   set (ff:= fun cc:coprod (paths _ x x) (neg (P x)) => 
     match cc with
          | ii1 e0 => transportb _ _ x x e0 p
          | ii2 phi => initmap (P x) (phi p)
          end).
   assert (ee: paths _ (ff (cnewx)) (ff (ii1 (paths _ x x) (neg (P x)) (idpath _ x)))).
    apply (maponpaths _ _ ff _ _ e).
   assert (eee: paths _  (ff (ii1 (paths _ x x) (neg (P x)) (idpath _ x))) p).
    apply idpath.
   fold (ff (cnew x)).
   assert (e2: paths _ (ff (cnew x)) (ff (cnewx))).
    apply (maponpaths _ _ ff _ _ e1).
   apply (pathscomp0 _ _ _ _ (pathscomp0 _ _ _ _ e2 ee) eee).
  apply (gradth _ _ f g egf efg).
 unfold isweq.
 intro.
 induction (y (g y0)).
Defined.

(** ** Propositions, inclusions  and sets. *)







(** *** Basics about types of h-level 1 - "propositions". *)




Lemma isweqimplimpl (X:UU)(Y:UU)(f:X->Y) : (Y->X) -> isaprop X -> isaprop Y -> isweq _ _ f.
Proof.
  intros X Y f g isx isy.
   assert (isx0: forall x:X, paths _ (g (f x)) x).
    intro.
    assert (iscontr X).
     apply (iscontraprop1 X isx x).
    apply (contrl2 X X0 (g (f x)) x).
   assert (isy0: forall y:Y, paths _ (f (g y)) y).
    intro.
    assert (iscontr Y).
     apply (iscontraprop1 Y isy y).
    apply (contrl2 Y X0 (f (g y)) y).
   apply (gradth _ _ f g isx0 isy0).
Defined.
   
Theorem isapropempty: isaprop empty.
Proof. unfold isaprop. unfold isofhlevel. intros. induction x. Defined. 


Lemma proofirrelevance (X:UU): isaprop X -> forall x x', paths X x x'. 
Proof. intros X X0 x x'. unfold isaprop in X0. unfold isofhlevel in X0.   apply (pr21 _ _ (X0 x x')). Defined. 


Lemma invproofirrelevance (X:UU): (forall (x x':X), paths _ x x') -> isaprop X.
Proof. intros X X0. unfold isaprop. unfold isofhlevel.  intro.  
assert (is: iscontr X).  split with x. intro.  apply (X0 t x). assert (is1: isaprop X).  apply isapropifcontr. assumption.   
unfold isaprop in is1. unfold isofhlevel in is1.  apply (is1 x). Defined. 




Lemma isapropifnegtrue (X:UU): neg X -> isaprop X.
Proof. intros. assert (is:isweq _ _ X0). intro. apply (initmap _ y).   apply (isofhlevelweqb 1 _ _ _ is isapropempty). Defined.


Definition isdecprop (X:UU):= dirprod (isaprop X) (decidable X).




(** *** Theorems saying that  [ iscontr T ], [ isweq f ] etc. are of h-level 1. *)



Theorem iscontriscontr: forall X:UU, iscontr(X)->iscontr(iscontr(X)).
Proof. intros. 

assert (is0: forall (x x':X), paths _ x x'). apply contrl2. assumption.

assert (is1: forall cntr:X, iscontr (forall x:X, paths _ x cntr)). intro. 
assert (is2: forall x:X, iscontr (paths _ x cntr)). 
assert (is2: isaprop X). apply isapropifcontr. assumption.  
unfold isaprop in is2. unfold isofhlevel in is2. intro. apply (is2 x cntr).
apply funcontr. assumption. 

set (f:= pr21 X (fun cntr:X => forall x:X, paths _ x cntr)). 
assert (X1:isweq _ _ f).  apply isweqpr21. assumption. change (total2 X (fun cntr : X => forall x : X, paths _ x cntr)) with (iscontr X) in X1.  apply (iscontrxifiscontry _ _ f X1). assumption.  Defined. 



Theorem isapropiscontr (T:UU): isaprop (iscontr T).
Proof. intros.  unfold isaprop.  unfold isofhlevel. intros. assert (is: iscontr(iscontr T)). apply iscontriscontr. apply x. assert (is2: isaprop (iscontr T)). apply (isapropifcontr _ is). apply (is2 x x'). Defined.  



Theorem isapropisweq (X:UU)(Y:UU)(f:X-> Y) : isaprop (isweq _ _ f).
Proof. intros. unfold isweq.  apply (impred 1 _ (fun y:Y => iscontr (hfiber X Y f y)) (fun y:Y => isapropiscontr (hfiber X Y f y))).  Defined. 


Theorem isapropisofhlevel (n:nat)(X:UU): isaprop (isofhlevel n X).
Proof. intro.  unfold isofhlevel.    induction n. apply isapropiscontr.  intro. 
assert (X0: forall (x x':X), isaprop  ((fix isofhlevel (n0 : nat) (X0 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X0
         | S m => forall x0 x'0 : X0, isofhlevel m (paths _ x0 x'0)
         end) n (paths _ x x'))). intros. apply (IHn (paths _ x x')). 
assert (is1: 
     (forall x:X, isaprop (forall  x' : X,
      (fix isofhlevel (n0 : nat) (X1 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X1
         | S m => forall x0 x'0 : X1, isofhlevel m (paths _ x0 x'0)
         end) n (paths _ x x')))). intro.  apply (impred 1 _ _ (X0 x)). apply (impred 1 _ _ is1). Defined. 

Corollary isapropisaprop (X:UU) : isaprop (isaprop X).
Proof. intro. apply (isapropisofhlevel 1). Defined. 





(** *** More results on types of h-level 1 (propositions) and functions of h-level 1 (inclusions). *)



Theorem isapropneg (X:UU): isaprop (neg X).
Proof. intro. apply (impredfun 1 X empty isapropempty). Defined.

Corollary isapropdneg (X:UU): isaprop (dneg X).
Proof. intro. apply (isapropneg (neg X)). Defined.


Definition isaninvprop (X:UU):= isweq _ _ (todneg X).

Definition invimpl (X:UU)(is: isaninvprop X): dneg X -> X := invmap _ _ (todneg X) is. 


Lemma isapropaninvprop (X:UU): isaninvprop X -> isaprop X.
Proof. intros X X0. 
apply (isofhlevelweqb 1 _ _ (todneg X) X0 (isapropdneg X)). Defined. 


Theorem isaninvpropneg (X:UU): isaninvprop (neg X).
Proof. intros. 
set (f:= todneg (neg X)). set (g:= negf (todneg X)). set (is1:= isapropneg X). set (is2:= isapropneg (dneg X)). apply (isweqimplimpl _ _ f g is1 is2).  Defined.


Theorem isapropisdec (X:UU): isaprop X -> isaprop (decidable X).
Proof. 
    intros X X0. 
    apply invproofirrelevance.
    intro x.
    induction x.
    (* yes *) intro x'. induction x'.
        (* yes *) apply maponpaths, proofirrelevance; assumption.
        (* no  *) apply initmap; auto.
    (* no  *) intro x'. induction x'.   
        (* yes *) apply initmap; auto.
        (* no  *) apply maponpaths, proofirrelevance, isapropneg.
    Defined. 

Theorem isaninv1 (X:UU): isdecprop X  -> isaninvprop X.
Proof. unfold isaninvprop. intros X is.  set (is1:= pr21 _ _ is). set (is2:= pr22 _ _ is). simpl in is2. 
assert (adjevinv: dneg X -> X). intro X0.  induction is2 as [ x | y ].  assumption. induction (X0 y). 
assert (is3: isaprop (dneg X)). apply (isapropneg (neg X)). apply (isweqimplimpl _ _ (todneg X) adjevinv is1 is3). Defined. 



Definition isincl (X Y:UU)(f:X -> Y):= isofhlevelf 1 _ _ f.

Lemma isofhlevelfsnincl (n:nat)(X Y:UU)(f:X -> Y)(is: isincl _ _ f): isofhlevelf (S n) _ _ f.
Proof. intros. unfold isofhlevelf.  intro. apply isofhlevelsnprop. apply (is y). Defined.   

Lemma iscontrhfiberofincl (X:UU)(Y:UU)(f:X -> Y): isincl _ _ f -> (forall x:X, iscontr (hfiber _ _ f (f x))).
Proof. intros X Y f X0 x. unfold isofhlevelf in X0. set (isy:= X0 (f x)).  apply (iscontraprop1 _ isy (hfiberpair _ _ f (f x) x (idpath _ (f x)))). Defined.


Lemma isweqonpathsincl (X:UU)(Y:UU)(f:X -> Y) : (isincl _ _ f) -> forall (x x':X), isweq _ _ (maponpaths _ _ f x x').
Proof. intros X Y f is x x'. apply (isofhlevelfonpaths O _ _ f x x' is). Defined.

Definition invmaponpathsincl (X Y:UU)(f:X -> Y) : (isincl _ _ f) -> forall (x x':X), paths _ (f x) (f x') -> paths _ x x'. 
Proof. intros X Y f is x x'.
 exact (invmap _ _ _ (isweqonpathsincl _ _ f is x x')).
 Defined.

Lemma isinclweqonpaths (X Y:UU)(f:X -> Y): (forall x x':X, isweq _ _ (maponpaths _ _ f x x')) -> isincl _ _ f.
Proof. intros X Y f X0.  apply (isofhlevelfsn O _ _ f X0). Defined.

Definition isofhlevelsourceofincl (n:nat)(X Y:UU)(f:X -> Y)(is: isincl _ _ f): isofhlevel (S n) Y -> isofhlevel (S n) X:= isofhlevelinfibseq (S n) _ _ f (isofhlevelfsnincl n _ _ f is).

Definition isinclpr21 (X:UU)(P:X -> UU)(is: forall x:X, isaprop (P x)): isincl _ _ (pr21 X P):= isofhlevelfpr21 1 X P is.




Theorem isapropweq (P P':UU) : isaprop P' -> isaprop (weq P P').
Proof.
  intros P P' is'.
  set (p:= underlying_function P P').
  assert (is: isincl _ _ p).
    apply (isofhlevelfpr21 1 (P -> P') _ (fun f: P -> P' => isapropisweq _ _ f)).
  assert (is2: isaprop (P -> P')).
    apply impred.
    intro.
    apply is'.
  apply (isofhlevelsourceofincl O _ _ p is is2).
Defined. 




Theorem samehfibers (X Y Z : UU) (f: X -> Y) (g: Y -> Z) (is1: isofhlevelf 1 _ _ g) ( y: Y)
                : isweq _ _ (hfibersftogf _ _ _ f g (g y) (hfiberpair _ _ g (g y) y (idpath _ _ ))).
Proof.
  intros.
  set (z:= g y).
  set (ye:= hfiberpair _ _ g z y (idpath _ _ )).
  unfold isweq.
  intro xe.
  assert (is2: isfibseq _ _ _
                        (hfibersftogf _ _ _ f g z ye)
                        (hfibersgftog _ _ _ f g z)
                        ye
                        (hfibersez _ _ _ f g z ye)).
    apply isfibseqhfibers.
  assert (w1: weq (paths _ (hfibersgftog _ _ _ f g z xe) ye) (hfiber _ _ (hfibersftogf _ _ _ f g z ye) xe)).
    split with (ezmap _ _ _
          (diff1f _ _ _
             (hfibersftogf _ _ _ f g z ye)
             (hfibersgftog _ _ _ f g z) ye (hfibersez _ _ _ f g z ye) is2 xe)
          (hfibersftogf _ _ _ f g z ye) xe
          (diff1ez _ _ _ 
             (hfibersftogf _ _ _ f g z ye)
             (hfibersgftog _ _ _ f g z) ye (hfibersez _ _ _ f g z ye) is2 xe)).
    apply isfibseqdiff1.
  apply (isweqcontr2 _ _ _ (pr22 _ _ w1)).
  apply isapropifcontr.
  apply iscontrhfiberofincl.
  assumption.
Defined. 












(** *** Basics about types of h-level 2 - "sets". *)


Corollary isapropisaset (X:UU): isaprop (isaset X).
Proof. intro. apply (isapropisofhlevel 2). Defined.


Lemma isaset1 (X:UU): (forall x:X, iscontr (paths _ x x)) -> isaset X.
Proof. intros X X0. unfold isaset. unfold isofhlevel. intros.   induction x0. set (is:= X0 x). apply isapropifcontr. assumption.  Defined. 

Lemma isaset2 (X:UU): isaset X -> forall x:X, iscontr (paths _ x x).
Proof. 
  intros X X0 x.
  apply (iscontraprop1 _ (X0 x x) (idpath _ x)).
Defined.


(**  A monic subtype of a set is a set. *)

Theorem isasetsubset (X Y : UU) (f: X -> Y) (is1: isaset Y) (is2: isincl _ _ f): isaset X.
Proof. intros. apply  (isofhlevelsourceofincl 1 X Y f is2). apply is1. Defined. 



(** The morphism from hfiber is an inclusion *)

Theorem isinlfromhfiber (X Y : UU) (f: X -> Y) (is : isaset Y) ( y: Y ) : isincl (hfiber _ _ f y) X (pr21 _ _ ).
Proof. intros. apply isofhlevelfd1fcor. assumption. Defined. 












(** ** Coprojections, isolated points and types with decidable equality. *)


(** *** Types with decidable equality are of h-level 2 (i.e. sets). *)




Definition isdeceq (X:UU): UU :=  forall x x':X, decidable (paths _ x' x).

Lemma dnegdec (X:UU): dneg (decidable X).
Proof. intros X r. cut (neg X). intro f. apply r.  apply no. exact f. intro x. apply r. apply yes. exact x. Defined.

Theorem isasetifdeceq (X:UU): isdeceq X -> isaset X.
Proof.
  intros X X0.
  apply isaset1. 
  intro.  
  set (f:= fun e: paths _ x x => coconusfromtpair _ x x e). 
  apply (iscontrxifiscontry _ _ f ). 
    apply onefiber.
    intro.
    apply tocoprod.
    apply X0.
  apply iscontrcoconusfromt. 
Defined. 


Theorem isapropisdeceq (X:UU): isaprop (isdeceq X).
Proof. intro. unfold isdeceq.
assert (X0:forall u u':isdeceq X, paths _ u u'). intros. 
assert (X1: forall x x':X, isaprop (decidable (paths _ x x'))). intros. 
assert (is0:isaprop (paths _ x x')). assert (is1: isaset X). apply (isasetifdeceq _ u).  set (is2:= is1 x x'). simpl in is2. unfold isaprop. unfold isofhlevel. assumption. 
apply (isapropisdec _ is0). 
assert (X2: isaprop (isdeceq X)). apply impredtwice. intros.  apply (X1 t' t). 
apply (proofirrelevance _ X2 u u'). apply (invproofirrelevance _ X0). Defined.


Corollary eqfromdnegeq (X:UU)(is: isdeceq X)(x x':X): dneg( paths _ x x') -> paths _ x x'.
Proof. intros X is x x' X0. 
  set (a:= dirprodpair (isasetifdeceq X is x x') (is x' x)).
  set (isinv:= isaninv1 _ a).
  apply (invimpl _ isinv X0).
Defined. 

Definition curry (x:bool) : UU := match x with false => empty | true => unit end.

Theorem nopathstruetofalse: neg ( paths _ true false ).
Proof. intro X. exact (transportf _ curry _ _ X tt).   Defined.

Corollary nopathsfalsetotrue: neg (paths _ false true).
Proof. intro X. exact (transportb _ curry _ _ X tt). Defined. 

Theorem isdeceqbool: isdeceq bool.
Proof. unfold isdeceq. intros.
  induction x. 
    induction x'. 
      apply yes. apply idpath. 
      apply no. unfold neg. apply nopathsfalsetotrue.
    induction x'.  
      apply no. unfold neg. apply nopathstruetofalse. 
      apply yes. apply idpath. 
Defined.

Theorem isasetbool: isaset bool.
Proof. apply (isasetifdeceq _ isdeceqbool). Defined. 


Lemma noneql1 (X Y: UU)(f:X -> Y)(x x':X): neg (paths _ (f x) (f x')) -> neg (paths _ x x').
Proof. intros X Y f x x' X0 X1. apply (X0 (maponpaths _ _ f _ _ X1)). Defined.  

Theorem nopathsOtoSx: forall x:nat, neg (paths _ O (S x)).
Proof. intro. 
    set (f:= fun n:nat => match n with O => true | S m => false end). 
    unfold neg.
    apply (noneql1 _ _ f O (S x) nopathstruetofalse).
Defined. 

Corollary nopathsSxtoO: forall x:nat, neg ( paths _ (S x) O ).
Proof. intros x X. apply (nopathsOtoSx x (pathsinv0 _ _ X)). Defined. 

Lemma noeqinjS: forall (x x':nat),  neg (paths _ x x') -> neg (paths _ (S x) (S x')).
Proof. 
  set (f:= fun n:nat => match n with O => O| S m => m end). 
  intro. intro. intro X. apply (noneql1 _ _ f (S x) (S x') X). Defined. 
 

Theorem isdeceqnat: isdeceq nat.
Proof. 
    unfold isdeceq.
    intro. induction x. 
    intro. destruct x'.
       apply yes. apply idpath.
       apply no. unfold neg. apply nopathsSxtoO.
    intro.  destruct x'.
       apply no. exact (nopathsOtoSx x).
       destruct (IHx x').
            apply yes. apply maponpaths. assumption.
            apply no. unfold neg. apply noeqinjS. assumption. 
Defined. 

Theorem isasetnat: isaset nat.
Proof.  apply (isasetifdeceq _ isdeceqnat). Defined. 




(** ** More on pairwise coproducts. *)


Definition coprodtobool (X Y:UU): coprod X Y -> bool:= fun xy:_ =>
match xy with
ii1 x => true|
ii2 y => false
end.
 

Definition boolsumfun (X Y:UU): bool -> UU := fun t:_ => 
match t with
true => X|
false => Y
end.

Definition coprodtoboolsum (X Y:UU): coprod X Y -> total2 bool (boolsumfun X Y).
Proof.
 intros X Y xy.
 set (P := boolsumfun X Y).
 destruct xy as [x|y].
  exact (tpair _ P true x).
  exact (tpair _ P false y).
Defined.

Definition boolsumtocoprod (X Y:UU): total2 bool (boolsumfun X Y) -> coprod X Y := (
  fun xy:_ =>
    match xy with 
      tpair true x => ii1 _ _ x|
      tpair false y => ii2 _ _ y
    end).

Theorem isweqcoprodtoboolsum (X Y:UU): isweq _ _ (coprodtoboolsum X Y).
Proof. intros. set (f:= coprodtoboolsum X Y). set (g:= boolsumtocoprod X Y). 
assert (egf: forall xy: coprod X Y , paths _ (g (f xy)) xy). destruct xy. apply idpath. apply idpath. 
assert (efg: forall xy: total2 bool (boolsumfun X Y), paths _ (f (g xy)) xy). intro. destruct xy as [ t x ]. destruct t.  apply idpath. apply idpath. apply (gradth _ _ f g egf efg). Defined.

Corollary isweqboolsumtocoprod (X Y:UU): isweq _ _ (boolsumtocoprod X Y ).
Proof. intros. apply (isweqinvmap _ _ _ (isweqcoprodtoboolsum X Y)). Defined.


Theorem isinclii1 (X Y:UU): isincl _ _ (ii1 X Y).
Proof. intros. set (f:= ii1 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun x:X => (g (f x))). set (gf':= fun x:X => tpair _ (boolsumfun X Y) true x). 
assert (h: forall x:X , paths _ (gf' x) (gf x)). intro. apply idpath. 
assert (is1: isofhlevelf 1 _ _ gf'). apply (isofhlevelfsnfib O bool (boolsumfun X Y) true (isasetbool true true)).
assert (is2: isofhlevelf 1 _ _ gf). apply (isofhlevelfhomot 1 _ _ gf' gf h is1).  
apply (isofhlevelff 1 _ _ _ _ _ is2 (isofhlevelfweq 2 _ _ _ (isweqcoprodtoboolsum X Y))). Defined. 


Theorem isinclii2 (X Y:UU): isincl _ _ (ii2 X Y).
Proof. intros. set (f:= ii2 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun y:Y => (g (f y))). set (gf':= fun y:Y => tpair _ (boolsumfun X Y) false y). 
assert (h: forall y:Y , paths _ (gf' y) (gf y)). intro. apply idpath. 
assert (is1: isofhlevelf 1 _ _ gf'). apply (isofhlevelfsnfib O bool (boolsumfun X Y) false (isasetbool false false)).
assert (is2: isofhlevelf 1 _ _ gf). apply (isofhlevelfhomot 1 _ _ gf' gf h is1).  
apply (isofhlevelff 1 _ _ _ _ _ is2 (isofhlevelfweq 2 _ _ _ (isweqcoprodtoboolsum X Y))). Defined. 




Lemma negintersectii1ii2 (X Y:UU)(z: coprod X Y): hfiber _ _ (ii1 X Y) z -> hfiber _ _ (ii2 _ _) z -> empty.
Proof. intros X Y z X0 X1. destruct X0 as [ t x ]. destruct X1 as [ t0 x0 ].  
set (e:= pathscomp0 _ _ _ _ x (pathsinv0 _ _ x0)). apply (negpathsii1ii2 _ _ _ _ e). Defined. 

Definition coprodsplit {X Y Z:UU}(f:X -> coprod Y Z): coprod (hfp f (ii1 Y Z)) (hfp f (ii2 Y Z)) -> X := 
sumofmaps (hfppr1 f (ii1 Y Z)) (hfppr1 f (ii2 Y Z)).


Definition coprodsplitinv {X Y Z:UU}(f:X -> coprod Y Z): X -> coprod (hfp f (ii1 Y Z)) (hfp f (ii2 Y Z)).
Proof. intros X Y Z f X0. set (fx0:= f X0). unfold hfp.
assert (int1: coprod (hfiber _ _ (ii1 Y Z) fx0) (hfiber _ _ (ii2 Y Z) fx0)). destruct fx0. apply (ii1 _ _ (hfiberpair _ _ _ (ii1 _ _ y) y (idpath _ _))). apply (ii2 _ _ (hfiberpair _ _ _ (ii2 _ _ z) z (idpath _ _))). 
apply (coprodf _ _ _ _ (hfppair f _ X0) (hfppair f _ X0) int1). Defined.


Theorem weqcoprodsplit {X Y Z:UU}(f:X -> coprod Y Z): weq (coprod (hfp f (ii1 Y Z)) (hfp f (ii2 Y Z))) X.
Proof. intros. set (ff:= coprodsplit f). split with ff. set (gg:= coprodsplitinv f).
assert (egf: forall x:_, paths _ (gg (ff x)) x). intro. destruct x as [ h | h ]. simpl. destruct h as [ t x ].  simpl. unfold gg. unfold coprodsplitinv. 

set (int1:= match
          f t as c
          return
            (coprod (hfiber Y (coprod Y Z) (ii1 Y Z) c)
               (hfiber Z (coprod Y Z) (ii2 Y Z) c))
        with
        | ii1 y =>
            ii1 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii1 Y Z y))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii1 Y Z y))
              (hfiberpair Y (coprod Y Z) (ii1 Y Z) 
                 (ii1 Y Z y) y (idpath _ (ii1 Y Z y)))
        | ii2 z =>
            ii2 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii2 Y Z z))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii2 Y Z z))
              (hfiberpair Z (coprod Y Z) (ii2 Y Z) 
                 (ii2 Y Z z) z (idpath _ (ii2 Y Z z)))
        end). destruct int1.  simpl. assert (e: paths _ h x). apply (proofirrelevance _ (isinclii1 _ _ (f t))).   induction e.  apply idpath. 
simpl. apply (initmap _ (negintersectii1ii2 _ _ (f t) x h)). 


simpl. destruct h as [ t x ].  simpl. unfold gg. unfold coprodsplitinv. 

set (int1:= match
          f t as c
          return
            (coprod (hfiber Y (coprod Y Z) (ii1 Y Z) c)
               (hfiber Z (coprod Y Z) (ii2 Y Z) c))
        with
        | ii1 y =>
            ii1 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii1 Y Z y))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii1 Y Z y))
              (hfiberpair Y (coprod Y Z) (ii1 Y Z) 
                 (ii1 Y Z y) y (idpath _ (ii1 Y Z y)))
        | ii2 z =>
            ii2 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii2 Y Z z))
              (hfiber Z (coprod Y Z) (ii2 Y Z) (ii2 Y Z z))
              (hfiberpair Z (coprod Y Z) (ii2 Y Z) 
                 (ii2 Y Z z) z (idpath _ (ii2 Y Z z)))
        end). destruct int1. apply (initmap _ (negintersectii1ii2 _ _ (f t) h x)).  simpl. assert (e: paths _ h x). apply (proofirrelevance _ (isinclii2 _ _ (f t))).   induction e.  apply idpath. 

assert (efg: forall x:_, paths _ (ff (gg x)) x). intro. unfold gg. unfold coprodsplitinv.  

set (int1:= match
             f x as c
             return
               (coprod (hfiber Y (coprod Y Z) (ii1 Y Z) c)
                  (hfiber Z (coprod Y Z) (ii2 Y Z) c))
           with
           | ii1 y =>
               ii1 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii1 Y Z y))
                 (hfiber Z (coprod Y Z) (ii2 Y Z) (ii1 Y Z y))
                 (hfiberpair Y (coprod Y Z) (ii1 Y Z) 
                    (ii1 Y Z y) y (idpath _ (ii1 Y Z y)))
           | ii2 z =>
               ii2 (hfiber Y (coprod Y Z) (ii1 Y Z) (ii2 Y Z z))
                 (hfiber Z (coprod Y Z) (ii2 Y Z) (ii2 Y Z z))
                 (hfiberpair Z (coprod Y Z) (ii2 Y Z) 
                    (ii2 Y Z z) z (idpath _ (ii2 Y Z z)))
           end). destruct int1.  simpl. apply idpath.  simpl. apply idpath.

apply (gradth _ _ ff gg egf efg). Defined. 


Definition subsetsplit (X:UU)(f:X -> bool): (coprod (hfiber _ _ f true) (hfiber _ _ f false)) -> X := fun ab:_ => match ab with ii1 xt => pr21 _ _ xt | ii2 xf => pr21 _ _ xf end.


Theorem weqsubsetsplit (X:UU)(f:X -> bool): weq (coprod (hfiber _ _ f true) (hfiber _ _ f false))  X.
Proof.  intros.  set (g:= pr21 _ _ (weqinv boolascoprod)). 
assert (et: paths _ (ii1 _ _ tt) (g true)). apply idpath. 
assert (ef: paths _ (ii2 _ _ tt) (g false)). apply idpath. 
set (gf:= fun x:X => g (f (x))). set (w1:= weqcoprodsplit gf). 

assert (w2: weq (hfiber X bool f true) (hfp gf (ii1 unit unit))). unfold hfiber. unfold hfp. 
assert (w2a: forall x:X, weq (paths _ (f x) true) (hfiber unit (coprod unit unit) (ii1 unit unit) (gf x))). intro. set (fx:= f x). change (gf x) with (g fx).  destruct fx. 
assert (is1: iscontr (paths _ true true)). apply (isaset2 _ isasetbool true). 
assert (is2: iscontr (hfiber unit (coprod unit unit) (ii1 unit unit) (g true))). induction et.  apply (iscontrhfiberofincl _ _ (ii1 _ _) (isinclii1 _ _) tt). apply (weqpair _ (ifcontrcontrthenweq _ _ (fun a:_ => pr21 _ _ is2) is1 is2)). 
assert (is1: weq (paths _ false true) empty). apply (weqpair _ (isweqtoempty _ nopathsfalsetotrue)). 
assert (is2: neg (hfiber unit (coprod unit unit) (ii1 unit unit) (g false))). destruct ef.  intro X0.  destruct X0 as [ t x0 ].  apply (negpathsii1ii2 _ _ _ _ x0). apply (weqcomp is1 (weqinv (weqpair _ (isweqtoempty _ is2)))). split with (totalfun _ _ _ (fun x:X => pr21 _ _ (w2a x))). apply (isweqfibtototal _ _ _ _ (fun x:X => pr22 _ _ (w2a x))). 

assert (w3: weq (hfiber X bool f false) (hfp gf (ii2 unit unit))). unfold hfiber. unfold hfp. 
assert (w3a: forall x:X, weq (paths _ (f x) false) (hfiber unit (coprod unit unit) (ii2 unit unit) (gf x))). intro. set (fx:= f x). change (gf x) with (g fx).  destruct fx. 

assert (is1: weq (paths _ true false) empty). apply (weqpair _ (isweqtoempty _ nopathstruetofalse)). 
assert (is2: neg (hfiber unit (coprod unit unit) (ii2 unit unit) (g true))). destruct ef.  intro X0.  destruct X0 as [ t x0 ].  apply (negpathsii2ii1 _ _ _ _ x0). apply (weqcomp is1 (weqinv (weqpair _ (isweqtoempty _ is2)))). 

assert (is1: iscontr (paths _ false false)). apply (isaset2 _ isasetbool false). 
assert (is2: iscontr (hfiber unit (coprod unit unit) (ii2 unit unit) (g false))). induction ef.  apply (iscontrhfiberofincl _ _ (ii2 _ _) (isinclii2 _ _) tt). apply (weqpair _ (ifcontrcontrthenweq _ _ (fun a:_ => pr21 _ _ is2) is1 is2)). 

split with (totalfun _ _ _ (fun x:X => pr21 _ _ (w3a x))). apply (isweqfibtototal _ _ _ _ (fun x:X => pr22 _ _ (w3a x))). 

apply (weqcomp (weqcoprodf _ _ _ _ w2 w3) w1). Defined. 







Definition fromhfibercoprodf1 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(x':X'):(hfiber _ _ (coprodf _ _ _ _ f g) (ii1 _ _ x')) -> hfiber _ _ f x'.
Proof. intros X Y X' Y' f g x' X0. destruct X0 as [ t x ].  destruct t. set (e:= invmaponpathsincl _ _ _ (isinclii1 X' Y') _ _ x). apply (hfiberpair _ _ _ _ x0 e). apply (initmap _ (negpathsii2ii1 _ _ _ _ x)). Defined. 


Theorem weqhfibercoprodf1 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(x':X'): weq (hfiber _ _ f x') (hfiber _ _ (coprodf _ _ _ _ f g) (ii1 _ _ x')).
Proof. intros.  set (ff:= fun xe: hfiber _ _ f x' => match xe with tpair x e => hfiberpair _ _ (coprodf _ _ _ _ f g) _ (ii1 X Y x) (maponpaths _ _ (ii1 X' Y') (f x) x' e) end). split with ff. set (gg:= fromhfibercoprodf1 _ _ _ _ f g x').
assert (egf: forall a:_, paths _ (gg (ff a)) a).  intro. destruct a as [ t x ].  simpl.  destruct x.  simpl. apply idpath. 
assert (efg: forall a:_, paths _ (ff (gg a)) a). intro. destruct a as [ t x ]. destruct t.  simpl in x. 
assert (eee: total2 (paths _ (f x0) x') (fun e:_ => paths _ (maponpaths _ _ (ii1 X' Y') _ _ e) x)). split with (invmaponpathsincl _ _ _ (isinclii1 X' Y') _ _ x).  apply (weqfg _ _ _ (isweqonpathsincl _ _ _ (isinclii1 X' Y') _ _ ) x).   destruct eee as [ t x1 ]. destruct x1. destruct t. apply idpath. 
simpl in x. apply (initmap _ (negpathsii2ii1 _ _ _ _  x)). 
apply (gradth _ _ _ _ egf efg). Defined.

(** !! For some reason Coq has to think a lot at the two [ apply idpath ] and at the [ Defined ] in the previous theorem. *) 




Definition fromhfibercoprodf2 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(y':Y'):(hfiber _ _ (coprodf _ _ _ _ f g) (ii2 _ _ y')) -> hfiber _ _ g y'.
Proof. intros X Y X' Y' f g y' X0. destruct X0 as [ t x ].  destruct t. apply (initmap _ (negpathsii1ii2 _ _ _ _ x)).  set (e:= invmaponpathsincl _ _ _ (isinclii2 X' Y') _ _ x). apply (hfiberpair _ _ _ _ y e). Defined. 




Theorem weqhfibercoprodf2 (X Y X' Y':UU)(f: X -> X')(g:Y -> Y')(y':Y'): weq (hfiber _ _ g y') (hfiber _ _ (coprodf _ _ _ _ f g) (ii2 _ _ y')).
Proof. intros.  set (ff:= fun xe: hfiber _ _ g y' => match xe with tpair y e => hfiberpair _ _ (coprodf _ _ _ _ f g) _ (ii2 X Y y) (maponpaths _ _ (ii2 X' Y') (g y) y' e) end). split with ff. set (gg:= fromhfibercoprodf2 _ _ _ _ f g y').
assert (egf: forall a:_, paths _ (gg (ff a)) a).  intro. destruct a as [ t x ].  simpl.  destruct x.  simpl. apply idpath. 
assert (efg: forall a:_, paths _ (ff (gg a)) a). intro. destruct a as [ t x ]. destruct t.  simpl in x. apply (initmap _ (negpathsii1ii2 _ _ _ _  x)). 
simpl in x. assert (eee: total2 (paths _ (g y) y') (fun e:_ => paths _ (maponpaths _ _ (ii2 X' Y') _ _ e) x)). split with (invmaponpathsincl _ _ _ (isinclii2 X' Y') _ _ x).  apply (weqfg _ _ _ (isweqonpathsincl _ _ _ (isinclii2 X' Y') _ _ ) x).   destruct eee as [ t x0 ]. destruct x0. destruct t. apply idpath. 
apply (gradth _ _ _ _ egf efg). Defined.

 

(** !! For some reason Coq has to think a lot at the two [ apply idpath ] and at the [ Defined ] in the previous theorem. *) 




(** *** Theorem saying that coproduct of two maps of h-level n is of h-level n. *)



Theorem isofhlevelfcoprodf (n:nat)(X Y Z T:UU)(f: X -> Z)(g: Y -> T)(is1: isofhlevelf n _ _ f)(is2: isofhlevelf n _ _ g): isofhlevelf n _ _  (coprodf _ _ _ _ f g).
Proof. intros. intro.  destruct y.  apply (isofhlevelweqf n _ _ _ (pr22 _ _ (weqhfibercoprodf1 _ _ _ _ f g z)) (is1 z)).  apply (isofhlevelweqf n _ _ _ (pr22 _ _ (weqhfibercoprodf2 _ _ _ _ f g t)) (is2 t)). Defined. 



(** *** Coprojections. *)



Definition isacoproj {X Y:UU}(f :X -> Y)(is: isincl _ _ f):= forall y:Y, coprod (hfiber _ _ f y) (neg (hfiber _ _ f y)). 

Lemma isacoprojii1 (X Y: UU): isacoproj (ii1 _ _) (isinclii1 X Y).
Proof. intros. unfold isacoproj. intro.  destruct y.   apply (ii1 _ _ (hfiberpair _ _ (ii1 _ _ ) (ii1 _ _ x) x (idpath _ _ ))). 
assert (int: (neg (hfiber X (coprod X Y) (ii1 X Y) (ii2 X Y y)))).  intro X0.  destruct X0 as [ t x ].  apply (negpathsii1ii2 _ _ _ _ x). apply (ii2 _ _ int).  Defined.  

 
Lemma isacoprojii2 (X Y: UU): isacoproj (ii2 _ _) (isinclii2 X Y).
Proof. intros. unfold isacoproj. intro.  destruct y.   
assert (int: (neg (hfiber Y (coprod X Y) (ii2 X Y) (ii1 X Y x)))).  intro X0.  destruct X0 as [ t x0 ].  apply (negpathsii1ii2 _ _ _ _ (pathsinv0 _ _ x0)). apply (ii2 _ _ int). apply (ii1 _ _ (hfiberpair _ _ (ii2 _ _ ) (ii2 _ _ y) y (idpath _ _ ))).   Defined.  







(** ** Some results on complements to a point *)


Definition complement (X:UU)(x:X):= total2 X (fun x':X => neg (paths _ x' x)).
Definition complementpair (X:UU)(x:X):= tpair X (fun x':X => neg (paths _ x' x)).


Definition recompl (X:UU)(x:X): coprod (complement X x) unit -> X := fun u:_ =>
match u with
ii1 x0 => pr21 _ _ x0|
ii2 tt => x
end.

Definition maponcomplementsincl (X:UU)(Y:UU)(f:X -> Y)(is: isofhlevelf 1 _ _ f)(x:X): complement X x -> complement Y (f x):= fun x0':_ =>
match x0' with
tpair x' neqx => tpair _ _ (f x') (negf (invmaponpathsincl _ _ _ is x' x) neqx)
end.

Definition maponcomplementsweq (X Y:UU)(f:X -> Y)(is: isweq _ _ f)(x:X):= maponcomplementsincl _ _ f (isofhlevelfweq 1 _ _ f is) x.


Theorem isweqmaponcomplements (X Y:UU)(f:X -> Y)(is: isweq _ _ f)(x:X): isweq _ _ (maponcomplementsweq _ _ f is x).
Proof. intros.  set (is1:= isofhlevelfweq 1 _ _ f is).   set (map1:= totalfun X (fun x':X => neg (paths _ x' x)) (fun x':X => neg (paths _ (f x') (f x))) (fun x':X => negf (invmaponpathsincl _ _ _ is1 x' x))). set (map2:= fpmap _ _ f (fun y:Y => neg (paths _ y (f x)))). 
assert (is2: forall x':X, isweq  _ _ (negf (invmaponpathsincl _ _ _ is1 x' x))). intro. 
set (invimpll:= (negf (maponpaths _ _ f x' x))). apply (isweqimplimpl _ _ (negf (invmaponpathsincl _ _ _ is1 x' x)) (negf (maponpaths _ _ f x' x)) (isapropneg _) (isapropneg _)). 
assert (is3: isweq _ _ map1). apply isweqfibtototal. assumption. 
assert (is4: isweq _ _ map2). apply (isweqfpmap _ _ f  (fun y:Y => neg (paths _ y (f x))) is).
assert (h: forall x0':_, paths _ (map2 (map1 x0')) (maponcomplementsweq _ _ f is x x0')). intro.  simpl. destruct x0'. simpl. apply idpath.
apply (isweqhomot _ _ _ _ h (twooutof3c _ _ _ _ _ is3 is4)).
Defined.


Definition weqoncomplements (X Y:UU)(x:X)(w: weq X Y): weq (complement X x) (complement Y (pr21 _ _ w x)):= weqpair _ (isweqmaponcomplements X Y (pr21 _ _ w) (pr22 _ _ w) x).




Definition tocompltoii1x (X Y:UU)(x:X): coprod (complement X x) Y -> complement (coprod X Y) (ii1 _ _ x).
Proof. intros X Y x X0. destruct X0.  split with (ii1 _ _ (pr21 _ _ c)). 

assert (e: neg(paths _ (pr21 _ _ c) x)). apply (pr22 _ _ c). apply (negf (invmaponpathsincl _ _ (ii1 _ _) (isinclii1 X Y) _ _) e). 
split with (ii2 _ _ y). apply (negf (pathsinv0 _ _) (negpathsii1ii2 X Y x y)). Defined.



Definition fromcompltoii1x (X Y:UU)(x:X): complement (coprod X Y) (ii1 _ _ x) ->  coprod (complement X x) Y.
Proof. intros X Y x X0. destruct X0 as [ t x0 ].  destruct t as [ x1 | y ]. 
assert (ne: neg (paths _ x1 x)). apply (negf (maponpaths _ _ (ii1 _ _) _ _) x0). apply (ii1 _ _ (complementpair _ _ x1 ne)). apply (ii2 _ _ y). Defined. 


Theorem isweqtocompltoii1x (X Y:UU)(x:X): isweq _ _ (tocompltoii1x X Y x).
Proof. intros. set (f:= tocompltoii1x X Y x). set (g:= fromcompltoii1x X Y x).
assert (egf:forall nexy:_ , paths _ (g (f nexy)) nexy). intro. destruct nexy as [ c | y ]. destruct c as [ t x0 ]. simpl. 
assert (e: paths _ (negf 
              (maponpaths _ _ (ii1 X Y) t x)
              (negf 
                 (invmaponpathsincl X (coprod X Y) 
                    (ii1 X Y) (isinclii1 X Y) t x) x0)) x0). apply (isapropneg (paths _ t x) _ _). 
apply (maponpaths _ _ (fun ee: neg(paths _ t x) => ii1 _ _ (complementpair X x t ee)) _ _ e). 
apply idpath.
assert (efg: forall neii1x:_, paths _ (f (g neii1x)) neii1x). intro.  destruct neii1x as [ t x0 ]. destruct t as [ x1 | y ].  simpl. 
assert (e: paths _  (negf 
           (invmaponpathsincl X (coprod X Y) (ii1 X Y) (isinclii1 X Y) x1 x)
           (negf 
              (maponpaths _ _ (ii1 X Y) x1 x) x0)) x0). apply (isapropneg (paths _ _ _)  _ _).
apply (maponpaths _ _ (fun ee: (neg (paths _ (ii1 X Y x1) (ii1 X Y x))) => (complementpair _ _ (ii1 X Y x1) ee)) _ _ e). 
simpl. 
assert (e: paths _ (negf 
           (pathsinv0 (ii2 X Y y) (ii1 X Y x))
           (negpathsii1ii2 X Y x y)) x0). apply (isapropneg (paths _ _ _) _ _).
apply (maponpaths _ _ (fun ee: (neg (paths _ (ii2 X Y y) (ii1 X Y x))) => (complementpair _ _ (ii2 X Y y) ee)) _ _ e). 
apply (gradth _ _ f g egf efg). Defined.






Definition tocompltoii2y (X Y:UU)(y:Y): coprod X (complement Y y) -> complement (coprod X Y) (ii2 _ _ y).
Proof. intros X Y y X0. destruct X0 as [ x | c ]. 
split with (ii1 _ _ x). apply (negf (pathsinv0 _ _) (negpathsii2ii1 X Y x y)). 
split with (ii2 _ _ (pr21 _ _ c)). 
assert (e: neg(paths _ (pr21 _ _ c) y)). apply (pr22 _ _ c). apply (negf (invmaponpathsincl _ _ (ii2 _ _) (isinclii2 X Y) _ _) e). 
Defined.



Definition fromcompltoii2y (X Y:UU)(y:Y): complement (coprod X Y) (ii2 _ _ y) ->  coprod X (complement Y y).
Proof. intros X Y y X0. destruct X0 as [ t x ].  destruct t as [ x0 | y0 ]. apply (ii1 _ _ x0). 
assert (ne: neg (paths _ y0 y)). apply (negf (maponpaths _ _ (ii2 _ _) _ _) x). apply (ii2 _ _ (complementpair _ _ y0 ne)). Defined. 


Theorem isweqtocompltoii2y (X Y:UU)(y:Y): isweq _ _ (tocompltoii2y X Y y).
Proof. intros. set (f:= tocompltoii2y X Y y). set (g:= fromcompltoii2y X Y y).
assert (egf:forall nexy:_ , paths _ (g (f nexy)) nexy). intro. destruct nexy as [ x | c ]. 
apply idpath.
destruct c as [ t x ]. simpl. 
assert (e: paths _ (negf 
              (maponpaths _ _ (ii2 X Y) t y)
              (negf 
                 (invmaponpathsincl _ (coprod X Y) 
                    (ii2 X Y) (isinclii2 X Y) t y) x)) x). apply (isapropneg (paths _ t y) _ _). 
apply (maponpaths _ _ (fun ee: neg(paths _ t y) => ii2 _ _ (complementpair _ y t ee)) _ _ e). 
assert (efg: forall neii2x:_, paths _ (f (g neii2x)) neii2x). intro.  destruct neii2x as [ t x ]. destruct t as [ x0 | y0 ].  simpl. 

assert (e: paths _ (negf 
           (pathsinv0 (ii1 X Y x0) (ii2 X Y y))
           (negpathsii2ii1 X Y x0 y)) x). apply (isapropneg (paths _ _ _) _ _).
apply (maponpaths _ _ (fun ee: (neg (paths _ (ii1 X Y x0) (ii2 X Y y))) => (complementpair _ _ (ii1 X Y x0) ee)) _ _ e). 
simpl.

assert (e: paths _  (negf 
           (invmaponpathsincl _ (coprod X Y) _ (isinclii2 X Y) y0 y)
           (negf 
              (maponpaths _ _ (ii2 X Y) y0 y) x)) x). apply (isapropneg (paths _ _ _)  _ _).
apply (maponpaths _ _ (fun ee: (neg (paths _ (ii2 X Y y0) (ii2 X Y y))) => (complementpair _ _ (ii2 X Y y0) ee)) _ _ e). 
 
apply (gradth _ _ f g egf efg). Defined.












Definition tocompltodisjoint (X:UU): X -> complement (coprod X unit) (ii2 _ _ tt) := fun x:_ => complementpair _ _ (ii1 _ _ x) (negpathsii1ii2 _ _ x tt).

Definition fromcompltodisjoint (X:UU): complement (coprod X unit) (ii2 _ _ tt) -> X.
Proof. intros X X0. destruct X0 as [ t x ].  destruct t. assumption.  destruct u. apply (initmap _ (x (idpath _ (ii2 X _ tt)))). Defined.


Lemma isweqtocompltodisjoint (X:UU): isweq _ _ (tocompltodisjoint X).
Proof. intros. set (ff:= tocompltodisjoint X). set (gg:= fromcompltodisjoint X). 
assert (egf: forall x:X, paths _ (gg (ff x)) x).  intro.  apply idpath.
assert (efg: forall xx:_, paths _ (ff (gg xx)) xx). intro. destruct xx as [ t x ].  destruct t.   simpl.  unfold ff. unfold tocompltodisjoint. simpl. assert (ee: paths _  (negpathsii1ii2 X unit x0 tt) x).  apply (proofirrelevance _ (isapropneg _) _ _). induction ee. apply idpath. destruct u.  simpl. apply (initmap _ (x (idpath _ _))). apply (gradth _ _ ff gg egf efg).  Defined. 

Corollary isweqfromcompltodisjoint (X:UU): isweq _ _ (fromcompltodisjoint X).
Proof. intros. apply (isweqinvmap _ _ _ (isweqtocompltodisjoint X)). Defined. 















(* Coprojections i.e. functions which are weakly equivalent to functions of the form ii1: X -> coprod X Y 


Definition locsplit (X:UU)(Y:UU)(f:X -> Y):= forall y:Y, coprod (hfiber _ _ f y) (hfiber _ _ f y -> empty).

Definition dnegimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => dneg(hfiber _ _ f y)).
Definition dnegimageincl (X Y:UU)(f:X -> Y):= pr21 Y (fun y:Y => dneg(hfiber _ _ f y)).

Definition xtodnegimage (X:UU)(Y:UU)(f:X -> Y): X -> dnegimage _ _ f:= fun x:X => tpair _ _ (f x) ((todneg _) (hfiberpair _ _ f (f x) x (idpath _ (f x)))). 

Definition locsplitsec (X:UU)(Y:UU)(f:X->Y)(ls: locsplit _ _ f): dnegimage _ _ f -> X := fun u: _ =>
match u with
tpair y psi =>
match (ls y) with 
ii1 z => pr21 _ _ z|
ii2 phi => initmap _ (psi phi)
end
end.


Definition locsplitsecissec  (X Y:UU)(f:X->Y)(ls: locsplit _ _ f)(u:dnegimage _ _ f): paths _ (xtodnegimage _ _ f (locsplitsec _ _ f ls u)) u.
Proof. intros.  set (p:= xtodnegimage _ _ f). set (s:= locsplitsec _ _ f ls).  
assert (paths _ (pr21 _ _ (p (s u))) (pr21 _ _ u)). unfold p. unfold xtodnegimage. unfold s. unfold locsplitsec. simpl. induction u. set (lst:= ls t). induction lst.  simpl. apply (pr22 _ _ x0). induction (x y).  
assert (is: isofhlevelf 1 _ _ (dnegimageincl _ _ f)). apply (isofhlevelfpr21 1 _ _ (fun y:Y => isapropdneg (hfiber _ _ f y))).  
assert (isw: isweq _ _ (maponpaths _ _ (dnegimageincl _ _ f) (p (s u)) u)). apply (isofhlevelfonpaths O _ _ _ _ _ is). 
apply (invmap _ _ _ isw X0). Defined.



Definition negimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => neg(hfiber _ _ f y)).
Definition negimageincl (X Y:UU)(f:X -> Y):= pr21 Y (fun y:Y => neg(hfiber _ _ f y)).


Definition imsum (X:UU)(Y:UU)(f:X -> Y): coprod (dnegimage _ _ f) (negimage _ _ f) -> Y:= fun u:_ =>
match u with
ii1 z => pr21 _ _ z|
ii2 z => pr21 _ _ z
end.

*)
 




(** ** Some results on types with an isolated point. *)


Definition isisolated (X:UU)(x:X):= forall x':X, decidable (paths _ x' x).

Lemma disjointl1 (X:UU): isisolated (coprod X unit) (ii2 _ _ tt).
Proof. intros.
   unfold isisolated. intros.  destruct x'. apply no. apply negpathsii1ii2.
   destruct u.  apply yes.  apply idpath.  
Defined.

Lemma isolatedtoisolatedii1 (X Y:UU)(x:X)(is:isisolated _ x): isisolated _ (ii1 X Y x).
Proof. intros.  intro.
   destruct x'. 
      destruct (is x0) as [|e].  
            apply yes. apply maponpaths. assumption.
            apply no. apply (negf (invmaponpathsincl _ _ (ii1 X Y) (isinclii1 X Y) _ _ ) e).
      apply no. apply negpathsii2ii1.
Defined. 

Lemma isolatedtoisolatedii2 (X Y:UU)(y:Y)(is:isisolated _ y): isisolated _ (ii2 X Y y).
Proof. intros.  intro.  
   destruct x'.
       apply no. apply negpathsii1ii2.
       destruct (is y0) as [ | e].
          apply yes. apply maponpaths. assumption.
          apply no.  exact (negf (invmaponpathsincl _ _ (ii2 X Y) (isinclii2 X Y) _ _ ) e).
Defined. 

Lemma isolatedifisolatedii1 (X Y:UU)(x:X)(is: isisolated _ (ii1 X Y x)): isisolated _ x.
Proof. intros. intro.  
   destruct (is (ii1 _ _ x')) as [ | e ].  
        apply yes.  exact (invmaponpathsincl _ _ _ (isinclii1 _ _) _ _ p).
        apply no.   exact (negf (maponpaths _ _ (ii1 _ _) _ _) e).
Defined. 

Lemma isolatedifisolatedii2 (X Y:UU)(y:Y)(is: isisolated _ (ii2 X Y y)): isisolated _ y.
Proof. intros. intro y'.
    destruct (is (ii2 _ _ y')) as [p|e].
         apply yes. exact (invmaponpathsincl _ _ _ (isinclii2 _ _) _ _ p).
         apply no.  exact (negf (maponpaths _ _ (ii2 _ _) _ _) e).
Defined. 

Definition recomplinv (X:UU)(x:X)(is: isisolated X x): X -> coprod (complement X x) unit:=
    fun x':X => match (is x') with
        yes e => ii2 _ _ tt|
        no  phi => ii1 _ _ (complementpair _ _ x' phi)
    end.

Theorem isweqrecompl (X:UU)(x:X)(is:isisolated X x): isweq _ _ (recompl X x).
Proof.
  intros.
  set (f:= recompl X x).
  set (g:= recomplinv X x is).
  unfold recomplinv in g.
  simpl in g.
  assert (efg: forall x':X, paths _ (f (g x')) x').
    intro.
    induction (is x') as [|y].
      induction x0.
      unfold f.
      unfold g.
      simpl.
      unfold recompl.
      simpl.
      induction (is x') as [|y].
        simpl.
        apply idpath.
      induction (y (idpath _ x')).
    unfold f.
    unfold g.
    simpl.
    unfold recompl.
    simpl.
    induction (is x').
      induction (y x0).
    simpl.
    apply idpath.
  assert (egf: forall u: coprod  (complement X x) unit, paths _ (g (f u)) u).
    unfold isisolated in is.
    intro.
    destruct (is (f u)).
      destruct u as [ c | u].
        simpl.
        destruct c as [ t x0 ].
        simpl in p.
        destruct (x0 p).
      destruct u.
      assert (e1: paths _  (g (f (ii2 (complement X x) unit tt))) (g x)).
        apply (maponpaths _ _ g _ _ p).
      assert (e2: paths _ (g x) (ii2 (complement X x) unit tt)).
        unfold g.
        destruct (is x).
          apply idpath.
        destruct (n (idpath _ x)).
      apply (pathscomp0 _ _ _ _ e1 e2).
    destruct u.
      simpl.
      destruct c as [ t x0 ].
      simpl.
      unfold isisolated in is.
      unfold g.
      destruct (is t).
        destruct (x0 p).
      simpl in g.
      unfold f.
      unfold recompl.
      simpl in n.
      assert (ee: paths _ n0 x0).
        apply (proofirrelevance _ (isapropneg (paths _ t x))).
      induction ee.
      apply idpath.
    unfold f.
    unfold g.
    simpl.
    induction u.
    induction (is x).
      apply idpath.
    induction (n0 (idpath _ x)).
  apply (gradth _ _ f g egf efg).
Defined.

Lemma isolatedtoisolated (X:UU)(Y:UU)(f:X -> Y)(is1:isweq _ _ f)(x:X)(is2: isisolated _ x): isisolated _ (f x).
Proof.  intros. unfold isisolated. intro. rename x' into y.  set (g:=invmap _ _ f is1). set (x':= g y). induction (is2 x').  apply (yes _ (pathsinv0 _ _ (pathsweq1' _ _ f is1 x y (pathsinv0 _ _ x0)))). 
assert (phi: neg (paths _ y (f x))). 
assert (psi: neg (paths _ (g y) x) -> neg (paths _ y (f x))). intro. intro.  apply (X0  (pathsinv0 _ _ (pathsweq1 _ _ f is1 x y (pathsinv0 _ _ X1)))). apply (psi n). apply (no _ phi). Defined.

(* End of the file uu0.v *)

(* 
 Local Variables: 
 compile-command: "make -C ../.. Main_Library/Generalities/uu0.vo "
 End: 
 *)
