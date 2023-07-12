%------------------------------------------------------------------------------
% File     : LCL926-1 : TPTP v8.1.2. Released v6.4.0.
% Domain   : Logic Calculi (Postive sential logic)
% Problem  : IO in TW+ [AxL,AxTO]
% Version  : [Sla02] axioms.
% English  : 

% Refs     : [Sla02] Slaney (2002), More Proofs of an Axiom of Lukasiewicz
% Source   : [Sla02]
% Names    : 

% Status   : Unsatisfiable
% Rating   : 1.00 v6.4.0
% Syntax   : Number of clauses     :    7 (   6 unt;   0 nHn;   2 RR)
%            Number of literals    :    9 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   13 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%------------------------------------------------------------------------------
cnf(modus_ponens,axiom,
    ( ~ p(i(A,B))
    | ~ p(A)
    | p(B) ) ).

cnf(axBp,axiom,
    p(i(i(A,B),i(i(B,C),i(A,C)))) ).

cnf(axL,axiom,
    p(i(i(i(X,Y),Y),i(i(Y,X),X))) ).

cnf(axTO,axiom,
    p(i(i(i(X,Y),i(Y,X)),i(Y,X))) ).

cnf(axorI1,axiom,
    p(i(X,or(X,Y))) ).

cnf(axorI2,axiom,
    p(i(Y,or(X,Y))) ).

cnf(io,negated_conjecture,
    ~ p(i(i(i(x,y),y),or(x,y))) ).

%------------------------------------------------------------------------------
