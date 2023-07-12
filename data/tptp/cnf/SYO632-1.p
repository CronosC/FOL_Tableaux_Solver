%------------------------------------------------------------------------------
% File     : SYO632-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : NDClauseSet1
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : NDClauseSet1 [Cer17]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   1 RR)
%            Number of literals    :    6 (   0 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :    7 (   6 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%------------------------------------------------------------------------------
cnf(clause_4_01,axiom,
    'LEQ'('AP'('0',K),'AP'(s(s('0')),K)) ).

cnf(clause_2_02,axiom,
    'E'(f('AP'(s(s('0')),K)),'0') ).

cnf(clause_0_03,axiom,
    'E'(f(B),s('0')) ).

cnf(clause_1_04,axiom,
    ( ~ 'E'(f(A_0),'0')
    | ~ 'E'(f(B_0),s('0')) ) ).

cnf(clause_3_05,axiom,
    'LEQ'('AP'(s('0'),K),B) ).

%------------------------------------------------------------------------------
