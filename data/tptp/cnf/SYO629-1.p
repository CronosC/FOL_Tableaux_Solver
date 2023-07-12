%------------------------------------------------------------------------------
% File     : SYO629-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : ECSClauseSet1
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [CL16]  Cerna & Leitsch (2016), Schematic Cut Elimination and
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : ECSClauseSet1 [Cer17]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.1.0
% Syntax   : Number of clauses     :   12 (   8 unt;   2 nHn;   7 RR)
%            Number of literals    :   20 (   0 equ;  10 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-1 aty)
%            Number of variables   :   13 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%------------------------------------------------------------------------------
cnf(clause_8_01,axiom,
    ~ 'E'(f(A_3),f(g(A_3))) ).

cnf(clause_0_02,axiom,
    iLEQ(A_3,A_3) ).

cnf(clause_11_03,axiom,
    ( ~ 'E'('0',f(A_3))
    | ~ 'E'('0',f(g(A_3)))
    | 'E'(f(A_3),f(g(A_3))) ) ).

cnf(clause_6_04,axiom,
    ( 'E'(s('0'),f(A))
    | 'LE'(f(A),s('0')) ) ).

cnf(clause_7_05,axiom,
    ~ 'LE'(f(A_3),'0') ).

cnf(clause_10_06,axiom,
    ( ~ 'LE'(f(A_1),s('0'))
    | ~ iLEQ(A_1,B_0)
    | 'E'('0',f(B_0))
    | 'LE'(f(B_0),'0') ) ).

cnf(clause_1_07,axiom,
    ( ~ 'E'(s('0'),f(A_2))
    | ~ 'E'(s('0'),f(g(A_2)))
    | 'E'(f(A_2),f(g(A_2))) ) ).

cnf(clause_2_08,axiom,
    ~ 'LE'(f(g(A_3)),'0') ).

cnf(clause_3_09,axiom,
    iLEQ(A_3,g(A_3)) ).

cnf(clause_5_10,axiom,
    iLEQ(A_2,g(A_2)) ).

cnf(clause_4_11,axiom,
    ~ 'E'(f(A_2),f(g(A_2))) ).

cnf(clause_9_12,axiom,
    iLEQ(A_2,A_2) ).

%------------------------------------------------------------------------------
