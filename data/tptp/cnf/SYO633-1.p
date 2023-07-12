%------------------------------------------------------------------------------
% File     : SYO633-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : NDClauseSet5
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : NDClauseSet5 [Cer17]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0
% Syntax   : Number of clauses     :   13 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :   46 (   0 equ;  34 neg)
%            Maximal clause size   :    6 (   3 avg)
%            Maximal term depth    :    9 (   3 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :   47 (  42 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%------------------------------------------------------------------------------
cnf(clause_3_01,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | ~ 'E'(f(A_1),s(s(s('0'))))
    | 'LEQ'('AP'(s(s('0')),K),'AP'(s(s(s(s(s(s('0')))))),K)) ) ).

cnf(clause_0_02,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | ~ 'E'(f(A_1),s(s(s('0'))))
    | ~ 'E'(f(A_2),s(s('0')))
    | 'LEQ'('AP'(s('0'),K),'AP'(s(s(s(s(s(s('0')))))),K)) ) ).

cnf(clause_5_03,axiom,
    ( ~ 'E'(f(A_2),s(s('0')))
    | ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(A_1),s(s(s('0'))))
    | ~ 'E'(f(A_3),s('0'))
    | ~ 'E'(f(A_4),'0')
    | ~ 'E'(f(B_0),s(s(s(s(s('0')))))) ) ).

cnf(clause_6_04,axiom,
    'E'(f(B_0),s(s(s(s('0'))))) ).

cnf(clause_8_05,axiom,
    'E'(f(B),s(s(s(s(s('0')))))) ).

cnf(clause_11_06,axiom,
    'LEQ'('AP'(s(s(s(s('0')))),K),B_0) ).

cnf(clause_2_07,axiom,
    ( ~ 'E'(f(A_2),s(s('0')))
    | ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(A_1),s(s(s('0'))))
    | ~ 'E'(f(A_3),s('0'))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | 'E'(f('AP'(s(s(s(s(s(s('0')))))),K)),'0') ) ).

cnf(clause_7_08,axiom,
    'LEQ'('AP'(s(s(s(s(s('0'))))),K),B) ).

cnf(clause_12_09,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | ~ 'E'(f(A_1),s(s(s('0'))))
    | ~ 'E'(f(A_2),s(s('0')))
    | 'E'(f('AP'(s(s(s(s(s(s('0')))))),K)),s('0')) ) ).

cnf(clause_1_10,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | 'E'(f(B_0),s(s(s('0')))) ) ).

cnf(clause_9_11,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | 'LEQ'('AP'(s(s(s('0'))),K),B_0) ) ).

cnf(clause_4_12,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | ~ 'E'(f(A_1),s(s(s('0'))))
    | 'E'(f('AP'(s(s(s(s(s(s('0')))))),K)),s(s('0'))) ) ).

cnf(clause_10_13,axiom,
    ( ~ 'E'(f(A_2),s(s('0')))
    | ~ 'E'(f(A_0),s(s(s(s('0')))))
    | ~ 'E'(f(A_1),s(s(s('0'))))
    | ~ 'E'(f(A_3),s('0'))
    | ~ 'E'(f(B_0),s(s(s(s(s('0'))))))
    | 'LEQ'('AP'('0',K),'AP'(s(s(s(s(s(s('0')))))),K)) ) ).

%------------------------------------------------------------------------------
