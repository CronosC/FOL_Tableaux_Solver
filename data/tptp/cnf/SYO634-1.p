%------------------------------------------------------------------------------
% File     : SYO634-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : NDClauseSet10
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : NDClauseSet10 [Cer17]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0
% Syntax   : Number of clauses     :   23 (   4 unt;   0 nHn;   5 RR)
%            Number of literals    :  141 (   0 equ; 119 neg)
%            Maximal clause size   :   11 (   6 avg)
%            Maximal term depth    :   14 (   4 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-2 aty)
%            Number of variables   :  139 ( 126 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%------------------------------------------------------------------------------
cnf(clause_21_01,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | 'E'(f(B_0),s(s(s(s(s(s(s(s('0'))))))))) ) ).

cnf(clause_14_02,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(A_8),s('0'))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_7),s(s('0')))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_6),s(s(s('0'))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'LEQ'('AP'('0',K),'AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)) ) ).

cnf(clause_11_03,axiom,
    'E'(f(B),s(s(s(s(s(s(s(s(s(s('0'))))))))))) ).

cnf(clause_4_04,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_6),s(s(s('0'))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'LEQ'('AP'(s(s('0')),K),'AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)) ) ).

cnf(clause_7_05,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | 'LEQ'('AP'(s(s(s(s(s(s(s(s('0')))))))),K),B_0) ) ).

cnf(clause_1_06,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | 'E'(f(B_0),s(s(s(s(s(s('0'))))))) ) ).

cnf(clause_5_07,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'LEQ'('AP'(s(s(s('0'))),K),'AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)) ) ).

cnf(clause_20_08,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'LEQ'('AP'(s(s(s(s('0')))),K),'AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)) ) ).

cnf(clause_17_09,axiom,
    'E'(f(B_0),s(s(s(s(s(s(s(s(s('0')))))))))) ).

cnf(clause_16_10,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_7),s(s('0')))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_6),s(s(s('0'))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'LEQ'('AP'(s('0'),K),'AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)) ) ).

cnf(clause_8_11,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_7),s(s('0')))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_6),s(s(s('0'))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'E'(f('AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)),s('0')) ) ).

cnf(clause_9_12,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'E'(f('AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)),s(s(s(s('0'))))) ) ).

cnf(clause_6_13,axiom,
    'LEQ'('AP'(s(s(s(s(s(s(s(s(s('0'))))))))),K),B_0) ).

cnf(clause_12_14,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | 'E'(f(B_0),s(s(s(s(s(s(s('0')))))))) ) ).

cnf(clause_18_15,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'E'(f('AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)),s(s(s('0')))) ) ).

cnf(clause_2_16,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | 'LEQ'('AP'(s(s(s(s(s(s('0')))))),K),B_0) ) ).

cnf(clause_3_17,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(A_8),s('0'))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_7),s(s('0')))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_6),s(s(s('0'))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | ~ 'E'(f(A_9),'0') ) ).

cnf(clause_13_18,axiom,
    ( ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | 'LEQ'('AP'(s(s(s(s(s(s(s('0'))))))),K),B_0) ) ).

cnf(clause_0_19,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_6),s(s(s('0'))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'E'(f('AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)),s(s('0'))) ) ).

cnf(clause_15_20,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'E'(f(B_0),s(s(s(s(s('0')))))) ) ).

cnf(clause_22_21,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'LEQ'('AP'(s(s(s(s(s('0'))))),K),B_0) ) ).

cnf(clause_10_22,axiom,
    ( ~ 'E'(f(A_1),s(s(s(s(s(s(s(s('0')))))))))
    | ~ 'E'(f(A_4),s(s(s(s(s('0'))))))
    | ~ 'E'(f(A_8),s('0'))
    | ~ 'E'(f(B_0),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ 'E'(f(A_5),s(s(s(s('0')))))
    | ~ 'E'(f(A_7),s(s('0')))
    | ~ 'E'(f(A_2),s(s(s(s(s(s(s('0'))))))))
    | ~ 'E'(f(A_6),s(s(s('0'))))
    | ~ 'E'(f(A_0),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ 'E'(f(A_3),s(s(s(s(s(s('0')))))))
    | 'E'(f('AP'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))),K)),'0') ) ).

cnf(clause_19_23,axiom,
    'LEQ'('AP'(s(s(s(s(s(s(s(s(s(s('0')))))))))),K),B) ).

%------------------------------------------------------------------------------
