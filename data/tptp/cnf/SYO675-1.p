%------------------------------------------------------------------------------
% File     : SYO675-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_4_0_3
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_4_0_3 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.3.0
% Syntax   : Number of clauses     :   30 (   2 unt;  16 nHn;  29 RR)
%            Number of literals    :  106 (   0 equ;  65 neg)
%            Maximal clause size   :    6 (   3 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :   29 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_11,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4)) ) ).

cnf(clause_27,axiom,
    ( ~ 'LE'(f(suc(suc(B_1))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_1))))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_20,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_2)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_2)))))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_31,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_10,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_0)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_0)))))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_23,axiom,
    ( ~ 'LE'(f(suc(B_2)),s('0'))
    | 'E'('0',f(suc(B_2)))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_26,axiom,
    ( ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_29,axiom,
    ( ~ 'LE'(f(B_0),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_0))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_14,axiom,
    ( ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_25,axiom,
    ( ~ 'LE'(f(suc(B_1)),s(s('0')))
    | 'E'(s('0'),f(suc(B_1)))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_18,axiom,
    ( ~ 'LE'(f(suc(suc(B_0))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_0))))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_19,axiom,
    ( ~ 'LE'(f(suc(B_0)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_0)))
    | 'LE'(f(B_0),s(s('0'))) ) ).

cnf(clause_24,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_2,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_37,axiom,
    ( ~ 'LE'(f(suc(suc(B_2))),s('0'))
    | 'E'('0',f(suc(suc(B_2))))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_13,axiom,
    ( ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_17,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_21,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_1,axiom,
    ( ~ 'LE'(f(suc(suc(B))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B))))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_36,axiom,
    ( ~ 'LE'(f(B),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_15,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_1)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_1)))))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_5,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3)))) ) ).

cnf(clause_4,axiom,
    ( ~ 'LE'(f(B_2),s('0'))
    | 'E'('0',f(B_2))
    | 'LE'(f(B_2),'0') ) ).

cnf(clause_8,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1))) ) ).

cnf(clause_32,axiom,
    ( ~ 'LE'(f(suc(B)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B)))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_16,axiom,
    ( ~ 'LE'(f(B_1),s(s('0')))
    | 'E'(s('0'),f(B_1))
    | 'LE'(f(B_1),s('0')) ) ).

cnf(clause_7,axiom,
    ( ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4)))) ) ).

cnf(clause_6,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B)))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(B)))))
    | 'LE'(f(B),s(s(s('0')))) ) ).

cnf(clause_34,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_30,axiom,
    'LE'(f(A),s(s(s(s('0'))))) ).

%------------------------------------------------------------------------------
